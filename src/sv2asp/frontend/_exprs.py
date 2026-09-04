from __future__ import annotations

import re


from ._stmts import _has_implicit_lane_ref, _has_lane_index
from ..ir.expr import (
    BinOp, BitSel, Concat, Cond, Const, ElemSel, EnumCast, Expr, LaneIdx, MemRef,
    Ref, SExt, Slice, Tag, UnOp,
    XVal,
)
from ..ir.nodes import CombItem, EdgeItem, Loc, Signal
from ..ir.types import IRType, Kind
from ._common import _BINOP, _CMP_OPS, _UNOP, _enum_name


def _lit_intake(has_unknown: bool, value: int, width: int) -> tuple[str, int]:
    """THE value-literal intake decision, as a pure function: ("refused", 0) when the literal
    carries x/z bits, ("value", value masked to width) otherwise.

    This is Fix 87's decision made checkable: int() on an unknown SVInt silently returns 0, so
    before the fix `8'hxx` FOLDED to the value 0 with a clean run. Now an unknown literal is
    refused loudly (the caller raises; the lowering safety net turns that into a coverage
    PROBLEM) and a known literal is masked to its width -- never a third outcome.

    Mirrored in Lean as `Xinit.litIntake`; checked against THIS function on every literal the
    translator really converts AND exhaustively (proofs/gen_xinit_lean.py). The exact-X reading
    of an unknown literal (an open value) is designed, not adopted (WORKLIST B6.3 note in
    notes/design/X_SEMANTICS.md)."""
    if has_unknown:
        return ("refused", 0)
    return ("value", value % (2 ** width))


_BOOL_NODE_OPS = frozenset(("eq", "ne", "lt", "le", "gt", "ge", "logand", "logor"))


def _has_bool_node(e: Expr) -> bool:
    """True if `e` contains a comparison, a logical op, a `lnot` or a nested ternary anywhere --
    the nodes the word cascade cannot lower and the bit emitter can."""
    if isinstance(e, BinOp):
        return e.op in _BOOL_NODE_OPS or _has_bool_node(e.left) or _has_bool_node(e.right)
    if isinstance(e, UnOp):
        return e.op == "lnot" or _has_bool_node(e.operand)
    if isinstance(e, Cond):
        return True
    for a in ("operand", "base"):
        if isinstance(getattr(e, a, None), Expr) and _has_bool_node(getattr(e, a)):
            return True
    for a in ("args", "parts"):
        if isinstance(getattr(e, a, None), (tuple, list)) and any(
                isinstance(x, Expr) and _has_bool_node(x) for x in getattr(e, a)):
            return True
    return False


class _NotAffineRead(Exception):
    """The window read must fold, not lower symbolically."""


class _ExprMixin:
    """_ExprMixin: exprs methods of PyslangFrontend (split out from the monolith)."""

    def _member_name(self, e) -> str:
        """A struct field reference p.f -> the subsignal name `p(f)`."""
        return f"{self._peel(e.value).symbol.name}({e.member.name})"

    def _member_chain(self, e) -> tuple[str, list]:
        """Walk a MemberAccess chain to its root: return (root_name, [members root-first])."""
        members = []
        cur = self._peel(e)
        while _enum_name(cur.kind) == "MemberAccess":
            members.append(cur.member)
            cur = self._peel(cur.value)
        members.reverse()
        return cur.symbol.name, members

    def _member_ref(self, e) -> Expr:
        """Read a struct field. ``p.f`` -> the subsignal ``Ref(p(f))``. A NESTED field ``p.a.x``
        keeps the one-level subsignal ``p(a)`` and slices it by the inner member offset(s) -- so
        the flat per-field model needs no recursive decomposition."""
        root, members = self._member_chain(e)
        subsig = f"{root}({members[0].name})"
        if len(members) == 1:
            return Ref(subsig)
        off = sum(m.bitOffset for m in members[1:])          # offset within the first-level field
        w = getattr(getattr(e, "type", None), "bitWidth", 1) or 1
        return Slice(Ref(subsig), off + w - 1, off)

    def _nest_path(self, parts: list[str], subst: dict[str, str] | None) -> str:
        """Build the instance-qualified functor from a (de-indexed) path: a.b.sig -> a(b(sig)).
        An absolute path led by the top module name drops that lead (the top is the bare scope);
        ``subst`` maps a leading interface-PORT formal to the actual connected instance."""
        parts = list(parts)
        if self._top and parts[0] == self._top:
            parts = parts[1:]
        parts[0] = (subst or {}).get(parts[0], parts[0])
        name = parts[-1]
        for inst in reversed(parts[:-1]):
            name = f"{inst}({name})"
        return name

    @staticmethod
    def _split_sel(p: str) -> tuple[str, str | None]:
        """Split a path element ``u_arr[1]`` into (``u_arr``, ``1``); a plain ``acc`` -> (``acc``, None)."""
        i = p.find("[")
        if i < 0:
            return p, None
        if not p.endswith("]"):
            raise NotImplementedError(f"malformed indexed path element {p!r}")
        return p[:i].strip(), p[i + 1:-1].strip()

    def _hier_name(self, e, subst: dict[str, str] | None = None) -> str:
        """Resolve a hierarchical reference -- ``inst.member`` (an interface signal access) OR a
        multi-level reach into submodule state ``a.b.…sig`` -- to the flat instance-qualified functor
        ``a(b(…(sig)))``: the SAME nested form flattening produces (``val(u_outer(u_inner(sig)),V,T)``),
        so a hand path and a flattened signal name coincide. The path is interpreted relative to the
        current scope; an absolute path led by the top module name (``top.u_sub.sig``) drops that lead.
        ``subst`` maps a submodule interface-PORT formal to the actual connected instance. INDEXED
        instance-array elements (``arr[i].sig``) are rejected here (a hierarchical WRITE into an array
        element is a backdoor driver); reads go through ``_hier_ref``."""
        txt = str(e.syntax).strip() if getattr(e, "syntax", None) is not None else ""
        if "[" in txt:
            raise NotImplementedError(f"indexed hierarchical reference {txt!r}")
        parts = [p.strip() for p in txt.split(".")]
        if len(parts) < 2 or not all(parts):
            raise NotImplementedError(f"hierarchical reference {txt!r}")
        return self._nest_path(parts, subst)

    def _hier_ref(self, e, subst: dict[str, str] | None = None) -> Expr:
        """Lower a hierarchical reference READ to an IR expression. A plain path -> ``Ref`` of the
        nested functor (``_hier_name``). An INDEXED instance-array element ``u_arr[i].sig`` -> the
        per-lane read ``ElemSel(u_arr(sig), i)`` (emits ``val(u_arr(sig), i, V, T)``): the array index
        IS the lane (catalog §4.6), the same INDEXED signal the array's lane-rolled body drives. Only
        a constant lane index is modeled (a runtime cross-hierarchy index flags)."""
        txt = str(e.syntax).strip() if getattr(e, "syntax", None) is not None else ""
        if "[" not in txt:
            name = self._hier_name(e, subst)
            # MODULAR: a read into a child's state (`u.q`) names the flat functor `u(q)`, which no
            # modular spec derives (the child's `q` lives at `val(u, q, ..)`). Record it so the
            # instance manifest bridges the two -- without that it was a dark read (caught by the
            # composed dark-read check, so it was loud, not silent).
            if getattr(self, "_modular", False):
                parts = [p.strip() for p in txt.split(".")]
                if (parts and parts[0] not in self._interfaces and parts[0] not in self._iface_ports
                        and not (subst and parts[0] in subst)):
                    self._modular_hier_reads.setdefault(self._current_module, set()).add(
                        (name, tuple(parts)))
            return Ref(name)
        parts = [p.strip() for p in txt.split(".")]
        if len(parts) < 2 or not all(parts):
            raise NotImplementedError(f"hierarchical reference {txt!r}")
        clean, sel = [], None
        for p in parts:
            nm, ix = self._split_sel(p)
            clean.append(nm)
            if ix is not None:
                if sel is not None:
                    raise NotImplementedError(f"multiple indexed levels in {txt!r}")
                sel = ix
        try:
            lane = int(sel)
        except (TypeError, ValueError):
            raise NotImplementedError(f"non-constant indexed hierarchical reference {txt!r}") from None
        return ElemSel(self._nest_path(clean, subst), Const(lane, 32))

    def _union_view(self, e) -> tuple[str, int, int] | None:
        """If a MemberAccess chain reads INTO a packed union, return (root, bit_offset, width);
        else None. The offset accumulates each member's bitOffset down to the leaf (union members
        overlay at 0, struct fields carry their offset); width is the leaf member's width."""
        width = getattr(getattr(e, "type", None), "bitWidth", 1) or 1
        off = 0
        cur = self._peel(e)
        while _enum_name(cur.kind) == "MemberAccess":
            off += cur.member.bitOffset
            cur = self._peel(cur.value)
        if _enum_name(cur.kind) == "NamedValue" and cur.symbol.name in self._unions:
            return cur.symbol.name, off, width
        return None

    _FOLD = {"add": lambda a, b: a + b, "sub": lambda a, b: a - b, "mul": lambda a, b: a * b,
             "div": lambda a, b: a // b if b else 0, "mod": lambda a, b: a % b if b else 0,
             "and": lambda a, b: a & b, "or": lambda a, b: a | b, "xor": lambda a, b: a ^ b,
             "shl": lambda a, b: a << b, "shr": lambda a, b: a >> b,
             "eq": lambda a, b: int(a == b), "ne": lambda a, b: int(a != b),
             "lt": lambda a, b: int(a < b), "le": lambda a, b: int(a <= b),
             "gt": lambda a, b: int(a > b), "ge": lambda a, b: int(a >= b),
             "logand": lambda a, b: int(bool(a) and bool(b)), "logor": lambda a, b: int(bool(a) or bool(b))}

    def _genvar_select_dims(self, e: object) -> tuple[str, int] | None:
        """If ``e`` is a chain of bare in-scope genvar selects ``base[gv]...[gv]``, return
        (base_name, #dims); else None. `sig[i]` -> (sig,1); `sig[i][j]` -> (sig,2). Assumes the
        genvars are used in nesting order (outer loop -> leftmost index)."""
        cur, dims = e, 0
        while (_enum_name(cur.kind) == "ElementSelect"
               and _enum_name(cur.selector.kind) == "NamedValue"
               and cur.selector.symbol.name in self._genvars):
            dims += 1
            cur = self._peel(cur.value)
        if dims == 0 or _enum_name(cur.kind) != "NamedValue":
            return None
        return cur.symbol.name, dims

    def _expr_uses_genvar(self, e: object) -> bool:
        """Return True if expression ``e`` references any in-scope genvar name.
        Used to detect broadcast lane-writes where the RHS is index-independent
        (e.g. ``ppSgn_M1[i] = expr_without_i``) so we can keep the signal as a
        plain word rather than marking it INDEXED with an unbound variable."""
        if e is None:
            return False
        k = _enum_name(getattr(e, "kind", None) or "")
        if k == "NamedValue":
            return getattr(getattr(e, "symbol", None), "name", None) in self._genvars
        # recursively check sub-expressions; cover the common node types
        for attr in ("left", "right", "operand", "value", "selector", "conditions"):
            sub = getattr(e, attr, None)
            if sub is not None:
                if isinstance(sub, list):
                    if any(self._expr_uses_genvar(s) for s in sub):
                        return True
                elif self._expr_uses_genvar(sub):
                    return True
        for attr in ("arguments", "elements", "operands"):
            lst = getattr(e, attr, None)
            if lst is not None and any(self._expr_uses_genvar(s) for s in lst):
                return True
        return False

    def _genvar_lane_slice(self, e) -> tuple[str, int] | None:
        """``(signal, W)`` if ``e`` is the byte-lane idiom -- an indexed part-select of a plain
        packed signal whose base is the in-scope genvar times the width, `sig[i*W +: W]` (or
        `sig[W*i +: W]`, or `sig[i*W + W-1 -: W]`): lane `i` of `sig` viewed as W-bit lanes. Such
        a select IS a lane read/write of `sig` with element width W -- exactly the shape a packed
        2-D `logic [N-1:0][W-1:0]` gets from `sig[i]` -- so it lowers to the same `Ref(sig)` with
        `_lane_elem_w[sig] = W`, and the lane<->word bridge decomposes/assembles at `I * W`.
        Anything else with a genvar in a slice bound stays a VALUE use of the genvar (refused)."""
        if not self._genvars or _enum_name(getattr(e, "kind", None) or "") != "RangeSelect":
            return None
        sk = getattr(getattr(e, "selectionKind", None), "name", "Simple")
        if sk not in ("IndexedUp", "IndexedDown"):
            return None
        base = self._peel(e.value)
        if _enum_name(base.kind) != "NamedValue" or getattr(getattr(base, "symbol", None),
                                                          "type", None) is None:
            return None
        if getattr(base.symbol.type, "isUnpackedArray", False):
            return None
        w = self._const_of(e.right)
        if w is None or w < 1:
            return None
        off = self._peel(e.left)                     # `gv * W`, `W * gv`, or (for -:) `gv*W + W-1`
        extra = 0
        if sk == "IndexedDown":
            if _enum_name(off.kind) != "BinaryOp" or _BINOP.get(_enum_name(off.op)) != "add":
                return None
            l, r = self._peel(off.left), self._peel(off.right)
            if self._const_of(r) == w - 1:
                off, extra = l, w - 1
            elif self._const_of(l) == w - 1:
                off, extra = r, w - 1
            else:
                return None
        if _enum_name(off.kind) != "BinaryOp" or _BINOP.get(_enum_name(off.op)) != "mul":
            return None
        l, r = self._peel(off.left), self._peel(off.right)
        for gv, k in ((l, r), (r, l)):
            if (_enum_name(gv.kind) == "NamedValue"
                    and getattr(getattr(gv, "symbol", None), "name", None) in self._genvars
                    and self._const_of(k) == w):
                return base.symbol.name, w
        return None

    def _check_genvar_index_order(self, e, gs) -> None:
        """A multi-index genvar select must use the genvars in NESTING order (`a[i][j]` under
        `for (i) for (j)`): the lowered lane read is the bare `Ref(a)`, rendered `a(I, J)` in
        the enclosing lane rule's own index order, so `a[j][i]` (a transpose) would silently
        read `a(I, J)` -- the un-transposed lane. Refuse it until a lane read can carry its own
        index permutation (found by the idiom sweep on a 2-D transpose)."""
        vs = self._genvar_select_vars(e)
        if len(vs) > 1 and vs != self._genvar_order[:len(vs)]:
            raise NotImplementedError(
                f"genvar select `{str(getattr(e, 'syntax', '')).strip()}` uses the genvars out of "
                f"nesting order ({vs} vs {self._genvar_order[:len(vs)]}): a lane read is rendered "
                f"in the enclosing rule's index order, so this would read the un-permuted lane "
                f"(deferred -- a transpose needs an index permutation on the read)")

    def _genvar_offset_select(self, e) -> tuple[str, int] | None:
        """``(signal, off)`` if ``e`` is `sig[gv + c]` / `sig[gv - c]` / `sig[c + gv]` -- a
        select of a plain packed signal at the in-scope genvar offset by a constant. As a WRITE
        target this is the carry-chain shape `c[i+1] = g[i] | (p[i] & c[i])`: the rule's head
        lane is `I + off` while the loop variable `I` ranges over the loop's own index set."""
        if not self._genvars or _enum_name(getattr(e, "kind", None) or "") != "ElementSelect":
            return None
        base = self._peel(e.value)
        if _enum_name(base.kind) != "NamedValue" or getattr(getattr(base, "symbol", None),
                                                          "type", None) is None:
            return None
        if getattr(base.symbol.type, "isUnpackedArray", False):
            return None
        sel = self._peel(e.selector)
        if _enum_name(sel.kind) != "BinaryOp" or _BINOP.get(_enum_name(sel.op)) not in ("add", "sub"):
            return None
        op = _BINOP[_enum_name(sel.op)]
        l, r = self._peel(sel.left), self._peel(sel.right)

        def is_gv(x) -> bool:
            return (_enum_name(x.kind) == "NamedValue"
                    and getattr(getattr(x, "symbol", None), "name", None) in self._genvars)
        if is_gv(l) and self._const_of(r) is not None:
            c = self._const_of(r)
            return base.symbol.name, (c if op == "add" else -c)
        if op == "add" and is_gv(r) and self._const_of(l) is not None:
            return base.symbol.name, self._const_of(l)
        return None

    def _note_lane_elem_w(self, name: str, w: int) -> None:
        """Record the per-lane element width a genvar select implies for ``name``, refusing a
        CONFLICT: `a[i]` (1-bit lanes) and `a[i*8 +: 8]` (8-bit lanes) on one signal are two
        lane views the single functor `a(I)` cannot carry at once."""
        prev = self._lane_elem_w.get(name)
        if prev is not None and prev != w:
            raise NotImplementedError(
                f"{name}: read/written as lanes of {prev} bit(s) and of {w} bit(s) -- one lane "
                f"element width per signal (deferred -- use one view, or a separate signal)")
        self._lane_elem_w[name] = w

    def _lhs_index_uses_genvar_arith(self, left) -> bool:
        """True if the write target's INDEX mentions an in-scope loop/genvar variable other than
        as a bare selector chain (`y[i+1]`, `y[2*i +: 2]`, `q[i][j-1]`). A bare `y[i]` lane-rolls;
        an arithmetic index would constant-fold to ONE iteration's value (the D1 defect, on the
        left-hand side, where nothing downstream can see the fold) -- so the caller refuses it."""
        if not self._genvars or self._genvar_select_dims(left) is not None \
                or self._genvar_lane_slice(left) is not None \
                or self._genvar_offset_select(left) is not None:
            return False
        cur = self._peel(left)
        while _enum_name(cur.kind) in ("ElementSelect", "RangeSelect"):
            for attr in ("selector", "left", "right"):
                sel = getattr(cur, attr, None)
                if sel is not None and hasattr(sel, "kind") and self._expr_uses_genvar(sel):
                    return True
            cur = self._peel(cur.value)
        return False

    def _expr_uses_var_as_value(self, e: object, names: set[str]) -> bool:
        """True if ``e`` references one of ``names`` in a VALUE position — anywhere other than as
        the bare SELECTOR of an ElementSelect. A bare selector (`sig[i]`) lane-rolls correctly:
        the index is fanned by the grounder. Any other occurrence needs the variable's VALUE,
        which a lane-rolled body cannot supply (there is no signal to read) — see defect D5."""
        if e is None:
            return False
        k = _enum_name(getattr(e, "kind", None) or "")
        if k == "NamedValue":
            return getattr(getattr(e, "symbol", None), "name", None) in names
        if k == "ElementSelect":
            sel = getattr(e, "selector", None)
            bare = (sel is not None and _enum_name(sel.kind) == "NamedValue"
                    and getattr(getattr(sel, "symbol", None), "name", None) in names)
            return (self._expr_uses_var_as_value(getattr(e, "value", None), names)
                    or (not bare and self._expr_uses_var_as_value(sel, names)))
        for attr in ("left", "right", "operand", "value", "selector", "conditions", "expr"):
            sub = getattr(e, attr, None)
            if isinstance(sub, (list, tuple)):
                if any(self._expr_uses_var_as_value(x, names) for x in sub):
                    return True
            elif sub is not None and self._expr_uses_var_as_value(sub, names):
                return True
        for attr in ("arguments", "elements", "operands"):
            lst = getattr(e, attr, None)
            if lst is not None and any(self._expr_uses_var_as_value(x, names) for x in lst):
                return True
        return False

    def _stmt_uses_var_as_value(self, s: object, names: set[str]) -> bool:
        """Statement-level walk of `_expr_uses_var_as_value` over a loop body."""
        if s is None or not hasattr(s, "kind"):
            return False
        for attr in ("expr", "condition", "left", "right"):
            if self._expr_uses_var_as_value(getattr(s, attr, None), names):
                return True
        for attr in ("body", "list", "stmt", "ifTrue", "ifFalse", "defaultCase"):
            c = getattr(s, attr, None)
            if isinstance(c, (list, tuple)):
                if any(self._stmt_uses_var_as_value(x, names) for x in c):
                    return True
            elif self._stmt_uses_var_as_value(c, names):
                return True
        for it in getattr(s, "items", []) or []:
            if self._stmt_uses_var_as_value(getattr(it, "stmt", None), names):
                return True
            if any(self._expr_uses_var_as_value(x, names) for x in getattr(it, "expressions", []) or []):
                return True
        return False

    def _genvar_select_vars(self, e) -> list[str]:
        """Genvar names of a bare-genvar select chain, OUTER (leftmost index) first: q[i][j] -> [i, j]."""
        names, cur = [], e
        while (_enum_name(cur.kind) == "ElementSelect"
               and _enum_name(cur.selector.kind) == "NamedValue"
               and cur.selector.symbol.name in self._genvars):
            names.append(cur.selector.symbol.name)
            cur = self._peel(cur.value)
        names.reverse()
        return names

    def _select_root(self, e):
        """Peel a (possibly nested) ElementSelect chain to its root NamedValue symbol, else None.
        For `q[i][j]` the root is `q` (whereas `_peel(e.value)` is the inner select `q[i]`)."""
        cur = self._peel(e)
        while _enum_name(cur.kind) == "ElementSelect":
            cur = self._peel(cur.value)
        return cur.symbol if _enum_name(cur.kind) == "NamedValue" else None

    def _select_indices(self, e, subst=None) -> list[Expr]:
        """Lowered selector exprs of a nested ElementSelect chain, OUTER-first: `q[a][b]` -> [a, b]."""
        idxs = []
        cur = self._peel(e)
        while _enum_name(cur.kind) == "ElementSelect":
            idxs.append(cur.selector)
            cur = self._peel(cur.value)
        return [self._lower_expr(ix, subst) for ix in reversed(idxs)]

    def _check_array_rank(self, name: str, got: int) -> None:
        """The index rank of a memory access must equal the array's declared rank; 3-D+ is deferred."""
        want = len(self._mem_dims.get(name, (1,)))
        if got != want:
            raise NotImplementedError(f"{name}: index rank {got} != array rank {want}")
        if want > 2:
            raise NotImplementedError(f"{name}: {want}-D unpacked array access (>=3 dims) deferred")

    # -- generate-over-vector (catalog §4.6): roll the genvar into the lane index -----
    def _wrap_name(self, name: str, inst: str, subst: dict[str, str]) -> str:
        """Qualify a submodule-local name by the instance: sig -> u_inst(sig). Clock/reset
        formals (in ``subst``) map to the parent actual instead (shared domain, not wrapped)."""
        return subst.get(name, f"{inst}({name})")

    def _wrap_expr(self, e: Expr, inst: str, subst: dict[str, str]) -> Expr:
        if isinstance(e, Const):
            return e
        if isinstance(e, Tag):       # an enum label is GLOBAL (package-level) -- no qualification
            return e
        if isinstance(e, Ref):
            return Ref(self._wrap_name(e.name, inst, subst))
        if isinstance(e, SExt):      # sign-extension: qualify the operand, keep the widths
            return SExt(self._wrap_expr(e.operand, inst, subst), e.from_w, e.to_w)
        if isinstance(e, BinOp):
            return BinOp(e.op, self._wrap_expr(e.left, inst, subst),
                         self._wrap_expr(e.right, inst, subst), e.width, signed=e.signed, opw=e.opw)
        if isinstance(e, UnOp):
            return UnOp(e.op, self._wrap_expr(e.operand, inst, subst), e.width)
        if isinstance(e, Slice):
            return Slice(self._wrap_expr(e.base, inst, subst), e.hi, e.lo)
        if isinstance(e, BitSel):
            return BitSel(self._wrap_expr(e.base, inst, subst), e.index)
        if isinstance(e, LaneIdx):   # a bare lane variable -- not instance-qualified
            return e
        if isinstance(e, MemRef):
            return MemRef(self._wrap_name(e.mem, inst, subst),
                          tuple(self._wrap_expr(a, inst, subst) for a in e.addrs))
        if isinstance(e, ElemSel):
            return ElemSel(self._wrap_name(e.base, inst, subst), self._wrap_expr(e.index, inst, subst), tuple(self._wrap_expr(x, inst, subst) for x in e.more))
        if isinstance(e, Concat):
            return Concat(tuple((self._wrap_expr(x, inst, subst), wd) for x, wd in e.parts))
        if isinstance(e, Cond):
            return Cond(self._wrap_expr(e.sel, inst, subst), self._wrap_expr(e.a, inst, subst),
                        self._wrap_expr(e.b, inst, subst), e.width)
        raise NotImplementedError(f"hierarchical wrap of expr {type(e).__name__}")

    def _wildcard_mask(self, label, width: int) -> tuple[int | None, int | None]:
        """Extract (care_mask, pattern) from a casez/casex arm literal. Cared bits are 0/1;
        x/z/? are don't-care (uniform for casez and casex). Parses the binary SVInt string;
        returns (None, None) for a non-binary literal (flagged by the caller)."""
        # the arm literal may be wrapped in a Conversion (cast to the case-expression type) -> peel to
        # the IntegerLiteral before reading its SVInt text.
        m = re.fullmatch(r"\d+'[sS]?[bB]([01xzXZ?]+)", str(getattr(self._peel(label), "value", "")))
        if not m:
            # no wildcard bits -> a FULLY-SPECIFIED arm (SVInt with no x/z stringifies as decimal, not
            # 'b...): every bit is cared, pattern = the constant value. A non-constant -> flag.
            cv = self._const_of(label)
            if cv is None:
                return None, None
            full = (1 << width) - 1
            return full, cv & full
        bits = m.group(1).lower().rjust(width, "0")  # MSB-first, left-pad with cared 0s
        care = pat = 0
        for ch in bits:
            care <<= 1
            pat <<= 1
            if ch in "01":
                care |= 1
                pat |= int(ch)
        return care, pat

    def _hoist_name(self, tag: str) -> str:
        """A fresh name for a hoisted intermediate: ``<ctx__><tag><N>`` off the monotone counter,
        SKIPPING any number whose name the design already declares. `c0`, `t1`, `gc2` are legal --
        and common -- SystemVerilog identifiers; without the skip, a hoisted `c0` silently took the
        user's `c0` Signal (its width, its atom), and the two were told apart only by whichever
        rendering each happened to get. Numbers are consumed, never rewound (see `_rec_seq`)."""
        pfx = f"{self._hoist_ctx}__" if self._hoist_ctx else ""
        while True:
            name = f"{pfx}{tag}{self._cond_n}"
            self._cond_n += 1
            if name not in self._blk_signals:
                return name

    def _hoist_masked_eq(self, sel_expr, mask: int, pat: int, width: int, loc) -> str:
        """Define a synthetic bit `g = (sel & care_mask) == pattern` and return its name."""
        name = self._hoist_name("gc")
        masked = BinOp("and", sel_expr, Const(mask, width), width)
        self._blk_comb.append(CombItem(lhs=name, rhs=BinOp("eq", masked, Const(pat, width), 1), loc=loc))
        self._blk_signals[name] = Signal(name=name, irtype=IRType(Kind.BIT, 1), is_reg=False,
                                         is_port=False, direction=None, initial=None, loc=loc)
        return name

    def _match_value(self, e) -> str:
        """The match value of a case-arm label: an enum member -> its tag; an integer literal /
        constant -> its value; else the signal name (fallback)."""
        p = self._peel(e)
        if _enum_name(p.kind) == "NamedValue" and p.symbol.name in self._enum_members:
            return p.symbol.name.lower()
        cv = self._const_of(e)
        if cv is not None:
            # canonical value encoding: a wide case value (>= 2^31) is a clingo String, matching the
            # selector's stored encoding (see emit/lib.py _we, stage3_emit _const_lit) -- else clingo's
            # 32-bit int would silently wrap the big decimal literal.
            return str(cv) if -(2 ** 31) <= cv < 2 ** 31 else f'"{cv}"'
        return self._ref_name(p)

    def _cond_signal(self, stmt) -> tuple[str, int]:
        cond = stmt.conditions[0].expr
        # !x -> (x, 0); a bare signal x -> (x, 1) -- for a ONE-BIT, non-enum x. A wider bare
        # condition is the LRM's non-zero test: `if (n)` with a 3-bit n used to become the guard
        # `val(n, 1, T)` (true for n == 1 only, dark for 2..7) and `if (!n)` -> `val(n, 0, T)`;
        # an ENUM condition `if (state)` tested the TAG against 1. Both now hoist `(x != 0)`
        # (found with the enum operator table on the dataset's fancytimer entry, 2026-08-19).
        def _bare_bit(x) -> bool:
            t = getattr(x, "type", None)
            return ((getattr(t, "bitWidth", 1) or 1) == 1 and not getattr(t, "isEnum", False))
        if _enum_name(cond.kind) == "UnaryOp" and _UNOP.get(_enum_name(cond.op)) == "lnot":
            inner = self._peel(cond.operand)
            if _enum_name(inner.kind) == "NamedValue" and _bare_bit(inner):
                return inner.symbol.name, 0
        peeled = self._peel(cond)
        if _enum_name(peeled.kind) == "NamedValue" and _bare_bit(peeled):
            return peeled.symbol.name, 1
        if _enum_name(peeled.kind) == "NamedValue":        # wide / enum bare condition: (x != 0)
            w = getattr(getattr(peeled, "type", None), "bitWidth", 1) or 1
            return self._hoist_bit(BinOp("ne", self._lower_expr(peeled), Const(0, w), 1),
                                   self._loc_expr(cond)).name, 1
        # a compound/comparison condition (a>b, x&&y, ...) -> HOIST into a synthetic 1-bit
        # combinational signal, define it, and guard on it. Works for any boolean expression.
        return self._hoist_bit(self._lower_expr(cond), self._loc_expr(cond)).name, 1

    def _lower_cond_sel(self, cexpr, subst) -> Expr:
        """Lower a ternary selector to a form `_cond_branches` splits directly. A comparison or a
        1-bit signal is native (no extra signal). Any other boolean expr hoists to a gcond bit:
        a 1-bit-wide expr (`!c`, `a&&b`, `|bus`, 1-bit `a&b`) as ``gcond = expr`` (truth-tabled);
        a MULTI-bit expr (`(a&b)`, `bus`) as ``gcond = (expr != 0)`` -- a word compare, so wide
        operands test nonzero and are never truncated to bit 0 (soundness)."""
        sel = self._lower_expr(cexpr, subst)
        width = getattr(getattr(cexpr, "type", None), "bitWidth", 1) or 1
        if isinstance(sel, BinOp) and sel.op in _CMP_OPS:
            return sel                                      # comparison -> emitted directly
        if isinstance(sel, Ref) and width == 1:
            return sel                                      # 1-bit signal -> polarity split directly
        loc = self._loc_expr(cexpr)
        if width == 1:
            return self._hoist_bit(sel, loc)                # 1-bit boolean expression
        return self._hoist_bit(BinOp("ne", sel, Const(0, width), 1), loc)   # wide -> (expr != 0)

    def _accumulator_tern(self, v: Cond, width: int, loc: Loc) -> Ref:
        """ONE tern per distinct scan-accumulator VALUE in the always_comb executor -- and the memo
        KEEPS THE OBJECT it keys. It was keyed by `id(v)` alone: once an accumulator's Cond died,
        a new Cond allocated at the same address got the OLD tern, so `!any` read a stale value
        and a priority encoder became last-wins -- in some full test runs and never in isolation,
        because it depended on allocation history, not on the input (F40, 2026-09-03: the sweep
        row prio_enc_first_wins, `idx = 7` where Icarus says 4, twice in three full runs)."""
        memo = self._cond_hoist_memo
        hit = memo.get(id(v))
        if hit is not None and hit[0] is v:
            return hit[1]
        ref = self._hoist_word(v, width, loc)
        memo[id(v)] = (v, ref)                   # the object is retained, so its address cannot be reused
        return ref

    def _hoist_word(self, expr: Expr, width: int, loc: Loc, enum_type: str | None = None) -> Ref:
        """Define a fresh combinational ``tern_N = expr`` (width-bit) and return a Ref to it, so a
        Cond (a nested ternary, or a function result built from if/else) can sit inside an enclosing
        word/bit expression as a plain value-term.

        ``enum_type``: the temp holds an ENUM (a ternary of tags, `next = data ? S1 : S` in a
        procedural block -- the statement path lowers its RHS as a sub-expression, so the ternary
        is hoisted). Without it the temp was a plain word whose tag arms lowered as the members'
        NUMBERS, `next` copied numbers into an enum register, no `case` arm matched and the FSM
        sat in its default arm: exit 0, `coverage: OK`, in both modes (the dataset's VerilogEval
        fancytimer reference, 2026-08-19). The `assign` form of the same ternary was never
        affected (`_emit_cond` sees the tags)."""
        name = self._hoist_name("t")
        if width == 1 and isinstance(expr, Cond):
            expr = self._hoist_bool_arms(expr, loc)        # a hoisted 1-bit ternary is an assign
        self._blk_comb.append(CombItem(lhs=name, rhs=expr, loc=loc))
        self._blk_signals[name] = Signal(name=name, irtype=IRType(Kind.BIT, width),
                                         is_reg=False, is_port=False, direction=None,
                                         initial=None, loc=loc, enum_type=enum_type)
        self._lane_local_temp(name, expr, width)
        return Ref(name)

    def _hoist_bool_arms(self, cond: Cond, loc: Loc) -> Cond:
        """A 1-bit ternary whose ARM contains a BOOLEAN operator -- a comparison or a logical
        op, `a ? b : ((n == 2) | (n == 3))` -- hoists that arm into a named 1-bit wire, which the
        item-level boolean emitter then handles like any other 1-bit comb item.

        F29 sent a compound 1-bit arm to the WORD cascade, which knows arithmetic and bitwise
        operators and nothing of `==` or `||`: such an arm was refused as `word expr BinOp`,
        nested or not, in both modes -- loud, and exactly the shape the one-cell stencil's
        canonical rule has (the third block's G27a, 2026-09-02). The procedural path has hoisted
        arms this way since `_hoist_bit_arms`; this is the same treatment on the continuous
        assign and on a hoisted temporary. Only an arm that CONTAINS a boolean node is hoisted:
        a pure word-operator arm stays on F29's path, so the corpus is byte-identical."""
        def arm(e: Expr) -> Expr:
            if isinstance(e, (Const, Ref, Tag)) or not _has_bool_node(e):
                return e
            return self._hoist_bit(e, loc)
        return Cond(cond.sel, arm(cond.a), arm(cond.b), cond.width)

    def _enum_type_name(self, t: object) -> str | None:
        """The enum_type name of a pyslang type, if it is an enum this module has declared a signal
        of (the name the declaration walk gave it -- the typedef, or `<first signal>_enum`)."""
        if not getattr(t, "isEnum", False):
            return None
        key = str(getattr(t, "canonicalType", t))
        if key in self._enum_type_of:
            return self._enum_type_of[key]
        nm = getattr(t, "name", None)
        return nm.lower() if nm else None

    def _edge_signal(self, sig: str, rising: bool, loc: Loc) -> Ref:
        """Define a fresh 1-bit ``<sig>__rose`` / ``<sig>__fell`` carried by an `EdgeItem`, and
        return a Ref to it. One signal per (sampled signal, direction, clock), so repeated uses
        of the same edge in a block share it."""
        name = f"{sig}__{'rose' if rising else 'fell'}"
        if name not in self._blk_signals:
            self._blk_signals[name] = Signal(name=name, irtype=IRType(Kind.BIT, 1),
                                             is_reg=False, is_port=False, direction=None,
                                             initial=None, loc=loc)
        if not any(x.lhs == name for x in self._blk_edges):
            self._blk_edges.append(EdgeItem(lhs=name, sig=sig, rising=rising,
                                            clock=self._blk_clock, loc=loc))
        return Ref(name)

    def _hoist_bit(self, expr: Expr, loc: Loc) -> Ref:
        """Define a fresh 1-bit combinational ``gcond_N = expr`` and return a Ref to it. Shared by
        if/case-condition hoisting (`_cond_signal`) and the ternary selector path -- any boolean
        sub-expression becomes a plain bit the downstream emit splits on its two polarities."""
        name = self._hoist_name("c")
        self._blk_comb.append(CombItem(lhs=name, rhs=expr, loc=loc))
        self._blk_signals[name] = Signal(name=name, irtype=IRType(Kind.BIT, 1),
                                         is_reg=False, is_port=False, direction=None,
                                         initial=None, loc=loc)
        self._lane_local_temp(name, expr, 1)
        return Ref(name)

    def _lane_local_temp(self, name: str, expr: Expr, width: int) -> None:
        """A temp hoisted INSIDE a generate whose expression reads a lane is itself a lane, by
        construction -- registered exactly as a net the author declares inside the generate body
        is (`_lower_generate_run`, the F17 rule: per-iteration SCOPE defines the lane).

        Without this the temp was a module-level scalar, and its rule was emitted OUTSIDE the
        lane context that gives a bare `Ref("x")` its `(I)`: `(pRecv & idxHot[i])` became a temp
        reading the WORD `idxHot`, `cap[i]` in an arm became the word `cap`, and `idxHot[i-1]`
        was left with its index unbound so the temp took every lane's value. Five one-hot phase
        flops printed by this route's own printer translated back to wrong rules at exit 0 and a
        2^64 join (F30, 2026-09-02). Whether the procedural path's temps came out right was an
        accident of the classifier's closure -- bob_demo's `c4(I)` -- not a decision anyone made;
        this makes it the decision, on every path, for the same reason F17 chose construction
        over closure.

        Only a temp that MENTIONS a lane is registered: an index-invariant selector (`a == b`)
        stays one scalar rather than N copies, which is also what keeps the corpus byte-identical.
        """
        if not self._genvars:
            return
        if not (_has_lane_index(expr) or _has_implicit_lane_ref(expr, self._lane_dims)):
            return
        self._lane_dims[name] = max(self._lane_dims.get(name, 0), 1)
        self._note_lane_elem_w(name, width)
        self._gen_locals[name] = max(self._gen_locals.get(name, 0), self._lane_hi)

    _BOOL_OPS = ("eq", "ne", "lt", "le", "gt", "ge", "logand", "logor")

    def _as_word(self, e: Expr, loc: Loc) -> Expr:
        """A boolean sub-value (a comparison / tag-compare / logical op) used in a WORD context
        (a concat part, an arithmetic operand) becomes a 1-bit ``gcond`` signal, so the word emitter
        reads it as an ordinary value instead of choking on a bare comparison node."""
        if isinstance(e, BinOp) and e.op in self._BOOL_OPS:
            return self._hoist_bit(e, loc)
        if isinstance(e, UnOp) and e.op == "lnot":
            return self._hoist_bit(e, loc)
        # a 1-bit WORD operation over boolean nodes -- `(w == 3) | (w == 4)`, the Booth encoder's
        # digit bits inside a concat -- is a boolean tree the word cascade cannot take
        # (`word expr BinOp`); as a named bit the item-level boolean emitter handles it
        if isinstance(e, (BinOp, UnOp)) and getattr(e, "width", None) == 1 and _has_bool_node(e):
            return self._hoist_bit(e, loc)
        return e

    def _ref_name(self, e) -> str:
        """Return a signal name for a case/casez selector expression ``e``.
        A plain ``NamedValue`` -> its name directly. A single-element concat ``{x}``
        unwraps to its inner expression (a common RTL idiom for ``case ({sig}) inside``).
        Any other non-name expression is hoisted to a synthetic word signal via
        ``_hoist_word`` so it can be used as a selector name -- never falls back to
        ``str(e)`` which would produce ``expressionKind.xxx`` garbage names."""
        e = self._peel(e)
        if hasattr(e, "symbol"):
            return e.symbol.name
        # single-element concatenation {x}: unwrap and recurse
        if _enum_name(e.kind) == "Concatenation":
            ops = list(e.operands)
            if len(ops) == 1:
                return self._ref_name(ops[0])
        # compound expression: hoist to a named comb signal
        lowered = self._lower_expr(e)
        w = getattr(getattr(e, "type", None), "bitWidth", 1) or 1
        loc = self._loc_expr(e) if hasattr(self, "_loc_expr") else Loc(file="?", line=0)
        return self._hoist_word(lowered, w, loc).name

    def _loc_expr(self, e) -> Loc:
        try:
            loc = e.sourceRange.start
            file = self._sm.getFileName(loc)
            line = self._sm.getLineNumber(loc)
            return Loc(file=file, line=line, text=self._line_text(file, line))
        except Exception:  # noqa: BLE001
            return Loc(file="?", line=0)

    # -- expression lowering -------------------------------------------------
    def _peel(self, e):
        while _enum_name(e.kind) == "Conversion":
            e = e.operand
        return e

    def _inline_call(self, e, subst: dict[str, Expr] | None) -> Expr:
        """Inline a pure user function call (catalog §1.11) by SYMBOLIC EXECUTION of its body:
        formals bind to the actual expressions, then each blocking assignment binds its local to
        the (already-substituted) RHS. A local read substitutes its bound expression, so a straight
        line of `local = expr; ...; funcname = expr;` collapses to one expression -- reassignment
        composes (SSA via substitution). The function's value is what its name is finally bound to."""
        if getattr(e, "isSystemCall", False):
            sysname = getattr(e, "subroutineName", "?")
            # $signed/$unsigned are reinterpret casts: SAME stored bits, only the signedness for
            # downstream ops changes -- and that is read from pyslang's elaborated types at each op
            # (a widening cast is handled by the surrounding Conversion -> SExt). So pass the
            # (single) argument through unchanged.
            if sysname in ("$signed", "$unsigned") and len(e.arguments) == 1:
                return self._lower_expr(e.arguments[0], subst)
            # popcount family: $countones(v) = #set-bits (a word); $onehot(v) = (#set == 1);
            # $onehot0(v) = (#set <= 1) -- both 1-bit. ow = operand width (the @popcnt mask).
            if sysname in ("$countones", "$onehot", "$onehot0") and len(e.arguments) == 1:
                ow = getattr(getattr(e.arguments[0], "type", None), "bitWidth", 1) or 1
                pc = UnOp("popcnt", self._lower_expr(e.arguments[0], subst), ow)
                if sysname == "$countones":
                    return pc
                op = "eq" if sysname == "$onehot" else "le"
                return BinOp(op, pc, Const(1, ow), 1, opw=ow)
            # SAMPLED-VALUE EDGE functions. `$rose(x)` is 1 exactly when `x` read 0 at the
            # PREVIOUS clock tick and 1 at this one -- two adjacent samples, so it becomes a
            # synthesized 1-bit signal carried by an `EdgeItem` rather than an expression the
            # same-instant cascade could compute.
            if sysname in ("$rose", "$fell") and len(e.arguments) == 1:
                arg = self._lower_expr(e.arguments[0], subst)
                if not isinstance(arg, Ref):
                    raise NotImplementedError(
                        f"{sysname} of an expression (only a plain signal is supported)")
                if not self._blk_clock:
                    raise NotImplementedError(f"{sysname} outside a clocked block")
                return self._edge_signal(arg.name, sysname == "$rose",
                                         self._loc_expr(e))
            raise NotImplementedError(f"system call {sysname!r} unsupported")
        sub = e.subroutine
        # A function is INLINED, so a recursive one has no fixed point to inline to. Without this
        # the inliner simply recursed until Python's stack gave out and the guard net reported
        # `RecursionError: maximum recursion depth exceeded` -- loud, but indistinguishable from
        # a bug in the tool. Recursion is not synthesizable; say so (Fix 79).
        active = getattr(self, "_fn_stack", None)
        if active is None:
            active = self._fn_stack = []
        if sub.name in active:
            raise NotImplementedError(
                f"function {sub.name!r} is RECURSIVE ({' -> '.join([*active, sub.name])}): "
                f"functions are inlined, and recursion has no bound to inline to. Not "
                f"synthesizable -- rewrite it with a constant-trip loop")
        actuals = [self._lower_expr(a, subst) for a in e.arguments]  # lower in caller context
        env: dict[str, Expr] = {f.name: a for f, a in zip(sub.arguments, actuals, strict=False)}
        save = self._eval_scope
        self._eval_scope = sub  # constant subexprs in the body eval in the function's scope
        active.append(sub.name)
        try:
            wenv = {f.name: (getattr(getattr(f, "type", None), "bitWidth", 1) or 1) for f in sub.arguments}
            self._exec_func_body(sub.body, sub.name, env, wenv)
            rt = getattr(sub, "returnType", None)
            if sub.name not in env and getattr(rt, "isStruct", False):
                # struct-return fn: the implicit return var was written field-by-field (mk.hi=a) ->
                # assemble the packed word from its field subsignals, MSB-first by offset (a never-
                # assigned field reads 0). Same Concat-by-offset shape as a whole-struct read.
                fields = sorted(((f.name, f.type.bitWidth, f.bitOffset) for f in rt.canonicalType),
                                key=lambda fwo: fwo[2], reverse=True)
                return Concat(tuple((env.get(f"{sub.name}({fn})", Const(0, w)), w) for fn, w, _ in fields))
            if sub.name not in env:
                raise NotImplementedError(f"function {sub.name!r}: return value never assigned")
            return env[sub.name]
        finally:
            self._eval_scope = save
            active.pop()

    def _insert_bits(self, cur: Expr, width: int, off: int, w: int, val: Expr) -> Expr:
        """``cur`` with bits [off+w-1:off] replaced by ``val`` -- `(cur & ~mask) | (val << off)`.
        The SSA form of a PART write inside a procedural block: a part write produces a new version of
        the WHOLE value, so a later read of the signal (or of any of its bits) sees the update. Without
        it the executor keyed a bit write as its own element (`y(2)`) while the whole signal kept its
        own value, which is the two-disagreeing-drivers defect F22."""
        mask = ((1 << w) - 1) << off
        keep = ((1 << width) - 1) & ~mask
        placed = BinOp("shl", val, Const(off, width), width) if off else val
        return BinOp("or", BinOp("and", cur, Const(keep, width), width), placed, width)

    def _exec_func_body(self, s, fname: str, env: dict[str, Expr], wenv: dict[str, int]) -> None:
        """Symbolically execute a pure function body statement, binding locals (and the function
        name) in ``env`` (and their widths in ``wenv``). Blocking assignments bind the (substituted)
        RHS; an ``if`` merges its branches per assigned variable into a ``Cond`` (so default-then-
        override and a balanced if/else both collapse to one expression). A variable assigned on
        only ONE branch with no prior value is incomplete (latch-like) -> flagged. Loops/case in a
        body are still flagged (NotImplementedError -> the caller's safety net)."""
        k = _enum_name(s.kind)
        if k in ("List", "Block"):
            for attr in ("body", "list"):
                c = getattr(s, attr, None)
                if isinstance(c, (list, tuple)):
                    for x in c:
                        self._exec_func_body(x, fname, env, wenv)
                elif c is not None and hasattr(c, "kind"):
                    self._exec_func_body(c, fname, env, wenv)
            return
        if k in ("VariableDeclaration", "VariableSymbol"):
            return  # a local declaration; bound on first assignment
        if k == "Empty":
            # F11: a NULL STATEMENT (`default: ;`) does nothing, which is exactly what a
            # `default` arm that deliberately falls through to the block's earlier defaults
            # is written to say. It reached the fallthrough below, raised, and took the WHOLE
            # always_comb block down with it -- "could not lower (blocking/loop)", naming
            # neither the arm nor the case. That is how an ordinary decoder ended up in F10:
            # emitted with no rules for its targets, exit 0.
            return
        if k == "ExpressionStatement" and _enum_name(s.expr.kind) == "Assignment":
            left = self._peel(s.expr.left)
            lk = _enum_name(left.kind)
            w = getattr(getattr(s.expr.left, "type", None), "bitWidth", 1) or 1
            # a COMPOUND assignment's `LValueReference` on the right resolves to this target (the
            # statement path sets the same context; the executor lowers the RHS itself, so it must too)
            saved_lv, self._lvalue_node = getattr(self, "_lvalue_node", None), s.expr.left
            try:
                rhs = self._lower_expr(s.expr.right, env)
            finally:
                self._lvalue_node = saved_lv
            fv = self._fold(rhs)   # collapse a loop-counter step (i=i+1) to a Const -> literal indices
            rhs_val = Const(self._mask(fv, w), w) if fv is not None else rhs
            if lk == "NamedValue":
                env[left.symbol.name] = rhs_val
                wenv[left.symbol.name] = w
                return
            if lk == "Concatenation":
                # `{up, left, down, right} = 0;` -- a concatenation TARGET, distributed MSB-first, each
                # piece an SSA update of its own target (a whole name, or a part of one)
                tg = self._concat_targets(s.expr.left)
                if tg is not None:
                    for nm_, regw_, toff_, w_, soff_, dyn_ in tg:
                        if dyn_ is not None:
                            raise NotImplementedError("executor: runtime-indexed concatenation target")
                        piece = Slice(rhs_val, soff_ + w_ - 1, soff_)
                        if toff_ == 0 and w_ == regw_:
                            env[nm_] = piece
                        else:
                            env[nm_] = self._insert_bits(env.get(nm_, Ref(nm_)), regw_, toff_, w_, piece)
                        wenv[nm_] = regw_
                    return
            # an array-element write arr[k] (k folds to a constant after loop unroll) -> a per-element
            # FUNCTOR signal arr(k) keyed in env, so an unrolled scan writes one element per iteration.
            base = self._peel(left.value)
            ci = self._fold(self._lower_expr(left.selector, env)) if lk == "ElementSelect" else None
            if ci is not None and _enum_name(base.kind) == "NamedValue":
                bname = base.symbol.name
                bt = getattr(left.value, "type", None)
                # a LANE signal's real representation IS per-element (`y(I)` from a generate or an
                # unrolled loop), so it keeps the element key; only a plain packed vector, whose value
                # lives as one word, takes the whole-value update
                unpacked = (getattr(bt, "isUnpackedArray", False)
                            or bname in getattr(self, "_mem_dims", {})
                            or bname in getattr(self, "_lane_dims", {}))
                bw = getattr(bt, "bitWidth", None)
                if not unpacked and bw:
                    # a PACKED vector: `y[2] = e` is an update of the whole value, not a separate
                    # element -- so a later read of `y` (or of `y[k]`) sees it (F22)
                    env[bname] = self._insert_bits(env.get(bname, Ref(bname)), bw, ci, 1, rhs_val)
                    wenv[bname] = bw
                    return
                key = f"{bname}({ci})"
                env[key] = rhs_val
                wenv[key] = w
                return
            if lk == "RangeSelect" and _enum_name(base.kind) == "NamedValue":
                bt = getattr(left.value, "type", None)
                bw = getattr(bt, "bitWidth", None)
                bounds = self._range_bounds(left)
                if (bw and bounds is not None and not getattr(bt, "isUnpackedArray", False)
                        and base.symbol.name not in getattr(self, "_mem_dims", {})
                        and base.symbol.name not in getattr(self, "_lane_dims", {})):
                    hi, lo = bounds
                    env[base.symbol.name] = self._insert_bits(
                        env.get(base.symbol.name, Ref(base.symbol.name)), bw, lo, hi - lo + 1, rhs_val)
                    wenv[base.symbol.name] = bw
                    return
            # a struct FIELD write `mk.f = expr` (e.g. a struct-return fn's implicit return var) -> a
            # per-field subsignal `mk(f)` in env; _inline_call assembles them into the packed return.
            if lk == "MemberAccess" and _enum_name(base.kind) == "NamedValue":
                key = f"{base.symbol.name}({left.member.name})"
                env[key] = rhs_val
                wenv[key] = w
                return
            raise NotImplementedError("function: partial/indexed local write not modeled")
        if k == "ExpressionStatement" and _enum_name(s.expr.kind) == "UnaryOp" \
                and _enum_name(s.expr.op) in ("Preincrement", "Postincrement", "Predecrement", "Postdecrement"):
            # a loop-control step `i++` / `i--` -> i = i +/- 1 (must fold to a Const so the loop is bounded)
            operand = self._peel(s.expr.operand)
            if _enum_name(operand.kind) == "NamedValue":
                name = operand.symbol.name
                w = getattr(getattr(s.expr.operand, "type", None), "bitWidth", 32) or 32
                cur = self._fold(env.get(name))
                if cur is not None:
                    step = 1 if "increment" in _enum_name(s.expr.op).lower() else -1
                    env[name] = Const(self._mask(cur + step, w), w)
                    wenv[name] = w
                    return
            raise NotImplementedError("function: non-constant increment/decrement (loop not statically bounded)")
        if k == "ForeachLoop":   # foreach (a[i][j]) -> unroll over each dim's declared index range
            self._unroll_foreach(s, fname, env, wenv)
            return
        if k == "Return":
            env[fname] = self._lower_expr(s.expr, env)
            wenv[fname] = getattr(getattr(s.expr, "type", None), "bitWidth", 1) or 1
            return
        if k == "Conditional":  # if (cond) ifTrue [else ifFalse] -- merge branches per variable
            sel = self._lower_cond_sel(s.conditions[0].expr, env)
            then_env, then_w = dict(env), dict(wenv)
            self._exec_func_body(s.ifTrue, fname, then_env, then_w)
            else_env, else_w = dict(env), dict(wenv)
            if getattr(s, "ifFalse", None) is not None:
                self._exec_func_body(s.ifFalse, fname, else_env, else_w)
            loc = self._loc_expr(s.conditions[0].expr)
            for var in set(then_env) | set(else_env):
                tv, ev = then_env.get(var), else_env.get(var)
                if tv is None or ev is None:
                    raise NotImplementedError(
                        f"function: {var!r} assigned on only one branch of if (incomplete/latch)")
                if tv is not ev:
                    w = then_w.get(var) or else_w.get(var) or wenv.get(var, 1)
                    # a branch that is itself a Cond (chained else-if) must hoist so this Cond's
                    # branches stay plain value-terms (_emit_cond reads them via _word_body).
                    self._hoist_ctx = var
                    if isinstance(tv, Cond):
                        tv = self._hoist_word(tv, then_w.get(var, w), loc)
                    if isinstance(ev, Cond):
                        ev = self._hoist_word(ev, else_w.get(var, w), loc)
                    self._hoist_ctx = ""
                    env[var] = Cond(sel, tv, ev, w)
                    wenv[var] = w
            return
        if k == "Case":  # case (sel) v: ...; default: ... -> a first-match priority Cond chain
            if _enum_name(getattr(s, "condition", "")) in ("WildcardJustZ", "WildcardXOrZ"):
                # casez/casex (wildcard match) -- the executor can only do exact `eq`, which would
                # silently drop the don't-care masks. Defer to the branch path's casez handler (which
                # masks correctly and flags a multi-label/non-binary arm).
                raise NotImplementedError("casez/casex in a blocking always_comb (wildcard, not exact)")
            sel = self._lower_expr(s.expr, env)
            loc = self._loc_expr(s.expr)
            arms = []   # (cond_expr, is_single_compare, arm_env, arm_w)
            for item in s.items:
                cmps = []
                for lab in item.expressions:   # label may be an int Const or an enum Tag
                    cmps.append(BinOp("eq", sel, self._lower_expr(lab, env), 1))
                cond = cmps[0]
                for extra in cmps[1:]:          # `v1, v2: ...` -> (sel==v1) || (sel==v2)
                    cond = BinOp("logor", cond, extra, 1)
                a_env, a_w = dict(env), dict(wenv)
                self._exec_func_body(item.stmt, fname, a_env, a_w)
                arms.append((cond, len(cmps) == 1, a_env, a_w))
            def_env, def_w = dict(env), dict(wenv)   # the "no arm matched" path = case default / pre-case
            if getattr(s, "defaultCase", None) is not None:
                self._exec_func_body(s.defaultCase, fname, def_env, def_w)
            assigned = set(def_env)
            for _c, _s, ae, _w in arms:
                assigned |= set(ae)
            for var in assigned:
                result = def_env.get(var)
                if result is None:
                    raise NotImplementedError(f"function: {var!r} not defined on the case default path")
                rw = def_w.get(var) or wenv.get(var, 1)
                for cond, single, ae, aw in reversed(arms):   # first arm ends up outermost (priority)
                    av = ae.get(var)
                    if av is None or av is result:
                        continue
                    w = aw.get(var) or rw
                    self._hoist_ctx = var
                    if isinstance(av, Cond):       # branches must be plain value-terms for _emit_cond
                        av = self._hoist_word(av, w, loc)
                    if isinstance(result, Cond):
                        result = self._hoist_word(result, w, loc)
                    selbit = cond if single else self._hoist_bit(cond, loc)
                    self._hoist_ctx = ""
                    result = Cond(selbit, av, result, w)
                    rw = w
                if result is not env.get(var):
                    env[var] = result
                    wenv[var] = rw
            return
        if k == "ForLoop":   # statically-counted loop -> bounded unroll (the loop var is a Const/iter)
            self._unroll_func_loop(s, fname, env, wenv)
            return
        if k == "WhileLoop":   # unroll while the (folded) condition holds -- body updates the control var
            for _ in range(self._UNROLL_CAP + 1):
                cond = self._fold(self._lower_expr(s.cond, env))
                if cond is None:
                    raise NotImplementedError("function while: non-constant condition (not statically bounded)")
                if not cond:
                    break
                self._exec_func_body(s.body, fname, env, wenv)
            else:
                raise NotImplementedError(f"function while: exceeded unroll cap {self._UNROLL_CAP}")
            return
        if k == "RepeatLoop":   # repeat (N) -> N body copies (N constant)
            n = self._fold(self._lower_expr(s.count, env))
            if n is None or n < 0:
                raise NotImplementedError("function repeat: non-constant count")
            if n > self._UNROLL_CAP:
                raise NotImplementedError(f"function repeat: count {n} exceeds unroll cap {self._UNROLL_CAP}")
            for _ in range(n):
                self._exec_func_body(s.body, fname, env, wenv)
            return
        raise NotImplementedError(f"function body statement {k} (forever/do-while loop deferred)")

    _UNROLL_CAP = 4096   # synthesizable loops are statically bounded; this guards a runaway unroll

    def _unroll_foreach(self, s, fname: str, env: dict[str, Expr], wenv: dict[str, int]) -> None:
        """Unroll a ``foreach (a[i][j])``: each loop dim iterates over the array's DECLARED index
        range (in SV left->right order), the loop var bound to a Const per iteration, accumulating
        into env (like _unroll_func_loop). Dims with no loop var (`foreach(a[,j])`) are skipped."""
        import itertools
        ranges = []
        for ld in s.loopDims:
            lv = getattr(ld, "loopVar", None)
            if lv is None:
                continue                                   # an unindexed dimension -- not iterated
            r = ld.range                                   # ConstantRange, e.g. [3:0]
            step = 1 if r.right >= r.left else -1
            ranges.append((lv.name, list(range(r.left, r.right + step, step))))   # SV left->right order
        combos = list(itertools.product(*[vals for _, vals in ranges])) if ranges else [()]
        if len(combos) > self._UNROLL_CAP:
            raise NotImplementedError(f"foreach: {len(combos)} iterations exceed unroll cap {self._UNROLL_CAP}")
        for combo in combos:
            for (name, _vals), v in zip(ranges, combo, strict=True):
                env[name] = Const(v, 32)
                wenv[name] = 32
            self._exec_func_body(s.body, fname, env, wenv)

    def _unroll_func_loop(self, s, fname: str, env: dict[str, Expr], wenv: dict[str, int]) -> None:
        """Unroll a statically-counted ``for`` in a function: the loop var is a constant each
        iteration, so the body is executed with it bound to a Const, accumulating into env (the
        body's `c = c + x[i]` builds a chain). Bound/step are folded to ints; a non-constant bound,
        step, or init -> flagged (NotImplementedError), as is exceeding the unroll cap."""
        lvs = list(getattr(s, "loopVars", []))
        if len(lvs) != 1:
            raise NotImplementedError("function loop: expected exactly one loop variable")
        lv = lvs[0]
        lname, lwidth = lv.name, (getattr(getattr(lv, "type", None), "bitWidth", 32) or 32)
        init = getattr(lv, "initializer", None)
        cur = self._fold(self._lower_expr(init)) if init is not None else None
        step = list(getattr(s, "steps", []))
        if cur is None or getattr(s, "stopExpr", None) is None or len(step) != 1:
            raise NotImplementedError("function loop: non-constant init / missing bound or step")
        saved = env.get(lname)
        for _ in range(self._UNROLL_CAP + 1):
            env[lname] = Const(cur, lwidth)
            cond = self._fold(self._lower_expr(s.stopExpr, env))
            if cond is None:
                raise NotImplementedError("function loop: non-constant loop bound")
            if not cond:
                break
            self._exec_func_body(s.body, fname, env, wenv)
            st = step[0]                                          # advance: `i = <expr>` or `i++`/`i--`
            if _enum_name(st.kind) == "UnaryOp":
                nxt = cur + (1 if "ncrement" in _enum_name(st.op) else -1)
            else:
                nxt = self._fold(self._lower_expr(st.right, env))
            if nxt is None:
                raise NotImplementedError("function loop: non-constant step")
            cur = nxt
        else:
            raise NotImplementedError(f"function loop: exceeded unroll cap {self._UNROLL_CAP} (not bounded?)")
        if saved is not None:
            env[lname] = saved
        else:
            env.pop(lname, None)

    def _lower_expr(self, e, subst: dict[str, Expr] | None = None, top: bool = False) -> Expr:
        width = getattr(getattr(e, "type", None), "bitWidth", 1) or 1
        # An enum member is a symbolic TAG -- this MUST precede the constant fold below, which
        # would otherwise collapse IDLE/RUN/... to their integer encodings.
        peeled = self._peel(e)
        if _enum_name(peeled.kind) == "NamedValue" and peeled.symbol.name in self._enum_members:
            return Tag(peeled.symbol.name.lower())
        # Any fully-constant subtree (literal, cast, concat, param ref, `1<<(W-1)`) folds.
        # Formal-arg expressions are not constant -> _const_of returns None -> structural.
        # A bare in-scope genvar IS the lane index: lower it to the lane variable the rule head
        # binds (`val(y(I), …) :- addr(y,I), …`), so `y[i] = a + i` emits
        # `V1 = @add(V0, I, 32)` and each lane computes its own value. This must precede the
        # constant fold below, which would otherwise collapse it to iteration 0 (defect D1).
        if (_enum_name(peeled.kind) == "NamedValue" and peeled.symbol.name in self._genvars
                and not (subst and peeled.symbol.name in subst)):
            nm = peeled.symbol.name
            if nm in self._genvar_order:
                return LaneIdx(self._genvar_order.index(nm))
        cv = self._const_of(e)
        # Likewise a COMPOUND subtree mentioning a genvar (`i + 1`, `i * 8`) must stay
        # structural, so the genvar inside it reaches the LaneIdx case above.
        if cv is not None and self._genvars and self._expr_uses_genvar(e):
            cv = None
        if cv is not None:
            # A genvar is a Parameter, so ANY subtree mentioning it folds to THIS entry's value.
            # Under lane-rolling (one entry lowered, the index fanned) that bakes entry[0]'s index
            # into every lane -- silently wrong. Record it; `_lower_generate` turns it into a loud
            # refusal (defect D1). A genvar used as a bare ElementSelect SELECTOR never reaches
            # here: it is handled structurally (`_genvar_select_dims`) and rolls correctly.
            if self._genvars and self._expr_uses_genvar(e):
                self._genvar_folded = getattr(e, "syntax", None) and str(e.syntax) or "<expr>"
            return Const(self._mask(cv, width), width)
        # A SIGNED value widened by a Conversion must SIGN-EXTEND (replicate the sign bit); pyslang
        # keys this off the SOURCE signedness regardless of the target's. Every other conversion
        # (zero-extend, same-width reinterpret, truncation) leaves the stored integer unchanged, so
        # _peel drops it. This is the ONE conversion that is not a no-op in the bit-pattern model.
        if _enum_name(e.kind) == "Conversion":
            ot = getattr(e.operand, "type", None)
            # a value -> enum cast `e'(x)` maps the numeric value to its TAG via enum_value/3, NOT a
            # bit-pattern passthrough (which would define the result as a value, read elsewhere as a tag).
            if getattr(getattr(e, "type", None), "isEnum", False) and not getattr(ot, "isEnum", False):
                ename = self._decl_base(getattr(e, "type", None))
                if not ename:
                    raise NotImplementedError("value-to-anonymous-enum cast (no enum type name to map)")
                return EnumCast(self._lower_expr(e.operand, subst), ename)
            fw = getattr(ot, "bitWidth", None)
            if (getattr(ot, "isSigned", False) and fw and width > fw
                    and not getattr(ot, "isEnum", False) and not getattr(ot, "isStruct", False)):
                return SExt(self._lower_expr(e.operand, subst), fw, width)
        e = self._peel(e)
        k = _enum_name(e.kind)
        width = getattr(getattr(e, "type", None), "bitWidth", 1) or 1
        if k == "HierarchicalValue":   # inst.member -> inst(member); arr[i].sig -> ElemSel(arr(sig), i)
            return self._hier_ref(e)
        if k == "MemberAccess":
            uv = self._union_view(e)
            if uv is not None:                 # union member read -> slice/view of the union word
                root, off, w = uv
                if off == 0 and w == self._unions[root]:
                    return Ref(root)           # whole-width member -> the word itself
                return Slice(Ref(root), off + w - 1, off)
            base = self._peel(e.value)         # array-of-structs: arr[i].field = slice of the cell
            if _enum_name(base.kind) == "ElementSelect":
                ab = self._peel(base.value)
                if _enum_name(ab.kind) == "NamedValue" and ab.symbol.name in self._struct_mems:
                    w, off = next((fw, fo) for fn, fw, fo in self._struct_mems[ab.symbol.name]
                                  if fn == e.member.name)
                    cell = MemRef(ab.symbol.name, (self._lower_expr(base.selector, subst),))
                    return Slice(cell, off + w - 1, off)
            return self._member_ref(e)         # struct field read (p.f, or nested p.a.x as a slice)
        if k == "NamedValue":
            name = e.symbol.name
            # A lane/loop variable used as a VALUE. Lane-rolling lowers the body ONCE with the
            # index fanned by the grounder, so there is no signal to read: emitting Ref(name)
            # yields `val(i, V, T)` with nothing defining it, and the whole rule never fires --
            # the target is left UNBOUND while coverage reports success (defect D5). Record it;
            # the loop/generate lowering turns it into a loud refusal. A loop var used as a
            # SELECT INDEX never reaches here (handled structurally by _genvar_select_dims).
            if name in self._genvars and name not in (subst or {}):
                self._genvar_folded = f"loop/genvar {name!r} used as a value"
            if name in self._structs:          # whole struct read -> concat of fields (MSB-first)
                fields = sorted(self._structs[name], key=lambda fwo: fwo[2], reverse=True)
                return Concat(tuple((Ref(f"{name}({fn})"), w) for fn, w, _ in fields))
            if name in self._enum_members:     # enum member -> symbolic tag (NOT folded to int)
                return Tag(name.lower())
            if subst and name in subst:        # formal arg -> actual (inlining) / executor local
                v = subst[name]
                # In the always_comb executor, a scan accumulator read as a SUB-operand (e.g. `cnt+1`,
                # where cnt is a Cond) must hoist to a plain tern_ Ref -- _word_body has no Cond case.
                if getattr(self, "_exec_comb", False) and isinstance(v, Cond) and not top:
                    return self._accumulator_tern(v, width, self._loc_expr(e))
                return v
            cv = self._const_of(e)             # e.g. a package parameter folds to its value
            return Const(self._mask(cv, width), width) if cv is not None else Ref(name)
        if k == "UnbasedUnsizedIntegerLiteral":
            # `'x` / `'z` (and `'0` / `'1`): the unbased-unsized literal, width taken from context.
            # The x/z forms are the same "unconstrained" statement as a sized `4'bx` (see XVal); the
            # 0/1 forms are ordinary values replicated across the width.
            if getattr(getattr(e, "value", None), "hasUnknown", False):
                return XVal(width)
            v = int(e.value)
            return Const(((1 << width) - 1) if v else 0, width)
        if k == "IntegerLiteral":
            # An x/z bit in a VALUE literal has no meaning in the 2-state model, and int() on an
            # unknown SVInt silently returns 0 -- `8'hxx` became 0 and `8'b1010xx01` became 0
            # (even the known bits vanished) with a clean run (Fix 87). Refuse LOUDLY instead:
            # raising here lands in `Design.flagged` via the lowering safety net, so it is a
            # coverage PROBLEM (--strict-coverage exits non-zero), exactly what the catalog
            # already promised. (casex/casez LABELS never reach this path -- their x/z bits are
            # pattern wildcards, consumed by `_hoist_masked_eq` from the label's syntax text.)
            # The exact-X reading of such a literal is designed but not adopted:
            # notes/design/X_SEMANTICS.md.
            kind, masked = _lit_intake(bool(getattr(e.value, "hasUnknown", False)),
                                       int(e.value), width)
            if kind == "refused":
                # UNCONSTRAINED, not refused (2026-08-20): the literal has no 2-state value, and
                # `_lit_intake` still says so -- what changed is what we do with that answer. In a
                # VALUE position the RTL is saying "the design does not constrain this here", which
                # the boundary layer already expresses as a choice. XVal carries the statement; the
                # emitter turns it into a guarded choice in the companion, and refuses it by name if
                # it reaches a place where a value is genuinely required (a comparison, arithmetic).
                return XVal(width)
            return Const(masked, width)
        if k == "Call":
            res = self._inline_call(e, subst)
            # a function whose result is a Cond (built from if/else in its body) must hoist when
            # used nested in a larger expression, exactly like a nested ternary.
            if isinstance(res, Cond) and not top:
                return self._hoist_word(res, res.width, self._loc_expr(e))
            return res
        if k == "BinaryOp":
            opname = _enum_name(e.op)
            if opname == "BinaryXnor":           # a ~^ b == ~(a ^ b) -- reuse not+xor (bit AND word)
                xor = BinOp("xor", self._lower_expr(e.left, subst), self._lower_expr(e.right, subst), width)
                return UnOp("not", xor, width)
            op = _BINOP.get(opname)
            if op is None:
                cv = self._const_of(e)
                if cv is not None:
                    return Const(self._mask(cv, width), width)
                raise NotImplementedError(f"binop {e.op}")
            # Signedness is read from pyslang's elaborated operand types (it inserts conversions to
            # apply SV's coercion rules for us). A compare is signed iff BOTH operands are signed;
            # >>> is arithmetic only when the shifted operand is signed; signed div/mod get @sidiv/@simod.
            lt, rt = getattr(e.left, "type", None), getattr(e.right, "type", None)
            lsig = bool(getattr(lt, "isSigned", False))
            rsig = bool(getattr(rt, "isSigned", False))
            lw = getattr(lt, "bitWidth", width) or width
            rw = getattr(rt, "bitWidth", width) or width
            if opname == "ArithmeticShiftRight" and not lsig:
                op = "shr"                                   # unsigned >>> is a logical shift
            if op in ("div", "mod") and (lsig or rsig):
                op = "sidiv" if op == "div" else "simod"
            signed = (op in _CMP_OPS and lsig and rsig) or op in ("ashr", "sidiv", "simod")
            opw = max(lw, rw) if op in _CMP_OPS else width
            left_ir  = self._lower_expr(e.left,  subst)
            right_ir = self._lower_expr(e.right, subst)
            # a ONE-bit bitwise and/or whose operands carry boolean nodes -- `(w == 3) | (w == 4)`,
            # the Booth encoder's digit bits -- is the logical connective of the same name at that
            # width, and only as such does the item-level boolean emitter take it (the word
            # cascade refused it as `word expr BinOp`; a field report, 2026-09-04)
            if width == 1 and op in ("and", "or") and (_has_bool_node(left_ir) or _has_bool_node(right_ir)):
                op = "log" + op
            # ── Replication-masked mux: {N{cond_1bit}} & data  →  Cond(cond, data, 0)
            # This RTL idiom implements a mux arm: all-ones mask passes data; all-zeros passes 0.
            # The correct translation is one rule per arm (firing independently on cond),
            # NOT one monolithic rule requiring all sources.  Mirrors how if/else translates.
            if op == "and" and width > 1:
                def _repl_mask(c: object, W: int):
                    """If c is Concat of W identical 1-bit parts, return the condition expr.
                    Unwraps a single-element Concat wrapper ({x} → x) before returning."""
                    if not isinstance(c, Concat) or len(c.parts) != W:
                        return None
                    first_e, first_w = c.parts[0]
                    if first_w != 1:
                        return None
                    if not all(pe == first_e and pw == 1 for pe, pw in c.parts):
                        return None
                    # Unwrap a single-element Concat wrapper: {x} → x
                    while isinstance(first_e, Concat) and len(first_e.parts) == 1:
                        first_e = first_e.parts[0][0]
                    return first_e
                cond = _repl_mask(left_ir, width)
                if cond is not None:
                    # {width{cond_1bit}} & data  →  Cond(cond, data, 0)
                    # When cond is compound (e.g. a & b), hoist it to a gcond_N bit first so the
                    # Cond selector is always a simple Ref that _cond_branches can split on.
                    loc = self._loc_expr(e)
                    if not isinstance(cond, Ref):
                        cond = self._hoist_bit(cond, loc)
                    node = Cond(cond, right_ir, Const(0, width), width)
                    return self._hoist_word(node, width, loc)
                cond = _repl_mask(right_ir, width)
                if cond is not None:
                    loc = self._loc_expr(e)
                    if not isinstance(cond, Ref):
                        cond = self._hoist_bit(cond, loc)
                    node = Cond(cond, left_ir, Const(0, width), width)
                    return self._hoist_word(node, width, loc)
            return BinOp(op, left_ir, right_ir, width, signed=signed, opw=opw)
        if k == "UnaryOp":
            uop = _UNOP[_enum_name(e.op)]
            # a REDUCTION (&x, |x, ^x, ...) yields 1 bit but the emitter needs the OPERAND width
            # (`&x == all-ones(W)`, parity over W bits) -> carry the operand width in `.width` (the
            # result is always 1, so the field is free). Non-reduction unaries keep the result width.
            if uop in ("ror", "rand", "rxor", "rnor", "rnand", "rxnor"):
                ow = getattr(getattr(e.operand, "type", None), "bitWidth", width) or width
                return UnOp(uop, self._lower_expr(e.operand, subst), ow)
            return UnOp(uop, self._lower_expr(e.operand, subst), width)
        if k == "LValueReference":
            # A COMPOUND assignment (`q_next[2] ^= q[0];`, `count += 1;`) elaborates to
            # `<target> = LValueReference <op> rhs`, where the reference stands for the target READ.
            # Resolve it by lowering the assignment's own LHS as an expression -- `_lvalue_node` is
            # set by the statement lowering around the RHS. Without this the whole always-block failed
            # with `NotImplementedError: expr kind LValueReference` (VerilogEval's lfsr5/lfsr32).
            node = getattr(self, "_lvalue_node", None)
            if node is None:
                raise NotImplementedError("compound assignment outside an assignment context")
            return self._lower_expr(node, subst)
        if k == "ConditionalOp":  # inline ternary  sel ? then : else
            cond = Cond(self._lower_cond_sel(e.conditions[0].expr, subst),
                        self._lower_expr(e.left, subst),    # arms lowered as children (top=False):
                        self._lower_expr(e.right, subst), width)   # a nested ternary arm hoists too
            if top:
                return cond            # top-level rhs -> emitted directly by _emit_cond
            # NESTED ternary (sub-expression) -> hoist into a synthetic combinational signal so the
            # enclosing word/bit emit sees a plain Ref (Cond can't be a single value-term). An
            # enum-valued ternary's temp is enum-typed (it holds TAGS) -- see _hoist_word.
            return self._hoist_word(cond, width, self._loc_expr(e),
                                    enum_type=self._enum_type_name(getattr(e, "type", None)))
        if k == "ElementSelect":
            sfm = self._struct_field_mem_select(e)
            if sfm is not None:    # s.arr[idx] read -> a memory cell of the struct-field memory s(arr)
                mem, sel = sfm
                return MemRef(mem, (self._lower_expr(sel, subst),))
            base = self._peel(e.value)
            gs = self._genvar_select_dims(e)
            root = self._select_root(e)          # `q` for q[i][j] (base.symbol is None there)
            root_mem = root is not None and getattr(getattr(root, "type", None), "isUnpackedArray", False)
            # genvar-indexed: a generate-nest packed lane, OR a memory cell lane-rolled over addr(mem,I[,J])
            if gs is not None:
                if root_mem:
                    self._check_genvar_index_order(e, gs)
                    self._check_array_rank(root.name, gs[1])
                    return MemRef(root.name, tuple(LaneIdx(p) for p in range(gs[1])))
                self._lane_dims[gs[0]] = max(self._lane_dims.get(gs[0], 0), gs[1])
                self._note_lane_elem_w(gs[0], getattr(getattr(e, "type", None), "bitWidth", 1) or 1)
                vs = self._genvar_select_vars(e)
                if vs != self._genvar_order[:len(vs)]:
                    # NOT the nesting-order prefix: the bare `Ref` would be rendered in the
                    # enclosing rule's own index order -- `a[c]` under `for (r) for (c)` read
                    # `a(I)`, the ROW, so a nested-generate register bank took the wrong input
                    # (F39, 2026-09-03); `a[j][i]` was the same defect refused as a transpose.
                    # An explicit lane select carries each genvar's OWN position instead.
                    pos = [LaneIdx(self._genvar_order.index(v)) for v in vs]
                    return ElemSel(gs[0], pos[0], more=tuple(pos[1:]))
                return Ref(gs[0])
            idx = self._lower_expr(e.selector, subst)
            # base substituted to an actual EXPRESSION (function inlining): a[i] is a bit-slice of
            # the actual, not a select on a named signal. The index must be constant -- fold the
            # SUBSTITUTED selector (so a loop var bound to a Const this iteration resolves).
            if _enum_name(base.kind) == "NamedValue" and subst and base.symbol.name in subst:
                ci = self._fold(idx)
                if ci is None:
                    raise NotImplementedError("dynamic index into a substituted (function-arg) expression")
                return Slice(subst[base.symbol.name], ci, ci)
            # an unpacked array is a memory cell read: q[a] / q[a][b] -> val(q, A1[, A2], V, T)
            if root_mem:
                idxs = self._select_indices(e, subst)
                rank = len(self._mem_dims.get(root.name, (1,)))
                # ONE index MORE than the array has dimensions: the first `rank` address the array
                # and the last selects a BIT INSIDE THE CELL. `pht[i][1]` is bit 1 of cell i -- how
                # a table of saturating counters is read (the MSB is the prediction). This was
                # refused wholesale as a rank mismatch, which it is not: the ranks agree, there is
                # simply a select on the value the cell holds. @slc composes over the cell read.
                if len(idxs) == rank + 1:
                    self._check_array_rank(root.name, rank)      # keeps the >=3-D refusal
                    ci = self._fold(idxs[rank])
                    if ci is None:
                        raise NotImplementedError(
                            f"{root.name}: a RUNTIME bit index into a memory cell "
                            f"(`{root.name}[a][b]`, b not constant)")
                    return Slice(MemRef(root.name, tuple(idxs[:rank])), ci, ci)
                self._check_array_rank(root.name, len(idxs))
                return MemRef(root.name, tuple(idxs))
            # a packed WORD select a[i] is a bit/element SLICE (val(a,i,..) would be a phantom lane).
            # A NESTED packed select a[i][j] (base is itself a select, no .symbol) recurses: the inner
            # select lowers to a Slice and the outer is a slice-of-that (@slc composes).
            if _enum_name(base.kind) == "NamedValue":
                name = base.symbol.name
                # A NEIGHBOURING-LANE read `x[i-1]` / `x[i+1]` of a packed signal is a lane read
                # `x(I-1)` UNCONDITIONALLY -- and it makes `x` a lane (element width = the select's)
                # the same way `x[i]` does. It used to be a lane read only if `x` was a lane
                # ALREADY (`name in self._lane_dims`), which made the decision depend on SOURCE
                # ORDER: `assign sh_d[i] = sh_q[i-1]` written ABOVE the generate that registers
                # `sh_q[i]` fell to the dynamic-element path below, `(sh_q >> (i-1)*8) & 255` on
                # the WORD -- and the emitter, by then knowing `sh_q` as a lane, read the bare
                # `Ref(sh_q)` inside the lane body as lane I: `sh_q(I) >> (I-1)*8`, a shift
                # register that never shifted, exit 0, VERDICT OK (F17). Written BELOW it, the same
                # line was refused as a "non-copy" lane comb. Same-target chains (`c[i] = c[i-1] &
                # p[i]`) were already safe because the WRITE registers the lane before the RHS is
                # lowered; a chain between two DIFFERENT lane signals was not.
                if (self._genvar_offset_select(e) is not None
                        and not getattr(base.symbol.type, "isUnpackedArray", False)):
                    ew = getattr(getattr(e, "type", None), "bitWidth", 1) or 1
                    self._lane_dims[name] = max(self._lane_dims.get(name, 0), 1)
                    self._note_lane_elem_w(name, ew)
                    return ElemSel(name, idx)
                if name in self._lane_dims:      # a genuine lane/INDEXED signal -> per-lane read
                    return ElemSel(name, idx)
                # F27: a COMPUTED genvar index (`q[(i+240) % 256]`, the toroid's wrap) is a lane
                # read like its affine sibling above -- WHATEVER the arithmetic. It used to fall
                # through to the word desugar below, and the emitter, knowing the base as a lane
                # by then, read the bare Ref inside the lane body as lane I and shifted THE ONE
                # BIT by the computed index: conwaylife's up(I) = (q(I) >> ((I+240)%256)) & 1,
                # exit 0, coverage OK -- found by the ASP-first round trip, silent to everything
                # else. The base is NOT forced into _lane_dims here: whether it ends up per-lane
                # is its own drivers' decision, and the emitter's ElemSel arm lowers by the FINAL
                # shape -- a lane read when INDEXED, the masked word shift when WORD -- so the
                # decision no longer depends on source order (the F17 lesson).
                if (getattr(getattr(e, "type", None), "bitWidth", 1) or 1) == 1 \
                        and self._genvars and _mentions_laneidx(idx):
                    return ElemSel(name, idx)
                base_expr = Ref(name)
            else:                                # nested packed select a[i][j] -> slice of a slice
                root = self._select_root(e)
                pd = self._packed_dims(root.type) if root is not None else ()
                if (root is not None and len(pd) >= 2 and self._genvars
                        and (getattr(getattr(e, "type", None), "bitWidth", 1) or 1) == 1
                        and not getattr(root.type, "isUnpackedArray", False)):
                    idxs = self._select_indices(e, subst)
                    # only when a genvar indexes a level BEYOND the first: `enc[i][2]` on a lane
                    # of 3-bit elements is bit 2 of lane i's ELEMENT (a slice of the lane's
                    # value, below), not a two-level lane read -- which registered a one-bit
                    # view of `enc` beside its three-bit one and refused the signal (a field
                    # report, 2026-09-04)
                    if len(idxs) == len(pd) and any(_mentions_laneidx(ix) for ix in idxs[1:]):
                        # F27's MULTI-LEVEL sibling: `q[f(r)][c]` on `logic [R-1:0][C-1:0] q`
                        # with a genvar in an index is a two-level LANE READ `q(f(I), J)`, not a
                        # slice of a slice of the word -- the word of a 256-bit port is the F32
                        # wall, and a scenario that pins the members never supplies it (the 2-D
                        # torus's round trip read nothing, 2026-09-03). The root is a lane with
                        # one level per packed dimension BY CONSTRUCTION (the F17 rule), so its
                        # word<->lane bridge decomposes per member.
                        self._lane_dims[root.name] = max(self._lane_dims.get(root.name, 0), len(pd))
                        self._note_lane_elem_w(root.name, 1)
                        return ElemSel(root.name, idxs[0], more=tuple(idxs[1:]))
                base_expr = self._lower_expr(e.value, subst)
            ew = getattr(getattr(e, "type", None), "bitWidth", 1) or 1
            ci = self._fold(idx)
            if ci is not None:                   # constant index -> a constant Slice (-> @slc)
                return Slice(base_expr, ci * ew + ew - 1, ci * ew)
            if ew == 1:
                # Dynamic BIT select `a[i]` -> a 1-bit word signal holding `(base >> i) & 1`.
                #
                # The mask is NOT optional. This used to emit a bare `BinOp("shr", base, i, 1)`
                # with the comment "width 1 self-masks" -- and `@shr` IGNORES its width argument
                # (`fShr a n _w = a >>> n`, proven in the M1 layer), so nothing masked anything.
                # `z = a[i]` became `(a >> i) != 0`, TRUE whenever any HIGHER bit was set: with
                # a = 8'b1011_0101 it read 1 at i = 1, 3 and 6, where the selected bit is 0
                # (Fix 84). Nested in a word expression the unmasked value flowed in whole.
                #
                # HOISTED rather than returned inline, because the 1-bit emitter decomposes a
                # boolean tree over registered leaves and cannot take `and(shr(..), 1)` as one:
                # as a named 1-bit signal it is an ordinary word rule, which every consumer --
                # bit path, word path, concat -- already reads correctly.
                return Slice(BinOp("shr", base_expr, idx, 1), 0, 0)
            sh = BinOp("mul", idx, Const(ew, 32), 32)   # dynamic element: (base >> i*ew) & mask
            return BinOp("and", BinOp("shr", base_expr, sh, ew), Const((1 << ew) - 1, ew), ew)
        if k == "RangeSelect":
            # The byte-lane idiom `a[i*W +: W]` is lane `i` of `a` as W-bit lanes: the same
            # `Ref(a)` a packed 2-D `a[i]` gives, with the element width recorded so the bridge
            # decomposes the word at `I * W`. It used to be refused as a genvar VALUE use.
            ls = self._genvar_lane_slice(e)
            if ls is not None and not (subst and ls[0] in subst):
                name, w = ls
                self._lane_dims[name] = max(self._lane_dims.get(name, 0), 1)
                self._note_lane_elem_w(name, w)
                return Ref(name)
            base = self._lower_expr(e.value, subst)
            sk = getattr(getattr(e, "selectionKind", None), "name", "Simple")
            # Any OTHER genvar in a slice BOUND (`a[i*8 + 4 +: 4]`) folds to this entry's value
            # just like a value use, and lane-rolling would give every lane iteration 0's slice.
            # Record it so `_lower_generate` refuses (defect D1); the bounds themselves still fold.
            if self._genvars and (self._expr_uses_genvar(e.left) or self._expr_uses_genvar(e.right)):
                # a window whose bounds are AFFINE in the genvar with a width the same at every
                # iteration -- `m[2*i+2 : 2*i]`, the Booth encoder's sliding window, or
                # `a[2*i +: 3]` -- is the word shifted right by the affine amount and masked
                # (the runtime-base form below, with the lane index as the amount). Anything
                # else in a bound still folds to one iteration and is recorded for the refusal
                # (a field report, 2026-09-04)
                try:
                    if self._lane_hi - self._lane_lo <= (self._lane_step or 1):
                        raise _NotAffineRead()      # ONE iteration: the genvar is that constant (D1 allows it) -- fold below
                    if sk == "Simple":
                        hi_ir, lo_ir = self._affine_ir(e.left), self._affine_ir(e.right)
                        ws = {self._eval_affine(hi_ir, i) - self._eval_affine(lo_ir, i) + 1 for i in self._lane_range()}
                    else:
                        wc = self._const_of(e.right)
                        b_ir = self._affine_ir(e.left)
                        lo_ir = b_ir if sk == "IndexedUp" else BinOp("sub", b_ir, Const(wc - 1, 32), 32)
                        ws = {wc} if wc is not None else set()
                    if len(ws) == 1 and next(iter(ws)) >= 1:
                        w = ws.pop()
                        return BinOp("and", BinOp("shr", base, lo_ir, w), Const((1 << w) - 1, w), w)
                except Exception:
                    pass
                if self._lane_hi - self._lane_lo <= (self._lane_step or 1):
                    # a single-iteration run: the bounds fold to that iteration's constants, which
                    # is exact -- and the target need not be a lane (the reporter's word-headed
                    # unsafe rule, 2026-09-04: `top = src[2*i +: 3]` under `if (i == 3)`)
                    pass
                else:
                    self._genvar_folded = "slice bound"
            if sk == "Simple":                      # [hi:lo] -- left is hi, right is lo
                hi = self._const_of(e.left)
                lo = self._const_of(e.right)
                return Slice(base, hi if hi is not None else 0, lo if lo is not None else 0)
            # indexed part-select [b +: w] / [b -: w]: left is the base, right the (constant) width.
            # +: selects [b+w-1 : b]; -: selects [b : b-w+1].
            b = self._const_of(e.left)
            w = self._const_of(e.right)
            if w is None:
                raise NotImplementedError("indexed part-select with a non-constant width")
            if b is not None:                                   # constant base -> a constant Slice
                lo, hi = (b, b + w - 1) if sk == "IndexedUp" else (b - w + 1, b)
                return Slice(base, hi, lo)
            # DYNAMIC base: a[i +: w] = (a >> i) & ((1<<w)-1); a[i -: w] shifts by i-(w-1).
            loff = self._lower_expr(e.left, subst)
            if sk == "IndexedDown":
                loff = BinOp("sub", loff, Const(w - 1, w), w)
            return BinOp("and", BinOp("shr", base, loff, w), Const((1 << w) - 1, w), w)
        if k == "Concatenation":
            cv = self._const_of(e)
            if cv is not None:
                return Const(self._mask(cv, width), width)
            # runtime concat: MSB-first parts, each with its own width. A boolean part
            # (`{(s==IDLE), x}`) hoists to a gcond bit so it reads as a 1-bit word value.
            lowered = [(self._lower_expr(op, subst), op) for op in e.operands]
            if all(isinstance(p, XVal) for p, _ in lowered):
                return XVal(width)                      # `{1'bx, 1'bx}` IS `2'bx` -- see _all_x below
            return Concat(tuple((self._as_word(p, self._loc_expr(op)), op.type.bitWidth)
                                for p, op in lowered))
        if k == "Replication":
            cv = self._const_of(e)
            if cv is not None:
                return Const(self._mask(cv, width), width)
            # {N{x}} -- N is always a constant (SV); x may be runtime -> an N-copy concat
            n = self._const_of(e.count) or 0
            unit = self._lower_expr(e.concat, subst)
            # A replication of `x` IS an x value of the whole width: `{n{1'bx}}` == `n'bx`, which is
            # how a reference says "this output means nothing when it is not valid". Fold it, so the
            # ASSIGNED-x path sees the statement it understands (no value rule + `dontcare_at`)
            # instead of an x buried inside a concat, which reads as computing WITH x and is refused.
            # A MIXED concat (`{a, 1'bx}`) is deliberately NOT folded: it says some bits are
            # unconstrained and others are not, and `dontcare_at` is a whole-signal declaration --
            # so it stays a named refusal rather than a quiet half-truth.
            if isinstance(unit, XVal):
                return XVal(width)
            return Concat(tuple([(unit, e.concat.type.bitWidth)] * n))
        if k == "SimpleAssignmentPattern":
            cv = self._const_of(e)
            if cv is not None:
                return Const(self._mask(cv, width), width)
        # constant-foldable fallback
        cv = self._const_of(e)
        if cv is not None:
            return Const(self._mask(cv, width), width)
        raise NotImplementedError(f"expr kind {k}: {str(e)[:50]}")


# re-export MemRead name used in Design (combinational reads are CombItems for M1)


def _mentions_laneidx(e) -> bool:
    """True when lowered expr ``e`` contains a LaneIdx -- i.e. the value depends on a genvar."""
    if isinstance(e, LaneIdx):
        return True
    for f in getattr(e, "__dataclass_fields__", {}):
        v = getattr(e, f)
        for x in (v if isinstance(v, tuple) else (v,)):
            if isinstance(x, tuple):
                if any(_mentions_laneidx(y) for y in x):
                    return True
            elif isinstance(x, Expr) and _mentions_laneidx(x):
                return True
    return False
