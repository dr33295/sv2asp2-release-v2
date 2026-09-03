from __future__ import annotations

import dataclasses

import re

import pyslang

from ..ir.expr import BinOp, BitSel, Concat, Cond, Const, ElemSel, EnumCast, EnumVal, Expr, MemRef, Ref, SExt, Slice, UnOp
from ..ir.nodes import (
    Branch, CellInfo, Clock, CombItem, DerivedClock, Design, Loc, Mem, MemWrite, MuxItem,
    LatchItem, Reset, SeqItem, Signal, VffItem,
)
from ..ir.types import IRType, Kind
from ._common import _ID_RUN



#: Fields this rebuild NORMALISES (they contain names that must become clingo constants).
_NORMALISED_FIELDS = frozenset({
    "name", "signals", "mems", "clocks", "comb", "seq", "mem_writes", "muxes", "vffs",
    "latches", "inferred_latches", "lane_signals", "lane_dims", "lane_elem_w", "lane_domains", "cells",
    "packed_dims", "derived_clocks", "edges",
})

#: Fields carried through UNCHANGED, because they hold no design-name strings.
_CARRIED_FIELDS = frozenset({
    "params", "resets", "mem_reads", "enums", "flagged", "warned", "stub_rules",
})


def _check_design_fields() -> None:
    """Every `Design` field must be classified: normalised here, or explicitly carried.

    The name-normalisation rebuild is the one place a new `Design` field can vanish without
    a symptom -- the translation simply proceeds as if the feature were absent. That has bitten
    twice. Enumerating the dataclass and refusing anything unclassified turns "remember to add
    it here" into a loud failure, the same way the proof ledger enumerates its obligation
    surface instead of trusting a list."""
    actual = {f.name for f in dataclasses.fields(Design)}
    unclassified = actual - _NORMALISED_FIELDS - _CARRIED_FIELDS
    if unclassified:
        raise AssertionError(
            f"Design field(s) {sorted(unclassified)} are not classified in _types.py. Add each "
            f"to _NORMALISED_FIELDS (and normalise it in the rebuild below) if it holds design "
            f"NAMES, or to _CARRIED_FIELDS if it does not. Leaving it out would silently drop "
            f"the field during name normalisation.")
    stale = (_NORMALISED_FIELDS | _CARRIED_FIELDS) - actual
    if stale:
        raise AssertionError(f"_types.py classifies Design field(s) {sorted(stale)} that no "
                             f"longer exist -- remove them.")


class _TypesMixin:
    """_TypesMixin: types methods of PyslangFrontend (split out from the monolith)."""

    def _line_text(self, file: str, line: int) -> str:
        lines = self._src_cache.get(file)
        if lines is None:
            try:
                with open(file) as f:
                    lines = f.read().splitlines()
            except OSError:
                lines = []
            self._src_cache[file] = lines
        return lines[line - 1].strip() if 0 < line <= len(lines) else ""

    def _loc(self, sym: object) -> Loc:
        loc = sym.location
        file = self._sm.getFileName(loc)
        line = self._sm.getLineNumber(loc)
        return Loc(file=file, line=line, text=self._line_text(file, line))

    def _kind(self, t: object) -> Kind:
        return Kind.SIGNED if getattr(t, "isSigned", False) else Kind.BIT

    @staticmethod
    def _decl_base(t: object) -> str:
        """The declared SV base keyword / typedef name as a clingo constant: ``logic[7:0]`` -> logic,
        ``int`` -> int, a typedef ``fifo_pkg.data_t`` -> data_t. Drops packed dims + signed modifier
        (width/signedness live in kind/width) and the scope qualifier; lowercased (a clingo constant
        starts lowercase, matching the enum/tag convention). An anonymous type whose name isn't a clean
        identifier (`enum{...}`, `struct packed{...}`) yields "" -> no decl_type atom (nothing to name)."""
        s = str(t)
        tok = s.split("[", 1)[0].split()[0].split(".")[-1].lower() if s.strip() else ""
        return tok if re.fullmatch(r"[a-z_][a-z0-9_]*", tok) else ""

    def _irtype(self, t: object) -> IRType:
        """IRType carrying both the interpretation (kind/width) and the declared SV type (base + 2/4-state)."""
        return IRType(self._kind(t), getattr(t, "bitWidth", 1) or 1,
                      sv_base=self._decl_base(t), four_state=bool(getattr(t, "isFourState", False)))

    @staticmethod
    def _packed_dims(t: object) -> tuple[int, ...]:
        """The packed-array dimension widths of a type, outer-to-inner: ``logic [3:0][7:0]`` -> (4, 8),
        ``logic [7:0]`` -> (8,), a scalar -> (). The type/3 width is the flattened product; only a
        signal with >=2 dims (a genuine matrix) needs the packed_dims schema atom."""
        cur = getattr(t, "canonicalType", t)
        dims: list[int] = []
        while "PackedArray" in str(getattr(cur, "kind", "")):
            rng = cur.range
            dims.append(abs(rng.left - rng.right) + 1)
            cur = cur.elementType.canonicalType
        return tuple(dims)

    @staticmethod
    def _mask(v: int, w: int) -> int:
        """Force a value into its w-bit two's-complement bit pattern (0..2^w-1). A negative
        SV constant literal (``int(SVInt)`` of a signed literal) becomes its stored pattern,
        preserving the invariant that every value in a val/4 atom is non-negative."""
        return v & ((1 << w) - 1) if v < 0 else v

    @staticmethod
    def _cv_int(cv: object) -> int | None:
        """ConstantValue -> python int, or None if not a clean integer constant.

        ``cv.value`` is an SVInt for integer constants; ``int()`` of it works.
        Non-constant / empty values raise or are absent -> None.

        x/z bits are checked EXPLICITLY: the old docstring claimed unknown values "raise",
        but ``int()`` of an unknown SVInt silently returns 0 -- `8'hxx` folded to 0 with a
        clean run (Fix 87). None here means "not a clean constant", which callers already
        handle; the LOUD refusal for value positions lives in `_const_of` and the
        IntegerLiteral lowering, where the safety net turns it into a coverage PROBLEM."""
        try:
            if getattr(cv.value, "hasUnknown", False):
                return None
            return int(cv.value)
        except Exception:  # noqa: BLE001
            return None

    def _const_of(self, e: object) -> int | None:
        """Return the constant value of an expression if it folds, else None.

        Tries the cached ``.constant`` first (populated for elaborated-context exprs);
        falls back to evaluating in the current scope (``self._eval_scope``) — needed
        for constant subexprs inside an uninstantiated function body (e.g. `1<<(W-1)`).
        """
        cv = getattr(e, "constant", None)
        # A folded constant carrying x/z bits is REFUSED, not silently misread: int() of an
        # unknown SVInt returns 0 (Fix 87), so without this check `8'hxx` becomes the value 0
        # and `a + 8'b1010xx01` becomes `a + 0` -- even the known bits vanish -- with a clean
        # run. Raising here lands in Design.flagged via the lowering safety net -> a coverage
        # PROBLEM. The exact-X reading is designed, not adopted: notes/design/X_SEMANTICS.md.
        if cv is not None and getattr(getattr(cv, "value", None), "hasUnknown", False):
            # BOTH refusal funnels route through the ONE pure decision `_lit_intake` (this
            # constant-fold funnel is the dominant one -- pyslang folds most literals before
            # the IntegerLiteral fallback ever sees them). Width is unknown at this funnel and
            # irrelevant to the refusal; 0 is the documented sentinel.
            from ._exprs import _lit_intake
            if _lit_intake(True, 0, 0)[0] == "refused":
                raise NotImplementedError(
                    f"x/z bits in a constant value ({cv}) -- no meaning in the 2-state model; "
                    "int() would silently read it as 0. See notes/design/X_SEMANTICS.md")
        v = self._cv_int(cv)
        if v is not None:
            return v
        scope = getattr(self, "_eval_scope", None)
        if scope is None:
            return None
        try:
            ctx = pyslang.ASTContext(scope, pyslang.LookupLocation.max)
            return self._cv_int(e.eval(pyslang.EvalContext(ctx)))
        except Exception:  # noqa: BLE001
            return None

    # -- module --------------------------------------------------------------
    @staticmethod
    def _cid(name: str) -> str:
        if not name:
            return name
        def fix(m: re.Match) -> str:
            s = m.group(0)
            if "A" <= s[0] <= "Z":
                return s[0].lower() + s[1:]
            return "u" + s if s[0] == "_" else s   # leading _ is also a variable -> prefix a letter
        return _ID_RUN.sub(fix, name)

    def _norm_expr(self, e: Expr) -> Expr:
        c, ne = self._cid, self._norm_expr
        if isinstance(e, Ref):
            return Ref(c(e.name))
        if isinstance(e, MemRef):
            return MemRef(c(e.mem), tuple(ne(a) for a in e.addrs))
        if isinstance(e, ElemSel):
            return ElemSel(c(e.base), ne(e.index), tuple(ne(x) for x in e.more))
        if isinstance(e, BinOp):
            return BinOp(e.op, ne(e.left), ne(e.right), e.width, e.signed, e.opw)
        if isinstance(e, UnOp):
            return UnOp(e.op, ne(e.operand), e.width)
        if isinstance(e, SExt):
            return SExt(ne(e.operand), e.from_w, e.to_w)
        if isinstance(e, Slice):
            return Slice(ne(e.base), e.hi, e.lo)
        if isinstance(e, BitSel):
            return BitSel(ne(e.base), e.index)
        if isinstance(e, Concat):
            return Concat(tuple((ne(x), w) for x, w in e.parts))
        if isinstance(e, Cond):
            return Cond(ne(e.sel), ne(e.a), ne(e.b), e.width)
        if isinstance(e, EnumCast):
            return EnumCast(ne(e.operand), e.enum)
        if isinstance(e, EnumVal):
            return EnumVal(ne(e.operand), e.enum)
        return e   # Const / Tag / LaneIdx -- no signal name to normalize

    def _check_cid_injective(self, d: Design) -> list[tuple[Loc, str]]:
        """`_cid` must not merge two DISTINCT SystemVerilog names into one ASP atom (Fix 75).

        ASP constants must start with a lowercase letter, so `_cid` lowercases a leading capital
        and prefixes a leading underscore with `u`. SystemVerilog is CASE-SENSITIVE, so that map
        is not injective: `Y_OUT` and `y_OUT` are two different signals and both become
        `y_OUT`; so do `_b` and `u_b`.

        The consequence is not an unbound signal, it is a MULTI-VALUED one -- both drivers write
        the same atom, so `val(y_OUT, 0, T)` and `val(y_OUT, 1, T)` are derivable in the same
        cycle. That breaks the single-value invariant every register and mux theorem assumes,
        and an inconsistent model proves anything: a property requiring a violation finds a
        spurious one, a property forbidding one comes back unsatisfiable. It translated cleanly
        with `coverage: OK` and exit 0.

        Reported rather than renamed. Making the map injective (escaping the case) would rename
        every signal in every emitted file and cost the legibility that makes reading the model
        a workable review step -- and a design with two names differing only in case is
        pathological RTL, not something to accommodate silently."""
        by_atom: dict[str, set[str]] = {}
        locs: dict[str, Loc] = {}
        for name, loc in [*((s.name, s.loc) for s in d.signals),
                          *((m.name, None) for m in d.mems),
                          *((ci.inst, None) for ci in d.cells),
                          *((ck.name, None) for ck in d.clocks)]:
            if name:
                by_atom.setdefault(self._cid(name), set()).add(name)
                if loc is not None:
                    locs.setdefault(self._cid(name), loc)
        out: list[tuple[Loc, str]] = []
        for atom, originals in sorted(by_atom.items()):
            if len(originals) > 1:
                out.append((locs.get(atom) or Loc(file=str(d.name), line=0), (
                    f"NAME COLLISION: {' and '.join(sorted(originals))} both become the ASP atom "
                    f"`{atom}` (constants must start lowercase, so a leading capital is "
                    f"lowercased and a leading `_` becomes `u`). They would share one atom and "
                    f"the signal becomes MULTI-VALUED -- rename one in the RTL")))
        return out

    #: Declared types with no place in a synthesizable, 2-state, integer-valued model. slang
    #: still gives them a bit width, so they lower to ordinary `val` atoms and a `real 1.5`
    #: silently becomes the integer 1 -- see `_check_supported_types`.
    _OUT_OF_SCOPE_BASES = {
        "real": "a floating-point type; the value model is integer bit patterns",
        "shortreal": "a floating-point type; the value model is integer bit patterns",
        "realtime": "a floating-point type; the value model is integer bit patterns",
        "string": "a dynamic string; not a hardware value",
        "event": "a simulation event; not a hardware value",
        "chandle": "a foreign pointer; not a hardware value",
    }

    def _check_supported_types(self, d: Design) -> list[tuple[Loc, str]]:
        """REFUSE a signal whose declared type has no hardware value model (Fix 78).

        slang assigns these a bit width, so nothing downstream noticed: `real r; r = 1.5;`
        emitted `val(r, 1, T)` -- the 1.5 TRUNCATED to an integer -- and a driven `real` OUTPUT
        vanished entirely with `coverage: OK` and exit 0. Both are silent, and the second is a
        driven port that produced no rule at all.

        These are simulation/testbench types; refusing them at the declaration is the honest
        answer, and it is what `docs/reference/SV_FEATURE_COVERAGE.md` already claims for the row."""
        out: list[tuple[Loc, str]] = []
        for s in d.signals:
            why = self._OUT_OF_SCOPE_BASES.get((s.irtype.sv_base or "").lower())
            if why:
                out.append((s.loc, f"signal `{s.name}` is declared `{s.irtype.sv_base}` -- "
                                   f"{why}. Out of scope: a value model for it would be a "
                                   f"fiction, so it is refused rather than approximated"))
        return out

    def _norm_design(self, d: Design) -> Design:
        d = dataclasses.replace(d, flagged=(*d.flagged, *self._check_cid_injective(d),
                                            *self._check_supported_types(d)))
        c, ne = self._cid, self._norm_expr
        gd = lambda gs: tuple((c(s), p) for s, p in gs)        # noqa: E731 (sig, polarity) guards
        tg = lambda ts: tuple((c(s), t) for s, t in ts)        # noqa: E731 (sig, tag/value) -- tag stays
        br = lambda b: Branch(gd(b.guards), ne(b.value), tg(b.tag_guards), tg(b.neg_matches), b.loc)  # noqa: E731
        signals = tuple(Signal(c(s.name), s.irtype, s.is_reg, s.is_port, s.direction,
                               ne(s.initial) if s.initial else None, s.loc, s.enum_type) for s in d.signals)
        seq = tuple(dataclasses.replace(
            it, reg=c(it.reg), clock=c(it.clock),
            reset=Reset(c(it.reset.signal), it.reset.active, it.reset.kind) if it.reset else None,
            branches=tuple(br(b) for b in it.branches),
            lane_domain=c(it.lane_domain) if it.lane_domain else None) for it in d.seq)
        comb = tuple(dataclasses.replace(it, lhs=c(it.lhs), rhs=ne(it.rhs)) for it in d.comb)
        edges = tuple(dataclasses.replace(e, lhs=c(e.lhs), sig=c(e.sig), clock=c(e.clock))
                      for e in d.edges)
        writes = tuple(dataclasses.replace(
            w, mem=c(w.mem), addrs=tuple(ne(a) for a in w.addrs), data=ne(w.data),
            guards=gd(w.guards), clock=c(w.clock),
            rmw_slices=tuple((o, ww, ne(v)) for o, ww, v in w.rmw_slices)) for w in d.mem_writes)
        muxes = tuple(dataclasses.replace(m, out=c(m.out), sel=c(m.sel),
                                          arms=tuple(ne(a) for a in m.arms)) for m in d.muxes)
        vffs = tuple(dataclasses.replace(v, q=c(v.q), d=c(v.d), en=c(v.en), clock=c(v.clock),
                                         inst=c(v.inst)) for v in d.vffs)
        cells = tuple(dataclasses.replace(ci, inst=c(ci.inst), cell_type=c(ci.cell_type),
                                          outs=tuple(c(o) for o in ci.outs),
                                          parent=c(ci.parent)) for ci in d.cells)
        mems = tuple(dataclasses.replace(m, name=c(m.name)) for m in d.mems)
        nd = lambda dct: {c(k): v for k, v in dct.items()}     # noqa: E731 lane/packed dicts keyed by name
        norm_clocks = tuple(Clock(c(ck.name), ck.derived,
                                  c(ck.base) if ck.base else None, c(ck.gate) if ck.gate else None)
                            for ck in d.clocks)
        # STRUCTURAL GUARD, not a convention. This rebuild used to LIST every field, so a new
        # one on `Design` was silently dropped here -- that has now happened twice (`lane_hi`
        # on CombItem, `latches`). `dataclasses.replace` carries everything not named, and
        # `_check_design_fields` fails loudly if a field is neither normalised nor explicitly
        # declared carry-as-is. Adding a field to `Design` therefore forces a decision.
        _check_design_fields()
        return dataclasses.replace(
            d,
            name=c(d.name), signals=signals, mems=mems, clocks=norm_clocks,
            comb=comb, edges=edges, seq=seq, mem_writes=writes, muxes=muxes, vffs=vffs,
            latches=tuple(dataclasses.replace(l, q=c(l.q), d=c(l.d), en=c(l.en))
                          for l in d.latches),
            inferred_latches=tuple(dataclasses.replace(il, lhs=c(il.lhs), value=ne(il.value))
                                   for il in d.inferred_latches),
            lane_signals=tuple(c(s) for s in d.lane_signals),
            lane_dims=nd(d.lane_dims), lane_elem_w=nd(d.lane_elem_w), lane_domains=nd(d.lane_domains),
            cells=cells, packed_dims=nd(d.packed_dims),
            derived_clocks=tuple(DerivedClock(c(dc.name), c(dc.base), c(dc.gate), dc.loc,
                                              kind=dc.kind)
                                 for dc in d.derived_clocks))

    def _fold(self, e: Expr) -> int | None:
        """Fold a lowered Expr of constants to a Python int (else None). Drives bounded loop unroll
        and constant index resolution -- the loop var is a Const each iteration, so the bound/step
        and any ``x[i]`` index collapse to integers."""
        if isinstance(e, Const):
            return e.value
        if isinstance(e, BinOp):
            a, b = self._fold(e.left), self._fold(e.right)
            fn = self._FOLD.get(e.op)
            return fn(a, b) if (a is not None and b is not None and fn) else None
        if isinstance(e, UnOp):
            v = self._fold(e.operand)
            if v is None:
                return None
            return int(not v) if e.op == "lnot" else (-v if e.op == "neg" else None)
        if isinstance(e, SExt):
            v = self._fold(e.operand)
            if v is None:
                return None
            sv = v - (1 << e.from_w) if (v >> (e.from_w - 1)) & 1 else v
            return sv & ((1 << e.to_w) - 1)
        return None

