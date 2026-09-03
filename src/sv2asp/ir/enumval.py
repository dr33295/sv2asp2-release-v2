"""Enum reads as numbers -- one IR pass, at the end of the frontend.

An enum signal's value is its TAG, which is what keeps an FSM legible (`val(state, run, T)`); but
SystemVerilog also lets an enum be read as its underlying NUMBER, and the tool rendered every such
read as `val(state, V, T)` -- binding the tag symbol into a numeric variable. The consequences
(found on the dataset's VerilogEval fancytimer reference, 2026-08-19, by probing each operator):
`state < B` compared the tag SYMBOLS by name (right only when the names sort like the values);
`state == 3'd2`, `state == n` (an int signal) and `case (state) 3'd1:` were always false; `if (state)`
tested the tag against 1; an ARITHMETIC read in a comb item was refused (Fix 76) while the same
read in a REGISTER's D-input (`q <= state + 1`) passed translation and crashed the grounder at
solve time. All exit 0 with `coverage: OK`, in both modes.

This pass makes the rule structural: every enum `Ref` in a NUMERIC position becomes `EnumVal(ref,
enum)`, which the emitter lowers as `val(s, Tag, T), enum_value(enum, Tag, V)`. The positions that
are NOT numeric keep the tag: an equality against a TAG or against another enum signal (a tag
compare), a bare copy into an enum-typed destination (`state <= next`), a case arm that names a
member. A case arm that names a NUMBER on an enum selector is mapped to the member carrying that
number (or to no member -- the arm can never match a tag-valued selector). A bare enum in a TRUTH
position (`state || x`, a Cond selector) becomes `EnumVal != 0`, the LRM's non-zero test.

The walk mirrors the emitter's `_enum_numeric_refs` (which is kept as the backstop: after this
pass it must find nothing). Both emitters consume the rewritten design, so the decision is made
once (hard rule 1 -- a shared decision function, not a fix applied to one emitter)."""

from __future__ import annotations

import dataclasses

from .expr import (BinOp, Cond, Const, EnumCast, EnumVal, Expr, Ref, Tag, UnOp, XVal)
from .nodes import Branch, CombItem, Design, MemRead, MemWrite, SeqItem

_CMP = frozenset({"eq", "ne", "lt", "le", "gt", "ge"})
_EQ = frozenset({"eq", "ne"})
_LOGICAL = frozenset({"logand", "logor"})


def x_misused(design: Design) -> tuple:
    """`(Loc, reason)` for every `x`/`z` literal used where a VALUE is genuinely required.

    An assigned `x` is UNCONSTRAINED and fully supported -- the emitter declares `dontcare_at` and the
    boundary companion supplies the choice. But `a === 4'bxxxx` or `a + 8'bxx01` asks what `x` EQUALS,
    which a 2-state model cannot answer, so it is refused BY NAME (X_SEMANTICS.md D1).

    Run in the FRONTEND, over the whole design, because both emitters consume this IR: putting the
    check in one emitter is the two-emitter split (hard rule 1) -- and the first version of this
    refusal did exactly that, so modular translated `a === 4'bxxxx` SILENTLY while flat refused it.

    An XVal is legal as the whole assigned value, or as an arm of a conditional (the case/ternary arm
    shape the references actually write); anywhere else it is misuse."""
    out: list = []

    def walk(e, ok: bool, loc, what: str) -> None:
        if isinstance(e, XVal):
            if not ok:
                out.append((loc, (
                    f"an `x`/`z` literal used as a VALUE to compute with in {what} -- an assigned `x` "
                    f"is translated as UNCONSTRAINED (a choice in the boundary companion), but a "
                    f"2-state model cannot answer what `x` EQUALS. See notes/design/X_SEMANTICS.md")))
            return
        if isinstance(e, Cond):                  # the arms inherit the position; the selector does not
            walk(e.sel, False, loc, what)
            walk(e.a, ok, loc, what)
            walk(e.b, ok, loc, what)
            return
        if isinstance(e, (list, tuple)):
            for x in e:
                walk(x, False, loc, what)
            return
        for f in getattr(e, "__dataclass_fields__", ()):
            walk(getattr(e, f), False, loc, what)

    for it in design.comb:
        walk(getattr(it, "rhs", None), True, getattr(it, "loc", None), f"the value of `{getattr(it, 'lhs', '?')}`")
    for it in design.seq:
        for br in getattr(it, "branches", ()):
            walk(getattr(br, "value", None), True, getattr(br, "loc", None) or getattr(it, "loc", None),
                 f"a branch of register `{getattr(it, 'reg', '?')}`")
    return tuple(out)


def enum_reads_as_numbers(design: Design) -> Design:
    enum_of = {s.name: s.enum_type for s in design.signals if s.enum_type}
    if not enum_of:
        return design
    # member label -> number, per enum type (for a case arm that names a NUMBER on an enum selector)
    members: dict[str, dict[int, str]] = {}
    label_vals: dict[str, set[int]] = {}                # label -> the numbers it carries (over all enums)
    for en in design.enums:
        members[en.name] = {int(v): lab for lab, v in en.members}
        for lab, v in en.members:
            label_vals.setdefault(lab, set()).add(int(v))
    enum_width = {}
    for sg in design.signals:
        if sg.enum_type and isinstance(sg.irtype.width, int):
            enum_width.setdefault(sg.enum_type, sg.irtype.width)
    mem_enum = {m.name: getattr(m, "enum_type", None) for m in design.mems}

    def is_enum_ref(e: Expr) -> bool:
        return isinstance(e, Ref) and e.name in enum_of

    def truth(e: Expr) -> Expr:
        """A TRUTH position: a bare enum is `EnumVal != 0`; anything else is its own test."""
        if is_enum_ref(e):
            return BinOp("ne", EnumVal(e, enum_of[e.name]), Const(0, 1), 1)
        return rw(e, False)

    def rw(e: Expr, numeric: bool) -> Expr:
        if isinstance(e, Ref):
            return EnumVal(e, enum_of[e.name]) if (numeric and e.name in enum_of) else e
        if isinstance(e, Tag):
            # a member in a NUMERIC position (`state < B`, `B + 1`) is its NUMBER; a label two
            # enums give different numbers is left as it is (the emitter's backstop then refuses)
            vals = label_vals.get(e.label, set())
            if numeric and len(vals) == 1:
                (v,) = vals
                w = max([w for en, ms in members.items() if e.label in ms.values()
                         for w in [enum_width.get(en, 0)]] + [max(1, v.bit_length())])
                return Const(v, w)
            return e
        if isinstance(e, (Const, EnumVal)):
            return e
        if isinstance(e, EnumCast):                    # value -> enum: the operand is a NUMBER
            return dataclasses.replace(e, operand=rw(e.operand, True))
        if isinstance(e, BinOp):
            if e.op in _CMP:
                l, r = e.left, e.right
                tagcmp = (e.op in _EQ
                          and (isinstance(l, Tag) or isinstance(r, Tag)
                               or (is_enum_ref(l) and is_enum_ref(r))))
                if tagcmp:                             # `state == IDLE`, `a == b` (both enums): tags
                    return dataclasses.replace(e, left=rw(l, False), right=rw(r, False))
                return dataclasses.replace(e, left=rw(l, True), right=rw(r, True))   # numbers
            if e.op in _LOGICAL:                        # && || : each operand is a truth
                return dataclasses.replace(e, left=truth(e.left), right=truth(e.right))
            return dataclasses.replace(e, left=rw(e.left, True), right=rw(e.right, True))
        if isinstance(e, UnOp):
            if e.op == "lnot":
                return dataclasses.replace(e, operand=truth(e.operand))
            return dataclasses.replace(e, operand=rw(e.operand, True))
        if isinstance(e, Cond):
            return dataclasses.replace(e, sel=truth(e.sel), a=rw(e.a, numeric), b=rw(e.b, numeric))
        # every other node (Slice / BitSel / Concat / SExt / MemRef / ElemSel / LaneIdx / FuncCall ..)
        # reads its operands as NUMBERS -- generic over the dataclass shape, so a new node is
        # walked rather than skipped
        changes = {}
        for f in dataclasses.fields(e):
            v = getattr(e, f.name)
            nv = _rw_field(v, rw)
            if nv is not v:
                changes[f.name] = nv
        return dataclasses.replace(e, **changes) if changes else e

    def case_value(sel: str, v: str) -> str:
        """A case arm value on an ENUM selector: a member label stays; a NUMBER maps to the member
        carrying it, or to a value no tag equals (the arm can never match)."""
        et = enum_of.get(sel)
        if et is None:
            return v
        try:
            n = int(v.strip('"'))
        except ValueError:
            return v                                   # a member label
        return members.get(et, {}).get(n, f"no_member_{n}")

    def rw_branch(b: Branch, numeric: bool) -> Branch:
        value = b.value
        if is_enum_ref(value) and numeric:             # `q <= state` into a NON-enum register
            value = EnumVal(value, enum_of[value.name])
        else:
            value = rw(value, numeric)
        tg = tuple((s, case_value(s, v)) for s, v in b.tag_guards)
        nm = tuple((s, case_value(s, v)) for s, v in b.neg_matches)
        return dataclasses.replace(b, value=value, tag_guards=tg, neg_matches=nm)

    # a comb item's TOP-LEVEL bare enum ref (`assign z = state`) keeps the emitter's own copy rule
    # (`val(z, V, T) :- val(state, Tag, T), enum_value(..)` -- the legible spelling); operands convert
    comb = tuple(c if is_enum_ref(c.rhs) else dataclasses.replace(c, rhs=rw(c.rhs, c.lhs not in enum_of))
                 for c in design.comb)
    seq = tuple(dataclasses.replace(s, branches=tuple(rw_branch(b, s.reg not in enum_of)
                                                       for b in s.branches))
                for s in design.seq)
    writes = tuple(dataclasses.replace(w, addrs=tuple(rw(a, True) for a in w.addrs),
                                       data=rw(w.data, mem_enum.get(w.mem) is None))
                   for w in design.mem_writes)
    reads = tuple(dataclasses.replace(r, addrs=tuple(rw(a, True) for a in r.addrs))
                  for r in design.mem_reads)
    return dataclasses.replace(design, comb=comb, seq=seq, mem_writes=writes, mem_reads=reads)


def _rw_field(v, rw):
    if isinstance(v, Expr):
        return rw(v, True)
    if isinstance(v, tuple):
        nv = tuple(_rw_field(x, rw) for x in v)
        return nv if any(a is not b for a, b in zip(nv, v)) else v
    if isinstance(v, list):
        nv = [_rw_field(x, rw) for x in v]
        return nv if any(a is not b for a, b in zip(nv, v)) else v
    return v


def _with_x_check(design: Design) -> Design:
    """`x_misused` appended to the design's flags, at the one place every Design is built."""
    bad = x_misused(design)
    if not bad:
        return design
    return dataclasses.replace(design, flagged=tuple(design.flagged) + bad)
