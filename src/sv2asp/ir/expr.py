"""Normalized expression IR.

All expressions are LSB-0 normalized with widths attached, decoupled from
pyslang. The frontend lowers pyslang expressions into these nodes; the emitter
lowers these into ``@func`` calls / pure-ASP per catalog Group 1.
"""

from __future__ import annotations

from dataclasses import dataclass

from .types import Width


class Expr:
    """Base class for the expression IR (a closed set of dataclasses below)."""


@dataclass(frozen=True)
class Const(Expr):
    """A constant value of a given bit width."""

    value: int
    width: Width


@dataclass(frozen=True)
class Ref(Expr):
    """A reference to a signal by canonical name."""

    name: str


@dataclass(frozen=True)
class Tag(Expr):
    """An enum member used as a symbolic value: val(S, <label>, T) (catalog §3.6 tag shape).
    ``label`` is the lowercased enum label (clingo constant)."""

    label: str


@dataclass(frozen=True)
class XVal(Expr):
    """An `x`/`z` literal in a VALUE position: the design does not constrain this here.

    Not a value -- the 2-state model has none for it -- but a statement ABOUT values, so it is carried
    as its own node rather than folded to a number (`int()` on an unknown SVInt silently reads 0, which
    is Fix 87's defect). The emitter turns it into a guarded CHOICE in the boundary companion and emits
    no design rule for that path: unconstrained means every value is possible, so a property must hold
    for all of them (notes/design/X_SEMANTICS.md, the 2026-08-20 decision).

    Legal only where a value is ASSIGNED (a whole RHS, a ternary arm, a case-arm value). Reaching a
    comparison or an arithmetic operand is refused by name -- a 2-state model cannot answer "is this x"
    and must not invent one."""

    width: Width


@dataclass(frozen=True)
class EnumCast(Expr):
    """A value-to-enum cast ``e'(x)``: maps the numeric value of ``operand`` to its enum TAG via the
    enum_value/3 table -- val(lhs, Tag, T) :- <operand>, enum_value(enum, Tag, V). ``enum`` is the
    (lowercased) enum type name."""

    operand: Expr
    enum: str


@dataclass(frozen=True)
class EnumVal(Expr):
    """An enum-typed signal READ AS ITS NUMBER -- the inverse of EnumCast. An enum signal's value is
    its TAG (`val(state, idle, T)`); wherever SystemVerilog reads it as the underlying number (an
    arithmetic/bitwise operand, an index, a slice, an ordering compare, an equality against a
    number or a non-enum signal, a truth test) the read goes through the enum_value/3 table:
    `val(state, Tag, T), enum_value(enum, Tag, V)` -- V is the number. Inserted by
    `ir.enumval.enum_reads_as_numbers` at the end of the frontend, so every consumer (the
    classifier, both emitters) sees one IR. A tag compare (`state == IDLE`) and a tag copy
    (`state <= next`) are NOT numeric reads and keep the tag."""

    operand: Ref
    enum: str


@dataclass(frozen=True)
class BinOp(Expr):
    """Binary operation. ``op`` is a catalog-level op name (add/sub/eq/lt/and/...)."""

    op: str
    left: Expr
    right: Expr
    width: Width  # result width (1 for comparisons/logical)
    signed: bool = False  # operands read as signed (signed compare / >>> / signed div-mod)
    opw: Width | None = None  # common OPERAND width (signed compare); None -> fall back to width


@dataclass(frozen=True)
class UnOp(Expr):
    """Unary operation (not/neg/lnot)."""

    op: str
    operand: Expr
    width: Width


@dataclass(frozen=True)
class FuncCall(Expr):
    """Direct application of a named ``@func``: ``V = @name(arg…, extra…)``.

    The generic escape hatch for SITE PLUGINS: a primitive whose behaviour is a custom
    grounding-time function (registered via ``sv2asp.toml [funcs]``) builds this node in
    its ``PrimSpec("comb", …, build=…)`` — no translator change needed. ``extra`` are
    trailing integer literals appended after the evaluated args (widths, mode flags).
    ``render_script`` fails loudly if ``name`` was never registered."""

    name: str
    args: tuple[Expr, ...]
    extra: tuple[int, ...]
    width: Width


@dataclass(frozen=True)
class SExt(Expr):
    """Sign-extension on widening: interpret ``operand`` as a ``from_w``-bit signed value and
    re-encode it in ``to_w`` bits (two's complement). Emitted when a SIGNED expression is widened
    (pyslang inserts a signed->wider Conversion); a no-op-for-unsigned widening never reaches here."""

    operand: Expr
    from_w: int
    to_w: int


@dataclass(frozen=True)
class Slice(Expr):
    """Constant part-select base[hi:lo] (LSB-0)."""

    base: Expr
    hi: int
    lo: int


@dataclass(frozen=True)
class BitSel(Expr):
    """Single-bit select base[index] (constant index)."""

    base: Expr
    index: int


@dataclass(frozen=True)
class MemRef(Expr):
    """A read of memory ``mem`` at address(es) ``addrs`` -- one Expr per unpacked dimension
    (``q[a]`` -> 1 addr, ``q[a][b]`` -> 2). Emits ``val(mem(A1[, A2]), V, T)`` (address in the functor)."""

    mem: str
    addrs: tuple[Expr, ...]


@dataclass(frozen=True)
class LaneIdx(Expr):
    """The loop/genvar lane index itself, as a bare lane variable (``pos`` 0->``I``, 1->``J``, …).
    Used ONLY as a ``MemRef``/``MemWrite`` address when a procedural ``for``/``while`` lane-rolls a
    memory over ``addr(mem, I[, J])`` -- emitted as the bare lane variable (no ``val`` read), so it
    unifies with the packed-vector lane var. A distinct node (not a reserved ``Ref`` name) so it
    cannot collide with a real signal and is matched by type."""

    pos: int = 0


@dataclass(frozen=True)
class ElemSel(Expr):
    """Packed-vector element select ``base[index]`` -- reads lane/bit ``index`` of an indexed
    vector. Distinct from MemRef (a memory cell read), though the read atom shape coincides:
    val(base(Idx), V, T) (functor). ``index`` may be constant or a runtime expression (dynamic select)."""

    base: str
    index: Expr
    #: further indices of a MULTI-LEVEL packed select `q[f(i)][g(j)]` (outer-first after
    #: ``index``): a two-level lane read `val(q(f(I), g(J)), V, T)` -- F27's multi-dimensional
    #: sibling (2026-09-03). Empty for the ordinary one-index select.
    more: tuple = ()


@dataclass(frozen=True)
class Concat(Expr):
    """Concatenation of (expr, width) parts, MSB-first as written."""

    parts: tuple[tuple[Expr, Width], ...]


@dataclass(frozen=True)
class Cond(Expr):
    """Ternary select: sel ? a : b  (a is the sel=1 value, b the sel=0 value)."""

    sel: Expr
    a: Expr
    b: Expr
    width: Width
