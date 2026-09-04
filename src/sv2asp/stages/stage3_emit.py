"""Stage 3 - emit positive-definite ASP from the IR + Stage-2 shapes.

Produces clingo text matching the conventions of examples/rtl2asp/hand_translated/sync_fifo.lp
(provenance comments, width-generic @func, positive hold rules, destination-gated
async reset). Concrete-param mode: widths are concrete integers (see frontend).
"""

from __future__ import annotations

import itertools
import math
import re
from dataclasses import dataclass, field
from typing import NamedTuple

from ..emit import lib as _lib_names
from ..emit.lib import FUNC_NAME, func_legend, render_script
from ..emit.sink import instance_index as _sink_instance_index
from ..emit.bitsource import (
    BitSrc,
    Bool1,
    CondBits,
    ConstBit,
    Indexed,
    Or2Bits,
    ReplBool1,
    Shift,
    WordBit,
)
from ..ir.expr import (
    BinOp,
    BitSel,
    Concat,
    Cond,
    Const,
    ElemSel,
    EnumCast, EnumVal,
    Expr,
    FuncCall,
    LaneIdx,
    MemRef,
    Ref,
    SExt,
    Slice,
    Tag,
    UnOp,
    XVal,
)
from ..ir.nodes import CombItem, Design, Loc, SeqItem
from ..ir.types import Shape
from ..state_inventory import family_join, state_family, state_terms
from .stage2_analysis import Analysis, analyze


def _prov(loc, extra: str = "") -> str:
    base = loc.file.split("/")[-1]
    tail = f"  {loc.text}" if loc.text else ""
    pre = f"  [{extra}]" if extra else ""
    return f"{base}:{loc.line}{pre}{tail}"


_CMP = {"eq", "ne", "lt", "le", "gt", "ge"}
_CMP_OP = {"eq": "=", "ne": "!=", "lt": "<", "le": "<=", "gt": ">", "ge": ">="}
# WIDE arithmetic: clingo's int is 32-bit signed, so a value >= 2^31 is stored as a canonical decimal
# clingo STRING (see emit/lib.py _wv/_we). A width >= 32 CAN exceed 2^31, so its value literals are
# emitted string-safe and its ORDERING compares route through @wcmp. Narrow (<=31) is unchanged.
_WIDE_BITS = 32


def _const_lit(v: int) -> str:
    """A value literal safe for clingo's 32-bit int: the decimal when it fits, else a canonical decimal
    STRING (matching the wide value encoding in emit/lib.py). v is the masked, non-negative bit pattern."""
    return str(v) if v < (1 << 31) else f'"{v}"'
# binary ops emitted as a width-generic @func cascade (word value out). sidiv/simod (signed div/mod)
# and ashr (arithmetic >>>) join the cascade -- their @func name equals the op name.
_WORD_OPS = ("add", "sub", "mul", "div", "mod", "sidiv", "simod",
             "and", "or", "xor", "shl", "shr", "ashr", "pow",
             "clz")   # count-leading-zeros / count-leading-sign-bits primitive kind
# "low-bits-preserving" ops: (a op b) mod 2^w is determined by the low w bits of a,b -- so they can be
# computed at the ASSIGNMENT's width (narrower) and still be exact. This both wraps correctly (a counter
# q[3:0]<=q+1 truncates to 4 bits) and keeps the @func value inside clingo's 32-bit Number (a 32-bit
# unsized-literal sub like q-1 would otherwise yield 4294967295 and overflow). div/mod/shr/ashr depend
# on the HIGH bits, so they keep their own width and are truncated only at the final assignment seam.
_LOW_BITS_OPS = frozenset({"add", "sub", "mul", "and", "or", "xor", "shl"})
# positional lane-index variables (generate nest depth 1, 2, 3, ...). Avoids the reserved
# uppercase vars V (value), T (time), A/B (memory address) and O (reads as 0).
_LANEVARS = ("I", "J", "K", "L", "M", "N", "P", "Q", "R")


def _idx(name: str, lane_dims: dict[str, int] | None) -> str:
    """The lane-index list for a signal, one var per lane dimension: 'I' (1), 'I, J' (2), ... so
    N-D generate nests fan over N indices. Beyond the supply of names -> raise (the guarded emit
    flags it) rather than silently truncate -- keeps an N-deep nest sound, not mistranslated."""
    d = (lane_dims or {}).get(name, 1)
    if d > len(_LANEVARS):
        raise NotImplementedError(f"{name}: {d} lane dimensions exceed {len(_LANEVARS)} index vars")
    return ", ".join(_LANEVARS[:d])


def _binds_lane_var(lits: list[str], lv: str) -> bool:
    """Does some POSITIVE body literal bind the lane variable `lv`?

    ASP safety: a variable must occur in a positive body literal; the head does not bind it,
    and neither does a comparison. A `val(...)` literal mentioning `lv`, or an explicit range
    `lv = 0..N`, binds it. Anything else (comparisons, `@func` assignments) does not."""
    tok = re.compile(rf"(?<![A-Za-z0-9_]){re.escape(lv)}(?![A-Za-z0-9_])")
    for lit in lits:
        t = lit.strip()
        if t.startswith("val(") and tok.search(t):
            return True
        if re.match(rf"^{re.escape(lv)}\s*=\s*-?\d+\.\.", t):
            return True
    return False


def _lane_term(name: str, idxstr: str) -> str:
    """Wrap a lane signal name with its lane-index list as a FUNCTOR: the lane axis lives INSIDE the
    signal term, not as a positional ``val`` argument -- ``val(q(I), V, T)``, not ``val(q, I, V, T)``.
    The index is injected at the LEAF (before the first ')') so a hierarchy-wrapped name composes:
    ``u_a(en)`` -> ``u_a(en(I))``, never the invalid curried ``u_a(en)(I)``. Flat: ``en`` -> ``en(I)``;
    2-D generate: ``y`` -> ``y(I, J)``. An empty ``idxstr`` (a non-lane signal) passes through bare."""
    if not idxstr:
        return name
    if ")" in name:
        i = name.index(")")
        return f"{name[:i]}({idxstr}){name[i:]}"
    return f"{name}({idxstr})"


def _lane(name: str, lane_dims: dict[str, int] | None) -> str:
    """The functor lane term for ``name`` over its lane dimensions (``_lane_term`` o ``_idx``)."""
    return _lane_term(name, _idx(name, lane_dims))


def _mem_atom(mem: str, addrs: str, v: str, t: str) -> str:
    """A memory data atom in FUNCTOR form: ``val(mem(A[, A2]), V, T)`` -- the address lives inside the
    memory term (like a lane), not as a positional ``val`` argument. Reuses ``_lane_term``'s LEAF
    injection so a hierarchy-qualified name composes: ``u_ram(mem)`` + ``"A"`` -> ``u_ram(mem(A))``,
    never the invalid curried ``u_ram(mem)(A)``. The address domain ``addr(mem, A)`` and the markers
    ``mem_hold``/``mem_def_ok`` stay POSITIONAL -- only this data atom is functor-shaped."""
    return f"val({_lane_term(mem, addrs)}, {v}, {t})"


def _word_bridged(sig: str, lane_dims: dict[str, int] | None,
                  lane_elem_w: dict[str, int] | None, widths: dict[str, int] | None,
                  packed_dims: dict[str, tuple] | None = None) -> tuple[int, ...] | None:
    """The PER-LEVEL lane counts if ``sig`` is a lane signal whose lanes assemble into a coherent WORD
    (the lane<->word bridge applies), else None. A bridged signal has both a per-lane form
    val(sig(I[, J..]),..) AND a whole-word form val(sig,..). Plain name only (a hierarchy-injected leaf
    has no flat word atom).

    Multi-level (``logic [1:0][3:0] dd`` -> ``(2, 4)``) is bridged exactly like 1-level: the declared
    packed extents give the lane counts, and lane (I, J) sits at bit ``(I*4 + J) * elemW``. Returning
    None for these -- as this did until Fix 71 -- left the word form and the lane form of the SAME
    signal with no rule connecting them, so a 2-D port was silently disconnected from its own lanes."""
    nd = (lane_dims or {}).get(sig, 1)
    if "(" in sig:
        return None
    ew = (lane_elem_w or {}).get(sig, 1)
    tw = (widths or {}).get(sig, ew)
    if ew < 1 or tw % ew != 0 or tw // ew < 2:
        return None
    if nd == 1:
        return (tw // ew,)
    pd = tuple((packed_dims or {}).get(sig) or ())[:nd]
    # Only bridge when the declared extents actually account for the whole word: otherwise the bit
    # offset of a lane is not determined, and a guessed layout would be silently wrong.
    if len(pd) != nd or any(n < 1 for n in pd) or math.prod(pd) * ew != tw:
        return None
    return pd


def _emit_lane_word_bridge(out: _Out, lane_signals, shapes: dict[str, Shape], by_name: dict,
                           lane_dims: dict[str, int], lane_elem_w: dict[str, int],
                           widths: dict[str, int],
                           bitvec_signals: frozenset[str] = frozenset(),
                           bitvec_word_consumers: frozenset[str] = frozenset(),
                           bitvec_word_form: frozenset[str] = frozenset(),
                           packed_dims: dict[str, tuple] | None = None) -> None:
    """The lane<->word boundary bridge (#8), shared by flat emit() and modular _spec_rules() so both
    paths bridge identically (hard rule 1). A lane signal may also be driven/read as a WORD; the
    word side links to the per-lane side in the ONE direction matching how the signal is DRIVEN: an INPUT
    port is word-driven -> decompose the word into lanes; an OUTPUT port OR an INTERNAL lane signal
    (genvar/proc-for/VFF/bitvec all drive per-lane) is lane-driven -> assemble the lanes into the word,
    so {.., s, ..} / s[3:0] / s+1 read the whole word. One direction only avoids a word<->lane cycle;
    additive -- a per-lane scenario never drives the word. In modular the rules are Inst-rewritten later.
    bitvec_word_form: bitvec signals whose comb driver is NOT bit-structural — emitted in word form by
    _emit_cond/_emit_comb. For these, decompose word->per-bit (same direction as an input port).
    Without this, per-bit atoms would never be derived for such signals (bridge would try to assemble
    from non-existent per-bit atoms).

    A MULTI-LEVEL lane signal (``logic [1:0][3:0]`` driven by a nested generate) bridges the same way,
    over the tuple of indices instead of one: lane (I, J) occupies the bits at ``(I*n1 + J)*elemW``.

    EVERY signal the analysis shaped INDEXED is bridged, not only the explicitly lane-declared
    ones: a signal pulled into the per-lane form by lane-group closure (`assign t = y | b`, with
    `y` a generate-lane vector and `b`, `t` plain vectors) has per-lane rules and per-lane reads
    like any other, and until it was bridged here `b(I)` was read by nothing that derived it and
    `t(I)` assembled into no word -- an output port with no value, at exit 0."""
    bridged = set(lane_signals) | {n for n, sh in shapes.items()
                                   if sh == Shape.INDEXED and n in by_name}
    for sig in sorted(bridged):
        s = by_name.get(sig)
        if (s is None or shapes.get(sig) != Shape.INDEXED
                or (s.is_port and s.direction == "inout")):      # inout: word<->lane source ambiguous
            continue
        dims = _word_bridged(sig, lane_dims, lane_elem_w, widths, packed_dims)
        if dims is None:                                  # not a coherent multi-lane word view
            continue
        n = math.prod(dims)                               # total lanes, across all index levels
        ew = lane_elem_w.get(sig, 1)
        tw = widths.get(sig, ew)
        word_driven = (s.is_port and s.direction == "input"    # only an input port is word-driven
                       or (sig in (bitvec_word_form or frozenset())))  # bitvec with word-form comb: decompose
        kind = "port" if s.is_port else "internal"
        out.construct(f"lane<->word bridge for {kind} {sig} ({n} x {ew}-bit)")

        if len(dims) > 1:
            # MULTI-LEVEL lanes (nested generate over `logic [1:0][3:0]`): same bridge, over a tuple
            # of indices. Lane (I, J, ..) is at bit ((I*n1 + J)*n2 + ..)*elemW -- outermost index
            # slowest, which is how SV flattens packed dimensions. Kept separate from the 1-level
            # code below so that path stays byte-identical.
            idx = [chr(ord("I") + k) for k in range(len(dims))]
            if word_driven:                               # word -> per-lane elements (decompose)
                lin = idx[0]                              # I, then I*n1 + J, then (I*n1 + J)*n2 + K, ..
                for k in range(1, len(dims)):
                    lin = f"{lin if lin.isidentifier() else f'({lin})'} * {dims[k]} + {idx[k]}"
                off = lin if ew == 1 else \
                    f"{lin if lin.isidentifier() else f'({lin})'} * {ew}"
                out.used.add("slc")
                out.rule(f"val({_lane_term(sig, ', '.join(idx))}, B, T)",
                         [f"val({sig}, V, T)"]
                         + [f"{v} = 0..{d - 1}" for v, d in zip(idx, dims)]
                         + [f"B = @slc(V, {off}, {ew})"])
            else:                                         # lanes -> word (assemble)
                body, acc = [], "L0"
                for k, tup in enumerate(itertools.product(*(range(d) for d in dims))):
                    lvar = f"L{k}"
                    body.append(f"val({_lane_term(sig, ', '.join(str(i) for i in tup))}, {lvar}, T)")
                    if k:
                        out.used.update(("shl", "or"))
                        body.append(f"S{k} = @shl({lvar}, {k * ew}, {tw})")
                        body.append(f"W{k} = @bor({acc}, S{k}, {tw})")
                        acc = f"W{k}"
                _emit_or_defer_word(out, s, sig, tw, getattr(shapes, "budget_bits", 20), f"val({sig}, {acc}, T)", body)
            continue

        # Wide-lane bitvec (phase 5): each lane has per-bit atoms val(sig(I,J),B,T).
        # The inner bridge val(sig(I), W, T) is only needed when a downstream rule reads
        # val(sig(I),V,T) as a word — detected by the bitvec_word_consumers classifier in stage2.
        # For pure bit-structural pipelines, val(sig(I,J),B,T) is the complete model.
        if ew > 1 and not word_driven and sig in (bitvec_signals or frozenset()) \
                and sig in (bitvec_word_consumers or frozenset()):
            inner_body = [f"val({_lane_term(sig, f'I, {j}')}, L{j}, T)" for j in range(ew)]
            inner_acc = "L0"
            for j in range(1, ew):
                out.used.update(("shl", "or"))
                inner_body.append(f"S{j} = @shl(L{j}, {j}, {ew})")
                inner_body.append(f"W{j} = @bor({inner_acc}, S{j}, {ew})")
                inner_acc = f"W{j}"
            out.rule(f"val({sig}(I), {inner_acc}, T)", inner_body)

        if word_driven:                                   # word -> per-lane elements (decompose)
            off = "I" if ew == 1 else f"I * {ew}"
            out.used.add("slc")
            out.rule(f"val({sig}(I), B, T)",
                     [f"val({sig}, V, T)", f"I = 0..{n - 1}", f"B = @slc(V, {off}, {ew})"])
        else:                                             # lanes -> word (assemble)
            has_inner = (ew > 1 and sig in (bitvec_signals or frozenset())
                         and sig in (bitvec_word_consumers or frozenset()))
            if ew > 1 and sig in (bitvec_signals or frozenset()) and not has_inner:
                # Pure wide-lane bitvec (no inner bridge): no val(sig(I), Wi, T) atoms exist.
                # Assemble the flat word directly from all N*W per-bit atoms in one O(N*W) rule.
                body = []
                acc_flat = "L0"
                k = 0
                for i in range(n):
                    for j in range(ew):
                        lvar = f"L{k}"
                        body.append(f"val({_lane_term(sig, f'{i}, {j}')}, {lvar}, T)")
                        if k == 0:
                            acc_flat = lvar
                        else:
                            bit_pos = i * ew + j
                            out.used.update(("shl", "or"))
                            body.append(f"S{k} = @shl({lvar}, {bit_pos}, {tw})")
                            body.append(f"W{k} = @bor({acc_flat}, S{k}, {tw})")
                            acc_flat = f"W{k}"
                        k += 1
                _emit_or_defer_word(out, s, sig, tw, getattr(shapes, "budget_bits", 20), f"val({sig}, {acc_flat}, T)", body)
            else:
                body = [f"val({sig}({i}), L{i}, T)" for i in range(n)]
                acc = "L0"
                for i in range(1, n):
                    out.used.update(("shl", "or"))
                    body.append(f"S{i} = @shl(L{i}, {i * ew}, {tw})")
                    body.append(f"W{i} = @bor({acc}, S{i}, {tw})")
                    acc = f"W{i}"
                _emit_or_defer_word(out, s, sig, tw, getattr(shapes, "budget_bits", 20), f"val({sig}, {acc}, T)", body)


@dataclass
class _Ctx:
    """Per-rule fresh-variable allocator + used-@func tracker."""

    used: set[str]
    _n: int = 0

    def fresh(self) -> str:
        v = f"V{self._n}"
        self._n += 1
        return v


class _UsedSet(set):
    """The used-@func set every ``_Ctx`` is built from -- and, riding on it, the three facts the
    word reader needs at every one of its forty-odd call sites (the bit path's delegation
    included) without a new argument: ``bit_atoms``, ``widths``, ``budget_bits`` (F32)."""
    bit_atoms: frozenset = frozenset()
    widths: dict = {}
    budget_bits: int = 20


@dataclass
class _Out:
    lines: list[str] = field(default_factory=list)
    used: set[str] = field(default_factory=_UsedSet)
    problems: list[tuple[object, str]] = field(default_factory=list)  # (Loc, reason)
    deferred_words: list = field(default_factory=list)   # (sig, nbits, loc, rule) above the budget (F32)
    #: (signal, width, clock, guard literals, Loc) per `x`-valued assignment -- the boundary
    #: companion turns each into a guarded choice; the design layer emits nothing for it.
    dontcare: list = field(default_factory=list)
    warnings: list[tuple[object, str]] = field(default_factory=list)  # (Loc, reason) -- see Design.warned

    def comment(self, c: str) -> None:
        self.lines.append(f"% {c}")

    def problem(self, loc: object, reason: str) -> None:
        """A construct we could NOT fully/correctly translate. Recorded (loc, reason) so the
        coverage layer surfaces it as a hard problem -- never a silent comment."""
        self.problems.append((loc, reason))
        self.comment(f"UNSUPPORTED ({reason})")  # also visible inline in the .lp

    def warning(self, loc: object, reason: str) -> None:
        """A faithful translation with a property the reader must know about -- NOT a coverage
        problem (nothing was dropped or mistranslated). Recorded and also written inline into
        the .lp, because reading the emitted model is a primary workflow here."""
        self.warnings.append((loc, reason))
        self.comment(f"WARNING ({reason})")

    def construct(self, c: str) -> None:
        """Provenance comment for a new construct, preceded by a blank separator."""
        if self.lines and self.lines[-1].strip() != "" and not self.lines[-1].startswith("% ----"):
            self.lines.append("")
        self.comment(c)

    def rule(self, head: str, body: list[str] | None = None) -> None:
        self.lines.append(f"{head}." if not body else f"{head} :- {', '.join(body)}.")

    def blank(self) -> None:
        self.lines.append("")

    def section(self, title: str) -> None:
        self.lines.append(f"% {'-' * 4} {title} {'-' * 4}")


# --------------------------------------------------------------------------
# expression lowering
# --------------------------------------------------------------------------
def _value_bits(ch: Expr, cap_w: int, widths: dict[str, int] | None) -> int | None:
    """UPPER bound, in bits, on the value ``ch`` emits when lowered under operand cap
    ``cap_w`` — used to decide whether a non-masking op's result needs a re-mask (Fix 48).
    ``None`` = unknown (treated as exceeding). Children that self-mask are bounded by the
    cap; children that compute at their own width are bounded by it."""
    if isinstance(ch, BinOp):
        # low-bits children are masked at min(width, cap) — @add/@sub/@mul/@shl mask
        # inherently, and a capped and/or/xor is re-masked by this very fix when needed.
        return min(ch.width, cap_w) if ch.op in _LOW_BITS_OPS else ch.width
    if isinstance(ch, UnOp):
        if ch.op in ("not", "neg"):
            return min(ch.width, cap_w)          # @bnot/@neg mask to their width argument
        if ch.op == "popcnt":
            return max(int(ch.width).bit_length(), 1)   # a count of ch.width bits
        return 1                                  # bit reductions
    if isinstance(ch, Const):
        return max(ch.value.bit_length(), 1)      # the literal's actual magnitude
    if isinstance(ch, Slice):
        return ch.hi - ch.lo + 1                  # @slc masks to the slice length
    if isinstance(ch, BitSel):
        return 1
    if isinstance(ch, SExt):
        return ch.to_w
    if isinstance(ch, Ref):
        return (widths or {}).get(ch.name)        # a signal read is bounded by its width (Wf)
    if isinstance(ch, Concat):
        return sum(w for _, w in ch.parts)
    return getattr(ch, "width", None)


def _lane_domains(ndim: int, pdims: tuple, lanes: int, lane_hi: int | None,
                  bound: tuple[bool, ...], lane_lo: int = 0, lane_step: int = 1
                  ) -> list[tuple[int, int, int, int]]:
    """Which lane variables need an explicit domain literal, and over what extent.

    Returns ``(position, lo, hi, step)`` per literal, meaning
    ``_LANEVARS[position] = lo..hi-1`` and, for a stride above 1, ``(I - lo) \ step = 0``.
    `bound[i]` says a positive body literal already binds that variable — the ordinary
    `y[i] = a[i] | b[i]` shape — in which case adding a domain would be redundant.

    Two things ride on this. SAFETY: a lane variable that is neither bound by the body nor given
    a domain makes the rule unsafe, and clingo rejects it. EXTENT: a partial loop (`lane_hi` below
    the lane count, `lane_lo` above 0, or a stride) must get the LOOP's index set, not the
    signal's, or the one rolled rule over-drives lanes the RTL never writes
    (`Lane.missing_range_guard_over_drives`, `Lane.missing_start_guard_over_drives`,
    `Lane.missing_step_guard_over_drives`). A loop from 1 or by 2 was refused, and before that
    rolled over every lane (0b L4).

    Mirrored in Lean as `Lane.laneDoms`, checked against this function on every lane-rolled rule
    the translator really emits (`proofs/gen_lane_lean.py` -> `LaneTable.lean`)."""
    if ndim > 1:
        if len(pdims) != ndim:
            return []                    # extents unknown -> emit nothing rather than guess
        return [(i, 0, n, 1) for i, n in enumerate(pdims) if not bound[i]]
    need_range = ((lane_hi is not None and lanes and lane_hi < lanes) or lane_lo > 0
                  or lane_step > 1)
    hi = lane_hi if (need_range and lane_hi is not None) else lanes
    if not hi or hi <= lane_lo:
        return []
    return [(0, lane_lo, hi, max(lane_step, 1))] if (need_range or not bound[0]) else []


def _lane_dom_lits(doms: list[tuple[int, int, int, int]]) -> list[str]:
    """Render `_lane_domains`' choices as body literals: the binding range, then the stride test
    (`I \ 2 = 0`, or `(I - 1) \ 2 = 0` off a non-zero start) when the loop steps by more than 1."""
    out: list[str] = []
    for i, lo, hi, step in doms:
        v = _LANEVARS[i]
        out.append(f"{v} = {lo}..{hi - 1}")
        if step > 1:
            out.append(f"{v} \\ {step} = 0" if lo == 0 else f"({v} - {lo}) \\ {step} = 0")
    return out


def _mem_partition(lane_hi: tuple, guard_pols: list[int], lane_lo: tuple = ()
                   ) -> tuple[list[tuple[str, int, int]], list[tuple[str, int, int]]]:
    """Split a lane-rolled memory write into the condition under which it WRITES a cell and the
    conditions under which the cell HOLDS.

    Returns ``(write, hold)``. `write` is one entry per bounded END of a dimension:
    ``("hi", dim, hi)`` — the cell is written only if ``lane[dim] < hi`` — and ``("lo", dim, lo)``
    for a loop starting above 0 (`for (i = 1; ...)`) — only if ``lane[dim] >= lo``; every guard
    must also read its own polarity. `hold` is one entry per way that can fail: ``("range", dim,
    hi)`` for past-the-bound, ``("below", dim, lo)`` for under-the-start, ``("guard", i, off)``
    for guard `i` reading the OTHER value.

    The two must be exactly complementary — the union of the holds is the complement of the
    written rectangle — because a gap leaves a cell UNBOUND at `T+1` (it silently loses its
    value) and an overlap makes it multi-valued. That is `Mem.mem_exactly_one`, and this
    function is what `proofs/gen_mem_lean.py` records to check the model against the code."""
    write: list[tuple[str, int, int]] = [("hi", d, hi) for d, hi in enumerate(lane_hi)
                                         if hi is not None]
    write += [("lo", d, lo) for d, lo in enumerate(lane_lo) if lo]
    hold: list[tuple[str, int, int]] = [("range", d, hi) for k, d, hi in write if k == "hi"]
    hold += [("below", d, lo) for k, d, lo in write if k == "lo"]
    hold += [("guard", i, 1 - p) for i, p in enumerate(guard_pols)]
    return write, hold


def _concat_offsets(widths: list[int]) -> list[int]:
    """Bit offset of each part of a concatenation, given the part widths MSB-FIRST (the order
    SystemVerilog writes them): a part sits above everything to its RIGHT, so the rightmost
    operand lands at 0 and is emitted with no `@shl` at all.

    Mirrored in Lean as `Ops.catOffsets`, and checked against THIS function on every
    concatenation the translator really builds (`proofs/gen_ops_lean.py` -> `OpsTable.lean`).
    A wrong offset here is the Fix-71 bug class: a plausible number, silently wrong."""
    offs, off = [], 0
    for w in reversed(widths):
        offs.append(off)
        off += w
    return offs[::-1]


def _bits_read(base: Expr, lo: int, hi: int, t: str, ctx: _Ctx) -> tuple | None:
    """A constant slice ``base[hi:lo]`` of a PER-BIT signal wider than the grounding budget, read
    from its bit atoms and assembled by plain arithmetic -- 2^(hi-lo+1) instances instead of the
    2^N join that assembling the whole word would cost. Below the budget the word read stands, so
    the corpus is byte-identical; a slice wider than 30 bits would overflow a bare Number and
    falls back too (hard rule 4). None = not this case (F32, 2026-09-03)."""
    while isinstance(base, Slice):          # a[i][j] is a slice of a slice: fold to one bit range
        lo, hi = base.lo + lo, base.lo + hi
        base = base.base
    u = ctx.used
    bit_atoms, widths = getattr(u, "bit_atoms", ()), getattr(u, "widths", None)
    if not (isinstance(base, Ref) and widths):
        return None
    name = base.name
    if name not in bit_atoms or not isinstance(widths.get(name), int):
        return None
    if widths[name] <= getattr(u, "budget_bits", 20) or hi - lo + 1 > 30:
        return None
    lits, vs = [], []
    for k in range(lo, hi + 1):
        v = ctx.fresh()
        lits.append(f"val({_lane_term(name, str(k))}, {v}, {t})")
        vs.append(v)
    res = ctx.fresh()
    expr = " + ".join(f"{v}*{1 << j}" if j else v for j, v in enumerate(vs))
    return [*lits, f"{res} = {expr}"], res


_WORD_DEFER = "%__word_assembly_deferred__ "


def _emit_or_defer_word(out: "_Out", s, sig: str, nbits: int, budget: int, head: str, body: list) -> None:
    """Write the bits->word assembly of ``sig`` now if it is within the grounding budget (the
    corpus path, byte for byte); otherwise leave a MARKER and decide at the end of emission,
    when every rule that could read the word has been written -- flat emits this bridge before
    its comb rules and modular after, so a decision taken here would see different programs in
    the two modes. `resolve_deferred_words` replaces the marker."""
    if nbits <= budget:
        out.rule(head, body)
        return
    if getattr(s, "is_port", False):
        # a PORT's word is read from OUTSIDE the design -- a scenario, a property, the round
        # trip's projection -- which no scan of the design's rules can see: always assembled,
        # its cost named (lane_add_demo's 32-bit `sum` output, 2026-09-03)
        _budget_note(out, s, sig, nbits, budget)
        out.rule(head, body)
        return
    out.deferred_words.append((sig, nbits, getattr(s, "loc", None), f"{head} :- {', '.join(body)}."))
    out.lines.append(_WORD_DEFER + sig)


def _budget_note(out: "_Out", s, sig: str, nbits: int, budget: int) -> None:
    """The named cost of a word assembled above the budget: inline where the rule is, and in
    the warnings the report and `--strict-warnings` see."""
    reason = (f"BUDGET: the word of {sig} ({nbits} bits) is assembled from its per-bit atoms -- a 2^{nbits} "
              f"join if those bits are free at grounding (above the budget of 2^{budget}); pinned/deterministic "
              f"runs ground it in one instance (F32)")
    out.lines.append(f"% WARNING ({reason})")          # the spelling the modular CLI scans for
    out.warnings.append((getattr(s, "loc", None), reason))


def resolve_deferred_words(out: "_Out", budget: int) -> None:
    """THE ONE DECISION for a word above the budget, taken over the emitted rules in both modes:
    read by some rule -> a refusal by name with the number (an `% UNSUPPORTED` line where the
    assembly would have been, and a coverage PROBLEM); read by nothing -> not assembled, its
    bits are the model (F32, 2026-09-03)."""
    if not out.deferred_words:
        return
    for sig, nbits, loc, rule in out.deferred_words:
        pol = _word_assembly_policy(sig, nbits, out, budget)
        marker = _WORD_DEFER + sig
        i = out.lines.index(marker)
        if pol == "drop":
            reason = (f"word of {sig} ({nbits} bits) NOT assembled: a 2^{nbits} join, above the grounding "
                      f"budget of 2^{budget}, and no rule of the design reads it as a word -- its bits "
                      f"val({sig}(0..{nbits - 1}), B, T) are the model; a scenario or property that reads "
                      f"val({sig}, V, T) reads nothing (F32)")
            out.lines[i] = f"% WARNING ({reason})"
            out.warnings.append((loc, reason))
        else:
            # READ as a whole: the rule stands, with its cost NAMED. A static refusal would be
            # wrong -- the join is 2^N only when the bits are FREE at grounding (a symbolic
            # power-on, free inputs); a concrete power-on with pinned inputs determines every
            # bit and grounds this in one instance (goldschmidt_cds's 32-bit q_tilde runs so
            # today). Which is the case is the SCENARIO's to know: scripts/scenario_budget.py
            # is where the refusal belongs, before a solve, with the number.
            reason = (f"BUDGET: the word of {sig} ({nbits} bits) is assembled from its per-bit atoms -- a "
                      f"2^{nbits} join if those bits are free at grounding (above the budget of 2^{budget}); "
                      f"pinned/deterministic runs ground it in one instance (F32)")
            out.lines[i] = f"% WARNING ({reason})"
            out.lines.insert(i + 1, rule)
            out.warnings.append((loc, reason))
    out.deferred_words.clear()


def _word_assembly_policy(sig: str, nbits: int, out: "_Out", budget: int) -> str:
    """emit | drop | refuse -- whether the bits->word bridge of ``sig`` is written. Assembling a
    word from N bit atoms is one rule joining all N: 2^N instances whenever the bits are not
    fixed at grounding, which a register-derived signal never is. Within the budget it is
    emitted as always. Above it, the rule is written only if some already-emitted rule READS the
    word -- then it is a refusal by name with the number, because the alternative is a hang
    that reads as a broken tool (the reporter's 36-bit count lane, F32); read by nothing, it is
    simply not written. The check reads the emitted rules, so it is one decision for both
    modes and cannot disagree with what was actually written."""
    if nbits <= budget:
        return "emit"
    pat = re.compile(r"\bval\(" + re.escape(sig) + r", ")
    for ln in out.lines:
        if ":-" in ln and not ln.lstrip().startswith("%") and pat.search(ln.split(":-", 1)[1]):
            return "refuse"
        if ":-" not in ln and not ln.lstrip().startswith("%") and pat.search(ln):
            return "refuse"                       # a fact/head-only line naming the word
    return "drop"


def _word_body(e: Expr, t: str, ctx: _Ctx, shapes: dict[str, Shape] | None = None,
               lane_dims: dict[str, int] | None = None, cap: int | None = None,
               lane_ctx: bool = False, widths: dict[str, int] | None = None) -> tuple[list[str], str]:
    """Return (body_literals, value_term) computing word-valued ``e`` at time ``t``. When
    ``shapes`` is given, an INDEXED ref is read per-lane (val(s(I[, J...]), V, t)) ONLY in a lane
    context (``lane_ctx`` -- the enclosing rule head is a lane that binds I); in a WORD/scalar context
    a bare INDEXED ref is the WHOLE WORD (val(s, V, t)), since lane I has nothing to bind it (e.g.
    {a, b}, a[3:0], a + 1 where ``a`` is also used as a[i] elsewhere -- the word form comes from the
    lane<->word bridge). ``cap`` is the destination (assignment) width: a low-bits-preserving op is
    computed at min(its width, cap) so a narrow assignment both wraps and stays inside clingo's 32-bit
    Number (see _LOW_BITS_OPS).

    Dispatch is a structural ``match`` over the Expr ADT (one arm per node kind) — a flat recursive
    descent, no isinstance ladder."""
    match e:
        case Const():
            return [], _const_lit(e.value)
        case XVal():
            # An `x` reached a position that genuinely needs a VALUE (a comparison operand, an
            # arithmetic operand, an index). Unconstrained is only meaningful where a value is
            # ASSIGNED -- "is this x" is a question a 2-state model cannot answer, and inventing an
            # answer is exactly the defect Fix 87 removed. Refused BY NAME (X_SEMANTICS.md D1).
            raise NotImplementedError(
                "an `x`/`z` literal used as a VALUE to compute with (a comparison or arithmetic "
                "operand, or an index). An assigned `x` is translated as UNCONSTRAINED -- a choice in "
                "the boundary companion -- but a 2-state model cannot answer what `x` EQUALS. "
                "See notes/design/X_SEMANTICS.md")
        case EnumVal():   # an enum read as its NUMBER (ir/enumval.py): tag -> value through the enum_value/3 table
            tg, v = ctx.fresh(), ctx.fresh()
            return [f"val({e.operand.name}, {tg}, {t})", f"enum_value({e.enum}, {tg}, {v})"], v
        case Tag():   # an enum member as a VALUE: the tag symbol itself (val(state, idle, T) is how enums are read)
            # `assign nxt_r = reset ? idle : nxt;` -- a continuous assign of an enum ternary with a tag arm
            # -- reached _emit_cond -> _assign_word -> here and was `NotImplementedError: word expr Tag`
            # (loud: a dark read of nxt_r); the register path's `read()` had the case, the word body not
            # (found by the dataset's first entry, ve137_fsm_serial, 2026-08-18)
            return [], e.label
        case Ref():
            v = ctx.fresh()
            sh = shapes.get(e.name) if shapes is not None else None
            if sh == Shape.INDEXED and lane_ctx:    # lane datapath: head binds I -> read this lane
                return [f"val({_lane(e.name, lane_dims)}, {v}, {t})"], v
            return [f"val({e.name}, {v}, {t})"], v   # scalar/word read (a 1-bit signal is a width-1 word)
        case BinOp() if e.op in _WORD_OPS:
            if e.op in _LOW_BITS_OPS:
                w = min(e.width, cap) if cap is not None else e.width   # compute at the destination width
                ocap = w                                                # ... and push it down to operands
            else:
                w, ocap = e.width, None    # div/mod/shr/ashr need high bits -> own width, no operand cap
            # shl is low-bits-preserving in its DATA operand only: the shift AMOUNT is
            # self-determined in SV, so it must never inherit the destination cap — a
            # computed amount that overflows the destination width would silently wrap
            # (Fix 44). The bitvec Shift path already computes the amount uncapped.
            rcap = None if e.op == "shl" else ocap
            ll, vl = _word_body(e.left, t, ctx, shapes, lane_dims, ocap, lane_ctx, widths)
            lr, vr = _word_body(e.right, t, ctx, shapes, lane_dims, rcap, lane_ctx, widths)
            res = ctx.fresh()
            ctx.used.add(e.op)
            lines = [*ll, *lr, f"{res} = @{FUNC_NAME.get(e.op, e.op)}({vl}, {vr}, {w})"]
            # @band/@bor/@bxor do NOT re-mask (a proven contract: proofs/lean Wf layer —
            # wf_fAnd/wf_fOr/wf_fXor need MASKED operands, unlike the self-masking
            # @add/@sub/@mul/@shl). When the destination cap narrowed w below an operand's
            # width, the wide operand's high bits would survive into the result and a
            # narrow signal would store an over-wide value — silent-wrong (Fix 48:
            # `y[3:0] = a16 & c16;` stored 65535 on a 4-bit signal; the SMT completion
            # route `_fit`s operands and was already correct — an ASP/SMT divergence).
            # Re-mask the result exactly when some operand may exceed the computed width.
            # Only the CAP can create that situation: without one (or with cap >= e.width)
            # SV context-determination already bounds every operand by the op width.
            if e.op in ("and", "or", "xor") and cap is not None and w < e.width:
                lb = _value_bits(e.left, w, widths)
                rb = _value_bits(e.right, w, widths)
                if lb is None or rb is None or lb > w or rb > w:
                    ctx.used.add("slc")
                    mres = ctx.fresh()
                    lines.append(f"{mres} = @slc({res}, 0, {w})")
                    res = mres
            return lines, res
        case UnOp() if e.op in ("not", "neg"):   # word-level ~x / -x (low-bits-preserving)
            w = min(e.width, cap) if cap is not None else e.width
            lb, vb = _word_body(e.operand, t, ctx, shapes, lane_dims, w, lane_ctx, widths)
            res = ctx.fresh()
            ctx.used.add(e.op)
            return [*lb, f"{res} = @{FUNC_NAME.get(e.op, e.op)}({vb}, {w})"], res
        case UnOp() if e.op == "popcnt":   # $countones: count 1-bits (e.width = operand width to mask)
            lb, vb = _word_body(e.operand, t, ctx, shapes, lane_dims, lane_ctx=lane_ctx)
            res = ctx.fresh()
            ctx.used.add("popcnt")
            return [*lb, f"{res} = @popcnt({vb}, {e.width})"], res
        case FuncCall():   # plugin escape hatch: V = @name(args..., extra...)
            lines: list[str] = []
            vals: list[str] = []
            for a in e.args:
                la, va = _word_body(a, t, ctx, shapes, lane_dims, lane_ctx=lane_ctx)
                lines += la
                vals.append(va)
            res = ctx.fresh()
            ctx.used.add(e.name)   # render_script fails loud if the @func was never registered
            call_args = ", ".join([*vals, *(str(x) for x in e.extra)])
            return [*lines, f"{res} = @{e.name}({call_args})"], res
        case UnOp() if e.op in ("rand", "ror", "rxor", "rnand", "rnor", "rxnor"):
            # a bit-reduction (&x/|x/^x + negated) used INSIDE a word expression -> a 0/1 value.
            # e.width carries the OPERAND width (set by the frontend; result is always 1 bit).
            lb, vb = _word_body(e.operand, t, ctx, shapes, lane_dims, lane_ctx=lane_ctx)
            res = ctx.fresh()
            ctx.used.add(e.op)
            return [*lb, f"{res} = @{e.op}({vb}, {e.width})"], res
        case SExt():   # sign-extend a signed value on widening: from_w -> to_w
            lb, vb = _word_body(e.operand, t, ctx, shapes, lane_dims, lane_ctx=lane_ctx)
            res = ctx.fresh()
            ctx.used.add("sext")
            return [*lb, f"{res} = @sext({vb}, {e.from_w}, {e.to_w})"], res
        case Slice():
            got = _bits_read(e.base, e.lo, e.hi, t, ctx)
            if got is not None:
                return got
            lb, vb = _word_body(e.base, t, ctx, shapes, lane_dims, lane_ctx=lane_ctx)
            res = ctx.fresh()
            ctx.used.add("slc")  # base[hi:lo] = (base >> lo) masked to (hi-lo+1) bits (lo=0 -> >>0)
            return [*lb, f"{res} = @slc({vb}, {e.lo}, {e.hi - e.lo + 1})"], res
        case Concat():
            # MSB-first parts: part i sits at offset = sum of widths to its RIGHT; OR them together
            total = sum(w for _, w in e.parts)
            offs = _concat_offsets([w for _, w in e.parts])
            body: list[str] = []
            acc: str | None = None
            for (expr, _w), off in zip(reversed(e.parts), reversed(offs)):   # LSB-first
                pb, pv = _word_body(expr, t, ctx, shapes, lane_dims, lane_ctx=lane_ctx)
                body.extend(pb)
                if off > 0:
                    s = ctx.fresh()
                    ctx.used.add("shl")
                    body.append(f"{s} = @shl({pv}, {off}, {total})")
                    pv = s
                if acc is None:
                    acc = pv
                else:
                    r = ctx.fresh()
                    ctx.used.add("or")
                    body.append(f"{r} = @bor({acc}, {pv}, {total})")
                    acc = r
            return body, (acc if acc is not None else "0")
        case LaneIdx():   # the loop lane index itself -> the bare lane variable (no val read)
            return [], _LANEVARS[e.pos]
        case MemRef():    # val(mem(A1[, A2]), V, t) -- one address term per unpacked dimension
            body, terms = [], []
            for a in e.addrs:
                la, va = _word_body(a, t, ctx, shapes, lane_dims, lane_ctx=lane_ctx)
                body += la
                terms.append(va)
            vcell = ctx.fresh()
            return [*body, _mem_atom(e.mem, ", ".join(terms), vcell, t)], vcell
        case ElemSel() if shapes is not None and shapes.get(e.base) == Shape.WORD:
            # F27's other half: the frontend defers every genvar-dependent packed select to the
            # FINAL classification by emitting ElemSel. A WORD-shaped base has no per-lane atoms,
            # so the select is the dynamic bit-select of the word -- the same masked shift the
            # old desugar produced (element width 1 by construction at the frontend).
            if e.more:
                raise NotImplementedError(f"multi-level packed select of the WORD-shaped signal {e.base} "
                                          f"(its lanes were never established)")
            li, vi = _word_body(e.index, t, ctx, shapes, lane_dims, lane_ctx=lane_ctx)
            v0, vs, res = ctx.fresh(), ctx.fresh(), ctx.fresh()
            ctx.used.update(("shr", "slc"))
            return [f"val({e.base}, {v0}, {t})", *li,
                    f"{vs} = @shr({v0}, {vi}, 1)", f"{res} = @slc({vs}, 0, 1)"], res
        case ElemSel():  # lane select: val(base(Idx), V, t) -- Idx const or runtime (unifies)
            # A NEIGHBOURING lane, `c[i-1]` / `q[i+1]` (a ripple/shift chain): the index is the
            # lane variable offset by a constant, written as the arithmetic term `c(I-1)` --
            # clingo evaluates it at grounding once I is bound by the rule's domain literal --
            # rather than through `@sub`. Legible, and verbatim-distinct from the head's `c(I)`,
            # which is exactly what the tightness check compares (a chain is founded, not a loop).
            lits, terms = [], []
            for ix in (e.index, *e.more):          # one index per lane level (F27, and its 2-D sibling)
                if (isinstance(ix, BinOp) and ix.op in ("add", "sub")
                        and isinstance(ix.left, LaneIdx) and isinstance(ix.right, Const)):
                    sign = "+" if ix.op == "add" else "-"
                    terms.append(f"{_LANEVARS[ix.left.pos]}{sign}{ix.right.value}")
                elif isinstance(ix, LaneIdx):
                    terms.append(_LANEVARS[ix.pos])
                elif isinstance(ix, Const):
                    terms.append(str(ix.value))
                else:
                    li, vi = _word_body(ix, t, ctx, shapes, lane_dims, lane_ctx=lane_ctx)
                    lits.extend(li); terms.append(vi)
            vcell = ctx.fresh()
            return [*lits, f"val({_lane_term(e.base, ', '.join(terms))}, {vcell}, {t})"], vcell
        case BitSel():
            got = _bits_read(e.base, e.index, e.index, t, ctx)
            if got is not None:
                return got
            lb, vb = _word_body(e.base, t, ctx, shapes, lane_dims, lane_ctx=lane_ctx)
            res = ctx.fresh()
            ctx.used.add("slc")
            return [*lb, f"{res} = @slc({vb}, {e.index}, 1)"], res   # bit i = (v >> i) & 1
    raise NotImplementedError(f"word expr {type(e).__name__}")


def _rhs_width(e: Expr, widths: dict[str, int] | None) -> int | None:
    """The width of value-expression ``e`` (for the narrowing-assignment decision), or None if unknown."""
    if isinstance(e, Ref):
        return (widths or {}).get(e.name)
    if isinstance(e, Const):
        return e.width
    if isinstance(e, Slice):
        return e.hi - e.lo + 1
    if isinstance(e, BitSel):
        return 1
    if isinstance(e, Concat):
        return sum(w for _, w in e.parts)
    return getattr(e, "width", None)


def _assign_word(rhs: Expr, t: str, ctx: _Ctx, shapes: dict[str, Shape] | None,
                 lane_dims: dict[str, int] | None, widths: dict[str, int] | None,
                 lhs_width: int | None) -> tuple[list[str], str]:
    """Lower an assignment RHS TRUNCATED to the destination width ``lhs_width`` (SV truncates the value
    assigned to a narrower target). Low-bits ops are computed at lhs_width via the cap; a wider top the
    cap did NOT clamp -- a Ref/Const copy wider than the target, or a div/mod/shr -- is masked with @slc.
    A value already sized to the target (slice/bit-select/concat, equal-width copy) or unknown -> no mask."""
    body, v = _word_body(rhs, t, ctx, shapes, lane_dims, lhs_width, widths=widths)
    if lhs_width is None:
        return body, v
    if (isinstance(rhs, BinOp) and rhs.op in _LOW_BITS_OPS) or \
       (isinstance(rhs, UnOp) and rhs.op in ("not", "neg")):
        return body, v                                   # already computed at lhs_width by the cap
    rw = _rhs_width(rhs, widths)
    if rw is None or rw <= lhs_width:
        return body, v                                   # already fits the destination (or unknown)
    res = ctx.fresh()
    ctx.used.add("slc")
    return [*body, f"{res} = @slc({v}, 0, {lhs_width})"], res   # truncate the assigned value


def _bit_lit(e: Expr) -> tuple[str, int]:
    """A 1-bit literal: Ref(x) -> (x,1); !Ref(x) -> (x,0)."""
    if isinstance(e, UnOp) and e.op == "lnot" and isinstance(e.operand, Ref):
        return e.operand.name, 0
    if isinstance(e, Ref):
        return e.name, 1
    raise NotImplementedError(f"bit literal {e}")


def _is_bit_lit(e: Expr, widths: dict[str, int] | None = None) -> bool:
    """A 1-BIT literal: a signal read or its negation -- and the WIDTH matters (Fix 94).

    `x && y` in SystemVerilog means `(x != 0) && (y != 0)`. Lowering a MULTI-BIT operand to the
    polarity literal `val(x, 1, T)` tests equality with ONE instead, so at `x = 2` neither the
    on-rule nor the off-rule fires and the head is left UNBOUND -- a property over it then
    passes vacuously. A wide operand is therefore not a bit literal; it falls through to the
    boolean emitter's word-expression path, which tests `!= 0` correctly."""
    def _w1(n: str) -> bool:
        return widths is None or widths.get(n, 1) <= 1
    if isinstance(e, Ref):
        return _w1(e.name)
    return (isinstance(e, UnOp) and e.op == "lnot" and isinstance(e.operand, Ref)
            and _w1(e.operand.name))


# --- general 1-bit boolean emitter (logic gates, muxes) via on-set/off-set --
_BOOL_CONN = ("and", "or", "xor", "logand", "logor")  # boolean connectives (operands are booleans)


def _expr_key(e: Expr) -> str:
    """A structural key so a boolean leaf appearing twice maps to ONE atom (consistent truth)."""
    if isinstance(e, Ref):
        return f"R:{e.name}"
    if isinstance(e, Const):
        return f"C:{e.value}"
    if isinstance(e, BinOp):
        return f"B:{e.op}({_expr_key(e.left)},{_expr_key(e.right)})"
    if isinstance(e, UnOp):
        return f"U:{e.op}({_expr_key(e.operand)})"
    if isinstance(e, SExt):
        return f"X:sext{e.from_w}_{e.to_w}({_expr_key(e.operand)})"
    if isinstance(e, Slice):
        return f"S:{_expr_key(e.base)}[{e.hi}:{e.lo}]"
    if isinstance(e, BitSel):
        return f"T:{_expr_key(e.base)}[{e.index}]"
    if isinstance(e, ElemSel):
        return f"E:{_expr_key(e.base)}[{','.join(_expr_key(x) for x in (e.index, *e.more))}]"
    if isinstance(e, MemRef):
        return f"M:{e.mem}[{','.join(_expr_key(a) for a in e.addrs)}]"
    if isinstance(e, LaneIdx):
        return f"L:{e.pos}"
    if isinstance(e, EnumVal):
        return f"N:{e.operand.name}"
    return f"X:{e!r}"                # by VALUE: an address is reused after the object dies (F40)


def _is_bool_conn(e: Expr) -> bool:
    return (isinstance(e, BinOp) and e.op in _BOOL_CONN) or (isinstance(e, UnOp) and e.op in ("not", "lnot"))


def _eval_bool(e: Expr, env: dict[str, int]) -> int:
    """Evaluate the boolean structure given truth values keyed per leaf. Connectives recurse;
    any non-connective node is an atomic LEAF (a 1-bit signal, a comparison, or a word `!=0`)."""
    if isinstance(e, UnOp) and e.op in ("not", "lnot"):
        return 1 - _eval_bool(e.operand, env)
    if isinstance(e, BinOp) and e.op in _BOOL_CONN:
        a, b = _eval_bool(e.left, env), _eval_bool(e.right, env)
        return {"and": a & b, "logand": a & b, "or": a | b, "logor": a | b, "xor": a ^ b}[e.op]
    return env[_expr_key(e)]   # leaf


def _bool_leaves(e: Expr) -> int:
    """Count leaves under boolean connectives (the minterm-enumeration cost is 2^this)."""
    if _is_bool_conn(e):
        if isinstance(e, UnOp):
            return _bool_leaves(e.operand)
        return _bool_leaves(e.left) + _bool_leaves(e.right)
    return 1


def _flatten_conn(e: BinOp) -> list[Expr]:
    """Flatten an associative boolean connective (a op b op c ...) into its operand list."""
    op = e.op
    out: list[Expr] = []
    for side in (e.left, e.right):
        if isinstance(side, BinOp) and side.op == op:
            out.extend(_flatten_conn(side))
        else:
            out.append(side)
    return out


_MAX_BOOL_LEAVES = 10   # above this, decompose structurally instead of enumerating 2^N minterms


def _or_of_ands_onset(
    expr: Expr,
    leaf_false: dict[str, list[str]],  # expr-key → false-polarity literals
    leaf_true: dict[str, list[str]],   # expr-key → true-polarity literals
) -> list[list[str]] | None:
    """Prime-implicant ON-set for OR-of-AND-terms boolean expressions.

    For ``f = T1 | T2 | ... | Tk``, emit one rule per AND-arm reading only that
    arm's factors.  Returns None if the structure is not OR-of-AND-terms."""
    is_or  = isinstance(expr, BinOp) and expr.op in ("or", "logor")
    is_and = isinstance(expr, BinOp) and expr.op in ("and", "logand")

    if is_or:
        arms = _flatten_conn(expr)
        onset: list[list[str]] = []
        for arm in arms:
            row = _arm_true_lits(arm, leaf_false, leaf_true)
            if row is None:
                return None
            onset.append(row)
        return onset

    if is_and:
        row = _arm_true_lits(expr, leaf_false, leaf_true)
        return [row] if row is not None else None

    # Bare leaf: ON-set is just the true-polarity literals.
    key = _expr_key(expr)
    tl = leaf_true.get(key)
    return [[*tl]] if tl is not None else None


def _arm_true_lits(
    arm: Expr,
    leaf_false: dict[str, list[str]],
    leaf_true: dict[str, list[str]],
) -> list[str] | None:
    """Collect all "must-be-true" body literals for an AND-arm to be true.
    Returns a flat list of literals, or None if the arm contains an unsupported structure."""
    is_and = isinstance(arm, BinOp) and arm.op in ("and", "logand")
    is_not = isinstance(arm, UnOp) and arm.op in ("not", "lnot")

    if is_and:
        factors = _flatten_conn(arm)
        result: list[str] = []
        for f in factors:
            lits = _arm_true_lits(f, leaf_false, leaf_true)
            if lits is None:
                return None
            result.extend(lits)
        return result

    if is_not:
        # ~leaf is true when leaf=0, i.e. the FALSE polarity of the inner leaf.
        inner = arm.operand
        key = _expr_key(inner)
        fl = leaf_false.get(key)
        return [*fl] if fl is not None else None

    # A positive leaf: true when its true-polarity literals hold.
    key = _expr_key(arm)
    tl = leaf_true.get(key)
    return [*tl] if tl is not None else None


# --------------------------------------------------------------------------
# Reduction-over-index functor lowering (collapse OR-of-index-templated arms)
# --------------------------------------------------------------------------
# An RHS that is an OR of N structurally-identical, bit-index-parameterized arms
# (e.g. the divider's srcBIsPowerOfTwo_D1 = "bit j is the sole set bit, below the
# sign region", one arm per j) minterm-explodes in _emit_bool (thousands of rules).
# Instead recognize the arm template and emit index-GENERIC functor rules over J,
# using prefix-reduction functors (zeros_below/zeros_above/ones_above) that are
# O(N) index recurrences. ~6 rules instead of thousands. Fail-loud: any arm that
# does not fit the template -> return False -> caller falls back to _emit_bool.
#
# Recognized per-arm AND-factors (each keyed by a single bit index j):
#   sole-bit       in[j]                 -> Slice(base, j, j) or BitSel(base, j)
#   zeros-below    ~|in[j-1:0]           -> UnOp(not, UnOp(ror, Slice(base, j-1, 0)))
#   zeros-above    ~|in[hi:j+1]          -> UnOp(not, UnOp(ror, Slice(base, hi, j+1)))
#   ones-above     &in[hi:j+1]           -> UnOp(rand, Slice(base, hi, j+1))
#   signed-above   ~|in[hi:j+1] | (&in[hi:j+1] & S)   (zeros-above OR (ones-above AND signal S))
#   free signal    an index-free Ref (e.g. sgnOp_D1)  -- same in every arm

def _base_name(e: Expr) -> str | None:
    return e.name if isinstance(e, Ref) else None


def _slice_of(e: Expr) -> tuple[str, int, int] | None:
    """(base_name, hi, lo) if e is a Slice/BitSel of a bare Ref, else None."""
    if isinstance(e, Slice) and isinstance(e.base, Ref):
        return (e.base.name, e.hi, e.lo)
    if isinstance(e, BitSel) and isinstance(e.base, Ref):
        return (e.base.name, e.index, e.index)
    return None


def _classify_arm_factor(f: Expr):
    """Classify one AND-factor into (kind, base, j, extra). kind in
    {'bit','zbelow','zabove','oabove','soabove'}; j is the parameterizing bit index;
    extra is the free signal name for 'soabove'. None if the factor does not fit."""
    # sole-bit  in[j]
    sl = _slice_of(f)
    if sl is not None and sl[1] == sl[2]:
        return ("bit", sl[0], sl[1], None)
    # ~|in[a:b]  == UnOp(not, UnOp(ror, Slice))
    if (isinstance(f, UnOp) and f.op == "not" and isinstance(f.operand, UnOp)
            and f.operand.op == "ror"):
        inner = _slice_of(f.operand.operand)
        if inner is not None:
            base, hi, lo = inner
            if lo == 0:                                  # zeros-below: ~|in[j-1:0], j = hi+1
                return ("zbelow", base, hi + 1, None)
            return ("zabove", base, lo - 1, None)        # zeros-above: ~|in[hi:j+1], j = lo-1
    # &in[hi:j+1]  == UnOp(rand, Slice)
    if isinstance(f, UnOp) and f.op == "rand":
        inner = _slice_of(f.operand)
        if inner is not None:
            base, hi, lo = inner
            return ("oabove", base, lo - 1, None)        # ones-above: &in[hi:j+1], j = lo-1
    # signed-above:  ~|in[hi:j+1] | (&in[hi:j+1] & S)
    if isinstance(f, BinOp) and f.op in ("or", "logor"):
        za = _classify_arm_factor(f.left)
        rhs = f.right
        if (za is not None and za[0] == "zabove" and isinstance(rhs, BinOp)
                and rhs.op in ("and", "logand")):
            oa = _classify_arm_factor(rhs.left)
            sig = _base_name(rhs.right)
            if oa is not None and oa[0] == "oabove" and sig is not None \
                    and oa[1] == za[1] and oa[2] == za[2]:
                return ("soabove", za[1], za[2], sig)
    return None


def _try_reduction_over_index(lhs: str, rhs: Expr, out: _Out, bitvec_signals,
                              clk: str, has_clock: bool) -> bool:
    """Recognize `lhs = OR over j of <template(j)>` where each arm's AND-factors are index-keyed
    reductions (sole-bit / zeros-below / signed-above). On success emit index-generic functor rules
    and return True; otherwise emit nothing and return False (caller falls back to _emit_bool).

    Correctness: the reduction functors are exact prefix folds over the bit index (induction on j);
    the term functor maps 1:1 onto each RTL arm; OR = existential (one positive rule + NAF off).
    """
    if not (isinstance(rhs, BinOp) and rhs.op in ("or", "logor")):
        return False
    arms = _flatten_conn(rhs)
    if len(arms) < 4:                                    # not worth it / not the pattern
        return False
    # Decompose each arm into AND-factors and classify. Require EVERY arm to have the SAME
    # multiset of factor kinds keyed by a single consistent j, over the SAME base signal.
    templates: list[tuple] = []
    base_name: str | None = None
    free_sig: str | None = None
    js: list[int] = []
    for arm in arms:
        factors = _flatten_conn(arm) if (isinstance(arm, BinOp) and arm.op in ("and", "logand")) \
            else [arm]
        kinds: dict[str, int] = {}
        arm_j: int | None = None
        arm_base: str | None = None
        arm_sig: str | None = None
        ok = True
        for f in factors:
            c = _classify_arm_factor(f)
            if c is None:
                ok = False
                break
            kind, b, j, extra = c
            kinds[kind] = kinds.get(kind, 0) + 1
            arm_base = arm_base or b
            if b != arm_base:
                ok = False
                break
            if arm_j is None:
                arm_j = j
            elif arm_j != j:
                ok = False
                break
            if extra is not None:
                arm_sig = extra
        if not ok or arm_j is None or arm_base is None:
            return False
        templates.append(tuple(sorted(kinds.items())))
        js.append(arm_j)
        base_name = base_name or arm_base
        if arm_base != base_name:
            return False
        if arm_sig is not None:
            free_sig = free_sig or arm_sig
            if arm_sig != free_sig:
                return False
    # All arms must fit ONE template shape modulo boundary degeneracy (at the top bit the
    # above-slice is empty; at the bottom bit the below-slice is empty -- those factors are
    # vacuously true and simply absent from that arm). Accept arms whose kind-set is a SUBSET of
    # the maximal template, and require the j's to cover a contiguous range exactly once.
    kind_union: set[str] = set()
    for t in templates:
        kind_union |= {k for k, _n in t}
    # each present factor kind must appear at most once per arm
    for t in templates:
        if any(n != 1 for _k, n in t):
            return False
    lo_j, hi_j = min(js), max(js)
    if sorted(js) != list(range(lo_j, hi_j + 1)):        # contiguous, no gaps/dups
        return False
    tmpl = {k: 1 for k in kind_union}
    # This narrow recognizer handles exactly the sole-bit power-of-two family:
    #   maximal template = { bit, zbelow, above } where `above` is zabove OR soabove.
    #   Boundary arms may omit zbelow (j=lo) or the above-factor (j=hi) -- both vacuously true
    #   there and reconstructed by the fold base cases.
    has_bit = tmpl.get("bit", 0) == 1
    has_zbelow = tmpl.get("zbelow", 0) == 1
    has_soabove = tmpl.get("soabove", 0) == 1
    has_zabove = tmpl.get("zabove", 0) == 1
    above_kind = "soabove" if has_soabove else ("zabove" if has_zabove else None)
    extra_kinds = set(tmpl) - {"bit", "zbelow", "soabove", "zabove"}
    # exactly one flavour of above-factor (a template can't mix a signed and unsigned above)
    if not has_bit or (has_soabove and has_zabove) or extra_kinds:
        return False
    if not has_zbelow and above_kind is None:            # nothing to fold -- not this pattern
        return False
    # verify boundary-only omissions: an arm missing zbelow must be at j=lo_j; missing above at j=hi_j.
    for t, j in zip(templates, js, strict=True):
        ks = {k for k, _n in t}
        if has_zbelow and "zbelow" not in ks and j != lo_j:
            return False
        if above_kind is not None and above_kind not in ks and j != hi_j:
            return False
        if "bit" not in ks:
            return False
    if base_name not in bitvec_signals:                  # need per-bit val(base(J),B,T) reads
        return False

    # ---- emit the index-generic functor rules ----
    base = base_name
    tg = f"time({clk}, T)" if has_clock else "time(_, T)"
    tag = _ATOM_SAFE.sub("_", lhs)                       # unique functor prefix per lhs

    # prefix-reduction recurrences (O(N) each; positive-definite folds over J)
    if has_zbelow:
        # zeros_below(J) == ~|base[J-1:0]
        out.rule(f"val({tag}__zbelow({lo_j}), 1, T)", [tg])
        out.rule(f"val({tag}__zbelow(J), 1, T)",
                 [f"J = {lo_j + 1}..{hi_j}", f"val({tag}__zbelow(J - 1), 1, T)",
                  f"val({base}(J - 1), 0, T)"])
    if above_kind is not None:
        # zeros_above(J) == ~|base[hi:J+1]  (fold from the top)
        out.rule(f"val({tag}__zabove({hi_j}), 1, T)", [tg])
        out.rule(f"val({tag}__zabove(J), 1, T)",
                 [f"J = {lo_j}..{hi_j - 1}", f"val({tag}__zabove(J + 1), 1, T)",
                  f"val({base}(J + 1), 0, T)"])
    if above_kind == "soabove":
        # ones_above(J) == &base[hi:J+1]; signed-above(J) == zeros_above(J) | (ones_above(J) & S)
        out.rule(f"val({tag}__oabove({hi_j}), 1, T)", [tg])
        out.rule(f"val({tag}__oabove(J), 1, T)",
                 [f"J = {lo_j}..{hi_j - 1}", f"val({tag}__oabove(J + 1), 1, T)",
                  f"val({base}(J + 1), 1, T)"])
        out.rule(f"val({tag}__soabove(J), 1, T)",
                 [f"J = {lo_j}..{hi_j}", f"val({tag}__zabove(J), 1, T)"])
        out.rule(f"val({tag}__soabove(J), 1, T)",
                 [f"J = {lo_j}..{hi_j}", f"val({tag}__oabove(J), 1, T)",
                  f"val({free_sig}, 1, T)"])

    # term(J): bit J set, (zeros below), (above)
    term_body = [f"J = {lo_j}..{hi_j}", f"val({base}(J), 1, T)"]
    if has_zbelow:
        term_body.append(f"val({tag}__zbelow(J), 1, T)")
    if above_kind is not None:
        term_body.append(f"val({tag}__{above_kind}(J), 1, T)")
    out.rule(f"val({tag}__term(J), 1, T)", term_body)

    # OR over J == exists J : term(J)   (positive), plus the NAF off-rule (boundary predicate)
    out.rule(f"val({lhs}, 1, T)", [f"val({tag}__term(_), 1, T)"])
    out.rule(f"val({lhs}, 0, T)", [tg, f"not val({lhs}, 1, T)"])
    return True



def _emit_bool(lhs: str, expr: Expr, out: _Out, style: str, clk: str, has_clock: bool,
               widths: dict[str, int] | None = None) -> None:
    """A boolean function over leaves -- 1-bit signals AND comparisons / word `!=0` tests (so
    `(a==b) && (x!=y)`, gates, muxes all work). Enumerate the leaf minterms: on-set -> true rules,
    off-set -> false rules (v1) or the excluded-middle complement (v2). A 1-bit result is a width-1
    word atom ``val(lhs, V, T)`` (no bit-position slot).

    A LARGE boolean tree (> _MAX_BOOL_LEAVES leaves) would blow up 2^N minterm enumeration, so it is
    DECOMPOSED structurally: the top associative connective is flattened and its operands chunked into
    fresh intermediate bit signals (`lhs__k`), then combined -- each sub-emit sees few leaves. Sound
    (positive-definite, identical models); linear in tree size instead of exponential."""
    if isinstance(expr, BinOp) and expr.op in _BOOL_CONN and _bool_leaves(expr) > _MAX_BOOL_LEAVES:
        ops = _flatten_conn(expr)
        # group operands so each group has <= _MAX_BOOL_LEAVES leaves; emit each as lhs__k
        groups: list[list[Expr]] = []
        cur: list[Expr] = []
        cur_lv = 0
        for o in ops:
            lv = _bool_leaves(o)
            if cur and cur_lv + lv > _MAX_BOOL_LEAVES:
                groups.append(cur)
                cur, cur_lv = [], 0
            cur.append(o)
            cur_lv += lv
        if cur:
            groups.append(cur)
        subsigs: list[Expr] = []
        for k, g in enumerate(groups):
            sub = f"{lhs}__b{k}"
            gexpr = g[0]
            for extra in g[1:]:
                gexpr = BinOp(expr.op, gexpr, extra, 1)
            _emit_bool(sub, gexpr, out, style, clk, has_clock, widths)
            subsigs.append(Ref(sub))
        combined = subsigs[0]
        for s in subsigs[1:]:
            combined = BinOp(expr.op, combined, s, 1)
        _emit_bool(lhs, combined, out, style, clk, has_clock, widths)   # combine (few leaves now)
        return
    ctx = _Ctx(out.used)
    leaves: list[tuple[str, list[str], list[str]]] = []   # (key, true_lits, false_lits)
    seen: dict[str, int] = {}

    def add_leaf(e: Expr) -> None:
        key = _expr_key(e)
        if key in seen:
            return
        br = _cond_branches(e, ctx, widths)                    # Ref / comparison -> (true, false)
        if br is not None:
            t_lits, f_lits = br
        elif isinstance(e, Ref) and (widths is None or widths.get(e.name, 1) <= 1):
            t_lits, f_lits = [f"val({e.name}, 1, T)"], [f"val({e.name}, 0, T)"]
        else:                                                 # a word expression used as a bool
            rb, rv = _word_body(e, "T", ctx)
            t_lits, f_lits = [*rb, f"{rv} != 0"], [*rb, f"{rv} = 0"]
        seen[key] = len(leaves)
        leaves.append((key, t_lits, f_lits))

    def collect(e: Expr) -> None:
        if _is_bool_conn(e):
            if isinstance(e, UnOp):
                collect(e.operand)
            else:
                collect(e.left)
                collect(e.right)
        else:
            add_leaf(e)

    collect(expr)
    out.used |= ctx.used
    leaf_false = {k: fl for k, _tl, fl in leaves}
    leaf_true  = {k: tl for k, tl, _fl in leaves}

    # SOP path: OR-of-AND-terms (the dominant RTL pattern).
    # ON-set  = one rule per AND-arm, reading only that arm's factors — no undefined leaves from
    #           orthogonal arms leak into a rule body.
    # OFF-set = NAF: val(lhs, 0, T) :- time(CK, T), not val(lhs, 1, T).
    #           Sound because the enable-gates-data invariant guarantees: when a data leaf is
    #           undefined its guard is 0, so no ON rule fires, and NAF correctly yields 0.
    #           Dual: if the expression is naturally POS (describes when output is 0), swap
    #           polarity and NAF gives 1.  Both avoid reading irrelevant path-specific leaves.
    pi_onset = _or_of_ands_onset(expr, leaf_false, leaf_true)
    if pi_onset is not None:
        bind = _bind_t
        for body in pi_onset:
            out.rule(f"val({lhs}, 1, T)", bind(body))
        # NAF zero: one rule derives val(lhs,0,T) when no ON arm fires.
        # Clocked: time(CK,T) in _false_bit(v2) binds T — no domain needed.
        # Clockless (unit-test only): use val(sig,_,T) from the first leaf so T binds from
        # whichever signal the scenario drives, without requiring all leaf signals to be present.
        if has_clock:
            domain: list[str] = []
        else:
            domain = []
            for _k2, tl, _fl in leaves:
                if tl and tl[0].startswith("val("):
                    name = tl[0].split(",")[0][4:]
                    domain = [f"val({name}, _, T)"]
                    break   # one signal is enough to bind T
        _false_bit(lhs, [], domain, out, "v2", clk, has_clock)
        return

    # Fallback: full truth-table minterm enumeration (XOR, comparisons, complex shapes).
    onset: list[list[str]] = []
    offset: list[list[str]] = []
    for mask in range(1 << len(leaves)):
        env = {leaves[i][0]: (mask >> i) & 1 for i in range(len(leaves))}
        body = [lit for i, (_k, tl, fl) in enumerate(leaves) for lit in (tl if (mask >> i) & 1 else fl)]
        (onset if _eval_bool(expr, env) else offset).append(body)

    bind = _bind_t
    for body in onset:
        out.rule(f"val({lhs}, 1, T)", bind(body))
    domain = [lit for _k, tl, _fl in leaves for lit in tl if lit.startswith("val(")]
    _false_bit(lhs, [bind(b) for b in offset], domain, out, style, clk, has_clock)


# --------------------------------------------------------------------------
# combinational (Group 1)
# --------------------------------------------------------------------------
def _sels_complementary(sel_a: "Expr", sel_b: "Expr",
                        comb_defs: dict[str, "Expr"] | None) -> bool:
    """True if sel_a and sel_b are provably complementary (one is ~the other).

    Checks direct UnOp("not"/"lnot") negation and one level of comb_defs substitution.
    This identifies the masked-mux pattern: or(Cond(sel,A,0), Cond(~sel,B,0)) → Cond(sel,A,B).
    """
    def _is_neg_of(neg: "Expr", pos: "Expr") -> bool:
        """True if neg == UnOp(not, pos) (structurally)."""
        return (isinstance(neg, UnOp) and neg.op in ("not", "lnot") and neg.operand == pos)

    if _is_neg_of(sel_b, sel_a) or _is_neg_of(sel_a, sel_b):
        return True
    # One level of comb_defs: sel_b = gcond_N where gcond_N = ~sel_a
    if comb_defs:
        if isinstance(sel_b, Ref):
            defn = comb_defs.get(sel_b.name)
            if defn is not None and _is_neg_of(defn, sel_a):
                return True
        if isinstance(sel_a, Ref):
            defn = comb_defs.get(sel_a.name)
            if defn is not None and _is_neg_of(defn, sel_b):
                return True
    return False


#: IR comparison OPCODES. An enum operand of one of these is fine -- the emitter routes it to a
#: TAG test (`val(busy,1,T) :- val(state,S,T), S != idle.`) with no `@func` in sight. Every
#: other operator builds a `@func` cascade, which cannot take a tag.
#: (Named `_CMP_IR_OPS`, not `_CMP_OPS`: that name is already taken further down for the
#: comparison SYMBOLS used when parsing emitted rule text, and the later definition shadows the
#: earlier one at module level -- which silently made every comparison look arithmetic here.)
_CMP_IR_OPS = frozenset({"eq", "ne", "lt", "le", "gt", "ge"})


def _enum_numeric_refs(e: object, enum_names: set[str]) -> set[str]:
    """Enum-typed signals read in a context that would build a `@func` cascade (Fix 76).

    An enum's value is its TAG, which is what keeps an FSM legible -- but a tag cannot be handed
    to `@add`. This finds exactly the reads that would, so a comparison against a tag stays
    supported while arithmetic is refused at translation time rather than crashing the grounder.

    Generic over the IR's dataclass shape, so a new expression node is walked rather than
    silently skipped."""
    found: set[str] = set()

    def bool_valued(x: object) -> bool:
        """A node whose value is a TRUTH (a comparison, a connective over such nodes, a non-enum
        ref): under a boolean connective it is its own test, not a number."""
        if isinstance(x, BinOp):
            if x.op in _CMP_IR_OPS:
                return True
            return x.op in _BOOL_CONN and bool_valued(x.left) and bool_valued(x.right)
        if isinstance(x, UnOp):
            return x.op in ("not", "lnot") and bool_valued(x.operand)
        return isinstance(x, Ref) and x.name not in enum_names

    def walk(x: object, numeric: bool) -> None:
        if isinstance(x, Ref):
            if numeric and x.name in enum_names:
                found.add(x.name)
            return
        if isinstance(x, (list, tuple)):
            for y in x:
                walk(y, numeric)
            return
        # A CONNECTIVE over boolean-valued operands, itself in a boolean context, is a boolean
        # tree: `state == B0 || state == B1` (the FSM-output decode idiom) reaches _emit_bool,
        # whose leaves are tag compares -- no @func sees a tag. The same shape on a plain signal
        # was always lowered that way; the enum one was refused because the walk marked every
        # operand of a non-comparison BinOp numeric (found by the dataset's fancytimer entry
        # on the VerilogEval reference, 2026-08-19). A bare enum operand of a connective
        # (`state || x`, the word-as-truth test) stays numeric, hence refused: its tag would
        # be compared with 0.
        if not numeric and isinstance(x, BinOp) and x.op in _BOOL_CONN \
                and bool_valued(x.left) and bool_valued(x.right):
            walk(x.left, False)
            walk(x.right, False)
            return
        if not numeric and isinstance(x, UnOp) and x.op in ("not", "lnot") and bool_valued(x.operand):
            walk(x.operand, False)
            return
        if isinstance(x, BinOp):
            sub = numeric or x.op not in _CMP_IR_OPS
            walk(x.left, sub)
            walk(x.right, sub)
            return
        if isinstance(x, Cond):
            walk(x.sel, False)          # the selector is its own 1-bit test
            walk(x.a, numeric)
            walk(x.b, numeric)          # arms inherit the destination's context
            return
        if isinstance(x, (EnumCast, EnumVal)):
            return                      # the two conversions: value -> tag, and tag -> value (ir/enumval.py)
        for f in getattr(x, "__dataclass_fields__", ()):
            walk(getattr(x, f), True)   # UnOp / Slice / Concat / SExt / BitSel: all numeric

    walk(e, False)
    return found


def _bitvec_flatten(e: Expr,
                    width: int | None = None,
                    bitvec_signals: frozenset[str] = frozenset(),
                    comb_defs: dict[str, "Expr"] | None = None) -> list[BitSrc] | None:
    """Flatten a bit-structural expression into its per-bit source list, LSB-first. Each entry is a
    :class:`BitSrc` variant (see emit/bitsource.py):
    ``WordBit(base, bit)``       -- output bit reads bit ``bit`` of packed-word signal ``base`` (@slc)
    ``ConstBit(v)``              -- a constant output bit (0 or 1)
    ``Bool1(expr)``              -- a 1-bit boolean expression; emitted via _emit_bool
    ``Indexed(src, bit)``        -- source is a per-bit signal; read as val(src(bit), B, T) directly
    ``Shift(data, op, amount, w)``-- index remap: data per-bit, amount a word expr; op shl/shr/ashr
    ``CondBits(sel, a, b, w)``   -- masked-mux Cond(sel,a,b) of two per-bit arm lists
    ``Or2Bits(a, b, w)``         -- OR of two bit-structural sub-expressions (two independent passes)
    Handles Ref (word or per-bit), Slice/BitSel, Concat (incl. nested replications), SExt, Const,
    BinOp("shl/shr/ashr", per-bit-Ref, word-amount), and BinOp("or"/"logor") of two bit-structural arms.
    ``comb_defs``: optional mapping from signal name → its RHS Expr.  When provided, a Ref to a bitvec
    signal is substituted through its definition so that named copy chains (tern_N = ...; lhs = tern_N)
    collapse into direct per-bit rules for the named target signal.
    Returns None if any leaf cannot be represented (caller flags)."""
    if isinstance(e, Const):
        w = width if width is not None else e.width
        return [ConstBit((e.value >> i) & 1) for i in range(w)]
    if isinstance(e, Ref):
        w = width if width is not None else 1
        if e.name in bitvec_signals:
            return [Indexed(e.name, i) for i in range(w)]        # per-bit source: direct indexed read
        return [WordBit(e.name, i) for i in range(w)]            # word source: assemble + @slc
    if isinstance(e, Slice) and isinstance(e.base, Ref):
        if e.base.name in bitvec_signals:                        # per-bit source
            return [Indexed(e.base.name, e.lo + i) for i in range(e.hi - e.lo + 1)]
        return [WordBit(e.base.name, e.lo + i) for i in range(e.hi - e.lo + 1)]
    if isinstance(e, BitSel) and isinstance(e.base, Ref):
        if e.base.name in bitvec_signals:
            return [Indexed(e.base.name, e.index)]
        return [WordBit(e.base.name, e.index)]
    if isinstance(e, SExt) and isinstance(e.operand, (Ref, Slice, BitSel)):
        low = _bitvec_flatten(e.operand, e.from_w, bitvec_signals, comb_defs)
        if low is None or len(low) != e.from_w:
            return None
        sign = low[-1]                                   # bit (from_w - 1) = the sign bit
        return low + [sign] * (e.to_w - e.from_w)        # replicate the sign bit into the high bits
    # Phase 2: variable shift of a per-bit signal — index remapping, not arithmetic.
    # `data << amount`: output bit I reads data bit (I-S) for shl, (I+S) for shr/ashr.
    # The Shift entry covers the entire output [0..W-1] and is handled specially by _emit_bitvec.
    # Handles both BinOp("shl", Ref(bitvec), ...) and BinOp("shl", Slice(Ref(bitvec), hi, lo), ...).
    if isinstance(e, BinOp) and e.op in ("shl", "shr", "ashr"):
        left = e.left
        # Unwrap a full-width or partial slice: Slice(Ref(bitvec), ...) with the bitvec left operand
        data_name: str | None = None
        if isinstance(left, Ref) and left.name in bitvec_signals:
            data_name = left.name
        elif (isinstance(left, Slice) and isinstance(left.base, Ref)
              and left.base.name in bitvec_signals):
            data_name = left.base.name
        if data_name is not None:
            w = width if width is not None else e.width
            return [Shift(data_name, e.op, e.right, w)]        # single entry covers all W output bits
    # Phase 4: Cond(sel, a, b) where both arms are bit-structural — masked-mux of two per-bit exprs.
    # The selector stays as a word expression (resolved by _cond_branches at emit time).
    # Returns a single-entry list with the CondBits entry covering all W output bits.
    if isinstance(e, Cond):
        w = width if width is not None else e.width
        bits_a = _bitvec_flatten(e.a, w, bitvec_signals, comb_defs)
        bits_b = _bitvec_flatten(e.b, w, bitvec_signals, comb_defs)
        if bits_a is not None and bits_b is not None:
            return [CondBits(e.sel, bits_a, bits_b, w)]        # single entry covers all W output bits
    # BinOp("or"): try to recognise or(Cond(sel,A,0), Cond(~sel,B,0)) → Cond(sel,A,B).
    # This covers the masked-mux pattern from Fix 29: {N{sel}}&A | {N{~sel}}&B.
    # The OR of two zero-masked Cond arms with complementary selectors is a ternary — use the
    # existing CondBits path so the result is disjoint-by-construction (no multi-valued risk).
    if isinstance(e, BinOp) and e.op in ("or", "logor"):
        w = width if width is not None else e.width
        lc, rc = e.left, e.right
        # Both arms must be Cond(sel, data, Const(0))
        if (isinstance(lc, Cond) and isinstance(lc.b, Const) and lc.b.value == 0
                and isinstance(rc, Cond) and isinstance(rc.b, Const) and rc.b.value == 0
                and _sels_complementary(lc.sel, rc.sel, comb_defs)):
            # or(Cond(sel,A,0), Cond(~sel,B,0))  ≡  Cond(sel,A,B)
            equiv = Cond(lc.sel, lc.a, rc.a, w)
            return _bitvec_flatten(equiv, w, bitvec_signals, None)
        # Fallback: not complementary — try Or2Bits (two independent arms, may be multi-valued)
        bits_a = _bitvec_flatten(lc, w, bitvec_signals, comb_defs)
        bits_b = _bitvec_flatten(rc, w, bitvec_signals, comb_defs)
        if bits_a is not None and bits_b is not None:
            return [Or2Bits(bits_a, bits_b, w)]
    if isinstance(e, Concat):
        out: list[BitSrc] = []
        for expr, w in reversed(e.parts):                # MSB-first written -> iterate LSB-first
            sub = _bitvec_flatten(expr, w, bitvec_signals, comb_defs)
            if sub is not None:
                # Coalesce single Bool1 from sub into a ReplBool1 group if it matches the previous
                # entry.  This handles {N{compound_expr}} lowered as N identical single-element
                # Concat wrappers, each returning [Bool1(expr)].
                if len(sub) == 1 and isinstance(sub[0], Bool1):
                    sub_expr = sub[0].expr
                    if out and isinstance(out[-1], ReplBool1) and out[-1].expr == sub_expr:
                        out[-1] = ReplBool1(out[-1].count + 1, sub_expr)
                    elif out and isinstance(out[-1], Bool1) and out[-1].expr == sub_expr:
                        out[-1] = ReplBool1(2, sub_expr)
                    else:
                        out.extend(sub)
                else:
                    out.extend(sub)
            elif w == 1:
                # Bare w=1 part that flatten couldn't reduce — coalesce identical Bool1 entries.
                if out and isinstance(out[-1], ReplBool1) and out[-1].expr == expr:
                    out[-1] = ReplBool1(out[-1].count + 1, expr)
                elif out and isinstance(out[-1], Bool1) and out[-1].expr == expr:
                    out[-1] = ReplBool1(2, expr)
                else:
                    out.append(Bool1(expr))
            else:
                return None
        return out
    return None


def _emit_bitvec(lhs: str, rhs: Expr, out: _Out, widths: dict[str, int],
                 lane_dims: dict[str, int], loc: object,
                 style: str = "v1", clk: str = "", has_clock: bool = False,
                 bitvec_signals: frozenset[str] = frozenset(),
                 seq_guards: list[str] | None = None,
                 head_t: str = "T",
                 _bits_override: list[tuple] | None = None,
                 _lane_prefix: str = "",
                 _lane_elem_w: int | None = None,
                 comb_defs: dict[str, "Expr"] | None = None) -> set[int]:
    """--bitvec: lower a bit-structural RHS to compact range-guarded per-bit rules.

    Combinational: head_t="T", seq_guards=None.
    Sequential capture: head_t="T+1", seq_guards=[time_guard, "T < k", *enable/branch_guards].

    Each run produces one rule:
      val(lhs(J), B, head_t) :- [rng], [seq_guards], <body_reading_source_bit>.
    For @indexed sources: body is val(src(term), B, T)  — pure index, no @slc.
    For word sources:      body is val(src, V0, T), V = @slc(V0, term, 1).
    For constant bits:     body is [time_guard] (or seq_guards).
    For @bool1:            ON rule with seq_guards; NAF OFF rule (only for combinational).

    _bits_override: if provided, skip _bitvec_flatten and use this pre-flattened list directly.
    Used by the @cond handler to emit each arm independently without re-flattening.

    _lane_prefix: when non-empty (e.g. "I"), the head functor gains an extra outer index from the
    lane dimension: val(lhs(I, J), ...) instead of val(lhs(J), ...). Used for wide-element lane
    signals from generate-for loops (phase 5). Sources are also prefixed: src(I, J) not src(J).

    Returns the set of output bit indices covered by the emitted rules (for coverage check)."""
    # Bit variable: "I" for scalar bitvec (no lane prefix), "J" for wide-lane bitvec (lane prefix=I).
    bit_var = "J" if _lane_prefix else "I"
    lh = _lane_term(lhs, f"{_lane_prefix}, {bit_var}") if _lane_prefix else _lane(lhs, lane_dims)
    # For wide-lane bitvec, flatten the per-lane width (elem_w), not the total signal width.
    # _lane_prefix is "I" for wide-lane signals; bits should cover one lane's worth of bits.
    if _lane_prefix and not _bits_override:
        flatten_w = _lane_elem_w if _lane_elem_w else widths.get(lhs)
        bits = _bitvec_flatten(rhs, flatten_w, bitvec_signals, comb_defs)
    else:
        bits = _bits_override if _bits_override is not None else _bitvec_flatten(rhs, widths.get(lhs), bitvec_signals, comb_defs)
    if bits is None:
        out.problem(loc, f"bitvec (per-bit) lowering unsupported for {lhs}")
        return set()

    covered: set[int] = set()
    n = len(bits)

    # Helper: build the source-bit term string (an I-expression or a constant)
    def _src_term(bit_at_lo: int, lo: int, step: int) -> str:
        if step == 0:
            return str(bit_at_lo)                        # replicated: constant index
        delta = bit_at_lo - lo
        return bit_var if delta == 0 else (f"{bit_var} + {delta}" if delta > 0 else f"{bit_var} - {-delta}")

    def _src_indexed_term(src_name: str, term: str) -> str:
        """Build the source functor for an @indexed read.
        For wide-lane bitvec (has lane prefix): src(I, term); otherwise src(term)."""
        if _lane_prefix:
            return f"{src_name}({_lane_prefix}, {term})"
        return f"{src_name}({term})"

    def _emit_one_run(lo: int, hi: int, entry: BitSrc, step: int = 1) -> None:
        """Emit one rule covering output bits [lo..hi]. ``entry`` is from the bits list.
        ``step`` is 0 (replicated bit) or 1 (contiguous slice)."""
        rng = f"{bit_var} = {lo}" if lo == hi else f"{bit_var} = {lo}..{hi}"
        covered.update(range(lo, hi + 1))

        if isinstance(entry, ConstBit):                  # constant bits
            val = entry.v
            if seq_guards:
                out.rule(f"val({lh}, {val}, {head_t})", [rng, *seq_guards])
            else:
                t_guard = f"time({clk}, T)" if has_clock else "time(_, T)"
                out.rule(f"val({lh}, {val}, {head_t})", [rng, t_guard])
            return

        if isinstance(entry, Bool1):                     # 1-bit bool expr; lo..hi if replicated
            expr = entry.expr
            ctx = _Ctx(out.used)
            vbody, vt = _word_body(expr, "T", ctx)
            out.used |= ctx.used
            if lo == hi:
                bit_lhs = _lane_term(lhs, f"{_lane_prefix}, {lo}") if _lane_prefix else _lane_term(lhs, str(lo))
                if seq_guards:
                    out.rule(f"val({bit_lhs}, 1, {head_t})", [*seq_guards, f"{vt} != 0", *vbody])
                else:
                    _emit_bool(bit_lhs, expr, out, style=style, clk=clk, has_clock=has_clock, widths=widths)
            else:
                # Replicated Bool1 across a range: one range-guarded rule covers lo..hi
                bit_lhs = _lane_term(lhs, f"{_lane_prefix}, {bit_var}" if _lane_prefix else bit_var)
                if seq_guards:
                    out.rule(f"val({bit_lhs}, 1, {head_t})", [rng, *seq_guards, f"{vt} != 0", *vbody])
                    out.rule(f"val({bit_lhs}, 0, {head_t})", [rng, *seq_guards, f"{vt} = 0", *vbody])
                else:
                    # F28's class, closed by audit: a constant-valued expr gives an empty vbody, and
                    # nothing else here binds T -- same missing-binder shape as the Shift fills.
                    if any(("val(" in g) or ("time(" in g) for g in vbody):
                        tb = []
                    else:
                        tb = [f"time({clk}, T)" if has_clock else "time(_, T)"]
                    out.rule(f"val({bit_lhs}, 1, {head_t})", [rng, *tb, f"{vt} != 0", *vbody])
                    out.rule(f"val({bit_lhs}, 0, {head_t})", [rng, *tb, f"{vt} = 0", *vbody])
            return

        if isinstance(entry, Indexed):                   # per-bit source: direct val(src(term), B, T)
            term = _src_term(entry.bit, lo, step)
            head_atom = _lane_term(lhs, f"{_lane_prefix}, {bit_var}" if _lane_prefix else bit_var)
            src_atom = _src_indexed_term(entry.src, term)
            out.rule(f"val({head_atom}, B, {head_t})",
                     [rng, *(seq_guards or []), f"val({src_atom}, B, T)"])
            return

        if isinstance(entry, Shift):                     # index remap: data(J±S) where S = word amount
            data_name, op, amount_expr, W = entry.data, entry.op, entry.amount, entry.w
            covered.update(range(W))
            ctx = _Ctx(out.used)
            amt_body, amt_var = _word_body(amount_expr, "T", ctx)
            out.used |= ctx.used
            base_guards = [*(seq_guards or []), *amt_body]
            # F28: the ZERO-FILL rules below have no data read to bind T -- with a CONSTANT amount
            # (amt_body = []) in a combinational context (no seq_guards) nothing does, and clingo
            # refuses the rule as unsafe (loud, F10). The fill is a constant at every instant, so it
            # takes the same time guard the ConstBit branch uses. Data-remap rules bind T through
            # their source read and are untouched; guarded contexts keep their bytes.
            if any(("val(" in g) or ("time(" in g) for g in base_guards):
                fill_guards = base_guards
            else:
                fill_guards = [*base_guards, f"time({clk}, T)" if has_clock else "time(_, T)"]
            # Helper: head functor with bit variable (possibly with offset) and optional lane prefix
            def _sh(bexpr: str) -> str:
                idx = f"{_lane_prefix}, {bexpr}" if _lane_prefix else bexpr
                return _lane_term(lhs, idx)
            if op == "shl":
                out.rule(f"val({_sh(f'{bit_var} + {amt_var}')}, B, {head_t})",
                         [f"{bit_var} = 0..{W - 1}", *base_guards,
                          f"val({_src_indexed_term(data_name, bit_var)}, B, T)",
                          f"{bit_var} + {amt_var} < {W}"])
                out.rule(f"val({_sh(bit_var)}, 0, {head_t})",
                         [f"{bit_var} = 0..{W - 1}", *fill_guards, f"{bit_var} < {amt_var}"])
            else:
                out.rule(f"val({_sh(bit_var)}, B, {head_t})",
                         [f"{bit_var} = 0..{W - 1}", *base_guards,
                          f"val({_src_indexed_term(data_name, f'{bit_var} + {amt_var}')}, B, T)",
                          f"{bit_var} + {amt_var} < {W}"])
                out.rule(f"val({_sh(bit_var)}, 0, {head_t})",
                         [f"{bit_var} = 0..{W - 1}", *fill_guards,
                          f"{bit_var} + {amt_var} >= {W}"])
            return

        if isinstance(entry, CondBits):                  # masked-mux of two bitvec arms
            sel_expr, bits_a, bits_b, W = entry.sel, entry.a, entry.b, entry.w
            covered.update(range(W))
            ctx = _Ctx(out.used)
            branches = _cond_branches(sel_expr, ctx)
            if branches is None:
                out.problem(loc, f"bitvec @cond: unsupported selector for {lhs}")
                return
            sel_t, sel_f = branches
            out.used |= ctx.used
            _emit_bitvec(lhs, rhs, out, widths, lane_dims, loc, style, clk, has_clock,
                         bitvec_signals, [*(seq_guards or []), *sel_t], head_t,
                         _bits_override=bits_a, _lane_prefix=_lane_prefix, _lane_elem_w=_lane_elem_w,
                         comb_defs=comb_defs)
            _emit_bitvec(lhs, rhs, out, widths, lane_dims, loc, style, clk, has_clock,
                         bitvec_signals, [*(seq_guards or []), *sel_f], head_t,
                         _bits_override=bits_b, _lane_prefix=_lane_prefix, _lane_elem_w=_lane_elem_w,
                         comb_defs=comb_defs)
            return

        if isinstance(entry, Or2Bits):                   # OR of two bit-structural arms (no selector)
            bits_a, bits_b, W = entry.a, entry.b, entry.w
            covered.update(range(W))
            _emit_bitvec(lhs, rhs, out, widths, lane_dims, loc, style, clk, has_clock,
                         bitvec_signals, seq_guards, head_t,
                         _bits_override=bits_a, _lane_prefix=_lane_prefix, _lane_elem_w=_lane_elem_w,
                         comb_defs=comb_defs)
            _emit_bitvec(lhs, rhs, out, widths, lane_dims, loc, style, clk, has_clock,
                         bitvec_signals, seq_guards, head_t,
                         _bits_override=bits_b, _lane_prefix=_lane_prefix, _lane_elem_w=_lane_elem_w,
                         comb_defs=comb_defs)
            return
        # WordBit: read bit of a packed-word signal via @slc
        base, bit_at_lo = entry.base, entry.bit
        term = _src_term(bit_at_lo, lo, step)
        ctx = _Ctx(out.used)
        v0, v = ctx.fresh(), ctx.fresh()
        ctx.used.add("slc")
        out.used |= ctx.used
        # a ONE-LEVEL LANE source inside a lane rule is read at the head's lane, `enc(I)` --
        # `mag[i] = enc[i][1:0]` on a two-level per-bit target read the WORD `enc` and left I
        # unbound (a field report, 2026-09-04: the Booth encoder's magnitude bits)
        src = _lane_term(base, "I") if (lane_dims.get(base, 0) == 1 and "(I" in lh) else base
        out.rule(f"val({lh}, {v}, {head_t})",
                 [rng, *(seq_guards or []), f"val({src}, {v0}, T)", f"{v} = @slc({v0}, {term}, 1)"])

    # Coalesce maximal runs by (variant, source) with constant step.
    # Bool1 never coalesces; ConstBit coalesces only equal-valued runs (step=0).
    i = 0
    while i < n:
        entry = bits[i]

        if isinstance(entry, ReplBool1):
            # N consecutive identical Bool1 entries — emit one range-guarded rule for all N bits.
            _emit_one_run(i, i + entry.count - 1, Bool1(entry.expr), 0)
            i += entry.count
            continue

        if isinstance(entry, (Bool1, Shift, CondBits, Or2Bits)):  # never coalesce — always single-run
            _emit_one_run(i, i, entry, 0)
            i += 1
            continue

        base_key = entry.base_key
        b0 = entry.cbit

        j = i
        step: int | None = None
        while j + 1 < n:
            nxt = bits[j + 1]
            if isinstance(nxt, (Bool1, Shift, CondBits, Or2Bits, ReplBool1)):
                break
            nxt_key = nxt.base_key
            nxt_b = nxt.cbit
            # cur_b = coalescing bit of the CURRENT last entry in the run
            cur_b = bits[j].cbit
            if nxt_key != base_key:
                break
            s = nxt_b - cur_b
            allowed = (0,) if isinstance(entry, ConstBit) else (0, 1)
            if s not in allowed:
                break
            if step is None:
                step = s
            elif s != step:
                break
            j += 1

        run_step = step if step is not None else 0
        # Reconstruct a canonical entry for _emit_one_run with b0 as the source bit at position lo=i
        if isinstance(entry, Indexed):
            run_entry: BitSrc = Indexed(entry.src, b0)
        elif isinstance(entry, ConstBit):
            run_entry = ConstBit(b0)
        else:                                            # WordBit
            run_entry = WordBit(entry.base, b0)

        _emit_one_run(i, j, run_entry, run_step)
        i = j + 1

    return covered


def _emit_comb(item: CombItem, shapes: dict[str, Shape], out: _Out, style: str, clk: str,
               has_clock: bool, widths: dict[str, int], lane_dims: dict[str, int],
               lane_elem_w: dict[str, int] | None = None,
               bitvec_signals: frozenset[str] = frozenset(),
               bitvec_word_consumers: frozenset[str] = frozenset(),
               comb_defs: dict[str, "Expr"] | None = None,
               packed_dims: dict[str, tuple] | None = None,
               enum_of: dict[str, str] | None = None,
               bitvec_word_form: frozenset[str] = frozenset()) -> None:
    out.construct(_prov(item.loc))
    lhs = item.lhs
    rhs = item.rhs
    if isinstance(rhs, XVal):
        # `assign y = 'x;`, or the `x` arm of a case/ternary that the executor hoisted into its own
        # comb net: the design constrains nothing here. Declare WHERE (value-free, so the design layer
        # stays positive-definite) and let the boundary companion say what unconstrained MEANS.
        out.rule(f"dontcare_at({lhs}, T)", ["time(_, T)"])
        out.dontcare.append((lhs, widths.get(lhs, 1), item.loc))
        return
    # ENUM read in a NUMERIC context (Fix 76). An enum signal's value is its TAG
    # (`val(s, run, T)`), which is the whole point of the tag form -- an FSM state compares by
    # name and the model stays legible. But SystemVerilog lets an enum be READ as its underlying
    # number, and the tool used to emit a plain copy for that:
    #
    #     val(o, V0, T) :- val(s, V0, T).          % o := s  -- o gets the TAG `run`, not 1
    #
    # so a property written numerically (`val(o, 1, T)`) matched nothing and passed VACUOUSLY,
    # and arithmetic was worse: `@add(run, 1, 2)` crashes the grounder at solve time (clingo
    # exits 65) on a translation that reported success. The schema already carries what is
    # needed -- `enum_value(st_t, run, 1)` -- so the copy becomes a conversion.
    _eo = enum_of or {}
    # Only convert into a DECLARED, non-enum, plain-named signal of this module. A
    # hierarchy-qualified leaf (`u_lane0(mode)`) is an instance's formal port that is itself
    # enum-typed -- the tag must flow into the submodule unchanged -- and it carries no entry
    # here, so converting it would break the port bridge.
    if (isinstance(rhs, Ref) and rhs.name in _eo and lhs not in _eo and "(" not in lhs
            and lhs in widths and shapes.get(lhs) != Shape.INDEXED):
        out.rule(f"val({lhs}, V, T)",
                 [f"val({rhs.name}, Tag, T)", f"enum_value({_eo[rhs.name]}, Tag, V)"])
        return
    if _eo:
        # An enum operand of a COMPARISON is fine -- `state != IDLE` emits the tag test
        # `val(busy, 1, T) :- val(state, S, T), S != idle.`, no @func involved. An enum operand
        # of ARITHMETIC is not: the cascade would hand a tag to a `@func` and clingo fails to
        # ground the whole program at solve time. Refuse at translation time instead.
        bad = sorted({n for n in _enum_numeric_refs(rhs, set(_eo)) if n != lhs})
        if bad:
            out.problem(item.loc,
                        f"enum signal(s) {', '.join(bad)} read in an ARITHMETIC/BITWISE context "
                        f"for {lhs}: an enum's value is its TAG, so the @func cascade would be "
                        f"handed a symbol and clingo could not ground the program. Cast it "
                        f"explicitly, or compare by tag")
            return
    if isinstance(rhs, Cond):
        # Per-bit bitvec path: if lhs is bitvec AND both Cond arms are bit-flattenable, emit
        # per-bit rules for each arm conditioned on the selector. Fall through to _emit_cond otherwise.
        _bv_flat = _bitvec_flatten(rhs, widths.get(lhs), bitvec_signals, comb_defs)
        if (lhs in bitvec_signals and shapes.get(lhs) == Shape.INDEXED
                and _bv_flat is not None
                and all(not isinstance(e, Or2Bits) for e in _bv_flat)):
            _elem_w = (lane_elem_w or {}).get(lhs, 1)
            _lane_pfx = "I" if (lhs in (lane_elem_w or {}) and _elem_w > 1) else ""
            _emit_bitvec(lhs, rhs, out, widths, lane_dims, item.loc, style=style, clk=clk,
                         has_clock=has_clock, bitvec_signals=bitvec_signals, _lane_prefix=_lane_pfx,
                         _lane_elem_w=_elem_w if _lane_pfx else None, comb_defs=comb_defs)
            return
        # inline ternary sel ? a : b -> two condition-gated rules (true picks a, false picks b).
        # A LANE target (`y[i] = s ? a[i] : b[i]` in a generate, not per-bit) falls through to the
        # INDEXED block below, which emits the mux PER LANE; here it was emitted as a WORD mux --
        # `val(y, V, T) :- val(s, 1, T), val(a, V, T)` -- so a per-lane consumer read `y(I)` dark
        # (loud), and a per-lane SELECTOR `s[i]` was tested as the whole word (found by the lane
        # arbiter's print, `gnt__e0 = any_m ? gm[i] : gr[i]`).
        # (a bitvec signal in WORD FORM -- pulled into the per-bit representation by closure but driven
        # by a Cond with a word-op arm, `neg = c ? ~a + 1 : 0` -- keeps the WORD mux; its bridge
        # DECOMPOSES the word into bits, Fix 42)
        if shapes.get(lhs) != Shape.INDEXED or lhs in bitvec_word_form:
            _emit_cond(lhs, rhs, shapes, out, item.loc, widths, lane_dims)
            return
    if isinstance(rhs, EnumCast):
        # value -> enum TAG: val(lhs, Tag, T) :- <operand value V>, enum_value(enum, Tag, V)
        ctx = _Ctx(out.used)
        body, vv = _word_body(rhs.operand, "T", ctx)
        out.used |= ctx.used
        out.rule(f"val({lhs}, Tag, T)", [*_bind_t(body), f"enum_value({rhs.enum}, Tag, {vv})"])
        return
    if shapes.get(lhs) == Shape.INDEXED and lhs in bitvec_word_form:
        # A bitvec signal in WORD FORM: pulled into the per-bit representation by group closure, but
        # driven by a NON-per-lane word op (`c = t + a`: an ADD over a per-bit `t`). Its rule is the
        # WORD rule -- `val(c, V, T) :- val(t, V0, T), val(a, V1, T), V2 = @add(V0, V1, 8)` reading t's
        # ASSEMBLED word -- and the bridge decomposes `c` into bits (Fix 42's direction). It used to
        # fall into the lane branch below and be lowered PER LANE: `val(c(I), ..) :- val(t(I), V0, T),
        # val(a, V1, T), V2 = @add(V0, V1, 8)` -- BIT I of t plus the word a, per bit -- silently wrong
        # (found by the lane arbiter's print, 2026-08-18; `wf3` in test_lane_roll_over_a_partial_index_set).
        ctx = _Ctx(out.used)
        body, vt = _assign_word(rhs, "T", ctx, shapes, lane_dims, widths, widths.get(lhs))
        out.used |= ctx.used
        out.rule(f"val({lhs}, {vt}, T)", _bind_t(body))
        return
    if shapes.get(lhs) == Shape.INDEXED:
        # lane shape: the lane index lives INSIDE the signal functor (q(I) / q(I,J)), by each
        # signal's lane dimension count. A bare Ref is a copy/bridge; a word op (q&mask, a+b, ...)
        # goes via the @func cascade; the grounder fans the rule over every lane (and nested lanes).
        lh = _lane(lhs, lane_dims)
        # `y[i+1] = ..` (the carry-chain shape): the head lane is the loop variable OFFSET by a
        # constant, `y(I+1)`, while the domain literal below still ranges over the LOOP's own
        # index set. Single-index targets only (the frontend refuses the rest).
        _off = getattr(item, "lane_off", 0)
        if _off:
            lh = _lane_term(lhs, f"I{'+' if _off > 0 else '-'}{abs(_off)}")
        # RANGE GUARD (Fix 50). The grounder fans the rule over the TARGET's whole lane domain,
        # but the loop/generate that produced it may cover only part of that domain:
        # `for (i=0;i<3;i++) y[i] = …` over `y[0:7]` drives lanes 0..2 and must leave 3..7
        # undriven. Without the guard every lane was driven — silently wrong whenever the
        # iteration count is narrower than the array.
        # Applied only to a SINGLE-dimension lane target, where the lane count is
        # width/element-width. A multi-dimensional target needs a per-dimension bound (as the
        # memory path computes); until that is threaded through, such a partial loop keeps the
        # previous behaviour rather than getting a wrong single-dimension guard.
        #
        # SAFETY (Fix 51). The guard is emitted as a DOMAIN literal `I = 0..hi-1`, never as a
        # bare comparison `I < hi`: a comparison does not bind I, so the rule would be unsafe
        # and clingo would refuse to ground it. The same applies with no guard at all -- a lane
        # target whose body reads only WORD signals (`y[i] = a + i`, the Fix 50 shape) has
        # nothing to bind I, because the head does not bind variables in ASP. So we emit the
        # full lane domain in that case. When some positive body literal already binds I (the
        # ordinary `y[i] = a[i] | b[i]` shape) nothing is added, which keeps every existing
        # rule byte-identical.
        _elem_w = (lane_elem_w or {}).get(lhs, 1) or 1
        _lanes = widths.get(lhs, 0) // _elem_w
        _ndim = (lane_dims or {}).get(lhs, 1)
        # PER-DIMENSION domains for a NESTED generate/loop (`y[i][j]`). A packed multi-D lane
        # target has no `addr` predicate to bind its indices (an unpacked array does), and its
        # dimensions are NOT interchangeable -- `I = 0..7` over a 2x4 target is simply wrong,
        # and leaves J unbound besides. `packed_dims` carries the real extents (2, 4, elemW),
        # so each lane variable gets its own domain.
        _pdims = ((packed_dims or {}).get(lhs) or ())[:_ndim]

        def _lane_dom(body_lits: list[str]) -> list[str]:
            """The lane-domain literals this rule needs, if any (see SAFETY above)."""
            bound = tuple(_binds_lane_var(body_lits, v) for v in _LANEVARS[:_ndim])
            return _lane_dom_lits(_lane_domains(_ndim, _pdims, _lanes,
                                                getattr(item, "lane_hi", None), bound,
                                                getattr(item, "lane_lo", 0),
                                                getattr(item, "lane_step", 1)))
        if isinstance(rhs, Cond):
            _emit_lane_cond(lhs, rhs, shapes, out, item.loc, widths, lane_dims, _lane_dom)
            return
        if lhs in bitvec_signals and (
                isinstance(rhs, (Concat, SExt, Slice, BitSel))
                or (isinstance(rhs, Cond) and
                    _bitvec_flatten(rhs, widths.get(lhs), bitvec_signals, comb_defs) is not None)
                or (isinstance(rhs, BinOp) and rhs.op in ("or", "logor") and
                    # Only take the bitvec path for OR if it resolves via the complementary
                    # selector rewrite to @cond — NOT if it falls to @or2 (multi-valued risk).
                    isinstance(rhs.left, Cond) and isinstance(rhs.right, Cond) and
                    isinstance(rhs.left.b, Const) and rhs.left.b.value == 0 and
                    isinstance(rhs.right.b, Const) and rhs.right.b.value == 0 and
                    _sels_complementary(rhs.left.sel, rhs.right.sel, comb_defs))
                or (isinstance(rhs, BinOp) and rhs.op in ("shl", "shr", "ashr")
                    and (
                        (isinstance(rhs.left, Ref) and rhs.left.name in bitvec_signals)
                        or (isinstance(rhs.left, Slice) and isinstance(rhs.left.base, Ref)
                            and rhs.left.base.name in bitvec_signals)
                    ))):
            # --bitvec: bit-structural or Cond(bitvec-arms) or shift-of-bitvec -> compact per-bit rules.
            # BinOp("or") covers masked-mux or(Cond(sel,A,0), Cond(~sel,B,0)) → Cond(sel,A,B).
            # For wide-element lane signals (phase 5), use _lane_prefix="I" to emit val(lhs(I,J),B,T).
            elem_w = (lane_elem_w or {}).get(lhs, 1)
            lane_pfx = "I" if (lhs in (lane_elem_w or {}) and elem_w > 1) else ""
            _emit_bitvec(lhs, rhs, out, widths, lane_dims, item.loc, style=style, clk=clk,
                         has_clock=has_clock, bitvec_signals=bitvec_signals, _lane_prefix=lane_pfx,
                         _lane_elem_w=elem_w if lane_pfx else None, comb_defs=comb_defs)
        elif isinstance(rhs, Ref):
            src = rhs.name
            src_ew = (lane_elem_w or {}).get(src, 1)
            if (src in bitvec_signals and src_ew > 1 and src not in bitvec_word_consumers):
                # Wide-lane bitvec source without inner bridge: no val(src(I),V,T) exists.
                # Emit a per-bit copy: val(lhs(I,J), B, T) :- val(src(I,J), B, T).
                pfx = "I"
                bv = "J"
                out.rule(f"val({_lane_term(lhs, f'{pfx}, {bv}')}, B, T)",
                         [f"{bv} = 0..{src_ew - 1}",
                          f"val({_lane_term(src, f'{pfx}, {bv}')}, B, T)"])
            else:
                # A lane-to-lane copy reads the source's lane; a WORD/BIT source (a scalar `b0`
                # in `assign c[0] = b0`, a broadcast) is read whole -- the analysis decides the
                # shape, and a non-INDEXED source has no lane atoms to read.
                src_lane = shapes.get(src) == Shape.INDEXED
                _cp = [f"val({_lane(src, lane_dims) if src_lane else src}, V, T)"]
                out.rule(f"val({lh}, V, T)", [*_lane_dom(_cp), *_cp])
        elif (lambda cs: len(cs) > 1 and all(_is_lane_conjunct(c) for c in cs)
              and any(isinstance(c, BinOp) and c.op in _CMP for c in cs))(_flatten_logand(rhs)):
            # per-lane AND of bit tests WITH a comparison in the chain (CAM-style), in
            # EITHER spelling -- && or 1-bit & -- consulted BEFORE the word path, because
            # a conjunct chain carrying a compare dies inside _word_body (eq is not a
            # word op) while this path lowers it whole. ONLY the compare-carrying case is
            # taken early: pure boolean chains keep their historical word-path lowering,
            # so the committed corpus is byte-identical (the first cut of this branch
            # rerouted them and broke seven lane tests -- the regeneration run, 2026-08-31)
            _emit_lane_and(lhs, _flatten_logand(rhs), shapes, out, style, lane_dims, lane_dom=_lane_dom)
        elif (isinstance(rhs, BinOp) and rhs.op in _WORD_OPS) or \
             (isinstance(rhs, UnOp) and rhs.op in ("not", "neg", "rand", "ror", "rxor",
                                                    "rnand", "rnor", "rxnor")) or \
             isinstance(rhs, (Slice, BitSel, SExt, Concat, ElemSel, Const)):
            # per-lane word op / unary ~a[i] / -a[i] / a per-lane REDUCTION (`par[i] = ^w[i]`,
            # parity of lane i's element) -- and a per-lane SLICE/bit-select of a word
            # expression (`y[i] = a[7-i]`, bit reversal: a dynamic bit-select of the WORD `a`
            # at `7-I`), which used to fall through to the refusal below -- and a BARE
            # neighbouring-lane read (`sh_d[i] = sh_q[i-1]`, the shift chain between two lane
            # signals: `val(sh_d(I), V, T) :- I = 1..3, val(sh_q(I-1), V, T)`), which was refused
            # as "non-copy" while the same read under an operator (`c[i-1] & p[i]`) lowered (F17)
            # -- and a CONSTANT on a lane target (a generate-local `logic [W-1:0] c; assign c = 1;`,
            # the same value in every iteration: `val(c(I), 1, T) :- time(_, T), I = 0..N-1`).
            ctx = _Ctx(out.used)
            body, vt = _word_body(rhs, "T", ctx, shapes, lane_dims, lane_ctx=True)  # head binds I
            out.used |= ctx.used
            body = _bind_t(body)                       # a constant body binds T via time(_, T)
            out.rule(f"val({lh}, {vt}, T)", [*_lane_dom(body), *body])
        elif all(_is_lane_conjunct(c) for c in _flatten_logand(rhs)):
            # the &&-spelling with single conjuncts still lands here, below the word path
            _emit_lane_and(lhs, _flatten_logand(rhs), shapes, out, style, lane_dims, lane_dom=_lane_dom)
        else:
            out.problem(item.loc, f"indexed (per-lane) non-copy combinational for {lhs}")
        return
    if shapes.get(lhs) == Shape.WORD:
        ctx = _Ctx(out.used)
        body, vt = _assign_word(rhs, "T", ctx, shapes, lane_dims, widths, widths.get(lhs))  # truncate to LHS
        out.used |= ctx.used
        out.rule(f"val({lhs}, {vt}, T)", _bind_t(body))   # constant word (assign w=8'd5) binds T via time(_,T)
        return
    # BIT-shape result
    if isinstance(rhs, UnOp) and rhs.op in ("ror", "rand", "rxor", "rnor", "rnand", "rxnor"):
        _emit_reduce(lhs, rhs, shapes, widths, out, item.loc, lane_dims, lane_elem_w)
        return
    if isinstance(rhs, ElemSel):
        # lane select into a scalar bit -- the word<->indexed reshape seam. The lane index may
        # be constant (read the lane directly) or a runtime value (dynamic select).
        if getattr(rhs, "more", ()):
            raise NotImplementedError(f"a multi-level packed select of {rhs.base} into a scalar bit")
        ctx = _Ctx(out.used)
        li, vi = _word_body(rhs.index, "T", ctx)
        out.used |= ctx.used
        vc = ctx.fresh()
        out.rule(f"val({lhs}, {vc}, T)", [*li, f"val({_lane_term(rhs.base, vi)}, {vc}, T)"])
        return
    # Packed-port bit-extraction: assign bit_sig = word_port[N]
    # Emit a named intermediate atom `word_bN` so scenarios can drive individual bits of the
    # packed word directly without providing the full word value.  This avoids grounding
    # explosion when a packed input port (e.g. clken_DX[11:1]) is driven per-T with different
    # values in a single-instruction scenario — the intermediate atoms are constant per rule
    # and clingo can share ground instances efficiently.
    if _is_packed_bit_extraction(rhs, widths):
        _emit_packed_bit_extraction(lhs, rhs, out, style, clk, has_clock, widths)
        return
    if isinstance(rhs, BinOp) and rhs.op in ("eq", "ne") and (isinstance(rhs.left, Tag) or isinstance(rhs.right, Tag)):
        _emit_tag_compare(lhs, rhs, out)                    # state == IDLE / state != IDLE
    elif isinstance(rhs, BinOp) and rhs.op in _CMP:
        _emit_compare(lhs, rhs, out, style, clk, has_clock)
    elif (isinstance(rhs, BinOp) and rhs.op == "logand"
          and _is_bit_lit(rhs.left, widths) and _is_bit_lit(rhs.right, widths)):
        _emit_logand(lhs, rhs, out, style, clk, has_clock)
    elif _try_reduction_over_index(lhs, rhs, out, bitvec_signals, clk, has_clock):
        pass                                              # OR-of-index-templated arms -> functor rules
    else:
        _emit_bool(lhs, rhs, out, style, clk, has_clock, widths)  # gates, muxes, general bit logic


def _is_packed_bit_extraction(rhs: Expr, widths: dict[str, int]) -> bool:
    """True when rhs is a single-bit extraction from a multi-bit word signal:
    Slice(Ref(name), N, N) or BitSel(Ref(name), N) where widths[name] > 1.
    These map to `assign bit = word[N]` — a packed-port bit-extraction."""
    if isinstance(rhs, Slice) and rhs.hi == rhs.lo and isinstance(rhs.base, Ref):
        return widths.get(rhs.base.name, 1) > 1
    if isinstance(rhs, BitSel) and isinstance(rhs.base, Ref):
        return widths.get(rhs.base.name, 1) > 1
    return False


def _packed_bit_atom(rhs: Expr) -> tuple[str, int]:
    """Return (base_signal_name, bit_index) for a packed-bit-extraction rhs."""
    if isinstance(rhs, Slice):
        return rhs.base.name, rhs.lo          # hi == lo for single-bit slice
    assert isinstance(rhs, BitSel)
    return rhs.base.name, rhs.index


_ATOM_SAFE = re.compile(r'[^a-zA-Z0-9_]')   # characters not safe in a clingo atom name


def _packed_bit_inter_name(base: str, idx: int) -> str:
    """Intermediate atom name for bit idx of base signal. Sanitises functor characters
    (e.g. 'mul_i2(resMul_M1)' → 'mul_i2__resMul_M1__') so the name is a valid clingo atom."""
    safe = _ATOM_SAFE.sub("_", base)
    return f"{safe}_b{idx}"


def _emit_packed_bit_extraction(lhs: str, rhs: Expr, out: _Out,
                                style: str, clk: str, has_clock: bool,
                                widths: dict[str, int] | None = None) -> None:
    """Emit a packed-port bit-extraction as a two-level derivation.

    assign bit_sig = word_port[N]  becomes:

        % intermediate: extract bit N from the packed word (using _emit_bool — SOP+NAF)
        val(word_bN, 1, T) :- val(word, V0, T), V1 = @slc(V0, N, 1), V1 != 0.
        val(word_bN, 0, T) :- time(CK, T), not val(word_bN, 1, T).   % via _emit_bool

        % derived 1-bit signal reads the intermediate (using _emit_bool on Ref(inter))
        val(bit_sig, 1, T) :- val(word_bN, 1, T).
        val(bit_sig, 0, T) :- time(CK, T), not val(bit_sig, 1, T).   % via _emit_bool

    Both zero rules come from _emit_bool's SOP+NAF path — positive-definite, no raw NAF.
    Scenarios can drive `word_bN` directly (without providing the full packed word)
    to control individual bits per T without grounding explosion."""
    base, idx = _packed_bit_atom(rhs)
    inter = _packed_bit_inter_name(base, idx)
    # Step 1 — emit intermediate as a standard combinational bit signal via _emit_bool.
    # _emit_bool handles the SOP ON-set (one rule from the @slc expression) and the
    # NAF zero correctly through _false_bit, keeping positive-definite design rules.
    _emit_bool(inter, rhs, out, style, clk, has_clock, widths)
    # Step 2 — emit lhs derived from the intermediate: a bare Ref is a single-arm SOP.
    # _emit_bool on Ref(inter) emits: val(lhs,1,T) :- val(inter,1,T) + NAF zero.
    _emit_bool(lhs, Ref(inter), out, style, clk, has_clock, widths)



def _cond_branches(sel: Expr, ctx: _Ctx,
                   widths: dict[str, int] | None = None) -> tuple[list[str], list[str]] | None:
    """Split a ternary selector into (true_body, false_body) literal lists. A comparison
    contributes the shared operand reads plus the op / its negation; a 1-bit signal the two
    polarities. Returns None for a selector shape we don't yet split (caller flags it)."""
    if isinstance(sel, BinOp) and sel.op in ("eq", "ne") and (isinstance(sel.left, Tag) or isinstance(sel.right, Tag)):
        ref, tag = (sel.left, sel.right) if isinstance(sel.right, Tag) else (sel.right, sel.left)
        if isinstance(ref, Ref):   # enum tag compare: state == IDLE / state != IDLE
            vs = ctx.fresh()
            match = [f"val({ref.name}, {tag.label}, T)"]
            mismatch = [f"val({ref.name}, {vs}, T)", f"{vs} != {tag.label}"]
            return (match, mismatch) if sel.op == "eq" else (mismatch, match)
    if isinstance(sel, BinOp) and sel.op in _CMP:
        reads, t_lit, f_lit = _cmp_terms(sel, ctx)
        return ([*reads, t_lit], [*reads, f_lit])
    if isinstance(sel, Ref):
        # Fix 94: only a 1-BIT read splits into polarity literals. A wider one means `!= 0`
        # in every boolean context SV puts it in, so it falls through to the word test --
        # `val(s, 1, T)` would test equality with ONE and leave `s = 2` unhandled.
        if widths is None or widths.get(sel.name, 1) <= 1:
            return ([f"val({sel.name}, 1, T)"], [f"val({sel.name}, 0, T)"])
        return None
    return None


def _emit_lane_cond(lhs: str, rhs: Cond, shapes: dict[str, Shape], out: _Out, loc: object,
                    widths: dict[str, int] | None, lane_dims: dict[str, int] | None,
                    lane_dom) -> None:
    """A ternary on a LANE target, per lane: `val(y(I), A, T) :- <sel true>, <arm a read at lane I>`
    and the mirror for the else-arm. The selector is a 1-bit signal (a per-lane one reads `s(I)`, a
    scalar one is a broadcast `s`), a comparison over lane-aware operands, or an enum tag compare;
    the arms are read lane-aware (`_word_body(lane_ctx=True)`); the loop's range comes from
    ``lane_dom`` like every other lane rule."""
    lh = _lane(lhs, lane_dims)
    ctx = _Ctx(out.used)
    sel = rhs.sel
    if isinstance(sel, Ref) and (widths is None or widths.get(sel.name, 1) <= 1 or shapes.get(sel.name) == Shape.INDEXED):
        st = _lane(sel.name, lane_dims) if shapes.get(sel.name) == Shape.INDEXED else sel.name
        sel_t, sel_f = [f"val({st}, 1, T)"], [f"val({st}, 0, T)"]
    elif isinstance(sel, ElemSel) and _elemsel_lane_idx(sel) is not None:
        st = _lane_term(sel.base, _elemsel_lane_idx(sel))          # a neighbouring-lane select `s[i-1] ? ..`
        sel_t, sel_f = [f"val({st}, 1, T)"], [f"val({st}, 0, T)"]
    elif isinstance(sel, BinOp) and sel.op in _CMP and not (isinstance(sel.left, Tag) or isinstance(sel.right, Tag)):
        lb, vl = _lane_word(sel.left, shapes, ctx, lane_dims)
        rb, vr = _lane_word(sel.right, shapes, ctx, lane_dims)
        t_lit, f_lit = _cmp_lits(vl, vr, sel, ctx.used)
        sel_t, sel_f = [*lb, *rb, t_lit], [*lb, *rb, f_lit]
    else:
        branches = _cond_branches(sel, ctx, widths)                 # enum tag compare, or unsupported
        if branches is None:
            out.problem(loc, f"ternary with unsupported selector for lane {lhs}")
            return
        sel_t, sel_f = branches
    ab, av = _word_body(rhs.a, "T", ctx, shapes, lane_dims, lane_ctx=True)
    bb, bv = _word_body(rhs.b, "T", ctx, shapes, lane_dims, lane_ctx=True)
    out.used |= ctx.used
    body_t, body_f = [*sel_t, *ab], [*sel_f, *bb]
    out.rule(f"val({lh}, {av}, T)", [*lane_dom(body_t), *body_t])
    out.rule(f"val({lh}, {bv}, T)", [*lane_dom(body_f), *body_f])


def _emit_cond(lhs: str, rhs: Cond, shapes: dict[str, Shape], out: _Out, loc: object,
               widths: dict[str, int] | None = None,
               lane_dims: dict[str, int] | None = None) -> None:
    bit = shapes.get(lhs) == Shape.BIT
    ctx = _Ctx(out.used)
    branches = _cond_branches(rhs.sel, ctx, widths)
    if branches is None:
        out.problem(loc, f"ternary with unsupported selector for {lhs}")
        return
    sel_t, sel_f = branches
    # Each ARM is an assignment to `lhs` and must be TRUNCATED to the destination width like
    # any other (Fix 91). Reading the arm with a bare `_word_body` stored the arm's full value:
    # `assign y[3:0] = s ? a8 : b8;` put 255 on a 4-bit signal -- the Fix-48 silent-wrong class,
    # and inconsistent with the very same SV written as `if (s) y = a; else y = b;`, which the
    # procedural path already truncated via `_assign_word`. A 1-bit destination is unaffected
    # (`_bit_read`'s values are masked by construction).
    lhs_w = (widths or {}).get(lhs)
    read = ((lambda e: _bit_read(e, "T", ctx)) if bit else
            (lambda e: _assign_word(e, "T", ctx, shapes, lane_dims, widths, lhs_w)))
    def arm(guards: list[str], e: Expr) -> None:
        # An `x` ARM of a continuous-assign ternary -- `assign y = valid ? v : 'x;`, how a reference
        # says an output means nothing when it is not valid. The design constrains NOTHING here, so
        # no value rule is emitted (a value would be invented) and only WHERE is declared; the
        # boundary companion turns that into the guarded choice, leaving the design layer
        # positive-definite (hard rule 3). The same statement the register-branch path makes for
        # `default: y = 'x;`. Without this the arm reached `_word_body`/`_bit_read` and the whole
        # assign was REFUSED, taking the valid arm -- the design's actual content -- down with it.
        if isinstance(e, XVal):
            out.rule(f"dontcare_at({lhs}, T)", _bind_t(list(guards)))
            out.dontcare.append((lhs, (widths or {}).get(lhs, 1), loc))
            return
        b, v = read(e)
        out.rule(f"val({lhs}, {v}, T)", [*guards, *b])

    arm(sel_t, rhs.a)   # condition true  -> then-value
    arm(sel_f, rhs.b)   # condition false -> else-value
    out.used |= ctx.used


def _emit_edge(ed, out: _Out) -> None:
    """`$rose(x)` / `$fell(x)` -- the sampled-value edge functions.

    The value at `T+1` is a function of the sampled signal at TWO adjacent ticks, so all four
    combinations are enumerated POSITIVELY (hard rule 3: design rules stay positive-definite;
    no negation-as-failure here). The four are disjoint and exhaustive over a 1-bit signal's
    values, so exactly one fires at every tick -- the same argument the minterm path makes.

    At `T = 0` there is no previous sample and the signal is deliberately UNBOUND: that is
    SystemVerilog's own answer (the previous sampled value is `x`). The partiality is
    announced, not hidden (TRANSLATION_SPEC S3.3), because a property over an unbound signal
    passes vacuously."""
    s, q, ck = ed.sig, ed.lhs, ed.clock
    out.construct(_prov(ed.loc, f"${'rose' if ed.rising else 'fell'}({s})"))
    hi, lo = (1, 0) if ed.rising else (0, 1)     # the (T+1, T) pair that makes the edge
    out.rule(f"val({q}, 1, T+1)",
             [f"time({ck}, T)", "T < k", f"val({s}, {lo}, T)", f"val({s}, {hi}, T+1)"])
    for prev, now in ((0, 0), (1, 1), (hi, lo)):
        out.rule(f"val({q}, 0, T+1)",
                 [f"time({ck}, T)", "T < k", f"val({s}, {prev}, T)", f"val({s}, {now}, T+1)"])
    out.warning(ed.loc, f"{q} is UNBOUND at T=0: ${'rose' if ed.rising else 'fell'}({s}) has "
                        f"no previous sample there (SV reads it as x)")


def _emit_tag_compare(lhs: str, rhs: BinOp, out: _Out) -> None:
    """A scalar bit from an enum comparison: state == IDLE / state != IDLE. The match is a
    positive read val(state, idle, T); the mismatch reads any other tag (S != idle)."""
    ref, tag = (rhs.left, rhs.right) if isinstance(rhs.right, Tag) else (rhs.right, rhs.left)
    sig, lab = ref.name, tag.label
    match = [f"val({sig}, {lab}, T)"]
    mismatch = [f"val({sig}, S, T)", f"S != {lab}"]
    eq = rhs.op == "eq"
    out.rule(f"val({lhs}, 1, T)", match if eq else mismatch)
    out.rule(f"val({lhs}, 0, T)", mismatch if eq else match)


def _bind_t(body: list[str]) -> list[str]:
    """A combinational wire is valid at EVERY time step of ANY clock. If a rule body binds T via no
    `val` read (a CONSTANT, e.g. `assign c = 1'b1` / `assign w = 8'd5`), prepend the clock-AGNOSTIC
    ``time(_, T)`` so T is bound (the harness supplies `time(clk, 0..k)`) instead of an unsafe free
    variable. Combinational rules relate values at the SAME T (head and body at T -- never T+1).
    Bodies that already read a signal bind T themselves -> untouched."""
    return body if any(lit.startswith("val(") for lit in body) else ["time(_, T)", *body]


def _false_bit(lhs: str, false_rules: list[list[str]], domain: list[str],
               out: _Out, style: str, clk: str, has_clock: bool) -> None:
    """Emit the 0-polarity of a bit signal: v1 = explicit positive rules; v2 = NAF complement.

    v2 needs the rule's variables bound for safety. For a scalar bit the natural domain is
    ``time(clk,T)`` (or the input reads when clockless).
    """
    if style == "v2":
        # scalar clocked: time(clk,T) binds T; a scalar COMBINATIONAL constant (empty domain)
        # binds T via the clock-agnostic time(_, T).
        guard = [f"time({clk}, T)"] if has_clock else (domain or ["time(_, T)"])
        out.rule(f"val({lhs}, 0, T)", [*guard, f"not val({lhs}, 1, T)"])
    else:
        for body in false_rules:
            out.rule(f"val({lhs}, 0, T)", body)


def _reads(literals: list[str]) -> list[str]:
    """The val(...) reads among body literals (they bind T); drop @func assignments."""
    return [lit for lit in literals if lit.startswith("val(")]


_ORDER_CMP = ("lt", "le", "gt", "ge")  # ordering ops differ signed vs unsigned (eq/ne are bit-identical)


def _signed_wrap(v: str, b: BinOp, used: set[str]) -> str:
    """For a SIGNED ordering compare, interpret the stored bit pattern as two's complement
    (@signed) before the native clingo compare. eq/ne and unsigned compares are bit-identical
    on the stored value -> returned unchanged. ``v`` must already be a computed value term."""
    if b.signed and b.op in _ORDER_CMP:
        used.add("signed")
        return f"@signed({v}, {b.opw or b.width})"
    return v


def _cmp_read(e: Expr, b: BinOp, ctx: _Ctx) -> tuple[list[str], str]:
    """Lower a comparison operand. For a SIGNED ordering compare, return the two's-complement
    signed interpretation: peel a sign-extension and read at the SOURCE width, since
    @signed(@sext(v,fw,tw),tw) == @signed(v,fw) -- this avoids a wide (>31-bit) sext intermediate
    that clingo's 32-bit Number cannot hold (e.g. the ubiquitous `x < 0`, where 0 is 32-bit)."""
    if b.signed and b.op in _ORDER_CMP and isinstance(e, SExt):
        lb, vb = _word_body(e.operand, "T", ctx)
        ctx.used.add("signed")
        return lb, f"@signed({vb}, {e.from_w})"
    lb, vb = _word_body(e, "T", ctx)
    return lb, _signed_wrap(vb, b, ctx.used)


def _cmp_lits(vl: str, vr: str, b: BinOp, used: set[str]) -> tuple[str, str]:
    """(true_literal, false_literal) from already-read operand VALUE terms `vl`,`vr`. WIDE ordering
    (op in lt/le/gt/ge, operand width >= _WIDE_BITS) routes through the 3-way @wcmp(a,b,w,signed):
    a wide value is a canonical decimal STRING, so native `<` would compare LEXICOGRAPHICALLY
    (`"9000000000" > "10000000000"`) and the `@signed` wrap would overflow clingo's 32-bit int. Narrow
    applies the two's-complement @signed wrap + native compare; eq/ne stay native at any width. THE single
    source of truth for compare routing -- both _cmp_terms (scalar) and _emit_lane_and (per-lane) call it."""
    op, neg = _CMP_OP[b.op], _NEG_CMP[_CMP_OP[b.op]]
    w = b.opw or b.width
    if b.op in _ORDER_CMP and isinstance(w, int) and w >= _WIDE_BITS:
        used.add("wcmp")
        cmp = f"@wcmp({vl}, {vr}, {w}, {1 if b.signed else 0})"
        return f"{cmp} {op} 0", f"{cmp} {neg} 0"
    vl, vr = _signed_wrap(vl, b, used), _signed_wrap(vr, b, used)
    return f"{vl} {op} {vr}", f"{vl} {neg} {vr}"


def _cmp_terms(b: BinOp, ctx: _Ctx) -> tuple[list[str], str, str]:
    """(reads, true_literal, false_literal) for a comparison BinOp. The wide-vs-narrow routing lives in
    _cmp_lits (shared with the per-lane path). The narrow signed path additionally peels a sign-extended
    operand (read at source width via _cmp_read) to avoid a wide sext intermediate; eq/ne stay native."""
    w = b.opw or b.width
    if b.op in _ORDER_CMP and isinstance(w, int) and w >= _WIDE_BITS:
        lb, vl = _word_body(b.left, "T", ctx)
        rb, vr = _word_body(b.right, "T", ctx)
        t, f = _cmp_lits(vl, vr, b, ctx.used)
        return [*lb, *rb], t, f
    lb, vl = _cmp_read(b.left, b, ctx)
    rb, vr = _cmp_read(b.right, b, ctx)
    op, neg = _CMP_OP[b.op], _NEG_CMP[_CMP_OP[b.op]]
    return [*lb, *rb], f"{vl} {op} {vr}", f"{vl} {neg} {vr}"


def _emit_compare(lhs: str, rhs: BinOp, out: _Out, style: str, clk: str, has_clock: bool) -> None:
    """word OP word -> true rule + false (v1: explicit; v2: excluded-middle)."""
    ctx = _Ctx(out.used)
    reads, t_lit, f_lit = _cmp_terms(rhs, ctx)
    out.used |= ctx.used
    out.rule(f"val({lhs}, 1, T)", [*reads, t_lit])
    _false_bit(lhs, [[*reads, f_lit]], _reads(reads), out, style, clk, has_clock)


def _emit_logand(lhs: str, rhs: BinOp, out: _Out, style: str, clk: str, has_clock: bool) -> None:
    """1-bit a && b -> true rule + false (v1: two positive rules; v2: excluded-middle)."""
    an, ap = _bit_lit(rhs.left)
    bn, bp = _bit_lit(rhs.right)
    out.rule(f"val({lhs}, 1, T)", [f"val({an}, {ap}, T)", f"val({bn}, {bp}, T)"])
    # clockless-domain binding: a and b present at T (any value)
    domain = [f"val({an}, _, T)", f"val({bn}, _, T)"]
    _false_bit(lhs, [[f"val({an}, {1 - ap}, T)"], [f"val({bn}, {1 - bp}, T)"]],
               domain, out, style, clk, has_clock)


_NEG_CMP = {"=": "!=", "!=": "=", "<": ">=", ">=": "<", ">": "<=", "<=": ">"}


def _flatten_logand(e: Expr) -> list[Expr]:
    """Flatten a chain of && into its conjuncts -- and of 1-bit bitwise & the same way:
    at one bit the two operators are the same function, and RTL written in the bitwise
    style (`amatch[i] = joinable[i] & (addr[i] == req)`) must reach the same CAM-style
    conjunct lowering the &&-spelling reaches (found by the regeneration run's
    human-shaped print, 2026-08-31)."""
    if isinstance(e, BinOp) and (e.op == "logand"
                                 or (e.op == "and" and getattr(e, "width", 0) == 1)):
        return _flatten_logand(e.left) + _flatten_logand(e.right)
    return [e]


def _lane_operand_base(e: Expr) -> Expr:
    """Peel slice/bit-select layers to the underlying operand (e.g. opcode[i][2:0] -> opcode[i])."""
    while isinstance(e, Slice | BitSel):
        e = e.base
    return e


def _is_lane_operand(e: Expr) -> bool:
    """An operand we can read per-lane in a conjunct: a ref/const, or a slice/bit-select of one
    (e.g. opcode[i][2:0] -- a field of a per-lane word, ubiquitous in opcode classification)."""
    return isinstance(_lane_operand_base(e), Ref | Const)


def _elemsel_lane_idx(e: Expr) -> str | None:
    """The lane-index TEXT of a lane read `x[i]` / `x[i-1]` / `x[i+1]` / `x[3]` (an ElemSel whose index
    is the loop variable, the loop variable offset by a constant, or a constant): `I`, `I-1`, `I+1`,
    `3`. None for any other index (a runtime index is not a per-lane conjunct)."""
    if not isinstance(e, ElemSel) or getattr(e, "more", ()):
        return None
    ix = e.index
    if isinstance(ix, LaneIdx):
        return _LANEVARS[ix.pos]
    if isinstance(ix, Const):
        return str(ix.value)
    if (isinstance(ix, BinOp) and ix.op in ("add", "sub")
            and isinstance(ix.left, LaneIdx) and isinstance(ix.right, Const)):
        return f"{_LANEVARS[ix.left.pos]}{'+' if ix.op == 'add' else '-'}{ix.right.value}"
    return None


def _is_lane_conjunct(e: Expr) -> bool:
    """A conjunct we can emit per-lane: a bit ref (or a neighbouring-lane bit read `x[i-1]`), its
    negation, or a compare of per-lane words (refs/consts and slices/bit-selects of them)."""
    if isinstance(e, Ref) or _elemsel_lane_idx(e) is not None:
        return True
    if isinstance(e, UnOp) and e.op in ("lnot", "not") and (isinstance(e.operand, Ref)
                                                    or _elemsel_lane_idx(e.operand) is not None):
        return True
    if isinstance(e, BinOp) and e.op in _CMP:
        return _is_lane_operand(e.left) and _is_lane_operand(e.right)
    return False


def _lane_word(e: Expr, shapes: dict[str, Shape], ctx: _Ctx,
               lane_dims: dict[str, int] | None) -> tuple[list[str], str]:
    """Read a word value, lane-aware: an INDEXED ref reads val(s, <I,J,...>, V, T) over its lane
    dims; a scalar reads val(s, V, T) (no lane index -- a broadcast shared across lanes)."""
    if isinstance(e, Const):
        return [], _const_lit(e.value)
    if isinstance(e, Ref):
        v = ctx.fresh()
        if shapes.get(e.name) == Shape.INDEXED:
            return [f"val({_lane(e.name, lane_dims)}, {v}, T)"], v
        return [f"val({e.name}, {v}, T)"], v
    # a slice / bit-select (or other word expr) of a per-lane word -> lane-aware via _word_body
    return _word_body(e, "T", ctx, shapes, lane_dims, lane_ctx=True)  # lane datapath: head binds I


def _emit_lane_and(lhs: str, conjuncts: list[Expr], shapes: dict[str, Shape],
                   out: _Out, style: str, lane_dims: dict[str, int] | None,
                   lane_dom=None) -> None:
    """Per-lane AND of bit tests and comparisons, e.g. valid[i][j] && (entry[i][j] == key).
    on-set: every conjunct true. off-set (v1): one rule per conjunct negated. Each signal carries
    its own lane-index list (I / I,J / ...); broadcast scalars carry none. A conjunct may be a
    NEIGHBOURING-lane bit read (`!any[i-1]`, a priority chain): `val(any(I-1), 0, T)`.

    ``lane_dom(body) -> literals`` is the caller's range decision (`_lane_dom`): the LOOP's index
    set as a domain literal when the generate covers only part of the target's lanes. This path
    used to skip it -- `for (i = 1; ..) y[i] = (a[i] == 1) && v[i]` was rolled over EVERY lane,
    lane 0 included, beside `assign y[0] = b0`: two values, UNSAT under t34, "no counterexample",
    exit 0 (the L4 hole on the boolean-conjunct path; the word-op and register paths had it closed)."""
    on_body: list[str] = []
    off_rules: list[list[str]] = []
    domain: list[str] = []  # val(s, <I,J,..>, _, T) for each indexed operand -> binds every lane var
    rng = lane_dom if lane_dom is not None else (lambda body: [])

    def note_indexed(name: str) -> None:
        if shapes.get(name) == Shape.INDEXED:
            lit = f"val({_lane(name, lane_dims)}, _, T)"
            if lit not in domain:
                domain.append(lit)

    def bit_atom(name: str, v: int) -> str:
        """A 1-bit test on a conjunct operand: functor lane atom if indexed, scalar bitpos 0 if not."""
        if shapes.get(name) == Shape.INDEXED:
            return f"val({_lane(name, lane_dims)}, {v}, T)"
        return f"val({name}, {v}, T)"

    for c in conjuncts:
        if isinstance(c, Ref | UnOp):
            opnd = c.operand if isinstance(c, UnOp) else c
            true_v = 0 if isinstance(c, UnOp) else 1
            if isinstance(opnd, ElemSel):                    # a lane read at an explicit index: x(I-1) / x(3)
                lt = _lane_term(opnd.base, _elemsel_lane_idx(opnd))
                on_body.append(f"val({lt}, {true_v}, T)")
                off_rules.append([f"val({lt}, {1 - true_v}, T)"])
                continue
            name = opnd.name
            on_body.append(bit_atom(name, true_v))
            off_rules.append([bit_atom(name, 1 - true_v)])
            note_indexed(name)
        else:  # BinOp compare
            ctx = _Ctx(out.used)
            lb, vl = _lane_word(c.left, shapes, ctx, lane_dims)
            rb, vr = _lane_word(c.right, shapes, ctx, lane_dims)
            t_lit, f_lit = _cmp_lits(vl, vr, c, ctx.used)   # wide ordering -> @wcmp (shared with _cmp_terms)
            out.used |= ctx.used
            on_body.extend([*lb, *rb, t_lit])
            off_rules.append([*lb, *rb, f_lit])
            for operand in (c.left, c.right):
                base = _lane_operand_base(operand)        # peel opcode[i][2:0] -> opcode[i]
                if isinstance(base, Ref):
                    note_indexed(base.name)

    lh = _lane(lhs, lane_dims)
    lanevars = list(_LANEVARS[: (lane_dims or {}).get(lhs, 1)])
    out.rule(f"val({lh}, 1, T)", [*rng(on_body), *on_body])
    if style == "v2":
        body = [*domain, f"not val({lh}, 1, T)"]
        out.rule(f"val({lh}, 0, T)", [*rng(body), *body])
    else:
        for body in off_rules:
            # every lane var must be bound; a conjunct that doesn't read all of them needs the domain.
            # A var now lives inside a functor (q(I)), so test for it as a whole token, not ", I,".
            txt = " ".join(body)
            safe = body if all(re.search(rf"\b{v}\b", txt) for v in lanevars) else [*domain, *body]
            out.rule(f"val({lh}, 0, T)", [*rng(safe), *safe])


def _emit_reduce(lhs: str, rhs: UnOp, shapes: dict[str, Shape], widths: dict[str, int],
                 out: _Out, loc: object, lane_dims: dict[str, int] | None = None,
                 lane_elem_w: dict[str, int] | None = None,
                 packed_dims: dict[str, tuple] | None = None) -> None:
    """Reduction to a scalar bit. Over an INDEXED vector: reduce over ALL its LANES (a positive
    existential + its complement) -- N lane dimensions, not just one. Over a WORD/expression
    operand: reduce over its BITS -- |x = (x != 0), &x = (x == all-ones), ^x = parity(x), and
    ~|/~&/~^."""
    op = rhs.op
    operand = rhs.operand

    # --- reduction over the LANES (all N dims) of an indexed vector ---
    if isinstance(operand, Ref) and shapes.get(operand.name) == Shape.INDEXED:
        name = operand.name
        # parity (^/~^) cannot be done by an existential over unbounded lanes -- but when the lanes
        # assemble into a coherent word (the bridge), ^a == parity of that whole word (XOR of all its
        # bits, regardless of per-lane width). Fall through to the word-bits path on the word atom.
        if op in ("rxor", "rxnor") and _word_bridged(name, lane_dims, lane_elem_w, widths) is not None:
            operand = Ref(name)                                  # read val(name, V, T) -- the word form
        else:
            lane = _lane(name, lane_dims)                            # name(I) / name(I,J) ...
            dims = (lane_dims or {}).get(name, 1)
            dom = f"val({_lane_term(name, ', '.join(['_'] * dims))}, _, T)"  # any lane(s) + any value
            if op not in ("ror", "rnor", "rand", "rnand"):
                out.problem(loc, f"lane reduction {op} (parity) for {lhs}")
                return
            # `|lanes` is a positive existential over the lane index; `&lanes` is the same
            # existential over the COMPLEMENTARY lane value (some lane is clear), which is why
            # the two differ only in which head value carries it (Ops.lane_reductions_denote).
            ex = 1 if op in ("ror", "rnor") else 0        # the lane value the existential seeks
            on, off = {"ror": ("1", "0"), "rnor": ("0", "1"),
                       "rand": ("0", "1"), "rnand": ("1", "0")}[op]
            out.rule(f"val({lhs}, {on}, T)", [f"val({lane}, {ex}, T)"])
            # The complement is written with NEGATION AS FAILURE -- the one place a design rule
            # does. The positive spelling (every lane reads the other value) computes exactly the
            # same function (Ops.naf_eq_positive_complement) and grounds to the same size, since
            # `val(name(_),_,T)` is a variable that already fans out over every lane. It was
            # measured and rejected on LEGIBILITY: at 64 lanes it is one 4 KB rule whose meaning
            # -- "no lane matched" -- is buried in 64 near-identical atoms, and reading the
            # emitted model is a primary workflow here.
            #
            # What makes the exception safe is not that it is small: it is that the negation is
            # STRATIFIED (`lhs`'s on-rule does not mention `lhs`), so the program stays tight and
            # Fages still gives completion = stable models. That is checked, not assumed --
            # `_check_stratified` below rejects any negative edge that closes a cycle.
            out.rule(f"val({lhs}, {off}, T)", [dom, f"not val({lhs}, {on}, T)"])
            return

    # --- reduction over the BITS of a word / expression operand ---
    ctx = _Ctx(out.used)
    xb, vx = _word_body(operand, "T", ctx)
    out.used |= ctx.used
    if op in ("rxor", "rxnor"):         # parity
        # The width literal MUST be the operand's real width: the ASP @parity ignores it
        # (stored values are already masked — proven, proofs/lean Wf layer), but the SMT
        # completion route reads it to build the bvxor bit fan-out; the old literal 1
        # made the SMT lowering "extract bit 0", silently wrong for words (Fix 43).
        w = widths.get(operand.name) if isinstance(operand, Ref) else getattr(operand, "width", None)
        if w is None:
            out.problem(loc, f"reduction {op}: cannot determine operand width for {lhs}")
            return
        out.used.add("parity")
        t, f = ("1", "0") if op == "rxor" else ("0", "1")
        out.rule(f"val({lhs}, {t}, T)", [*xb, f"@parity({vx}, {w}) = 1"])
        out.rule(f"val({lhs}, {f}, T)", [*xb, f"@parity({vx}, {w}) = 0"])
        return
    if op in ("ror", "rnor"):           # x != 0  /  x == 0
        on, off = ("1", "0") if op == "ror" else ("0", "1")
        out.rule(f"val({lhs}, {on}, T)", [*xb, f"{vx} != 0"])
        out.rule(f"val({lhs}, {off}, T)", [*xb, f"{vx} = 0"])
        return
    if op in ("rand", "rnand"):         # x == all-ones (needs the operand width)
        w = widths.get(operand.name) if isinstance(operand, Ref) else getattr(operand, "width", None)
        if w is None:
            out.problem(loc, f"reduction {op}: cannot determine operand width for {lhs}")
            return
        allones = _const_lit((1 << w) - 1)   # wide all-ones (>= 2^31) -> canonical String literal
        on, off = ("1", "0") if op == "rand" else ("0", "1")
        out.rule(f"val({lhs}, {on}, T)", [*xb, f"{vx} = {allones}"])
        out.rule(f"val({lhs}, {off}, T)", [*xb, f"{vx} != {allones}"])
        return
    out.problem(loc, f"reduction {op} for {lhs}")


# --------------------------------------------------------------------------
# encoded-select mux (out = arms[sel]) - one rule per select arm
# --------------------------------------------------------------------------
def _emit_inferred_latch(item, out: _Out, default_init: bool = False) -> None:
    """An INFERRED latch: an `always_comb` target whose bits are not all driven on every path.

    SystemVerilog says the undriven bits RETAIN their value. Rather than refuse the design, it
    is translated with latch semantics (proven in `Latch.lean`) and reported LOUDLY -- the same
    policy as the incomplete selector (D4) and the combinational loop (T2).

        % INFERRED LATCH: bit(s) [7:4] of y are not assigned on every path -- they HOLD.
        val(y, Vn, T+1) :- val(y, Vo, T), T < k, …, Vn = (Vo & KEEP) | <driven>.

    The hold reads the PREVIOUS instant, so this crosses a time index and is NOT a
    combinational loop -- the tightness detector correctly leaves it alone.

    **No `val(y, 0, 0)` (F4).** This used to emit one, with the comment that it "takes the same
    power-on default a register without reset gets" -- but an unreset register gets a CHOICE in
    `__xinit.lp`, so that comment described an inconsistency, not a convention. An inferred
    latch has no reset and holds, so it powers on unknown exactly like one, and its choice now
    lives in the companion with every other element's. `default_init` survives for the
    reset-snapshot route alone (see `emit`)."""
    out.construct(_prov(item.loc, f"latch {item.lhs} (INFERRED -- see the problem report)"))
    out.comment(f"INFERRED LATCH: bit(s) [{item.bits}] of {item.lhs} are not assigned on every "
                f"path through the always_comb, so they RETAIN their value. This is a LATCH.")
    out.comment(f"  Add a default (`{item.lhs} = '0;`) in the block if that was not intended.")
    if default_init:
        out.rule(f"val({item.lhs}, 0, 0)")     # reset-snapshot only: a concrete start to solve from
    # The DRIVEN bits are combinational -- they must read their inputs at the SAME instant as
    # the head (`T+1`), not at `T`. Only the HELD bits carry from the previous instant. Reading
    # everything at `T` would give the driven bits a one-cycle delay, which is precisely the
    # flop-for-latch error `Latch.flop_is_latch_delayed` proves wrong.
    #
    # A GUARDED slice contributes one rule per combination of its guards, each gated at `T+1`
    # (destination-gating: exactly one applies, so the schema stays single-valued). Without the
    # split the `guard ? val : lhs[region]` conditional is hoisted into a temp that reads `lhs`
    # at the head's own instant -- a combinational loop (Fix 83).
    for guards, value in (item.variants or (((), item.value),)):
        ctx = _Ctx(out.used)
        body, vt = _word_body(value, "T+1", ctx)
        out.used |= ctx.used
        # ...and the ONLY reads of the target itself are the prior value (the RMW base and each
        # held region), so those move back to `T`.
        body = [re.sub(rf"^val\({re.escape(item.lhs)}, (\w+), T\+1\)$",
                       rf"val({item.lhs}, \1, T)", b) for b in body]
        glits = [f"val({g}, {p}, T+1)" for g, p in guards]
        out.rule(f"val({item.lhs}, {vt}, T+1)", ["T < k", *glits, *body])


def _emit_latch(item, out: _Out) -> None:
    """A LEVEL-SENSITIVE latch: transparent while enabled, holding otherwise.

        val(q, V, T)   :- val(en, 1, T), val(d, V, T).      -- transparent, SAME time index
        val(q, V, T+1) :- val(en, 0, T+1), val(q, V, T).    -- opaque, hold across the boundary

    Both guards read `en` at the instant the head is derived (DESTINATION-gating), so exactly
    one applies at every instant, with no hypothesis relating the enable to a clock -- the same
    argument that makes the async-reset flop single-valued. Proven in `Latch.lean`
    (`latch_exactly_one`, `transparent_is_immediate`, `opaque_holds`).

    The transparent rule is a genuine SAME-TIME dependency `d -> q`, which is what a transparent
    latch is. The tightness detector therefore sees it, so a latch inside a combinational loop
    is reported -- a real hazard that the old flop modelling hid."""
    if getattr(item, "hold_only", False):
        # INFERRED latch: the transparent half is the block's own combinational rules, which are
        # already emitted -- `val(y, V, T) :- val(s, 1, T), val(a, V, T).` IS the driven case.
        # Only the retention is missing, and it must read the PRIOR instant, which is what keeps
        # it out of the combinational dependency graph.
        out.construct(_prov(item.loc, f"latch {item.q} (INFERRED -- enable {item.en})"))
        out.comment(f"INFERRED LATCH: {item.q} is not assigned on every path through the "
                    f"always_comb, so it RETAINS its value when `{item.en}` is low. This is a "
                    f"LATCH, not a wire.")
        out.comment(f"  Add a default (`{item.q} = '0;`) in the block if that was not intended.")
        out.rule(f"val({item.q}, V, T+1)", [f"val({item.en}, 0, T+1)", f"val({item.q}, V, T)"])
        return
    out.construct(_prov(item.loc, f"latch {item.q} (level-sensitive, {item.inst})"))
    out.rule(f"val({item.q}, V, T)", [f"val({item.en}, 1, T)", f"val({item.d}, V, T)"])
    out.rule(f"val({item.q}, V, T+1)", [f"val({item.en}, 0, T+1)", f"val({item.q}, V, T)"])


def _emit_mux(item, out: _Out, widths: dict | None = None) -> None:
    out.construct(_prov(item.loc, f"mux {item.out}"))
    # LOUD MESSAGE when the arms do not cover the selector (D4). One rule per arm, guarded by
    # `val(sel, i, T)`, is total only if every representable selector value has an arm -- the
    # condition `2 ^ selWidth <= arms`, proven as `mux_total_iff`. A MUX3 on a 2-bit select
    # (4 > 3) leaves the output UNBOUND at sel = 3, so a property over it passes VACUOUSLY
    # there. The cell defines no behaviour at that value either, so we do NOT invent one: the
    # translation is unchanged and the gap is announced instead of being left silent.
    _sw = (widths or {}).get(item.sel, 1) or 1
    _onehot = getattr(item, "onehot", False)
    _covered = len(item.arms) + 1 if _onehot else len(item.arms)   # one-hot also covers sel = 0
    if _sw <= 16 and (1 << _sw) > _covered:
        out.warning(item.loc,
                    f"mux {item.out}: selector `{item.sel}` is {_sw} bits ({1 << _sw} values) "
                    f"but only {_covered} are covered"
                    + (" (the one-hot codes plus all-zero)" if _onehot else
                       f" ({len(item.arms)} arms)")
                    + " -- the output is UNBOUND for the rest, so a property over it "
                      "passes VACUOUSLY on any trace reaching them")
    for i, arm in enumerate(item.arms):
        ctx = _Ctx(out.used)
        lits, v = (_word_body(arm, "T", ctx) if _onehot else _bit_read(arm, "T", ctx))
        out.used |= ctx.used
        code = (1 << i) if _onehot else i          # one-hot: bit i set, i.e. the value 2**i
        out.rule(f"val({item.out}, {v}, T)", [f"val({item.sel}, {code}, T)", *lits])
    if _onehot:                                    # defensive all-zero select -> 0
        out.rule(f"val({item.out}, 0, T)", [f"val({item.sel}, 0, T)"])


# --------------------------------------------------------------------------
# sequential (Group 2) - async reset destination-gated
# --------------------------------------------------------------------------
def _rst_lits(reset, t: str) -> tuple[str, str]:
    """Return (asserted_literal_at_t, deasserted_literal_at_t) for the reset signal."""
    asserted = 0 if reset.active == "low" else 1
    return (f"val({reset.signal}, {asserted}, {t})",
            f"val({reset.signal}, {1 - asserted}, {t})")


def _bit_read(e: Expr, t: str, ctx: _Ctx) -> tuple[list[str], str]:
    """Read a 1-bit value: Ref -> val(s,V,t); Const -> literal; a 1-bit Slice/BitSel of a word
    (e.g. `clkenDup_D4[0]`) -> read the word and extract the bit via _word_body."""
    if isinstance(e, Const):
        return [], str(e.value & 1)
    if isinstance(e, Ref):
        v = ctx.fresh()
        return [f"val({e.name}, {v}, {t})"], v
    if isinstance(e, (Slice, BitSel)):
        return _word_body(e, t, ctx)
    # ANY OTHER EXPRESSION IS A WIDTH-1 WORD. `assign x = c ? a : b;` on a 1-bit wire is
    # ordinary SystemVerilog, and a compound ARM (`(q & a) | b`) reached here and was refused
    # -- "use a named wire" -- so five phase flops of a one-hot FSM could be printed and not
    # translated back, and the round trip reported them all as dark reads. The frontend
    # already hoists a compound 1-bit value into a named wire on the CLOCKED register path
    # (`_stmts._hoist_bit`, twice); the mux/comb path beside it never got the same treatment,
    # which is the shape this translator keeps paying for -- a fix applied to the path in
    # front of it and not the one beside it.
    #
    # Delegating is better than hoisting here, and cheaper: `_word_body` is the general
    # expression lowering, this function ALREADY delegates Slice and BitSel to it, and the
    # comment two hundred lines down says the same thing outright -- "a 1-bit reg is a
    # width-1 word". Nothing is invented; the arm is lowered exactly as any other expression.
    # (F29, 2026-09-02, from the second block's rung 7.)
    return _word_body(e, t, ctx)


def _neg_match_lits(neg_matches: tuple, ctx: _Ctx, term=None) -> list[str]:
    """A case `default` arm: read each selector once and require it != every explicit arm value.
    ``term(sig)`` renders the selector's atom -- lane-aware in a lane rule (see `_emit_seq`)."""
    bysig: dict[str, list[str]] = {}
    for sig, v in neg_matches:
        bysig.setdefault(sig, []).append(v)
    lits: list[str] = []
    for sig, vals in bysig.items():
        x = ctx.fresh()
        lits.append(f"val({term(sig) if term else sig}, {x}, T)")
        lits.extend(f"{x} != {v}" for v in vals)
    return lits


def _emit_seq(item: SeqItem, out: _Out, shapes: dict[str, Shape],
              lane_dims: dict[str, int] | None = None, widths: dict[str, int] | None = None,
              bitvec_signals: frozenset[str] = frozenset(),
              lane_elem_w: dict[str, int] | None = None) -> None:
    comb = item.combinational
    out.construct(_prov(item.loc, f"{'comb' if comb else 'reg'} {item.reg}"))
    clk = item.clock
    shape = shapes.get(item.reg)
    bit = shape == Shape.BIT
    idx = _idx(item.reg, lane_dims) if shape == Shape.INDEXED else None  # lane reg/comb (for-loop)
    reg = item.reg
    # `y[i+1] <= ..`: the head (and its own-lane hold read) is lane I+off; the domain literal and
    # every operand read still use the loop variable I.
    hidx = idx
    if idx == "I" and getattr(item, "lane_off", 0):
        _o = item.lane_off
        hidx = f"I{'+' if _o > 0 else '-'}{abs(_o)}"
    nxt = "T" if comb else "T+1"   # always_comb is same-cycle; always_ff is next-cycle
    lane_lit = [f"lane({item.lane_domain}, {idx})"] if (item.lane_domain and idx is not None) else []
    # The RANGE of the loop/generate that rolled this register (`for (i = lo; i < hi; i++)
    # q[i] <= ..`), as a domain literal -- the same decision the comb path takes (`_lane_dom`),
    # so a PARTIAL loop drives only its own lanes. Without it the rule fanned over every lane
    # of `q` (bound by the body's lane reads), so `for (i = 0; i < 3; i++)` over an 8-lane
    # register drove lanes 3..7 too, and a loop from 1 drove lane 0. Single-index lane targets
    # only (a nested loop keeps the per-dimension `lane(...)` binding it has).
    def range_lits(body: list[str]) -> list[str]:
        if idx != "I" or lane_lit or not (widths or {}).get(reg):
            return []
        ew = (lane_elem_w or {}).get(reg, 1) or 1
        lanes = (widths or {}).get(reg, 0) // ew
        bound = (_binds_lane_var(body, "I"),)
        return _lane_dom_lits(_lane_domains(1, (), lanes, item.lane_hi, bound, item.lane_lo,
                                            item.lane_step))
    # --bitvec: a register in bitvec_signals whose shape is INDEXED gets per-bit capture rules.
    # Sequential holds are handled by _emit_multiclock (multi-clock) or by the explicit hold branch
    # (en=0 hold branch) — both handled correctly via the per-bit flatten path.
    bitvec_reg = (not comb and reg in bitvec_signals and shape == Shape.INDEXED)

    def head(v: str) -> str:
        if idx is not None:
            return f"val({_lane_term(reg, hidx)}, {v}, {nxt})"
        return f"val({reg}, {v}, {nxt})"   # bit or word: a 1-bit reg is a width-1 word

    def at_t(v: str) -> str:
        if idx is not None:
            return f"val({_lane_term(reg, hidx)}, {v}, T)"
        return f"val({reg}, {v}, T)"

    def read(e: Expr, ctx: _Ctx) -> tuple[list[str], str]:
        if isinstance(e, Tag):           # enum next-state: a symbolic tag, no body
            return [], e.label
        if idx is not None:              # lane reg: read operands per-lane (lane-aware, head binds I)
            return _word_body(e, "T", ctx, shapes, lane_dims, lane_ctx=True)
        if bit:
            return _bit_read(e, "T", ctx)
        return _assign_word(e, "T", ctx, shapes, lane_dims, widths, (widths or {}).get(reg))

    if not comb and item.reset is not None:
        asserted, deasserted = _rst_lits(item.reset, "T")
        # a WIDE reset value (>= 2^31) must be a canonical decimal STRING, else clingo's signed-32-bit
        # Number parse silently wraps it (hard rule 4) -- _const_lit quotes by magnitude.
        rv = item.reset_value if isinstance(item.reset_value, str) else _const_lit(item.reset_value)
        # (A) async clear, head at T (an enum resets to its TAG). A LANE register (a generate over a
        # packed 2-D, `sh_q[i] <= ..` under `if (!rst_n)`) needs its lane DOMAIN here too: nothing
        # in the body `val(rst_n, 0, T)` binds I, so without it the rule was UNSAFE -- refused,
        # loudly, in both modes (found by the spec2rtl lane print, next to F17).
        a_body = [*lane_lit, asserted]
        out.rule(at_t(rv), [*range_lits(a_body), *a_body])
        # THE EDGE UNDER RESET. A clocked update is gated on the reset being deasserted at BOTH
        # ends of the edge: at T (the edge lies in interval T and sees its inputs -- rst_n among
        # them, exactly as en and d are read at T) and at T+1 (else the async rule (A) at T+1
        # would also fire: two values). An edge taken while reset is asserted at T and released
        # at T+1 loads NOTHING -- rule (R) below carries the reset value across it. Gating on
        # T+1 alone (the schema until 2026-08-16) made such an edge load, one cycle before any
        # simulator with inputs stable across edges does: an LFSR reset to 1 read 2,4,8 where
        # Icarus read 1,2,4 (worklist 0c S4). Source-only gating double-drives
        # (`Async.source_gated_reset_is_multi_valued`); both ends is the single-valued reading.
        gate_deassert = f"{deasserted}, {_rst_lits(item.reset, 'T+1')[1]}"
        rel_body = [*lane_lit, f"time({clk}, T)", "T < k", asserted, _rst_lits(item.reset, "T+1")[1]]
        out.rule(head(rv), [*range_lits(rel_body), *rel_body])   # (R) the release edge: reset value, at T+1
    else:
        gate_deassert = None

    def gterm(g: str) -> str:
        """A guard/selector's atom, lane-aware: a per-lane (INDEXED) signal read inside a lane
        register's rule carries the register's lane index (`g(I)`); a scalar/broadcast one stays
        bare. Guards had this; CASE selectors (`tag_guards`, `neg_matches`) did not, so a
        `case (a[i])` inside a generate read its hoisted per-lane selector `t0` as the WORD
        `val(t0, ..)`, which nothing derives -- the register was dark, exit 0.

        But INDEXED alone is not "per lane". A multi-bit register is INDEXED because BITVEC split it
        into bits, and its value as a case SELECTOR is still the WORD: `case (state)` with a 4-bit
        `state` became `val(state(I), 0, T)` -- "bit I is 0" -- so several arms matched at once, the
        register took two values, and every interesting trace was UNSATISFIABLE while the run reported
        `VERDICT: OK`. A checker asking only "is `bad` reachable?" reads that as conformance; it was
        caught by the dataset's rule that the GOALS must stay reachable on the design under test
        (F23, on VerilogEval's fsm_hdlc reference, 2026-08-20). A genuine lane signal is in
        `bitvec_signals`, and its VALUE is the assembled word the bridge provides -- so a selector
        that is a bitvec expansion reads as the WORD, and only a genuine per-lane signal reads per
        lane. (`lane_dims` cannot make the distinction: the emitter's copy contains bitvec signals
        too, which is what a first attempt at this fix got wrong.)"""
        if shapes.get(g) != Shape.INDEXED or g in (bitvec_signals or frozenset()):
            return g
        return _lane(g, lane_dims)

    def gval(g: str, p: int) -> str:
        return f"val({gterm(g)}, {p}, T)"

    covered_bits: set[int] = set()  # for bitvec coverage check across all branches
    for br in item.branches:
        guard_lits = [gval(g, p) for g, p in br.guards]
        tag_lits = [f"val({gterm(sig)}, {tag}, T)" for sig, tag in br.tag_guards]  # case-arm matches
        if isinstance(br.value, XVal):
            # `default: y = 'x;` -- the design does not constrain y on this path. NO design rule is
            # emitted (a value would be invented); the guarded CHOICE goes to the boundary companion,
            # so the design layer stays positive-definite (hard rule 3) exactly as power-on does.
            # Recorded here, on the emitted branch, so the guards are the ones that actually fired.
            ctx = _Ctx(out.used)
            neg = _neg_match_lits(br.neg_matches, ctx, gterm)
            out.used |= ctx.used
            body = [*lane_lit, *guard_lits, *tag_lits, *neg]
            if not comb:
                body = [f"time({clk}, T)", "T < k", *body]
            elif not body:
                body = [f"time({clk}, T)"] if clk else []
            # A LANE head needs its index bound: nothing in an x-arm's guards mentions `I`, so without
            # the domain literal the rule is unsafe and clingo refuses to ground it (`shift18`). Same
            # decision the value rules take just below (`range_lits`).
            body = [*range_lits(body), *body]
            # The DECLARATION carries no value -- it says only WHERE the design is unconstrained, so
            # the design layer stays positive-definite. The companion turns it into the choice.
            out.rule(f"dontcare_at({_lane(reg, lane_dims) if shapes.get(reg) == Shape.INDEXED else reg}, T)", body)
            out.dontcare.append((reg, widths.get(reg, 1), br.loc or item.loc))
            continue
        base_guards = [] if comb else [f"time({clk}, T)", "T < k"]
        base_guards = [*lane_lit, *base_guards]
        if gate_deassert:
            base_guards.append(gate_deassert)
        if br.loc is not None and br.loc.line != item.loc.line:
            out.comment(_prov(br.loc))

        if bitvec_reg:
            # Per-bit sequential capture: build seq_guards = base + branch guards, then
            # let _emit_bitvec emit range-guarded T+1 rules.  The width comes from bitvec_width
            # (same as widths[reg]); the negative lits aren't in bitvec_signals so no neg_lits.
            ctx = _Ctx(out.used)
            neg_lits = _neg_match_lits(br.neg_matches, ctx, gterm)
            out.used |= ctx.used
            seq_guards = [*base_guards, *tag_lits, *neg_lits, *guard_lits]
            reg_width = (widths or {}).get(reg, 0)
            if (reg_width and item.lane_domain is None and (lane_elem_w or {}).get(reg, 1) == 1
                    and not isinstance(br.value, Tag)
                    and _bitvec_flatten(br.value, reg_width, bitvec_signals, None) is None):
                # A WORD-DRIVEN branch of a per-bit register. The register is per-bit because
                # another branch shifts it (`scount <= {scount[2:0], data}`); THIS branch is word
                # arithmetic (`scount <= scount - 1'b1`) that no per-bit source expresses. Lower it
                # at the WORD -- reading the register's own ASSEMBLED word `val(scount, V, T)`
                # (the bridge assembles every per-bit signal) -- and DECOMPOSE the result into the
                # cells: the bridge-direction-follows-the-driver rule, per branch. It used to be
                # refused ("bitvec lowering unsupported") -- loud, but on the dataset's
                # VerilogEval fancytimer reference, a shift-in-then-count-down register
                # (2026-08-19). Tight: cell I at T+1 reads the word at T.
                wctx = _Ctx(out.used)
                vbody, vt = _assign_word(br.value, "T", wctx, shapes, lane_dims, widths, reg_width)
                out.used |= wctx.used
                out.used.add("slc")
                vb = wctx.fresh()
                out.rule(f"val({_lane(reg, lane_dims)}, {vb}, T+1)",
                         [f"I = 0..{reg_width - 1}", *seq_guards, *vbody, f"{vb} = @slc({vt}, I, 1)"])
                covered_bits |= set(range(reg_width))
                continue
            covered = _emit_bitvec(reg, br.value, out, widths or {}, lane_dims or {},
                                   br.loc or item.loc,
                                   bitvec_signals=bitvec_signals,
                                   seq_guards=seq_guards, head_t="T+1")
            covered_bits |= covered
            continue

        # Word-form path (unchanged)
        ctx = _Ctx(out.used)
        vbody, vt = read(br.value, ctx)
        neg_lits = _neg_match_lits(br.neg_matches, ctx, gterm)
        out.used |= ctx.used
        body = [*base_guards, *tag_lits, *neg_lits, *guard_lits, *vbody]
        body = [*range_lits(body), *body]
        # A COMBINATIONAL assignment of a CONSTANT reads no signal and has no clock literal, so
        # nothing binds T and the rule is unsafe -- `always_comb y = 8'd99;` emitted the bare
        # fact `val(y, 99, T).`, which clingo cannot ground. The `assign` form of the same thing
        # already routes through `_bind_t`; this path did not (Fix 79). A clocked branch always
        # has `time(clk, T)` in `base_guards`, so it is untouched.
        out.rule(head(vt), _bind_t(body) if comb else body)

    # Coverage check for per-bit registers: every bit in [0..width-1] must be covered.
    if bitvec_reg:
        reg_width = (widths or {}).get(reg, 0)
        if reg_width and covered_bits != set(range(reg_width)):
            missing = sorted(set(range(reg_width)) - covered_bits)
            out.problem(item.loc,
                        f"bitvec seq reg {reg}: bits {missing} not covered across all capture branches")

    # Branches carry full path conditions (else-negation) and explicit holds, so they are
    # mutually exclusive and exhaustive -> no implicit-hold rule needed (has_hold is False).
    if item.has_hold:  # legacy path; current frontend emits explicit hold branches instead
        base = [f"time({clk}, T)", "T < k", *([gate_deassert] if gate_deassert else [])]
        off = [gval(g, 1 - p) for g, p in {g for br in item.branches for g in br.guards}]
        out.rule(head("V"), [*base, *off, at_t("V")])


def _emit_vff(item, out: _Out) -> None:
    """Vectored flop -> lane-lifted per-lane flops (catalog §4.6).

    Each lane is a FUNCTOR signal q(I): ``val(q(I), V, T)``. The lane domain is qualified by the
    INSTANCE name (``lane(inst, I)``) -- the unique owner of the lanes -- not the output net, which
    can collide when two instances drive slices of one shared net. Lane I captures d(I) when en(I)=1,
    else holds q(I). The per-lane value V keeps its OWN shape: at width 1 it is the bit, at width>1 it
    is the whole width-bit WORD (word arithmetic on a lane works) -- ONE rule shape either way. The
    per-lane width is self-described by ``lane_shape(q, lanes(N), width(W))`` for W>1 (lets a later
    bit-select into a lane know its width)."""
    out.construct(_prov(item.loc, f"vff {item.inst} -> {item.q}  ({item.lanes} lanes x {item.width} bits)"))
    clk = item.clock
    q, d = _lane_term(item.q, "I"), _lane_term(item.d, "I")
    # a BROADCAST enable (`.En({N{x}})`) is the one net x, read as a scalar by every lane
    en = _lane_term(item.en, "I") if getattr(item, "en_lane", True) else item.en
    out.rule(f"lane({item.inst}, 0..{item.lanes - 1})")
    if item.width > 1:   # self-describing: q is a lane signal of N lanes, each a W-bit word
        out.rule(f"lane_shape({item.q}, lanes({item.lanes}), width({item.width}))")
    base = [f"lane({item.inst}, I)", f"time({clk}, T)", "T < k"]
    out.rule(f"val({q}, V, T+1)", [*base, f"val({en}, 1, T)", f"val({d}, V, T)"])
    out.rule(f"val({q}, V, T+1)", [*base, f"val({en}, 0, T)", f"val({q}, V, T)"])


# --------------------------------------------------------------------------
# memory (Group 2/3 Section 2.9)
# --------------------------------------------------------------------------
def _emit_comb_mem_write(mem: str, w, out: _Out, gate: bool) -> None:
    """One combinational memory write rule (cell IS the data at T -- no state/T+1). ``gate`` adds the
    ``mem_def_ok`` suppressor so a DEFAULT only applies where a later override doesn't claim the cell;
    a gated write must be constant-address (a dynamic-address default can't be statically gated)."""
    ctx = _Ctx(out.used)
    ab, av = _word_body(w.addrs[0], "T", ctx)
    db, dv = _word_body(w.data, "T", ctx)
    out.used |= ctx.used
    g = [f"val({s}, {p}, T)" for s, p in w.guards]
    if ab:  # variable address -> rename the address term to A
        if gate:
            out.problem(w.loc, f"combinational memory {mem}: dynamic-address default write "
                        "(can't statically suppress it at the override cell)")
            return
        out.rule(_mem_atom(mem, "A", dv, "T"), _bind_t([*g, *_subst(ab, av, "A"), *db]))
    else:   # constant address (mem[0] = ...) -> the literal cell index
        gate_lit = [f"mem_def_ok({mem}, {av}, T)"] if gate else []
        out.rule(_mem_atom(mem, av, dv, "T"), _bind_t([*g, *db, *gate_lit]))


def _emit_comb_mem(mem: str, writes: list, out: _Out,
                   shapes: dict[str, Shape] | None = None,
                   lane_dims: dict[str, int] | None = None) -> None:
    """A combinational memory's writes, resolved together at the SAME T (no state). Two shapes:
    - **straight-line** -- each cell written once, unconditionally (`mem[0]=a; mem[1]=b; ...`):
      one rule per write.
    - **write-enable** -- unconditional DEFAULT writes then a single trailing GUARDED override
      (`...defaults...; if(we) mem[addr]=data;`, addr constant or DYNAMIC): last-write-wins, so the
      override claims its cell and the defaults apply everywhere else. We suppress each default at the
      overridden address with a positive ``mem_def_ok`` marker (the combinational analogue of the
      sequential ``mem_hold``) -- so a cell is NEVER multi-valued.
    Anything else (multiple overrides, a non-trailing override) flags loud (fail-loud)."""
    out.construct(_prov(writes[0].loc, f"{mem} comb write port"))
    if any(w.lane_rolled for w in writes):              # generate `assign mem[i]=expr` -> lane-rolled
        if len(writes) != 1 or not writes[0].lane_rolled:
            out.problem(writes[0].loc, f"combinational memory {mem}: lane-rolled write mixed with others")
            return
        _emit_lane_mem_write(writes[0], out, False, shapes, lane_dims)
        return
    if any(len(w.addrs) != 1 for w in writes):          # 2-D combinational memory not modeled yet
        out.problem(writes[0].loc, f"multi-dimensional combinational memory {mem} (deferred)")
        return
    overrides = [w for w in writes if w.guards]
    if not overrides:                                   # straight-line: each write drives its cell
        for w in writes:
            _emit_comb_mem_write(mem, w, out, gate=False)
        return
    if len(overrides) != 1 or writes[-1] is not overrides[0]:
        out.problem(writes[0].loc, f"combinational memory {mem}: only 'unconditional defaults + one "
                    f"trailing guarded override' is supported ({len(overrides)} guarded writes)")
        return
    ovr = overrides[0]
    _emit_comb_mem_write(mem, ovr, out, gate=False)     # the override claims its (const/dynamic) cell
    # mem_def_ok(mem, A, T): a default value applies at A iff the override does NOT claim A this T --
    #   override DISABLED (any guard off) -> applies everywhere; ENABLED but a DIFFERENT cell (A != B).
    for s, p in ovr.guards:
        out.rule(f"mem_def_ok({mem}, A, T)", [f"addr({mem}, A)", f"val({s}, {1 - p}, T)"])
    g = [f"val({s}, {p}, T)" for s, p in ovr.guards]
    ctx = _Ctx(out.used)
    ab, av = _word_body(ovr.addrs[0], "T", ctx)
    out.used |= ctx.used
    diff = [*_subst(ab, av, "B"), "A != B"] if ab else [f"A != {av}"]
    out.rule(f"mem_def_ok({mem}, A, T)", [f"addr({mem}, A)", *g, *diff])
    for w in writes[:-1]:                               # the defaults, suppressed at the override cell
        _emit_comb_mem_write(mem, w, out, gate=True)


def _emit_lane_mem_write(w, out: _Out, default_init: bool,
                         shapes: dict[str, Shape] | None = None,
                         lane_dims: dict[str, int] | None = None) -> None:
    """A `for`[`for`] write q[i][j]<=expr lane-rolled over the address domain: one rule fanning the
    loop var(s) over `addr(mem, I[, J])` (catalog 2.9 / 4.6) -- val(mem(I, J), V, T+1). MemRef reads in
    the data carry the same I,J, so q[i][j]<=src[i][j] reads val(src(I, J), V, T). A PACKED-vector lane
    operand in the data (q[i]<=a[i]&b[i], a/b INDEXED) is read per-lane too -- the rule head binds I, so
    the data is lowered with lane_ctx=True (else a/b would read as the whole word -> silent-wrong). Full
    range writes every cell (no hold); a partial loop (lane_hi[d] set) or a guarded write holds the rest.
    A cell is held if it is out of range in ANY dimension OR the write is disabled -> one hold rule per
    such case (their union is exactly the complement of the written rectangle)."""
    lv = [_LANEVARS[a.pos] for a in w.addrs]           # lane vars, e.g. ["I"] or ["I", "J"]
    ixs = ", ".join(lv)
    dom = f"addr({w.mem}, {ixs})"
    ctx = _Ctx(out.used)
    db, dv = _word_body(w.data, "T", ctx, shapes, lane_dims, lane_ctx=True)  # head binds I -> per-lane data
    out.used |= ctx.used
    guard = [f"val({g}, {p}, T)" for g, p in w.guards]
    write_c, hold_c = _mem_partition(w.lane_hi, [p for _g, p in w.guards], w.lane_lo)
    rng = [f"{lv[d]} < {b}" if k == "hi" else f"{lv[d]} >= {b}" for k, d, b in write_c]
    if not w.clock:                                    # COMBINATIONAL memory: every cell driven at T,
        if rng or guard:                               # no state/T+1, no hold. A partial/guarded comb
            out.problem(w.loc, f"combinational memory {w.mem}: partial/guarded lane write "
                               "(uncovered cells undriven -- no combinational hold)")
            return
        out.rule(_mem_atom(w.mem, ixs, dv, "T"), [dom, *db])
        return
    clk = w.clock
    # A memory with a RESET takes its power-on from that reset, exactly as `_xinit_kind` answers
    # 'skip' for a reset register -- pinning cells to 0 here as well double-drove every cell at T=0
    # once the array reset started lowering (F25).
    if default_init and w.reset is None:
        out.rule(_mem_atom(w.mem, ixs, "0", "0"), [dom])
    # THE EDGE UNDER RESET, for cells. A clocked update is gated on the reset being deasserted at BOTH
    # ends of the edge -- the same rule `arff` follows for a register (worklist 0c S4). The memory path
    # gated only the SOURCE end, so a write launched the cycle before an async reset landed at T+1
    # beside the reset's own force and the cell took two values. Invisible until the array reset
    # started lowering (F25); the generate form (F16) has the same shape and was never exercised by a
    # mid-run reset.
    rel_lit = [f"val({w.reset[0]}, {w.reset[1]}, T+1)"] if w.reset is not None else []
    out.rule(_mem_atom(w.mem, ixs, dv, "T+1"),
             [dom, *rng, f"time({clk}, T)", "T < k", *guard, *rel_lit, *db])
    # hold the cells this write does NOT cover (one rule per out-of-range dim / per disabled guard).
    holds: list[list[str]] = []
    for kind, d, hi in hold_c:
        if kind == "range":                            # past the bound in dim d -> hold (time binds T)
            holds.append([dom, f"time({clk}, T)", f"{lv[d]} >= {hi}"])
        elif kind == "below":                          # under the loop's start in dim d -> hold
            holds.append([dom, f"time({clk}, T)", f"{lv[d]} < {hi}"])
        else:                                          # write disabled -> all cells hold (val binds T)
            holds.append([dom, f"val({w.guards[d][0]}, {hi}, T)"])
    for body in holds:
        out.rule(f"mem_hold({w.mem}, {ixs}, T)", body)
    if holds:
        out.rule(_mem_atom(w.mem, ixs, "V", "T+1"),
                 [f"time({clk}, T)", "T < k", _mem_atom(w.mem, ixs, "V", "T"),
                  *rel_lit, f"mem_hold({w.mem}, {ixs}, T)"])   # ...and the hold, for the same reason


def _addr_terms(addrs: tuple, dst: str, ctx: _Ctx) -> tuple[list[str], list[str]]:
    """Lower each address Expr to its head TERM: a runtime address renames to a dst-var (1 addr -> 'A',
    N -> 'A1','A2',...) bound by the returned body; a CONSTANT cell index ``q[0]`` becomes the literal
    itself (so a constant write head is ``val(q, ...)``, not an unbound ``A``). Returns (body, terms)."""
    names = [dst] if len(addrs) == 1 else [f"{dst}{p + 1}" for p in range(len(addrs))]
    body: list[str] = []
    terms: list[str] = []
    for a, v in zip(addrs, names, strict=True):
        ab, av = _word_body(a, "T", ctx)
        if not ab and av.lstrip("-").isdigit():        # constant index -> the literal, no free var
            terms.append(av)
        else:
            body += _subst(ab, av, v)
            terms.append(v)
    return body, terms


def _not_writing(w, head_avars: list[str], ctx: _Ctx, vbase: str) -> list[list[str]]:
    """Disjuncts (positive literal-lists) whose OR == 'write ``w`` does NOT claim cell ``head_avars`` at
    T'. Positive-definite (no NAF): a guard-off (port idle) is one disjunct per guard; an enabled write
    to a DIFFERENT address is one disjunct per coordinate (all guards on, that coordinate != head)."""
    disj = [[f"val({g}, {1 - p}, T)"] for g, p in w.guards]   # any guard off -> port writes nothing
    gon = [f"val({g}, {p}, T)" for g, p in w.guards]
    bbody, bvars = _addr_terms(w.addrs, vbase, ctx)              # the port's own address, fresh var(s)
    for a, b in zip(head_avars, bvars, strict=True):
        disj.append([*gon, *bbody, f"{a} != {b}"])              # enabled but a different cell
    return disj


def _product(disjuncts_per_port: list[list[list[str]]]) -> list[list[str]]:
    """Cartesian product of the per-port disjunct sets: pick one disjunct (literal-list) from each port
    and merge (dedup, order-preserving). Encodes the AND-over-ports of an OR-of-disjuncts as a DNF."""
    combos: list[list[str]] = [[]]
    for disj in disjuncts_per_port:
        combos = [[*c, *d] for c in combos for d in disj]
    out = []
    for c in combos:
        seen: set[str] = set()
        out.append([lit for lit in c if not (lit in seen or seen.add(lit))])
    return out


def _not_writing_lane(w, head_avars: list[str]) -> list[list[str]]:
    """`_not_writing` for a LANE-ROLLED port: it does not claim cell ``head_avars`` at T iff a guard
    is off, or the cell lies outside the loop's window in some dimension -- under the start
    (`A < lo`) or past the bound (`A >= hi`), the same partition `_mem_partition` gives the
    single-port hold. Positive-definite: comparisons over the already-bound address vars."""
    disj = [[f"val({g}, {1 - p}, T)"] for g, p in w.guards]
    write_c, _hold = _mem_partition(w.lane_hi, [p for _g, p in w.guards], w.lane_lo)
    for kind, d, b in write_c:
        disj.append([f"{head_avars[d]} >= {b}"] if kind == "hi" else [f"{head_avars[d]} < {b}"])
    return disj


def _emit_mem_multi(mem: str, writes: list, out: _Out, default_init: bool,
                    shapes: dict[str, Shape] | None = None,
                    lane_dims: dict[str, int] | None = None) -> None:
    """Two+ clocked write PORTS to one memory, COORDINATED. Each port writes its cell unless a LATER
    port writes the same cell (last-write-wins), and a cell holds iff NO port writes it (ONE combined
    hold -- the per-port mem_hold of the single-write path would over-fire, double-valuing a cell whenever
    any other port is idle). A LANE-ROLLED port (`for (i = 1; ..) m[i] <= m[i-1]` beside `m[0] <= d`,
    a shift chain through a memory) is coordinated too: its window `lo..hi-1` is what it claims,
    and everything else -- including a later port's suppression of it -- is the same "does not
    write this cell" disjunction. Before this it fell back to the UNCOORDINATED per-port path,
    whose two `mem_hold`s over-fired and made every cell the other port left alone multi-valued
    -- UNSAT under any scenario, which a property check reads as "no counterexample".
    An RMW port or mixed clocks still fall back to the per-write path."""
    if any(w.rmw_slices or w.clock != writes[0].clock for w in writes):
        for w in writes:                                        # uncoordinated fallback (rare/complex)
            _emit_mem_write(w, out, default_init, shapes, lane_dims)
        return
    out.construct(_prov(writes[0].loc, f"{mem} write ports (x{len(writes)}, last-write-wins + joint hold)"))
    nd = len(writes[0].addrs)
    head = ["A"] if nd == 1 else [f"A{p + 1}" for p in range(nd)]
    ah = ", ".join(head)
    clk = writes[0].clock

    def not_writing(w, avars: list[str], ctx: _Ctx, vbase: str) -> list[list[str]]:
        return _not_writing_lane(w, avars) if w.lane_rolled else _not_writing(w, avars, ctx, vbase)

    # THE ARRAY'S ASYNC RESET (F26). `_emit_mem_write` has forced every cell at the reset LEVEL
    # since F16 and gated the write edge at BOTH ends since F25 -- and this path, taken the moment a
    # memory acquires a SECOND write port, did NEITHER. A table written by two guarded ports and
    # cleared by `if (rst) for (i...) tab[i] <= C;` got no reset rule at all, and the joint hold told
    # every cell to KEEP its value while reset was asserted -- the exact opposite of the RTL, at exit
    # 0 with `coverage: OK`. Same defect as F25 one write port over: the fix was applied to the path
    # in front of it and not to the path beside it.
    resets = {w.reset for w in writes if w.reset is not None}
    if len(resets) > 1:      # ports disagreeing about the reset is not a shape we can compose
        raise NotImplementedError(
            f"{mem}: write ports disagree about the array's reset ({sorted(resets)})")
    rst = next(iter(resets), None)
    # the release edge: deasserted at BOTH ends, so a write launched the cycle before the reset
    # lands does not arrive beside the force and double-value the cell.
    rel_lit = [f"val({rst[0]}, {rst[1]}, T+1)"] if rst is not None else []
    if rst is not None:
        out.rule(_mem_atom(mem, ah, str(rst[2]), "T"),
                 [f"addr({mem}, {ah})", f"val({rst[0]}, {1 - rst[1]}, T)"])
    if default_init and rst is None:   # a RESET memory's power-on IS its reset -- pinning 0 beside
        out.rule(_mem_atom(mem, ah, "0", "0"), [f"addr({mem}, {ah})"])   # the force is F25's defect
    for i, w in enumerate(writes):
        ctx = _Ctx(out.used)
        guard = [f"val({g}, {p}, T)" for g, p in w.guards]
        if w.lane_rolled:                                       # the loop's window IS the written set
            aterms = [_LANEVARS[a.pos] for a in w.addrs]
            write_c, _h = _mem_partition(w.lane_hi, [p for _g, p in w.guards], w.lane_lo)
            rng = [f"{aterms[d]} < {b}" if k == "hi" else f"{aterms[d]} >= {b}" for k, d, b in write_c]
            abody = [f"addr({mem}, {', '.join(aterms)})", *rng]
            db, dv = _word_body(w.data, "T", ctx, shapes, lane_dims, lane_ctx=True)  # head binds I
        else:
            abody, aterms = _addr_terms(w.addrs, "A", ctx)      # this port's WRITTEN cell (literal or A)
            db, dv = _word_body(w.data, "T", ctx)
        wr = ", ".join(aterms)
        base = [f"time({clk}, T)", "T < k", *guard, *rel_lit, *abody, *db]
        later = [(j, lw) for j, lw in enumerate(writes) if j > i]
        if not later:
            out.rule(_mem_atom(mem, wr, dv, "T+1"), base)       # the last port: never overridden
        else:
            # Suppressed where a LATER port claims THIS cell (last-write-wins). Left INLINED, unlike
            # the joint hold below: this rule is instantiated at the port's OWN written cell, which may
            # be a CONSTANT, and the named condition is quantified over the memory's address DOMAIN --
            # which a per-bit register reaching this path (`w[0] <= ..; w[2] <= ..`) does not have, so
            # the named form would never derive and every such write would go DARK. It is also the
            # shape the SMT completion reads literally. The product here is over LATER ports only,
            # which for the two-port memories that occur is one disjunct set, not an explosion.
            disj = [not_writing(lw, aterms, ctx, f"B{j}") for j, lw in later]
            for combo in _product(disj):
                out.rule(_mem_atom(mem, wr, dv, "T+1"), [*base, *combo])
        out.used |= ctx.used
    # THE JOINT HOLD -- one NAMED predicate per port, not a DNF cross-product.
    #
    # "cell A holds" means "NO port writes A", and "port p does not write A" is a DISJUNCTION (a guard
    # is off, OR the written address is a different cell). A rule body is a conjunction only, so a
    # conjunction-of-disjunctions used to be expanded into DNF -- one rule per combination, k^n of
    # them. Two ports with four ways of not-writing each gave SIXTEEN rules for one hold, and most
    # were junk: both ports share a guard, so pairing "port 0 idle because we=0" with "port 1 idle
    # because we=1" yields a body that can NEVER fire, and `arst=1, we=0` is strictly subsumed by
    # `arst=1`. Sound -- an inert rule derives nothing -- but every one of them still GROUNDS, and
    # sixteen near-identical rules with contradictory literals buried inside them is precisely the
    # output that defeats reading the completion, which is how several silent-wrongs here were found.
    #
    # Naming each port's condition turns k^n into n*k + 1 and leaves every rule saying ONE thing. It is
    # also what the single-write path has always done (`mem_hold`); this path inlined what that one
    # named. NOT `mem_hold` itself, though -- that predicate means "this port is idle", and with two
    # ports it would over-fire, holding a cell the OTHER port is writing (the defect this function was
    # written to fix). `mem_nowrite/4` is per PORT, and the hold requires all of them.
    for j, w in enumerate(writes):
        ctx = _Ctx(out.used)
        for d in not_writing(w, head, ctx, f"B{j}"):
            # T must be BOUND. A guard-off disjunct (`val(en,0,T)`) binds it; the different-cell
            # disjunct of an UNCONDITIONAL write to a CONSTANT address is just `A != 3` and binds
            # nothing -- these literals used to sit inside the hold rule, which bound T for them, and
            # standing alone they are unsafe (clingo cannot ground them). Same case, and the same fix,
            # as the single-write path's `tbind` (Fix 77); the safety check caught it here too.
            body = [f"addr({mem}, {ah})", *d]
            if not any(lit.startswith("val(") for lit in d):
                body.insert(0, f"time({clk}, T)")
            out.rule(f"mem_nowrite({mem}, {j}, {ah}, T)", body)
        out.used |= ctx.used
    out.rule(_mem_atom(mem, ah, "V", "T+1"),
             [f"time({clk}, T)", "T < k", f"addr({mem}, {ah})", _mem_atom(mem, ah, "V", "T"), *rel_lit,
              *[f"mem_nowrite({mem}, {j}, {ah}, T)" for j in range(len(writes))]])


def _emit_mem_write(w, out: _Out, default_init: bool,
                    shapes: dict[str, Shape] | None = None,
                    lane_dims: dict[str, int] | None = None) -> None:
    out.construct(_prov(w.loc, f"{w.mem} write port"))
    if w.reset is not None:
        # F16 (2026-08-18): the array's async reset arm (`if (!rst_n) q[i] <= C`) resets EVERY cell -- a
        # per-cell LEVEL force, the exact mirror of a register's rule (A). The reset-as-guard on the
        # write plus the hold under reset then carry C across the release edge (the cell IS C at T).
        # Before this the reset was lowered onto a phantom word register and the cells never reset
        # (found by the ASP-first lane print; the model allowed q(0)=7 after reset, Icarus gave 0).
        rsig, rel, rv = w.reset
        ah0 = "A" if len(w.addrs) == 1 else ", ".join(f"A{p + 1}" for p in range(len(w.addrs)))
        out.rule(_mem_atom(w.mem, ah0, str(rv), "T"), [f"addr({w.mem}, {ah0})", f"val({rsig}, {1 - rel}, T)"])
    if w.lane_rolled:                # a loop write q[i][j]<=.. lane-rolled over addr(mem, I[, J])
        _emit_lane_mem_write(w, out, default_init, shapes, lane_dims)
        return
    # addr/mem_hold are qualified by the memory name (like lane(q,I) for a VFF) so two
    # memories never share an address domain or hold predicate -- both producer and consumer.
    ah = "A" if len(w.addrs) == 1 else ", ".join(f"A{p + 1}" for p in range(len(w.addrs)))  # DOMAIN var(s)
    if default_init and w.reset is None:          # see above: a reset memory's power-on IS its reset
        out.rule(_mem_atom(w.mem, ah, "0", "0"), [f"addr({w.mem}, {ah})"])  # default-zero T=0 (else: bridge)
    clk = w.clock
    ctx = _Ctx(out.used)
    abody, aterms = _addr_terms(w.addrs, "A", ctx)
    wr = ", ".join(aterms)                               # the WRITTEN cell (a literal if constant, else A)
    guard = [f"val({g}, {p}, T)" for g, p in w.guards]
    # THE EDGE UNDER RESET, for cells: deasserted at BOTH ends (see the lane path's note; F25).
    rel_lit = [f"val({w.reset[0]}, {w.reset[1]}, T+1)"] if w.reset is not None else []
    base = [f"time({clk}, T)", "T < k", *guard, *rel_lit, *abody]  # runtime addr term(s) bind A / A1,A2
    if w.rmw_slices:
        # FIELD write: read-modify-write the cell -- untouched fields keep the OLD value at addr A.
        cw = w.cell_width
        vold = ctx.fresh()
        smask, parts, sbody = 0, [], []
        for off, sw, val in w.rmw_slices:
            vb, vv = _word_body(val, "T", ctx)
            sbody.extend(vb)
            smask |= ((1 << sw) - 1) << off
            if off:
                vs = ctx.fresh()
                ctx.used.add("shl")
                sbody.append(f"{vs} = @shl({vv}, {off}, {cw})")
                parts.append(vs)
            else:
                parts.append(vv)
        acc = parts[0]
        for pv in parts[1:]:
            r = ctx.fresh()
            ctx.used.add("or")
            sbody.append(f"{r} = @bor({acc}, {pv}, {cw})")
            acc = r
        keep = ((1 << cw) - 1) & ~smask
        if keep:
            ka = ctx.fresh()
            nv = ctx.fresh()
            ctx.used.update(("and", "or"))
            sbody.append(f"{ka} = @band({vold}, {keep}, {cw})")
            sbody.append(f"{nv} = @bor({ka}, {acc}, {cw})")
            acc = nv
        out.used |= ctx.used
        out.rule(_mem_atom(w.mem, wr, acc, "T+1"), [*base, _mem_atom(w.mem, wr, vold, "T"), *sbody])
    else:
        db, dv = _word_body(w.data, "T", ctx)
        out.used |= ctx.used
        out.rule(_mem_atom(w.mem, wr, dv, "T+1"), [*base, *db])
    # hold (positive): unwritten cells preserve
    out.rule(_mem_atom(w.mem, ah, "V", "T+1"),
             [f"time({clk}, T)", "T < k", _mem_atom(w.mem, ah, "V", "T"),
              *rel_lit, f"mem_hold({w.mem}, {ah}, T)"])
    # hold when the write is DISABLED -- only exists if there's a write-enable guard (an
    # unconditional write is never disabled; emitting this with no guard leaves T unbound).
    # ONE RULE PER GUARD: the write is disabled when ANY guard reads its other value. This
    # used to be a single rule requiring EVERY guard off -- with two guards (`if (a) if (b)
    # mem[x] <= d`, or a write in an async-reset block, which now carries the reset as a guard)
    # the state "one guard off, the other on" had neither a write nor a hold: the cells went
    # DARK at T+1, silently. The lane path (`_mem_partition`) and the multi-port path
    # (`_not_writing`) already enumerate per guard; this was the third copy of the same
    # decision, wrong on its own.
    for g, pol in w.guards:
        out.rule(f"mem_hold({w.mem}, {ah}, T)", [f"addr({w.mem}, {ah})", f"val({g}, {1 - pol}, T)"])
    # hold a cell whose address DIFFERS from the written one -- two cells differ if ANY coord differs,
    # so emit one rule per coordinate (1-D -> a single A != B).
    ctx2 = _Ctx(out.used)
    bbody, bterms = _addr_terms(w.addrs, "B", ctx2)       # the written cell again, fresh B var(s)/literal
    out.used |= ctx2.used
    # T must be BOUND. A guard (`val(en,1,T)`) or a runtime address term binds it; an
    # unconditional write to a CONSTANT address has neither, and the rule was then unsafe --
    # clingo cannot ground it, which the safety check reports but which is a defect here, not in
    # the RTL (Fix 77). Bind it explicitly in exactly that case, so every design that already
    # bound T keeps its output byte-identical.
    tbind = [] if (guard or bbody) else [f"time({clk}, T)"]
    for dom, wrc in zip(ah.split(", "), bterms, strict=True):   # a domain cell differs in this coord
        out.rule(f"mem_hold({w.mem}, {ah}, T)",
                 [f"addr({w.mem}, {ah})", *tbind, *guard, *bbody, f"{dom} != {wrc}"])


def _subst(body: list[str], term: str, new: str) -> list[str]:
    """Rename the final-result variable ``term`` to ``new`` throughout ``body``."""
    return [_replace_var(b, term, new) for b in body]


def _replace_var(s: str, old: str, new: str) -> str:
    return re.sub(rf"\b{re.escape(old)}\b", new, s)


# --------------------------------------------------------------------------
# orchestration
# --------------------------------------------------------------------------
def _guard(out: _Out, loc: object, what: str, fn) -> None:
    """Last-resort soundness net: emit a construct, but if ANYTHING goes wrong (unhandled
    expression, missing case) record it as a hard problem rather than crashing the whole
    translation or silently skipping the construct."""
    n = len(out.lines)
    try:
        fn()
    except Exception as e:  # noqa: BLE001 - intentional catch-all: a construct we cannot emit MUST flag
        del out.lines[n:]   # drop any partial output for this construct
        out.problem(loc, f"{what}: {type(e).__name__}: {e}")


def _state_clocks(design: Design) -> set[str]:
    """Distinct real clock domains across every state element (registers, lane regs, VFFs, memory),
    PLUS each gated clock from an ICG primitive and its base clock -- so a flop on a gated clock and the
    free clock are >=2 domains and the master-tick HOLD fires for the gated flop between its (suppressed)
    edges (catalog §6.7)."""
    cl = {it.clock for it in design.seq if not it.combinational and it.clock}
    cl |= {w.clock for w in design.mem_writes if w.clock}
    cl |= {v.clock for v in design.vffs if v.clock}
    cl |= {dc.name for dc in design.derived_clocks} | {dc.base for dc in design.derived_clocks}
    return cl


def _emit_multiclock(design: Design, shapes: dict[str, Shape], lane_dims: dict[str, int],
                     out: _Out, global_tick: str = "gtime(T)",
                     bitvec_signals: frozenset[str] = frozenset()) -> None:
    """Master-tick multi-clock linkage. When a design spans >=2 clock domains, the SLOWER clocks are
    sub-rates of the FASTEST: one global tick line ``gtime/1`` = the union of all clock edges (the
    fastest clock, by construction, ticks every step). A state element CAPTURES on its OWN clock's edge
    (the existing seq rules, guarded by ``time(clk,T)``) and HOLDS between its edges (the rules here,
    guarded by ``no_tick(clk,T)``) -- so its value is defined at EVERY global tick and a cross-domain
    read just reads at global T. A single-clock design has an edge every step, so the hold never fires;
    it is omitted there to keep the output byte-identical to the no-linkage form.

    ``no_tick(clk,T)`` is a DERIVED POSITIVE ATOM: its single NAF rule is isolated here, so hold rules
    read it positively (no NAF in design rule bodies).  In ASP stable-model semantics, absence-of-proof
    (``not time``) and proof-of-absence (``no_tick``) have different meanings; the latter is a genuine
    witness in the model that the clock did not tick at T."""
    if len(_state_clocks(design)) < 2:
        return                                  # single clock: hold is a no-op -> don't emit it
    out.section("MULTI-CLOCK LINKAGE (master = fastest clock; slow domains hold between own edges)")
    if global_tick == "gtime(T)":
        out.comment("gtime/1 = global tick line (union of all clock edges; the fastest clock ticks every")
        out.comment("step). A register changes only on its OWN clock edge and HOLDS otherwise (so its")
        out.comment("value is defined at every global T -> cross-domain reads share one time base).")
    else:
        out.comment("time(T) = global tick line (from the scenario's bare time(0..k)).")
        out.comment("A register changes only on its OWN clock edge and HOLDS otherwise.")
    out.comment("no_tick(Clk,T): derived positive witness that clock Clk does NOT tick at T.")
    out.comment("  NAF is isolated to this one derivation; hold rules below read no_tick positively.")
    if global_tick == "gtime(T)":
        out.rule("gtime(T)", ["time(CK, T)"])
    # Collect the set of slow clocks (those that don't tick every global step) so we emit one
    # no_tick derivation per distinct slow clock — not one per register.
    slow_clocks: set[str] = set()
    for it in design.seq:
        if not it.combinational and it.clock:
            slow_clocks.add(it.clock)
    for v in design.vffs:
        if v.clock:
            slow_clocks.add(v.clock)
    for m in design.mems:
        clk = next((w.clock for w in design.mem_writes if w.mem == m.name and w.clock), None)
        if clk:
            slow_clocks.add(clk)
    for c in sorted(slow_clocks):
        out.rule(f"no_tick({c}, T)", [global_tick, f"not time({c}, T)"])
    out.blank()
    for it in design.seq:
        if it.combinational or not it.clock:
            continue
        # an async reset is level-sensitive: it forces the reset value at every T it is asserted, so
        # the off-edge hold must yield to it (else both fire at T+1 -> two values). Gate on deassert.
        rst = [_rst_lits(it.reset, "T+1")[1]] if it.reset is not None else []
        if shapes.get(it.reg) == Shape.INDEXED:
            term = _lane_term(it.reg, _idx(it.reg, lane_dims))
            dom = [f"lane({it.lane_domain}, {_idx(it.reg, lane_dims)})"] if it.lane_domain else []
            out.rule(f"val({term}, V, T+1)",
                     [*dom, global_tick, "T < k", f"no_tick({it.clock}, T)", *rst, f"val({term}, V, T)"])
        else:
            out.rule(f"val({it.reg}, V, T+1)",
                     [global_tick, "T < k", f"no_tick({it.clock}, T)", *rst, f"val({it.reg}, V, T)"])
    for v in design.vffs:
        if not v.clock:
            continue
        q = _lane_term(v.q, "I")
        out.rule(f"val({q}, V, T+1)", [f"lane({v.inst}, I)", global_tick, "T < k",
                                       f"no_tick({v.clock}, T)", f"val({q}, V, T)"])
    for m in design.mems:
        clk = next((w.clock for w in design.mem_writes if w.mem == m.name and w.clock), None)
        if not clk:
            continue
        dims = m.dims or (m.depth,)
        aterm = ", ".join(["A"] if len(dims) == 1 else [f"A{p + 1}" for p in range(len(dims))])
        cell = f"{m.name[:-1]}({aterm}))" if m.name.endswith(")") else f"{m.name}({aterm})"
        out.rule(f"val({cell}, V, T+1)",
                 [f"addr({m.name}, {aterm})", global_tick, "T < k", f"no_tick({clk}, T)",
                  f"val({cell}, V, T)"])
    out.blank()


# --------------------------------------------------------------------------
# emit-time SAFETY CHECK  (hard rule 2: a clean run must mean a USABLE program)
# --------------------------------------------------------------------------
_ASP_VAR = re.compile(r"(?<![A-Za-z0-9_])([A-Z][A-Za-z0-9_]*)")
_CMP_OPS = ("!=", "<=", ">=", "=", "<", ">")


def _strip_quoted(s: str) -> str:
    """Blank out quoted strings so a wide decimal value like "4000000000" cannot contribute
    spurious variables or confuse the top-level splitter."""
    out, q = [], False
    for c in s:
        if c == '"':
            q = not q
            out.append(" ")
        else:
            out.append(" " if q else c)
    return "".join(out)


def _top_split(s: str) -> list[str]:
    """Split a rule body on TOP-LEVEL commas (not those inside f(...) / @f(...) / {...})."""
    parts, depth, cur = [], 0, []
    for c in s:
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        if c == "," and depth == 0:
            parts.append("".join(cur))
            cur = []
        else:
            cur.append(c)
    if cur:
        parts.append("".join(cur))
    return [p.strip() for p in parts if p.strip()]


def _classify_rule(rule: str):
    """Split a rule into the pieces the SAFETY analysis reasons over, or None if the rule uses a
    construct the analysis deliberately does not model (directive, conditional literal, NAF,
    aggregate) -- in which case it reports nothing rather than a false alarm.

    Returns ``(head, literals, positively_bound_vars, [(target, rhs_term), ...])``.

    Extracted from `_unsafe_vars` so the STAGE-C generator can reach the SAME classification the
    analysis uses (`proofs/gen_checks_lean.py`): the generated table then checks the Lean
    fixpoint model against this implementation on real emitted rules, instead of against a
    transcription of it. Pure refactor -- `_unsafe_vars` below is its only other caller and its
    behaviour is unchanged (the divider stays byte-identical)."""
    r = _strip_quoted(rule).strip().rstrip(".")
    if not r or r.startswith("%") or r.startswith("#") or ":" in r.replace(":-", ""):
        return None                       # directive / conditional literal -> not modelled
    head, sep, body = r.partition(":-")
    lits = _top_split(body) if sep else []
    if any(l.startswith("not ") or l.startswith("#") or "{" in l for l in lits):
        return None                       # NAF / aggregate -> not modelled
    bound: set[str] = set()
    assigns: list[tuple[str, str]] = []
    for l in lits:
        # a comparison binds nothing, EXCEPT `X = <term>` which binds X when <term> is bound
        op = next((o for o in _CMP_OPS if o in l), None)
        if op is None:
            bound |= set(_ASP_VAR.findall(l))          # positive literal: binds its variables
            continue
        lhs, _, rhs = l.partition(op)
        lv = _ASP_VAR.findall(lhs.strip())
        if op == "=" and len(lv) == 1 and lhs.strip() == lv[0]:
            assigns.append((lv[0], rhs))
    return head, lits, bound, assigns


def _unsafe_vars(rule: str) -> set[str]:
    """Variables a rule leaves UNBOUND -- i.e. the reasons clingo would refuse to ground it.

    ASP safety: every variable must occur in a positive body literal. The head binds nothing,
    and neither does a comparison. `X = <term>` (including `X = 0..N` and `X = @f(...)`) binds
    X once every variable in <term> is bound, so binding is computed to a fixpoint.

    Deliberately CONSERVATIVE: any rule using a construct this does not model (aggregates,
    conditional literals, negation-as-failure) returns no findings rather than a false alarm.
    Its job is to catch the Fix-51 class -- a lane/index variable with no domain literal --
    at translation time instead of at grounding time."""
    cl = _classify_rule(rule)
    if cl is None:
        return set()
    head, lits, bound, assigns = cl
    changed = True
    while changed:                                      # fixpoint over `X = <term>` chains
        changed = False
        for v, rhs in assigns:
            if v not in bound and set(_ASP_VAR.findall(rhs)) <= bound:
                bound.add(v)
                changed = True
    need = set(_ASP_VAR.findall(head))
    for l in lits:                                      # comparison operands must be bound too
        if any(o in l for o in _CMP_OPS):
            need |= set(_ASP_VAR.findall(l))
    return {v for v in need - bound if v != "_"}


def _logical_rules(text: str):
    """Yield whole LOGICAL rules from emitted text. A long body is wrapped across several
    physical lines, so a rule is accumulated until it terminates in `.` -- checking a
    continuation line on its own would report every variable in it as unbound (the divider
    emits exactly such wrapped rules)."""
    buf: list[str] = []
    for ln in text.splitlines():
        t = ln.strip()
        if not buf and (not t or t.startswith("%") or t.startswith("#")):
            continue
        if t.startswith("%"):            # a comment interleaved in a wrapped rule
            continue
        buf.append(t)
        if _strip_quoted(" ".join(buf)).rstrip().endswith("."):
            yield " ".join(buf)
            buf = []
    if buf:
        yield " ".join(buf)


def _val_term_time(lit: str) -> tuple[str, str] | None:
    """(signal term, time term) of a `val(...)` literal, or None if it is not one.

    Two shapes: flat `val(Sig, V, T)` and modular `val(Inst, Sig, V, T)`. The SIGNAL TERM is
    kept verbatim (`y`, `y(I)`, `y(I-1)`, `p(fld)`) -- see `_check_comb_loops` for why."""
    t = lit.strip()
    if not t.startswith("val(") or not t.endswith(")"):
        return None
    args = _top_split(t[4:-1])
    if len(args) == 3:
        return (args[0].strip(), args[2].strip())
    if len(args) == 4:
        return (args[1].strip(), args[3].strip())
    return None


def _comb_edges(text: str) -> dict[str, set[str]]:
    """The WITHIN-TIME-INDEX positive dependency graph of an emitted program: an edge `a -> b`
    means the rule deriving `b` reads `a` at the SAME time term.

    Extracted from `_check_comb_loops` so the STAGE-C generator can obtain the graph the detector
    actually builds (`proofs/gen_tight_lean.py`) rather than a transcription of it -- the same
    move `_classify_rule` makes for the safety analysis. Pure refactor: `_check_comb_loops` is
    its only other caller and its behaviour is unchanged.

    Negative literals are skipped: tightness is about POSITIVE dependencies (`_check_stratified`
    is the companion that looks at exactly those). A register's rule has its head at `T+1` and
    body at `T`, so it contributes no edge -- which is how sequential logic breaks cycles."""
    edges: dict[str, set[str]] = {}
    for rule in _logical_rules(text):
        r = _strip_quoted(rule).strip().rstrip(".")
        head, sep, body = r.partition(":-")
        if not sep:
            continue
        h = _val_term_time(head)
        if h is None:
            continue
        hterm, htime = h
        for lit in _top_split(body):
            if lit.strip().startswith("not "):
                continue                      # NAF is not a positive dependency
            b = _val_term_time(lit)
            if b is None:
                continue
            bterm, btime = b
            if btime == htime:                # same time index -> a comb edge (incl. self-loop)
                edges.setdefault(bterm, set()).add(hterm)
    return edges


def _check_mem_addr_range(design: object, out: "_Out") -> None:
    """F5 -- an ADDRESS that can leave the array is a lint error, and was silent.

    With a depth-5 array and a 3-bit address, values 5..7 are reachable. Today the WRITE
    rule carries no range guard, so it derives `val(mem(5), ..)` -- a cell OUTSIDE the
    `addr` domain, which the domain-guarded hold rules never carry, so it appears for one
    instant and vanishes. The READ derives nothing at those addresses, so its destination
    has no value and properties over it pass VACUOUSLY.

    Both halves come from one fact the emitter already knows: `addr_width` and `depth` sit
    on the `Mem` record. If 2^addr_width > depth the design can address past the end, and
    that is a DESIGN defect a linter reports -- the RTL is what needs fixing (a wider array,
    a narrower address, or a guard), so the message says which. Reported through both
    channels for the same reason as F3.
    """
    # Only a RUNTIME address can leave the array. A constant index, or a lane index bound by
    # an elaboration-time loop, is in range by construction -- and a lane-rolled array whose
    # depth is not a power of two (`y [0:N-1]` with N=3) would otherwise be flagged for a
    # risk it does not have. So the check needs an access whose address is a signal READ.
    runtime = set()
    for acc in list(getattr(design, "mem_writes", ())) + list(getattr(design, "mem_reads", ())):
        addrs = getattr(acc, "addrs", None) or ((getattr(acc, "addr", None),))
        for ad in addrs:
            if isinstance(ad, Ref):
                runtime.add(getattr(acc, "mem", None))
    for mem in getattr(design, "mems", ()):
        aw, depth = getattr(mem, "addr_width", None), getattr(mem, "depth", None)
        if aw is None or depth is None or (1 << aw) <= depth:
            continue
        if mem.name not in runtime:
            continue          # every access is a constant or lane index: in range already
        why = (f"memory `{mem.name}` can be addressed PAST ITS END: the address is {aw} "
               f"bit(s) (reaches 0..{(1 << aw) - 1}) and the array has {depth} cell(s) "
               f"(0..{depth - 1}). A write to {depth}..{(1 << aw) - 1} lands on a cell "
               f"outside the address domain and vanishes the next instant; a read there "
               f"derives nothing, so its destination has NO value and properties over it "
               f"pass vacuously. Widen the array to {1 << aw}, narrow the address, or guard "
               f"the access in the RTL")
        out.comment(f"PROBLEM: {why}")
        out.problem(getattr(mem, "loc", None), why)


def _check_partial_enum_cast(design: object, out: "_Out") -> None:
    """F3 -- a cast into a NON-FULL enum is PARTIAL, and silently so.

    `val(lhs, Tag, T) :- <operand V>, enum_value(e, Tag, V)` derives a tag exactly when the
    operand's value IS a member value. At any other value it derives NOTHING: the
    destination has no value at that instant and every property over it passes VACUOUSLY.
    With an n-bit operand there are 2^n patterns, so the cast is total iff the enum has a
    member for each -- the resolution version 4 settled on as its D4.

    Called from BOTH emitters, and it reports through BOTH channels, because the two paths
    surface problems differently: `problem()` feeds the flat coverage layer, while the
    modular CLI scans the emitted text for `% PROBLEM:` markers (`_spec_rules` returns only
    (rules, ops) and discards `out.problems`). A check wired into one path alone silently
    does not run in the other -- which is the root cause of F2, met here a third time.
    """
    members = {en.name: len(en.members) for en in design.enums}
    sigw = {sg.name: sg.irtype.width for sg in design.signals}
    for it in design.comb:
        r = getattr(it, "rhs", None)
        if not isinstance(r, EnumCast):
            continue
        w = sigw.get(getattr(r.operand, "name", None), getattr(r.operand, "width", None))
        n = members.get(r.enum)
        if w is None or n is None or n >= (1 << w):
            continue
        lhs = getattr(it, "lhs", "?")
        why = (f"cast into enum `{r.enum}` is PARTIAL: the operand is {w} bit(s) "
               f"({1 << w} patterns) and the enum has {n} member(s), so an operand value "
               f"with no label leaves `{lhs}` with NO value at that instant and properties "
               f"over it pass vacuously. Give the enum a member for every pattern, or "
               f"narrow/guard the operand")
        out.comment(f"PROBLEM: {why}")          # the marker MODULAR scans for
        out.problem(getattr(it, "loc", None), why)   # the FLAT coverage layer


def _check_comb_loops(text: str, out: "_Out", where: str = "", loc: object = None) -> None:
    """**T2 — the tightness obligation.** A COMBINATIONAL LOOP is a within-time-index cycle:
    `val(p,·,T)` depends on `val(q,·,T)` and back. Synthesis forbids it, and it is the
    precondition the completion route rests on (synthesizable RTL is tight + stratified, so
    the Clark completion's models ARE the stable models). The translator must not report
    success on a design that violates it.

    The design is still fully TRANSLATED -- we report the defect, we do not refuse the input.

    Edges are drawn only between literals at the SAME time term, so a register (head at `T+1`,
    body at `T`) correctly breaks a cycle -- that is exactly how sequential logic makes real
    hardware acyclic. Negative literals are skipped: tightness concerns positive dependencies.

    Signal terms are compared VERBATIM, deliberately. `c(I+1)` depending on `c(I)` is a ripple
    carry -- a legal, founded chain, not a loop -- and normalising lane indices away would
    report every ripple as a defect. The cost is that a cycle passing through DIFFERENT lane
    indices is not reported; those are founded chains in the overwhelming majority of cases."""
    edges = _comb_edges(text)
    # Tarjan-free cycle report: iterative DFS colouring, first cycle per component
    WHITE, GREY, BLACK = 0, 1, 2
    colour: dict[str, int] = {}
    reported: set[frozenset] = set()
    for root in sorted(edges):
        if colour.get(root, WHITE) != WHITE:
            continue
        stack = [(root, iter(sorted(edges.get(root, ()))))]
        path = [root]
        colour[root] = GREY
        while stack:
            node, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                colour[node] = BLACK
                stack.pop()
                path.pop()
                continue
            if colour.get(nxt, WHITE) == GREY:                # back edge -> cycle
                cyc = path[path.index(nxt):] if nxt in path else [nxt]
                key = frozenset(cyc)
                if key not in reported:
                    reported.add(key)
                    out.problem(loc or Loc("<emitted>", 0),
                                f"COMBINATIONAL LOOP{where}: {' -> '.join([*cyc, cyc[0]])} "
                                f"form a cycle within one time index. Synthesis forbids this, "
                                f"and the completion route's soundness rests on the program "
                                f"being tight -- the design is translated, but this must be "
                                f"fixed in the RTL")
            elif colour.get(nxt, WHITE) == WHITE:
                colour[nxt] = GREY
                path.append(nxt)
                stack.append((nxt, iter(sorted(edges.get(nxt, ())))))


def _signed_edges(text: str) -> tuple[dict[tuple, set[tuple]], dict[tuple, set[tuple]]]:
    """The SAME-TIME dependency graph of an emitted program, split by SIGN: ``(pos, neg)``, each
    mapping a head node to the body nodes it reads. A node is a ``(signal term, VALUE)`` pair --
    see `_check_stratified` for why the value matters and why edges stay within one time index.

    Extracted so the STAGE-C generator can obtain the graph the checker actually builds
    (`proofs/gen_strat_lean.py`), like `_comb_edges` and `_classify_rule` before it. Pure
    refactor: `_check_stratified` is its only other caller and its behaviour is unchanged."""
    def parse(lit: str) -> tuple[str, str | None, str] | None:
        s = lit.strip()
        if not s.startswith("val(") or not s.endswith(")"):
            return None
        args = [a.strip() for a in _top_split(s[4:-1])]
        if len(args) == 3:
            term, v, t = args[0], args[1], args[2]
        elif len(args) == 4:
            term, v, t = args[1], args[2], args[3]
        else:
            return None
        return (term, v if re.fullmatch(r'-?\d+|"[^"]*"', v) else None, t)

    pos: dict[tuple, set[tuple]] = {}
    neg: dict[tuple, set[tuple]] = {}
    for rule in _logical_rules(text):
        r = _strip_quoted(rule).strip().rstrip(".")
        head, sep, body = r.partition(":-")
        if not sep:
            continue
        hn = parse(head)
        if hn is None:
            continue
        for lit in _top_split(body):
            s = lit.strip()
            negated = s.startswith("not ")
            bn = parse(s[4:] if negated else s)
            if bn is None or bn[2] != hn[2]:      # different time index -> not a same-step edge
                continue
            (neg if negated else pos).setdefault(hn[:2], set()).add(bn[:2])
    return pos, neg


def _check_stratified(text: str, out: "_Out", where: str = "", loc: object = None) -> None:
    """**The other half of the completion's precondition: STRATIFIED negation.**

    Hard rule 3 keeps design rules positive, and one construct deliberately does not: the
    complement of a lane reduction, `val(hit, 0, T) :- val(match(_), _, T), not val(hit, 1, T)`.
    The positive spelling (every lane reads the other value) computes the same function and
    grounds to the same size, but at 64 lanes it is one 4 KB rule whose meaning is buried in 64
    near-identical atoms -- so the negated form is kept, because reading the emitted model is a
    primary workflow.

    What makes that safe is not its size. It is that the negation is STRATIFIED: `hit`'s
    on-rule does not depend on `hit`, so no negative edge closes a cycle, the program stays
    tight, and Fages still gives completion = stable models. An UNSTRATIFIED negation would
    break exactly that -- `p :- not q. q :- not p.` has two stable models and a completion that
    describes neither faithfully.

    So the rule becomes checkable rather than remembered: every negative literal is an edge, and
    a negative edge inside a cycle is a hard PROBLEM. `_check_comb_loops` deliberately SKIPS
    negative literals (tightness is about positive dependencies); this is the companion check
    that looks at exactly the ones it skips.

    A node is a (signal term, VALUE) pair, not a signal. That distinction is the whole check:
    the ordinary off-set rule `val(x, 0, T) :- .., not val(x, 1, T)` reads as a self-negation at
    signal granularity, and it is not one -- `val(x,0,T)` and `val(x,1,T)` are different atoms,
    and `x`'s 1-rule never mentions `x`'s 0-rule. A VARIABLE value argument (`val(y, V0, T)`) is
    "some value", recorded as `None` and treated as reaching every value of that signal, which
    is the conservative direction.

    Edges are drawn only WITHIN one time index, exactly as `_check_comb_loops` draws them. Every
    negative literal the emitter produces has its head and body at the same `T`, so nothing is
    lost -- and a register (head at `T+1`, body at `T`) cannot close a cycle in the GROUND
    program, since `T` strictly increases along that edge. Ignoring time instead reports every
    ordinary counter as unstratified: `c0@0 :- not c0@1`, `c0@1 :- cnt`, `cnt@T+1 :- c0@0` is a
    cycle on paper and none at all over ground atoms."""
    pos, neg = _signed_edges(text)
    if not neg:
        return                                   # a fully positive design layer: nothing to check
    # A negative edge is unstratified when its target can reach back to the head through ANY
    # edges (positive or negative) -- that is the cycle Fages' theorem does not survive.
    both: dict[tuple, set[tuple]] = {}
    for d in (pos, neg):
        for h, bs in d.items():
            both.setdefault(h, set()).update(bs)
    by_sig: dict[str, set[tuple]] = {}
    for n in {*both, *(b for bs in both.values() for b in bs)}:
        by_sig.setdefault(n[0], set()).add(n)

    def succ(n: tuple) -> set[tuple]:
        # a rule whose head value is a VARIABLE defines every value of that signal, so its
        # body edges apply to each of them
        return both.get(n, set()) | both.get((n[0], None), set())

    ordkey = lambda n: (n[0], n[1] or "")   # noqa: E731 - None sorts before any literal value
    reported: set[tuple] = set()
    for head, targets in sorted(neg.items(), key=lambda kv: ordkey(kv[0])):
        for tgt in sorted(targets, key=ordkey):
            start = by_sig.get(tgt[0], set()) if tgt[1] is None else {tgt}
            seen, stack = set(start), list(start)
            while stack:
                n = stack.pop()
                if n == head:
                    key = (head, tgt)
                    if key not in reported:
                        reported.add(key)
                        out.problem(loc or Loc("<emitted>", 0),
                                    f"UNSTRATIFIED NEGATION{where}: val({head[0]}, {head[1]}) "
                                    f"depends on not val({tgt[0]}, {tgt[1]}), which depends back "
                                    f"on it. Stratified negation is what lets the design layer "
                                    f"use `not` at all (the completion still characterises the "
                                    f"stable models); a negative edge inside a cycle breaks that")
                    break
                for m in sorted(succ(n), key=ordkey):
                    if m not in seen:
                        seen.add(m)
                        stack.append(m)


def _check_safety(text: str, out: "_Out", where: str = "", loc: object = None) -> None:
    """Every emitted rule must be groundable. An unsafe rule makes the WHOLE program unusable,
    so this is a hard PROBLEM -- the translator must never report success on a program clingo
    will refuse (hard rule 2: a clean run means complete AND usable). This is the check that
    would have caught Fix 51 at translation time instead of at grounding time."""
    for rule in _logical_rules(text):
        bad = _unsafe_vars(rule)
        if bad:
            out.problem(loc or Loc("<emitted>", 0),
                        f"UNSAFE RULE{where}: variable(s) {', '.join(sorted(bad))} are not "
                        f"bound by any positive body literal, so clingo cannot ground this "
                        f"rule -- {rule[:110]}")


# atoms that DECLARE a signal: the name is always the first argument. `element_type` is absent
# on purpose -- its first argument is a TYPE name, not a signal. The captured name is the ROOT of
# that argument, because a declaration may carry a FUNCTOR term: a struct has no atom of its own
# and is declared field-by-field (`type(p(hi), bit, 4)`), so matching only a bare name would call
# every read of an input struct underivable.
_DECL_ATOMS = ("type", "array", "port", "reg", "param", "dims", "latch")
_DECL_RE = re.compile(r"^\s*(?:" + "|".join(_DECL_ATOMS) + r")\(\s*([a-z_][A-Za-z0-9_]*)")


def _root_of(term: str) -> str:
    """The signal ROOT of a `val` signal term: `y` / `y(I)` / `p(fld)` / `mem(A)` -> `y`,`y`,`p`,`mem`."""
    return term.split("(", 1)[0].strip()


def _check_underivable_reads(text: str, out: "_Out", where: str = "", loc: object = None) -> None:
    """Every atom a rule READS must be capable of having a value: declared, or derived by some
    rule's head. A read of neither can NEVER fire, so the rule is dead -- and its companion
    off-rule then fires unconditionally, silently pinning the signal.

    This is the gate that was missing when Fix 95 was found. `_check_safety` asks whether a rule
    can be GROUNDED and says yes here: `val(cnt, V1, T)` is a perfectly good positive literal
    that binds `V1`. Nothing asked whether `cnt` was a name the program could ever derive. A
    clean run has to mean USABLE, not merely groundable (hard rule 2), so this is a PROBLEM.

    Deliberately conservative in three ways, because a false alarm here fails a correct design:
      * only CONSTANT roots (lowercase) -- a variable signal term is a schema-driven read;
      * only POSITIVE body literals -- an underivable atom under `not` is the exception-net
        pattern (`_guard`), where absence is exactly the point;
      * a name DECLARED but underived is fine (a free input is read, never written)."""
    declared: set[str] = set()
    derived: set[str] = set()
    reads: list[tuple[str, str]] = []
    for rule in _logical_rules(text):
        r = _strip_quoted(rule).strip().rstrip(".")
        m = _DECL_RE.match(r)
        if m:
            declared.add(m.group(1))
            continue
        head, sep, body = r.partition(":-")
        h = _val_term_time(head)
        if h is not None:
            derived.add(_root_of(h[0]))
        if not sep:
            continue
        for lit in _top_split(body):
            if lit.strip().startswith("not "):
                continue                       # NAF: absence is the point, not a defect
            b = _val_term_time(lit)
            if b is not None:
                reads.append((_root_of(b[0]), rule))
    for root, rule in reads:
        if root and root[0].islower() and root not in declared and root not in derived:
            out.problem(loc or Loc("<emitted>", 0),
                        f"UNDERIVABLE READ{where}: `{root}` is read but is neither declared nor "
                        f"derived by any rule, so this rule can never fire -- {rule[:110]}")


def emit(design: Design, analysis: Analysis, *, k: int = 8, style: str = "v1",
         default_init: bool = False, problems: list | None = None,
         primary_clock: str | None = None,
         clock_hierarchy: dict | None = None) -> str:
    """The design's TRANSITION RELATION as ASP -- and, since F4, nothing else.

    `default_init` is OFF, and that is the F4 decision rather than a defaulting choice: the
    translation says what the design DOES, not where it starts. An init-free program is a
    transition relation, which is the object the completion and Lean routes want, and a
    property can then quantify over power-on ("for all initial states, P") instead of
    inheriting one baked-in start. Initial state is a separate artifact -- `__xinit.lp` for the
    symbolic range, `__init0.lp` for a concrete test vector -- and both are replaceable.

    It survives as a parameter for the RESET-SNAPSHOT route only, which solves the design
    forward from a concrete start to recover the post-reset state and therefore needs one."""
    ch = dict(clock_hierarchy) if clock_hierarchy else {}   # normalise: None -> {}
    global_tick = "time(T)" if ch else "gtime(T)"          # hold/no_tick base
    shapes = analysis.shape
    widths = {s.name: s.irtype.width for s in design.signals}  # for all-ones in &x reduction
    lane_dims = dict(design.lane_dims)                          # genvar-indexed signal -> # of dims
    lane_elem_w = dict(design.lane_elem_w)                      # lane signal -> per-lane element width
    lane_signals = list(design.lane_signals)                   # signals with a per-lane form (+ bitvec)
    for v in design.vffs:                                       # VFF ports are single-index lanes
        for name in ((v.en,) if getattr(v, "en_lane", True) else ()) + (v.d, v.q):
            lane_dims.setdefault(name, 1)                        # a broadcast enable is a scalar, not a lane
    # --bitvec: fold the per-bit signals into the LOCAL lane bookkeeping (design stays frozen). Each
    # chosen signal becomes a 1-wide-lane signal, so the existing lane<->word bridge (assemble the word
    # for arithmetic/compare consumers) and per-lane rules apply with no new bridge code.
    # For wide-lane bitvec signals (phase 5: generate-for with elem_w>1), preserve the original elem_w
    # so _emit_comb can set _lane_prefix="I" for 2-D head functors.
    for name in analysis.bitvec_signals:
        lane_dims[name] = 1
        if lane_elem_w.get(name, 1) <= 1:   # scalar bitvec: set elem_w=1 as before
            lane_elem_w[name] = 1
        # wide-lane bitvec (elem_w>1): keep original elem_w; bridge still works (treats each bit as a lane)
        if name not in lane_signals:
            lane_signals.append(name)
    out = _Out()
    out.used.bit_atoms = getattr(shapes, "bit_atoms", frozenset())     # F32: the word reader's facts,
    out.used.widths = widths                                            # on the set every ctx carries
    out.used.budget_bits = getattr(shapes, "budget_bits", 20)
    _check_partial_enum_cast(design, out)   # F3 -- in BOTH emitters
    _check_mem_addr_range(design, out)      # F5 -- likewise
    clocks_all = ({it.clock for it in design.seq if not it.combinational}
                  | {w.clock for w in design.mem_writes if w.clock})   # "" = combinational memory
    real_clocks = {c for c in clocks_all if c}
    derived = {dc.name for dc in design.derived_clocks}
    # the master clock is the declared primary_clock (a free-running input, not a gated/derived one);
    # else the alphabetically-first real clock. Used for the CLOCK/HORIZON section + the scenario stub.
    if primary_clock and primary_clock in real_clocks and primary_clock not in derived:
        clk = primary_clock
    else:
        clk = sorted(clocks_all)[0] if clocks_all else "clk"

    # schema (full Stage-1: module, params, per-signal type + port/reg, clock/reset, memory)
    out.section("SCHEMA")
    # legend -- the field layout of each schema atom (comments only; no effect on solving)
    for line in (
        "LEGEND -- fields of each schema atom (comments only):",
        "  module(Name)   param(Name, Value)   enum_value(EnumType, Label, Value)",
        "  type(Sig, Kind, Width)               -- Kind: bit | signed | enum (Width = flattened bits)",
        "  dims(Sig, K(N), ..)  K = packed(W) (bits in the word) | unpacked(N) (addressed cells); "
        "outer-to-inner",
        "  decl_type(Sig, SvBase, Width, State) -- declared SV type; State: two_state | four_state",
        "  port(Sig, Dir, Module)               -- Dir: input | output | inout",
        "  reg(Sig)   clock(Sig, Clk)   reset(Sig, RstSig, active_low | active_high)",
        "  lane(Owner, 0..N-1)   -- lane signal: val(Sig(I), V, T) (lane I inside the functor); "
        "lane_shape(Sig, lanes(N), width(W))",
        "  element_type(Elem, Kind, W)   "
        "array(Mem, Elem, unpacked, addr_w(W)[, addr_w(W2)])   addr(Mem, A[, A2])",
        "  cell(Inst, CellType, Parent)         -- instance Inst of cell/module CellType under Parent",
        "  (@func ops -- @add/@slc/@wcmp/... -- are listed in the @func LEGEND above the #script block)",
    ):
        out.comment(line)
    out.blank()
    out.rule(f"module({design.name})")
    for p in design.params:
        if p.value is None:
            continue   # a non-constant-foldable param has no schema value (folded at use, or flagged)
        # a WIDE parameter/localparam value (>= 2^31) is a canonical String, else clingo's 32-bit
        # parse would silently wrap the schema atom (e.g. a 64-bit localparam 2^33 -> 0).
        out.rule(f"param({p.name}, {_const_lit(p.value)})")
    # enum types: tag domain + encoding (catalog §3.6). The state machine ranges over these.
    for en in design.enums:
        for label, value in en.members:
            out.rule(f"enum_value({en.name}, {label}, {value})")
    # every signal gets a type/3 (incl. 1-bit); ports carry direction; regs marked
    for s in design.signals:
        if s.enum_type is not None:
            out.rule(f"type({s.name}, enum, {s.enum_type})")
        else:
            out.rule(f"type({s.name}, {s.irtype.kind.value}, {s.irtype.width})")
        # provenance: the declared SV type (base keyword / typedef name + 2-state vs 4-state) that
        # the interpretation kind/width above collapses (logic[7:0] and bit[7:0] both -> bit, 8).
        if s.irtype.sv_base:
            state = "four_state" if s.irtype.four_state else "two_state"
            out.rule(f"decl_type({s.name}, {s.irtype.sv_base}, {s.irtype.width}, {state})")
        if s.is_port and s.direction:
            out.rule(f"port({s.name}, {s.direction}, {design.name})")
        if s.is_reg:
            out.rule(f"reg({s.name})")
        # dimensional shape, unified across packed & unpacked: dims(Sig, <kind>(N), ...) outer-to-inner,
        # each dim tagged packed(W) (bits within the word) or unpacked(N) (separate addressed cells).
        # Packed multi-D (logic[3:0][7:0] -> dims(s, packed(4), packed(8))) records the shape the
        # flattened type/3 width collapses; lane signals self-describe via lane_shape, so skip them.
        pd = design.packed_dims.get(s.name)
        if pd and s.name not in design.lane_signals:
            out.rule(f"dims({s.name}, {', '.join(f'packed({d})' for d in pd)})")
    # clock domain per stateful signal
    clk_seen: set[str] = set()
    for it in design.seq:
        if not it.combinational and it.reg not in clk_seen:  # always_comb signals have no clock
            out.rule(f"clock({it.reg}, {it.clock})")
            clk_seen.add(it.reg)
    for w in design.mem_writes:
        if w.clock and w.mem not in clk_seen:   # a combinational memory (clock="") has no clock fact
            out.rule(f"clock({w.mem}, {w.clock})")
            clk_seen.add(w.mem)
    # reset path per reset register
    rst_seen: set[str] = set()
    for it in design.seq:
        if it.reset is not None and it.reg not in rst_seen:
            out.rule(f"reset({it.reg}, {it.reset.signal}, active_{it.reset.active})")
            rst_seen.add(it.reg)
    # array-instance lane domains: lane(owner, 0..N-1[, 0..M-1]) fans the array index(es) (the lane(s)).
    # An N-D nested generate of instances (`for(i) for(j) sub u(.x(a[i][j]))`) has one range per genvar.
    for owner, dims in sorted(design.lane_domains.items()):
        out.rule(f"lane({owner}, {', '.join(f'0..{n - 1}' for n in dims)})")
    # lane<->word boundary bridge (#8): a lane signal may also be driven/read as a WORD.
    by_name = {s.name: s for s in design.signals}
    _emit_lane_word_bridge(out, lane_signals, shapes, by_name, lane_dims, lane_elem_w, widths,
                           analysis.bitvec_signals, analysis.bitvec_word_consumers,
                           analysis.bitvec_word_form, design.packed_dims)
    # memory schema. N-D unpacked array -> one addr_w per dimension + a 2..N-arg addr domain.
    for m in design.mems:
        dims = m.dims or (m.depth,)
        out.rule(f"reg({m.name})")
        out.rule(f"element_type({m.elem.name}, {m.elem.kind.value}, {m.elem.width})")
        aws = ", ".join(f"addr_w({max(1, (n - 1).bit_length())})" for n in dims)
        out.rule(f"array({m.name}, {m.elem.name}, unpacked, {aws})")
        # unified shape view: the unpacked dimension COUNTS + the packed element width (>1) -- the same
        # dims/N vocabulary as a packed matrix, so a consumer reads any signal's shape one way.
        ud = ", ".join(f"unpacked({n})" for n in dims)
        ew = f", packed({m.elem.width})" if m.elem.width > 1 else ""
        out.rule(f"dims({m.name}, {ud}{ew})")
        avars = ["A"] if len(dims) == 1 else [f"A{p + 1}" for p in range(len(dims))]
        dom = ", ".join(f"{v} = 0..{n - 1}" for v, n in zip(avars, dims, strict=True))
        out.rule(f"addr({m.name}, {', '.join(avars)})", [dom])  # per-memory address domain
    # structural instance manifest: every instantiated cell/submodule, its (lowercased) cell type,
    # and its parent module -- recovers the instance->celltype structure that flattening discards
    # (the behaviour rules stay flattened). A future cell_out(Inst, Net) could add the driven-net link.
    for c in design.cells:
        out.rule(f"cell({c.inst}, {c.cell_type}, {c.parent})")
    out.blank()

    # clock / horizon -- the RUN length is NOT part of the design.
    # The scenario/harness (or `clingo -c k=N`) supplies `#const k.` and `time(clk,0..k).`
    # so the same design runs at any horizon without re-translation.
    out.section("CLOCK / HORIZON  (supplied by the run: #const k. + time(clk,0..k).)")
    if ch:
        out.comment("Scenario supplies only:  #const k = N.  time(0..k).")
        out.comment("Clock derivation rules are emitted by the translator (see CLOCK DERIVATION below).")
    if primary_clock and primary_clock != clk:   # declared but not a usable free master here -- surface it
        out.comment(f"NOTE: declared primary_clock '{primary_clock}' is not a free clock here "
                    f"(clocks: {sorted(real_clocks) or 'none'}); master falls back to {clk}")
    if len(real_clocks) > 1 and not ch:
        out.comment(f"MASTER clock = {clk}{' (declared primary_clock)' if primary_clock == clk else ''}"
                    " -- drive time(<master>,0..k) every step; derive the others as sub-rates of it")
    for c in sorted(clocks_all):
        out.comment(f"design references time({c}, T) and the bound T < k")
    # the full clock structure, collected up front (like params) so the run knows every domain: which
    # clocks are FREE (driven by the scenario) vs GATED (derived from a free clock by a 1-bit enable).
    if design.clocks:
        out.comment("CLOCKS (the design's full clock structure):")
        for ck in design.clocks:
            if ck.derived:
                out.comment(f"  {ck.name}  -- gated from {ck.base} by {ck.gate} (derive; do NOT drive)")
            elif ck.name in ch:
                out.comment(f"  {ck.name}  -- derived from clock_hierarchy (do NOT drive)")
            else:
                out.comment(f"  {ck.name}  -- free (drive time({ck.name}, 0..k) in the scenario)")
    out.blank()

    # derived (gated) clocks from ICG primitives: a gated clock is its own clock DOMAIN that ticks only
    # on the cycles where the gate is high (§6.7). A flop on it then advances only then and HOLDS between
    # edges via the master-tick linkage above. (Selection is automatic: an ICG primitive -> a clock domain
    # here; a flop/FF `en` pin -> a flop enable, NOT here.)
    if design.derived_clocks:
        out.section("DERIVED (GATED) CLOCKS  (ICG clock gating, §6.7: time(gclk):-time(clk),val(en,1))")
        out.comment("no_tick(gclk,T): positive witness that the gated clock did NOT tick at T.")
        out.comment("  Derived via a single isolated NAF rule; hold rules read no_tick positively.")
        for dc in design.derived_clocks:
            if getattr(dc, "kind", "gate") == "rise":
                out.comment(_prov(dc.loc, f"edge-derived clock {dc.name}: an internal register "
                                          f"output used as a clock (F27); ticks across its own "
                                          f"0->1 transitions on {dc.base}'s axis"))
                out.rule(f"time({dc.name}, T)",
                         [f"time({dc.base}, T)", f"val({dc.name}, 0, T)", f"val({dc.name}, 1, T+1)"])
            else:
                out.comment(_prov(dc.loc, f"gated clock {dc.name} = {dc.base} gated by {dc.gate}"))
                out.rule(f"time({dc.name}, T)", [f"time({dc.base}, T)", f"val({dc.gate}, 1, T)"])
            # when clock_hierarchy is active, no_tick base is time(T); else the derived clock's base
            no_tick_base = "time(T)" if ch else f"time({dc.base}, T)"
            out.rule(f"no_tick({dc.name}, T)", [no_tick_base, f"not time({dc.name}, T)"])
        out.blank()

    # Clock derivation rules from sources.json clock_hierarchy.
    # Each entry derives a clock domain from its parent at a given divisor.
    # "base": "time" means the clock runs at the global rate (time(T)).
    # "base": "parent", "div": N  means: tick every N-th parent tick (T \ N == 0).
    if ch:
        out.section("CLOCK DERIVATION (frequency hierarchy from sources.json clock_hierarchy)")
        out.comment("Derived from the global time axis.  Scenario: #const k = N.  time(0..k).")
        for clk_name, entry in ch.items():
            base = entry.get("base", "time")
            div  = int(entry.get("div", 1))
            if base == "time":
                out.rule(f"time({clk_name}, T)", ["time(T)"])
            elif div == 1:
                out.rule(f"time({clk_name}, T)", [f"time({base}, T)"])
            else:
                out.rule(f"time({clk_name}, T)", [f"time({base}, T)", f"T \\ {div} == 0"])
        out.blank()

    # Multiple free clocks: if two clocks have no ICG/derived relationship, the scenario
    # must drive each one explicitly.  We emit a comment listing them so the scenario author
    # knows what to provide.  Do NOT auto-alias them — that would override independent gating
    # (e.g. clk vs gclk in a clock_gating demo where the scenario controls gclk separately).
    # If two clocks genuinely run at the same rate with no relationship, add the alias rule
    # manually in the scenario:  time(clk_B, T) :- time(clk_A, T).
    free_clocks = sorted(real_clocks - {dc.name for dc in design.derived_clocks})
    if len(free_clocks) > 1:
        out.section("FREE CLOCKS  (no ICG relation detected between these; scenario must drive each)")
        out.comment("Drive each free clock independently in the scenario:")
        for c in free_clocks:
            out.comment(f"  time({c}, 0..k)  -- free clock, no derived relationship")
        out.comment("If two clocks are co-incident (same rate/phase), alias in the scenario:")
        out.comment("  time(clk_B, T) :- time(clk_A, T).")
        out.blank()

    # combinational
    out.section(f"COMBINATIONAL (Group 1)  [style={style}]")
    has_clock = bool(clocks_all)
    # comb_defs: map signal name → its RHS Expr for transparent copy elimination in bitvec flatten.
    # Signals with exactly one comb driver are included; multi-driver and no-driver signals excluded.
    _comb_driver_counts: dict[str, int] = {}
    for _ci in design.comb:
        _comb_driver_counts[_ci.lhs] = _comb_driver_counts.get(_ci.lhs, 0) + 1
    comb_defs: dict[str, "Expr"] = {_ci.lhs: _ci.rhs for _ci in design.comb
                                    if _comb_driver_counts.get(_ci.lhs, 0) == 1}
    # enum-typed signals: their value is a TAG, so reading one numerically needs the
    # `enum_value` conversion rather than a copy (Fix 76)
    enum_of: dict[str, str] = {s_.name: s_.enum_type for s_ in design.signals
                               if s_.enum_type is not None}
    for item in design.comb:
        _guard(out, item.loc, f"combinational {item.lhs}",
               lambda item=item: _emit_comb(item, shapes, out, style, clk, has_clock, widths, lane_dims,
                                            lane_elem_w, analysis.bitvec_signals,
                                            analysis.bitvec_word_consumers, comb_defs,
                                            packed_dims=design.packed_dims, enum_of=enum_of,
                                            bitvec_word_form=analysis.bitvec_word_form))
    for item in design.muxes:
        _guard(out, item.loc, f"mux {item.out}", lambda item=item: _emit_mux(item, out, widths))
    for item in design.latches:
        _guard(out, item.loc, f"latch {item.q}", lambda item=item: _emit_latch(item, out))
    for item in design.inferred_latches:
        _guard(out, item.loc, f"inferred latch {item.lhs}",
               lambda item=item: _emit_inferred_latch(item, out, default_init))
    out.blank()

    # sampled-value EDGE functions ($rose/$fell): a two-time-point test, so neither a
    # combinational rule (same instant) nor a register (own state).
    for ed in design.edges:
        _guard(out, ed.loc, f"edge {ed.lhs}", lambda ed=ed: _emit_edge(ed, out))
    if design.edges:
        out.blank()

    # sequential
    out.section("SEQUENTIAL (Group 2)")
    for item in design.seq:
        _guard(out, item.loc, f"register {item.reg}",
               lambda item=item: _emit_seq(item, out, shapes, lane_dims, widths,
                                                  bitvec_signals=analysis.bitvec_signals,
                                                  lane_elem_w=lane_elem_w))
    for item in design.vffs:
        _guard(out, item.loc, f"vff {item.q}", lambda item=item: _emit_vff(item, out))
    out.blank()

    # memory: sequential writes emit per-write; combinational writes to one memory are emitted
    # together (a default + override must reconcile to a single value -- see _emit_comb_mem).
    out.section("MEMORY (Section 2.9)")
    comb_mem: dict[str, list] = {}
    seq_mem: dict[str, list] = {}
    for w in design.mem_writes:
        (comb_mem if w.clock == "" else seq_mem).setdefault(w.mem, []).append(w)
    for mem, ws in seq_mem.items():
        if len(ws) == 1:
            _guard(out, ws[0].loc, f"memory {mem}",
                   lambda w=ws[0]: _emit_mem_write(w, out, default_init, shapes, design.lane_dims))
        else:   # multiple write ports -> coordinate (last-write-wins + one joint hold)
            _guard(out, ws[0].loc, f"memory {mem}",
                   lambda mem=mem, ws=ws: _emit_mem_multi(mem, ws, out, default_init, shapes, design.lane_dims))
    for mem, ws in comb_mem.items():
        _guard(out, ws[0].loc, f"comb memory {mem}",
               lambda mem=mem, ws=ws: _emit_comb_mem(mem, ws, out, shapes, design.lane_dims))
    out.blank()

    # multi-clock: link slower clock domains to the fastest via a global tick line + per-state holds.
    _emit_multiclock(design, shapes, lane_dims, out, global_tick=global_tick, bitvec_signals=analysis.bitvec_signals)

    # project-local FUNCTIONAL STUBS (sources.json `stubs`): verbatim hand-written ASP replacing a
    # submodule's implementation. Emitted as-is; the port bridges live in design.comb (already above).
    if design.stub_rules:
        out.section("FUNCTIONAL STUBS (hand-written models; sources.json `stubs`)")
        for line in design.stub_rules:
            out.lines.append(line)
        out.blank()
        # a stub may call @func ops not otherwise used -> register them so the #script block defines them.
        _stub_funcs = set(re.findall(r'@([a-z][a-z0-9]*)\s*\(', "\n".join(design.stub_rules)))
        for fn in _stub_funcs:
            # Map the emitted @-name back to its library key. DERIVED from the legend
            # (emit/lib.KEY_OF_EMITTED), not a hand-written table: a builtin whose emitted name
            # differs from its key would otherwise fail to register the moment someone forgot to
            # extend the table, and the stub would reference an undefined @func at grounding
            # time. A name that is not a builtin is left as-is (a site-plugin func).
            out.used.add(_lib_names.key_of_emitted(fn) or fn)

    resolve_deferred_words(out, getattr(shapes, "budget_bits", 20))   # F32: after every rule is written
    _check_safety("\n".join(out.lines), out,          # groundable, or a hard problem
                  loc=Loc(f"<{design.name}>", 0))
    _check_stratified("\n".join(out.lines), out,      # the design layer's `not` stays stratified
                      loc=Loc(f"<{design.name}>", 0))
    _check_comb_loops("\n".join(out.lines), out,      # T2: tight, or a hard problem
                      loc=Loc(f"<{design.name}>", 0))
    _check_underivable_reads("\n".join(out.lines), out,   # every read can have a value (Fix 95)
                             loc=Loc(f"<{design.name}>", 0))
    if problems is not None:
        problems.extend(out.problems)
    # assemble: @func legend + script block first, then body
    script = render_script(out.used)
    legend = func_legend(out.used)
    legend_block = ("\n".join(legend) + "\n") if legend else ""
    header = (
        f"% Auto-generated by sv2asp from {design.name} "
        f"(design layer only; scenario + properties hand-authored).\n"
    )
    return header + legend_block + ("\n" + script + "\n" if script else "") + "\n".join(out.lines) + "\n"


# Clark/HLR completion (Route 2) is a TRANSFORM on this emit() output -- see sv2asp.completion
# (completion_asp / completion_smt), wired in cli.py.


# --------------------------------------------------------------------------
# MODULAR emit (--mode modular): each module translated ONCE (per param-tuple) into rules
# parameterised by an instance variable I, + an instance manifest that links them. Reuses the
# flat behaviour helpers, then rewrites every val/4 atom to carry the leading instance term.
# --------------------------------------------------------------------------
# The flat -> per-instance rule lift (the "RuleSink" seam) lives in emit/sink.py so the transform that
# makes modular byte-identical to flat is a single, named, documented unit. Alias kept for call sites.
_instance_index = _sink_instance_index


def _spec_base_clock(design: Design) -> str:
    """The spec's FREE base clock (the one resolved per instance via clkof) -- a derived/gated clock
    name is never the base. Considers every clocked element (registers, MEMORY writes, VFFs -- a
    memory-only module has empty design.seq). Falls back to 'clk' for a combinational-only spec."""
    derived = {dc.name for dc in design.derived_clocks}
    clocked = {it.clock for it in design.seq if not it.combinational and it.clock}
    clocked |= {w.clock for w in design.mem_writes if w.clock}
    clocked |= {it.clock for it in design.vffs if it.clock}
    cl = sorted(c for c in clocked if c not in derived)
    return cl[0] if cl else "clk"


def _spec_rules(design: Design, spec: str, *, bitvec: bool = False) -> tuple[list[str], set[str], list[str]]:
    """Emit one spec's OWN behaviour (its assigns/always/primitives), instance-parameterised."""
    analysis = analyze(design, bitvec=bitvec)
    shapes = analysis.shape
    widths = {s.name: s.irtype.width for s in design.signals}
    lane_dims = dict(design.lane_dims)
    lane_elem_w = dict(design.lane_elem_w)
    lane_signals = list(design.lane_signals)
    for name in analysis.bitvec_signals:               # --bitvec: fold into local lane bookkeeping
        lane_dims[name] = 1
        if lane_elem_w.get(name, 1) <= 1:            # scalar bitvec: elem_w=1; wide-lane: preserve
            lane_elem_w[name] = 1
        if name not in lane_signals:
            lane_signals.append(name)
    out = _Out()
    out.used.bit_atoms = getattr(shapes, "bit_atoms", frozenset())     # F32: the word reader's facts,
    out.used.widths = widths                                            # on the set every ctx carries
    out.used.budget_bits = getattr(shapes, "budget_bits", 20)
    _check_partial_enum_cast(design, out)   # F3 -- in BOTH emitters
    _check_mem_addr_range(design, out)      # F5 -- likewise
    clocks_all = {it.clock for it in design.seq if not it.combinational and it.clock}
    clk = _spec_base_clock(design)
    has_clock = bool(clocks_all)
    _comb_driver_counts_s: dict[str, int] = {}
    for _ci in design.comb:
        _comb_driver_counts_s[_ci.lhs] = _comb_driver_counts_s.get(_ci.lhs, 0) + 1
    comb_defs_s: dict[str, "Expr"] = {_ci.lhs: _ci.rhs for _ci in design.comb
                                      if _comb_driver_counts_s.get(_ci.lhs, 0) == 1}
    enum_of_s: dict[str, str] = {s_.name: s_.enum_type for s_ in design.signals
                                 if s_.enum_type is not None}
    for item in design.comb:
        _guard(out, item.loc, f"comb {item.lhs}",
               lambda item=item: _emit_comb(item, shapes, out, style="v1", clk=clk,
                                             has_clock=has_clock, widths=widths, lane_dims=lane_dims,
                                             lane_elem_w=lane_elem_w,
                                             bitvec_signals=analysis.bitvec_signals,
                                             bitvec_word_consumers=analysis.bitvec_word_consumers,
                                             comb_defs=comb_defs_s, enum_of=enum_of_s,
                                             bitvec_word_form=analysis.bitvec_word_form,
                                          packed_dims=design.packed_dims))
    for item in design.muxes:
        _guard(out, item.loc, f"mux {item.out}", lambda item=item: _emit_mux(item, out, widths))
    for item in design.latches:
        _guard(out, item.loc, f"latch {item.q}", lambda item=item: _emit_latch(item, out))
    for item in design.inferred_latches:
        # F13: this read a name that is not bound in this function, so `_guard` turned EVERY
        # inferred latch in the DEFAULT compile into `% UNSUPPORTED (... NameError ...)` and the
        # construct was never lowered -- flat emitted it, modular did not. Hardcoded to match
        # the flat default, exactly as the two memory call sites below already are. The
        # two-emitter split (hard rule 1) producing the same class of bug a fifth time.
        _guard(out, item.loc, f"inferred latch {item.lhs}",
               lambda item=item: _emit_inferred_latch(item, out, False))
    # F2: sampled-value EDGE functions ($rose/$fell). This loop did not exist, so modular
    # emitted the CONSUMER (`val(Inst, pulse, V0, T+1) :- ... val(Inst, sig__rose, V0, T)`) and
    # nothing that derives `sig__rose` -- the signal had no value at any instant and every
    # property over it passed vacuously. Same emitter as flat; the instance lift and the
    # per-instance clock resolution (`time(clk, T)` -> `clkof(Inst, clk, CK), time(CK, T)`) are
    # the sink's job, which is why one shared `_emit_edge` is all this needs.
    for ed in design.edges:
        _guard(out, ed.loc, f"edge {ed.lhs}", lambda ed=ed: _emit_edge(ed, out))
    for item in design.seq:
        _guard(out, item.loc, f"reg {item.reg}",
               lambda item=item: _emit_seq(item, out, shapes, lane_dims, widths,
                                                  bitvec_signals=analysis.bitvec_signals,
                                                  lane_elem_w=lane_elem_w))
    for item in design.vffs:
        _guard(out, item.loc, f"vff {item.q}", lambda item=item: _emit_vff(item, out))
    # memory: the SAME init/write/hold emission as flat, instance-parameterised. The cell value carries
    # the instance (val(I, mem(A), V, T)); the address DOMAIN and per-cell HOLD are instance-qualified by
    # _instance_index. Combinational vs sequential writes split exactly as in the flat MEMORY section.
    comb_mem: dict[str, list] = {}
    seq_mem: dict[str, list] = {}
    for w in design.mem_writes:
        (comb_mem if w.clock == "" else seq_mem).setdefault(w.mem, []).append(w)
    # F4: no `val(Inst, mem(A), 0, 0)`. These two were HARDCODED `True` while flat's came from
    # `emit`'s parameter, which is why F4's first attempt fixed flat only -- the two-emitter
    # split (hard rule 1) again. There is no parameter to thread now: the modular route has no
    # reset-snapshot mode, so the answer is False unconditionally, in both call sites.
    for mem, ws in seq_mem.items():
        if len(ws) == 1:
            _guard(out, ws[0].loc, f"memory {mem}",
                   lambda w=ws[0]: _emit_mem_write(w, out, False, shapes, lane_dims))
        else:
            _guard(out, ws[0].loc, f"memory {mem}",
                   lambda mem=mem, ws=ws: _emit_mem_multi(mem, ws, out, False, shapes, lane_dims))
    for mem, ws in comb_mem.items():
        _guard(out, ws[0].loc, f"comb memory {mem}",
               lambda mem=mem, ws=ws: _emit_comb_mem(mem, ws, out, shapes, lane_dims))
    # lane<->word bridge (shared with flat emit), so a bitvec / lane signal read as a whole word
    # assembles here too. Emitted into out.lines -> Inst-rewritten below (the rules are plain val/@func).
    by_name = {s.name: s for s in design.signals}
    _emit_lane_word_bridge(out, lane_signals, shapes, by_name, lane_dims, lane_elem_w, widths,
                           analysis.bitvec_signals, analysis.bitvec_word_consumers,
                           analysis.bitvec_word_form, design.packed_dims)
    resolve_deferred_words(out, getattr(shapes, "budget_bits", 20))   # F32: every rule is written by here
    derived = frozenset(dc.name for dc in design.derived_clocks)
    # Keep the provenance comments (% file:line) and block spacing the per-construct emit already produced
    # (hard rule 7: every rule traces to its SV source) -- only the RULE lines get instance-parameterised;
    # comment/blank lines pass through verbatim. This makes the modular spec as legible as the flat .lp.
    rules = [ln if (not ln or ln.startswith("%")) else _instance_index(ln, spec, derived)
             for ln in out.lines]
    # per-instance memory address domain: addr(Inst, mem, A) :- isa(Inst, spec), A = 0..N-1 (the one
    # load-bearing memory schema fact -- the init/hold rules fan over it). Multi-dim arrays get one A-var
    # per dimension; the index vars are I/J… and never collide with the instance var Inst.
    if design.mems:
        rules.append("% per-instance memory address domain (one cell family per address)")
    for m in design.mems:
        dims = m.dims or (m.depth,)
        avars = ["A"] if len(dims) == 1 else [f"A{p + 1}" for p in range(len(dims))]
        dom = ", ".join(f"{v} = 0..{n - 1}" for v, n in zip(avars, dims, strict=True))
        rules.append(f"addr(Inst, {m.name}, {', '.join(avars)}) :- isa(Inst, {spec}), {dom}.")
    # per-instance array-instance LANE domain: lane(Inst, owner, K) :- isa(Inst, spec), K = 0..N-1. Only
    # array-of-instances lanes (`sub u[N]`) need the fact -- VFF and genvar lanes fan over operand reads.
    if design.lane_domains:
        rules.append("% per-instance array-instance lane domain (one lane index per generate genvar)")
    for owner, dims in sorted(design.lane_domains.items()):
        kvars = [f"K{i + 1}" for i in range(len(dims))] if len(dims) > 1 else ["K"]
        dom = ", ".join(f"{k} = 0..{n - 1}" for k, n in zip(kvars, dims, strict=True))
        rules.append(f"lane(Inst, {owner}, {', '.join(kvars)}) :- isa(Inst, {spec}), {dom}.")
    # per-instance derived (gated) clock domains (ICG, §6.7): the gated clock ticks on the cycles where
    # this instance's gate is high. The base is the instance's own (free) clock domain via clkof, so the
    # SAME spec at two instances yields two distinct gated ticks (each gated by that instance's enable).
    for dc in design.derived_clocks:
        if getattr(dc, "kind", "gate") == "rise":
            rules.append(f"time({dc.name}(Inst), T) :- isa(Inst, {spec}), clkof(Inst, {dc.base}, CK), "
                         f"time(CK, T), val(Inst, {dc.name}, 0, T), val(Inst, {dc.name}, 1, T+1).")
        else:
            rules.append(f"time({dc.name}(Inst), T) :- isa(Inst, {spec}), clkof(Inst, {dc.base}, CK), "
                         f"time(CK, T), val(Inst, {dc.gate}, 1, T).")
    # project-local functional stubs (sources.json `stubs`): emit into the spec.
    # In modular mode the stub rules were written (and @INST@ substituted) in flat 3-arg style:
    #   val(inst_sig(port), V, T) :- val(inst_sig(port2), V2, T), ...
    # They must be promoted to the 4-arg modular form:
    #   val(Inst, inst_sig(port), V, T) :- isa(Inst, spec), val(Inst, inst_sig(port2), ...), ...
    # We detect stub signals by their functor shape — `word(word` — and prefix `Inst,`.
    if design.stub_rules:
        rules.append("% FUNCTIONAL STUBS (hand-written models; sources.json `stubs`)")
        # Promote stub rules from flat 3-arg to modular 4-arg form.
        # Stub rules use val(inst_sig(port), V, T) — a functor as the first arg.
        # In modular mode these must become val(Inst, inst_sig(port), V, T) with isa(Inst,spec).
        # Each element of design.stub_rules may be a multi-line string; process rule-by-rule.
        _stub_val = re.compile(r'\bval\(([a-z][a-z0-9_]*\([^)]*\))')
        def _promote_stub_block(block: str) -> str:
            """Promote all rules in a (possibly multi-line) stub block to 4-arg modular form."""
            out_lines: list[str] = []
            for ln in block.splitlines():
                # Comment lines pass through unchanged.
                stripped = ln.lstrip()
                if not stripped or stripped.startswith("%"):
                    out_lines.append(ln)
                    continue
                # A rule: contains :- somewhere (possibly mid-line).
                # Only the HEAD before :- gets its val promoted; body gets val promoted + isa prepended.
                if ":-" in ln:
                    head, _, body = ln.partition(":-")
                    head_new = _stub_val.sub(lambda m: f"val(Inst, {m.group(1)}", head)
                    body_new = _stub_val.sub(lambda m: f"val(Inst, {m.group(1)}", body)
                    body_new = body_new.lstrip()
                    if not body_new.startswith(f"isa(Inst, {spec})"):
                        body_new = f"isa(Inst, {spec}), {body_new}"
                    out_lines.append(f"{head_new}:-{body_new}")
                else:
                    # Continuation line (no :-): only promote val( body literals.
                    out_lines.append(_stub_val.sub(lambda m: f"val(Inst, {m.group(1)}", ln))
            return "\n".join(out_lines)
        for stub_block in design.stub_rules:
            rules.append(_promote_stub_block(stub_block))
        _stub_funcs = set(re.findall(r'@([a-z][a-z0-9]*)\s*\(', "\n".join(design.stub_rules)))
        _name_map = {"band": "and", "bor": "or", "bxor": "xor", "bnot": "not",
                     "ipow": "pow", "idiv": "div", "imod": "mod"}
        for fn in _stub_funcs:
            out.used.add(_name_map.get(fn, fn))
    return rules, out.used, [reason for _loc, reason in out.problems]


def _bridge_terms(formal: str, actual: str, shape: Shape | None,
                  ndims: int = 0) -> tuple[str, str, str]:
    """(child_sig_term, parent_sig_term, value_tail) for a modular port bridge, by shape. A lane
    signal carries its lane index INSIDE the signal functor -- val(Inst, sig(L), V, T) -- so the
    bridge fans over every lane; otherwise the signal name passes through bare.

    ``ndims`` > 0 marks an UNPACKED ARRAY port and is F7's fix. Such a port used to fall through
    to the word case, emitting `val(u, buf_, V, T) :- val(top, arr, V, T)` over an atom nothing
    derives: an array's atoms are its CELLS (`arr(A)`), and it has none under its bare name. The
    child then read `val(Inst, buf_(V0), ..)` and had no value at any instant, so every property
    over it passed VACUOUSLY -- and both the array and its consumer translated with no
    complaint. Bridging PER CELL is the whole fix: the index lives inside the signal functor
    exactly as it does for a lane, and the address is bound by the body, so the rule is safe
    without an extra domain literal.
    """
    if shape == Shape.TAG:
        return formal, actual, "G"           # a symbolic tag passes through
    if shape == Shape.INDEXED:
        return f"{formal}(L)", f"{actual}(L)", "V"   # per-lane: lane L lives in the signal functor
    if ndims:                                # unpacked array: one bridge covering every cell
        ix = ", ".join(["A"] if ndims == 1 else [f"A{i + 1}" for i in range(ndims)])
        return _lane_term(formal, ix), _lane_term(actual, ix), "V"
    return formal, actual, "V"               # word


def _spec_holds(design: Design, spec: str, shapes: dict[str, Shape],
                lane_dims: dict[str, int],
                global_tick: str = "gtime(T)") -> tuple[list[str], list[str]]:
    """Instance-parameterised multi-clock holds for a spec (emitted only when the TOP spans >=2 clock
    domains): a state element holds its value at every global tick where its OWN clock does NOT have an
    edge, so its value is defined at every global T and cross-domain reads share one time base (the
    master-tick model -- the per-instance mirror of _emit_multiclock). Covers scalar/word registers, lane
    registers, VFFs, and memories (the index/address fans over the lane/addr domain). Returns no problems
    -- every state element is held."""
    rules: list[str] = []

    def hold_guard(clock: str) -> str:    # the off-edge guard for state on `clock` (free or gated)
        if clock in {dc.name for dc in design.derived_clocks}:
            return f"isa(Inst, {spec}), {global_tick}, T < k, no_tick({clock}(Inst), T)"
        return f"isa(Inst, {spec}), clkof(Inst, {clock}, CK), {global_tick}, T < k, no_tick(CK, T)"

    # For per-instance derived (gated) clocks, emit no_tick in this spec file —
    # the generic manifest rule (via clkof) doesn't cover gclk(Inst)-style functors.
    # Use gtime(T) as the base (true at every global tick) so no_tick fires even at
    # steps where the base clock does not tick.
    for dc in design.derived_clocks:
        rules.append(f"no_tick({dc.name}(Inst), T) :- isa(Inst, {spec}), "
                     f"gtime(T), not time({dc.name}(Inst), T).")

    for it in design.seq:
        if it.combinational or not it.clock:
            continue
        # async reset is level-sensitive -> the hold yields to it (gate on the deassert literal, with
        # the reset signal read on this instance: val(Inst, rst, deasserted, T+1)).
        rst = f", val(Inst, {it.reset.signal}, {1 if it.reset.active == 'low' else 0}, T+1)" \
            if it.reset is not None else ""
        g = hold_guard(it.clock)
        if shapes.get(it.reg) == Shape.INDEXED:   # lane register -> fan over the lane index
            term = _lane_term(it.reg, _idx(it.reg, lane_dims))
            dom = f", lane(Inst, {it.lane_domain}, {_idx(it.reg, lane_dims)})" if it.lane_domain else ""
            rules.append(f"val(Inst, {term}, V, T+1) :- {g}{dom}{rst}, val(Inst, {term}, V, T).")
        else:
            rules.append(f"val(Inst, {it.reg}, V, T+1) :- {g}{rst}, val(Inst, {it.reg}, V, T).")
    for v in design.vffs:                          # vectored flop -> per-lane hold (lane index I)
        if not v.clock:
            continue
        q = _lane_term(v.q, "I")
        rules.append(f"val(Inst, {q}, V, T+1) :- {hold_guard(v.clock)}, lane(Inst, {v.inst}, I), "
                     f"val(Inst, {q}, V, T).")
    for m in design.mems:                          # memory -> per-cell hold (address fans over addr)
        clk = next((w.clock for w in design.mem_writes if w.mem == m.name and w.clock), None)
        if not clk:
            continue
        dims = m.dims or (m.depth,)
        aterm = ", ".join(["A"] if len(dims) == 1 else [f"A{p + 1}" for p in range(len(dims))])
        rules.append(f"val(Inst, {m.name}({aterm}), V, T+1) :- {hold_guard(clk)}, "
                     f"addr(Inst, {m.name}, {aterm}), val(Inst, {m.name}({aterm}), V, T).")
    return rules, []


def _struct_fields(design: Design, formal: str) -> list[str]:
    """The field names of a struct port ``formal`` in ``design`` (empty if not a struct). A packed
    struct decomposes into per-field subsignals ``formal(field)`` (the functor principle); we recover the
    fields from those signal names so the modular port bridge can wire each field across the boundary."""
    pre = formal + "("
    return [s.name[len(pre):-1] for s in design.signals
            if s.name.startswith(pre) and s.name.endswith(")") and "(" not in s.name[len(pre):-1]]


#: Schema families the FLAT header declares that the modular set deliberately does not mirror,
#: with the reason. Consulted by `test_f6_modular_schema_matches_flat`, which otherwise requires
#: every flat schema family to have an instance-qualified counterpart -- so this list is the
#: complete, reviewed set of exceptions rather than whatever the code happens to omit.
MODULAR_SCHEMA_EXEMPT: dict[str, str] = {
    "module": "flat has ONE module; a modular spec is a (module, param-tuple) VARIANT, and "
              "`module(counter_v2)` would name a module the RTL does not contain. The instance "
              "layer states the same thing precisely: isa(Inst, spec) in <top>__inst.lp.",
    "cell": "the structural instance manifest -- flat's RECOVERY of a hierarchy it flattened "
            "away. Modular represents that hierarchy natively (isa / clkof / the manifest's "
            "port bridges), so emitting cell/3 here would re-encode it, not declare it.",
}


def _spec_schema(design: Design, spec: str) -> list[str]:
    """Instance-parameterised SCHEMA for a spec -- the per-instance mirror of the flat header
    schema, keyed by `Inst` via `isa(Inst, spec)`. This makes the modular spec set
    SELF-DESCRIBING (every signal carries its width/direction/reg/clock/declared-type under the
    spec's own -- modular -- names, e.g. `gcond_0`), so a consumer reads it directly instead of
    cross-mapping to the flat design. Behaviourally inert (no `val`), so modular/flat observable
    parity is unaffected.

    **F6 (fixed 2026-08-16) was wider than the finding said.** It was recorded as "the memory
    schema is under-declared: the spec files declare type/port/clock and the `addr` domain but
    not the memory's element shape". Measured against the flat header across all 97 committed
    designs, NINE families were missing, not one: `decl_type` (every signal, 97 designs),
    `param` (20), `dims` (12), `element_type` / `array` (11), `reg` for MEMORIES (8 -- the
    signal-level `reg` was already here, which is exactly why the gap read as smaller than it
    was), and `reset` (8). A consumer could not tell which registers had a reset path at all.

    Every one is emitted instance-qualified, following the convention the rest of this function
    already sets: two instances of one spec share these facts by construction (a spec IS a
    param-tuple), and qualifying them means a consumer holding an instance asks it directly
    rather than joining back through `isa`. What is deliberately NOT mirrored is
    `MODULAR_SCHEMA_EXEMPT`, and the parity test reads that list rather than a hand-kept
    expectation."""
    g = f":- isa(Inst, {spec})."
    out: list[str] = ["% schema (self-describing): type/decl_type/port/reg/clock/reset, the "
                      "array shape, and params -- per instance of this spec"]
    for p in design.params:
        if p.value is None:
            continue   # a non-constant-foldable param has no schema value (folded at use, or flagged)
        # a WIDE parameter value (>= 2^31) is a canonical String, else clingo's 32-bit parse
        # would silently wrap the schema atom -- the same guard the flat header applies.
        out.append(f"param(Inst, {p.name}, {_const_lit(p.value)}) {g}")
    for s in design.signals:
        if s.enum_type is not None:
            out.append(f"type(Inst, {s.name}, enum, {s.enum_type}) {g}")
        else:
            out.append(f"type(Inst, {s.name}, {s.irtype.kind.value}, {s.irtype.width}) {g}")
        # provenance: the declared SV type (base keyword / typedef name + 2-state vs 4-state)
        # that the interpretation kind/width above collapses (logic[7:0] and bit[7:0] both ->
        # bit, 8). The 2/4-state bit is what decides a power-on choice, so a consumer reading
        # the spec set alone could not previously reconstruct that decision.
        if s.irtype.sv_base:
            state = "four_state" if s.irtype.four_state else "two_state"
            out.append(f"decl_type(Inst, {s.name}, {s.irtype.sv_base}, {s.irtype.width}, "
                       f"{state}) {g}")
        if s.is_port and s.direction:
            out.append(f"port(Inst, {s.name}, {s.direction}) {g}")
        if s.is_reg:
            out.append(f"reg(Inst, {s.name}) {g}")
        pd = design.packed_dims.get(s.name)
        if pd and s.name not in design.lane_signals:
            out.append(f"dims(Inst, {s.name}, "
                       f"{', '.join(f'packed({d})' for d in pd)}) {g}")
    clk_seen: set[str] = set()
    for it in design.seq:
        if not it.combinational and it.reg not in clk_seen:
            out.append(f"clock(Inst, {it.reg}, {it.clock}) {g}")
            clk_seen.add(it.reg)
    for w in design.mem_writes:
        if w.clock and w.mem not in clk_seen:
            out.append(f"clock(Inst, {w.mem}, {w.clock}) {g}")
            clk_seen.add(w.mem)
    # the RESET PATH per reset register. Missing here meant the spec set could not say which
    # state elements reset defines -- the one question `state_unreset` and the power-on walk
    # both turn on.
    rst_seen: set[str] = set()
    for it in design.seq:
        if it.reset is not None and it.reg not in rst_seen:
            out.append(f"reset(Inst, {it.reg}, {it.reset.signal}, active_{it.reset.active}) {g}")
            rst_seen.add(it.reg)
    # THE MEMORY SHAPE -- F6 as originally recorded. `addr(Inst, mem, A)` (emitted with the
    # rules) gives the address DOMAIN; these give the cell's element type and the array's
    # dimensional shape, in the same `dims/N` vocabulary a packed matrix uses, so a consumer
    # reads any signal's shape one way.
    for m in design.mems:
        dims = m.dims or (m.depth,)
        out.append(f"reg(Inst, {m.name}) {g}")
        out.append(f"element_type(Inst, {m.elem.name}, {m.elem.kind.value}, "
                   f"{m.elem.width}) {g}")
        aws = ", ".join(f"addr_w({max(1, (n - 1).bit_length())})" for n in dims)
        out.append(f"array(Inst, {m.name}, {m.elem.name}, unpacked, {aws}) {g}")
        ud = ", ".join(f"unpacked({n})" for n in dims)
        ew = f", packed({m.elem.width})" if m.elem.width > 1 else ""
        out.append(f"dims(Inst, {m.name}, {ud}{ew}) {g}")
    return out


def emit_modular(modular: dict, *, bitvec: bool = False,
                 clock_hierarchy: dict | None = None) -> dict[str, str]:
    """Render the modular file set: one `<spec>.lp` per (module, param-tuple) + a `<top>__inst.lp`
    manifest (isa / clkof / port bridges) + a shared `__lib.lp` (@func defs). Compose at solve time:
    `clingo <dir>/*.lp scenario.lp`. ``modular`` is the dict from PyslangFrontend.parse_modular."""
    specs, tree = modular["specs"], modular["tree"]
    used: set[str] = set()
    files: dict[str, str] = {}
    ch = dict(clock_hierarchy) if clock_hierarchy else {}
    global_tick_m = "time(T)" if ch else "gtime(T)"
    spec_shapes: dict[str, dict] = {}
    # multi-clock when the design resolves to >=2 distinct clock domains (see _emit_multiclock / the
    # master-tick model): each spec then needs off-edge HOLD rules and the manifest a global tick line.
    # A DERIVED (gated) clock is also a second domain (it ticks on a subset of its base), so a design with
    # any ICG gating needs the same off-edge holds even with a single free clock. With per-port clkof a
    # SINGLE module can itself span >1 domain, so count distinct resolved clocks across all instances.
    has_gating = any(d.derived_clocks for d in specs.values())
    all_clocks = {ck for n in tree for ck in n["clks"].values()}
    multiclock = has_gating or len(all_clocks) >= 2

    hdr = "% Auto-generated by sv2asp (modular mode); compose: clingo <dir>/*.lp scenario.lp\n"
    for key, design in sorted(specs.items()):
        rules, u, rule_problems = _spec_rules(design, key, bitvec=bitvec)
        used |= u
        shapes = analyze(design, bitvec=bitvec).shape
        spec_shapes[key] = shapes
        # the rule builder's own problems (a `_guard`-caught construct, a word above the
        # budget) used to be RECORDED and never RETURNED: modular showed only `% UNSUPPORTED`
        # inline and relied on the dark-read check for its exit code, flat counted them (F32's
        # refusal exited 1 flat and 0 modular -- the two-emitter split, 2026-09-03)
        problems: list[str] = list(rule_problems)
        if multiclock:
            holds, problems = _spec_holds(design, key, shapes, dict(design.lane_dims),
                                           global_tick=global_tick_m)
            rules = [*rules, "% multi-clock: hold each state element between its own clock's edges", *holds]
        # MEMORY (scalar, lane-rolled, multi-dim), VFF, genvar lanes, array-of-instances lanes, and
        # value<->enum CASTs are all supported now: _spec_rules emits the init/write/hold + the per-instance
        # addr/lane domains; the global enum_value(...) facts are emitted ONCE in the manifest (below); and
        # the instance variable `Inst` never collides with the lane/address index `I`/`J`. (Anything truly
        # unhandled still surfaces as a frontend `design.flagged` -> a coverage PROBLEM; hard rule 2.)
        schema = _spec_schema(design, key)
        # SAFETY: the same check flat mode runs -- a spec whose rules cannot ground makes the
        # whole composed program unusable, so it is a PROBLEM here too, not a silent pass.
        _sc = _Out()
        _check_safety("\n".join(rules), _sc, where=f" in spec {key}")
        _check_stratified("\n".join(rules), _sc, where=f" in spec {key}")
        _check_comb_loops("\n".join(rules), _sc, where=f" in spec {key}")
        problems = [*problems, *(r for _l, r in _sc.problems)]
        body = "\n".join([*([f"% PROBLEM: {p}" for p in problems]), *schema, "", *rules])
        files[f"{key}.lp"] = (
            hdr
            + f"% spec: module {design.name} -- instance-parameterised, every rule guarded by "
              f"isa(Inst, {key}).\n"
            + (("% variant " + key.split("__", 1)[1] + ": "
                + ", ".join(f"{p.name}={_const_lit(p.value)}"
                            for p in design.params if p.value is not None)
                + "\n") if "__" in key and not key.endswith("__inst") else "")
            + "% The instance var is Inst (I/J/... are lane/address indices); see __inst.lp for the "
              "atom legend + wiring.\n"
            + body + "\n")

    manifest: list[str] = [
        hdr.rstrip("\n"),
        "% ============================ MODULAR ATOM LEGEND ============================",
        "% Each module is translated ONCE into a generic spec (<spec>.lp) whose rules range over an",
        "% instance variable Inst and are guarded by isa(Inst, Spec). This manifest INSTANTIATES and",
        "% WIRES those specs. Compose at solve time: clingo <dir>/*.lp scenario.lp",
        "%   isa(Inst, Spec)          -- instance Inst is of module-spec Spec (binds Inst in the rules)",
        "%   clkof(Inst, Port, Clk)   -- instance Inst's clock PORT resolves to domain Clk (one per clock",
        "%                               port, so a module with several clocks resolves each independently)",
        "%   val(Inst, Sig, V, T)     -- signal Sig of instance Inst has value V at time T",
        "%       functor Sig: lane sig(L) / field sig(f) / memory mem(A[,A2]) / nested hier u(sig)",
        "%       tag form:   val(Inst, Sig, Label, T) for an enum signal",
        "%   type(Inst,Sig,Kind,W) / port(Inst,Sig,Dir) / reg(Inst,Sig) / clock(Inst,Sig,Clk)",
        "%                            -- per-instance SCHEMA (each spec is self-describing; see its .lp)",
        "%   addr(Inst, Mem, A[,A2])  -- the per-instance memory address domain (the cell family)",
        "%   time(gclk(Inst), T)      -- a per-instance GATED (ICG) clock; gtime(T) = union of all edges",
        "%   port bridges below       -- val(Child, formal,..) <- val(Parent, actual,..) and back",
        "% Note: Inst is the INSTANCE variable; I/J/... are lane/address indices (never the instance).",
        "% ----------------------------------------------------------------------------",
        "%   enum_value(Enum, Label, V) -- the GLOBAL enum encoding (same for every instance); a value",
        "%       <-> enum cast `e'(x)` reads it: val(Inst, c, Label, T) :- val(Inst, x, V, T), enum_value(..,Label,V)",
        "%   @func ops (@add/@slc/@wcmp/...) -- see the @func LEGEND at the top of __lib.lp",
        "% instance manifest: isa(Inst, Spec) / clkof(Inst, Port, Clk) / port bridges"]
    if multiclock:                               # global tick line = union of all clock edges
        if not ch:
            manifest.append("gtime(T) :- time(CK, T).")
        # Generic no_tick: positive witness that clock CK did NOT tick at T.
        # CK is bound via clkof (every resolved clock name appears there).
        # NAF isolated here; hold rules in each spec read no_tick(CK,T) positively.
        manifest.append(f"no_tick(CK, T) :- {global_tick_m}, clkof(_, _, CK), not time(CK, T).")
    # clock_hierarchy derivation rules in modular manifest (global infrastructure, not per-instance)
    if ch:
        manifest.append("% CLOCK DERIVATION (frequency hierarchy from sources.json clock_hierarchy)")
        for clk_name, entry in ch.items():
            base = entry.get("base", "time")
            div  = int(entry.get("div", 1))
            if base == "time":
                manifest.append(f"time({clk_name}, T) :- time(T).")
            elif div == 1:
                manifest.append(f"time({clk_name}, T) :- time({base}, T).")
            else:
                manifest.append(f"time({clk_name}, T) :- time({base}, T), T \\ {div} == 0.")
    # GLOBAL enum encoding (not per-instance -- the label<->value map is the same for every instance);
    # a value<->enum cast rule in a spec reads it. Collected across all specs, de-duplicated.
    enum_facts = {f"enum_value({en.name}, {label}, {value})."
                  for d in specs.values() for en in d.enums for label, value in en.members}
    manifest.extend(sorted(enum_facts))
    for n in tree:
        manifest.append(f"isa({n['path']}, {n['spec']}).")
    for n in tree:                               # one clkof per (instance, clock PORT) -> resolved domain,
        for formal, actual in sorted(n["clks"].items()):   # so a multi-clock module resolves each clock
            manifest.append(f"clkof({n['path']}, {formal}, {actual}).")
    for n in tree:
        if n["parent"] is None:
            continue
        spec_design = specs[n["spec"]]
        shapes = spec_shapes.get(n["spec"], {})
        for formal, direction, actual in n["conns"]:
            fields = _struct_fields(spec_design, formal)
            if fields:                               # struct port: bridge each field subsignal (functor)
                bridges = [(f"{formal}({fld})", f"{actual}({fld})", "V") for fld in fields]
            else:
                # F7: an unpacked ARRAY port bridges per CELL, not as a word. The arity comes
                # from the CHILD's own declaration -- the formal is what the child reads, and
                # the child is where the array's `addr` domain and cell atoms are defined.
                _mem = next((m for m in spec_design.mems if m.name == formal), None)
                _nd = len(_mem.dims or (_mem.depth,)) if _mem is not None else 0
                bridges = [_bridge_terms(formal, actual, shapes.get(formal), _nd)]
            for fterm, aterm, tail in bridges:
                child = f"val({n['path']}, {fterm}, {tail}, T)"
                parent = f"val({n['parent']}, {aterm}, {tail}, T)"
                manifest.append(f"{child} :- {parent}." if direction == "In"
                                else f"{parent} :- {child}.")
        # interface ports: a bundle of shared wires. Each interface signal aliases the connected parent
        # interface instance's net iface(sig); the modport direction decides which way (In: the spec
        # reads the shared net; Out: the spec drives it). Functor subsignals, like a struct port.
        for formal, ifi, sigdirs in n.get("iconns", ()):
            for sig, d in sigdirs:
                child = f"val({n['path']}, {formal}({sig}), V, T)"
                shared = f"val({n['parent']}, {ifi}({sig}), V, T)"
                manifest.append(f"{child} :- {shared}." if d == "In" else f"{shared} :- {child}.")
    # hierarchical READS (`assign twice = u.q << 1;`): the parent's flat functor `u(q)` is the
    # child instance's own `q` -- bridge it, or the parent reads an atom no spec derives.
    for n in tree:
        for fname, child_path, sig in n.get("hreads", ()):
            manifest.append(f"val({n['path']}, {fname}, V, T) :- val({child_path}, {sig}, V, T).")
    files[f"{modular['top']}__inst.lp"] = "\n".join(manifest) + "\n"

    script = render_script(used)
    if script:
        legend = func_legend(used)
        legend_block = ("\n".join(legend) + "\n") if legend else ""
        files["__lib.lp"] = hdr + legend_block + script
    return files


# --------------------------------------------------------------------------
# Scenario stub generator (modular mode)
# --------------------------------------------------------------------------
def _enum_labels(design: Design, sig) -> tuple[str, ...]:
    """The enum member labels for a TAG signal (in declaration order)."""
    for e in design.enums:
        if e.name == sig.enum_type:
            return tuple(label for label, _ in e.members)
    return ()


def _shape_note(shape: Shape | None, sig, design: Design) -> str:
    """A human-readable shape/type note for the FILL comment beside a stub line."""
    if shape == Shape.TAG:
        labels = _enum_labels(design, sig)
        return f"enum {sig.enum_type} {{{'|'.join(labels) or '...'}}}"
    if shape == Shape.BIT:
        return "bit"
    if shape == Shape.INDEXED:
        return "per-lane vector (one fact per lane index L)"
    w = sig.irtype.width
    return f"word [w={w}]" if isinstance(w, int) else "word"


def _legend() -> list[str]:
    """The field-layout legend: what each val-atom argument means, by shape, with an example."""
    return [
        "% Atom field layout -- replace only the VALUE field, keep the rest:",
        "%   bit/word sig:  val(Inst, Sig, Value, Time)           e.g. val(top, go, 1, 2)     = go is 1 at T=2",  # noqa: E501
        "%               (a 1-bit signal is a width-1 word: value 0/1, no bit-position slot)",
        "%   enum signal :  val(Inst, Sig, Label, Time)           e.g. val(top, mode, inc, 0) = mode is inc at T=0",  # noqa: E501
        "%   per-lane    :  val(Inst, Sig(Lane), Value, Time)     (lane is a FUNCTOR; one fact per lane L)",  # noqa: E501
        "%   memory      :  val(Inst, Mem(Addr), Value, Time)     (one ground fact per address A)",
        "% Inputs are GROUND facts -- one per cycle, set each value at each T. Do NOT write a rule",
        "% `val(...,T) :- time(clk,T)`: that pins ONE value for every cycle and then collides with a",
        "% per-cycle fact (the signal would hold two values at that T). Registers get a T=0 fact only.",
        "% WIDE VALUES: a value >= 2^31 must be a CANONICAL STRING (quoted decimal), e.g.",
        "%   val(top, x, \"4000000000\", T)  -- or use @sv(\"4000000000\") / @sv(\"32'hEE6B2800\") via",
        "%   lib/svlit.lp. A BARE integer >= 2^31 silently WRAPS (clingo's Number is signed 32-bit:",
        "%   4000000000 -> -294967296), which corrupts width-extension/compare downstream.",
    ]


def _stub_input(top: str, sig, shape: Shape | None, design: Design, k: int) -> list[str]:
    """A per-input stimulus block: a shape header comment + one GROUND fact per cycle T=0..k (each
    value editable). INDEXED/ADDRESSED are emitted as a commented template (they need a concrete
    lane index / address), so the skeleton never grounds to an error before the user fills it in."""
    note = _shape_note(shape, sig, design)
    head = f"% {sig.name} : {note}"
    if shape == Shape.INDEXED:
        return [head, f"%   val({top}, {sig.name}(L), 0, T).   % one fact per (lane L, cycle T)"]
    if shape == Shape.ADDRESSED:
        return [head, f"%   val({top}, {sig.name}(A), 0, T).   % one fact per (address A, cycle T)"]
    if shape == Shape.TAG:
        v = (_enum_labels(design, sig) or ("tag",))[0]
        facts = [f"val({top}, {sig.name}, {v}, {t})." for t in range(k + 1)]
    else:  # bit or word (a 1-bit signal is a width-1 word)
        facts = [f"val({top}, {sig.name}, 0, {t})." for t in range(k + 1)]
    return [head, "  ".join(facts)]


#: Above this width one element's power-on is not enumerated (2^w ground atoms): the file carries
#: guidance instead -- seal the wide unknown behind a boundary predicate (CDS, methodology
#: doc section 5.8) or take the completion->Lean forall-input route, both exact-X for wide values.
XINIT_CAP = 16

#: ...and above this many ground atoms for one element FAMILY, likewise. A plain register is one
#: cell, so its budget is exactly 2^XINIT_CAP and the width test alone decides it. An ADDRESSED or
#: PER-LANE element multiplies by its cell/lane count, and `logic [15:0] m [4096]` would ground
#: 2^28 atoms with every individual width comfortably under the cap. F4 opened memories and lanes,
#: so the cost became per family and the budget has to say so.
XINIT_ATOM_CAP = 1 << XINIT_CAP


class _XElem(NamedTuple):
    """One state element as the power-on walk sees it: what it is, and what shape its rule takes."""

    name: str
    kind: str            # _xinit_kind: skip / two_state / enum_pool / wide / choice
    form: str            # _xinit_form: plain / addressed / lane
    width: int           # bits of ONE cell / lane / signal
    cells: int           # cells (memory) or lanes; 1 for a plain signal
    dims: tuple          # per-index extents, for form == 'lane'; () = extent NOT DETERMINED
    labels: tuple        # enum member labels, for kind == 'enum_pool'
    avars: tuple         # address variable name(s), for form == 'addressed'
    what: str            # the construct, for the comment ("register", "array cell", ...)
    #: (enable signal, its OPAQUE value) for a level-sensitive latch: a concrete power-on FACT
    #: applies only when the latch is opaque at t=0 -- transparent, its value IS the data
    #: (`val(q, V, 0) :- val(en, 1, 0), val(d, V, 0)`), and an unconditional `val(q, 0, 0)` beside
    #: it made the register multi-valued (UNSAT) whenever the enable was high at power-on
    #: (found by the convention audit's `latch_transparent`). None for everything else.
    gate: tuple | None = None
    #: the largest number of this element's atoms one emitted rule reads in a single body
    #: (`family_join`); the budget is measured at `width * join`, see `_xinit_kind`
    join: int = 1


def _xinit_kind(has_reset: bool, four_state: bool, is_enum: bool,
                width: int, cells: int = 1, join: int = 1) -> str:
    """THE x-init decision, as a pure function -- which power-on treatment a state element gets.

    ``join`` is the largest number of the element's atoms one emitted rule reads in a single
    body (`state_inventory.family_join`): a per-lane word bridge joins all n lanes, the per-bit
    assembly all w bits. The grounder instantiates such a rule once per COMBINATION of the free
    atoms' values -- 2^(width * join) -- so that, not `2^width` alone, is the width the cap
    is measured against. Before this the cap saw the atoms (64 one-bit choices; 4 eight-bit
    lanes) and not the join (2^64; 2^32), and each hung a solve.

    Returns one of:
      'skip'      -- a reset branch determines power-on; NEVER opened;
      'two_state' -- unreset but 2-state: LRM 6.8 says the default is 0, not x -> comment;
      'enum_pool' -- unreset enum: choice over the MEMBER POOL (the domain is the member set,
                     never 2^width -- the Fix 86 lesson);
      'wide'      -- unreset, but enumerating the family would exceed the grounding budget:
                     guidance comment, never the blowup;
      'choice'    -- unreset 4-state element: the domain choice.

    **F4 changed this function's SHAPE, not just its policy.** It used to take `is_mem` and
    `is_lane` and answer 'skip' / 'lane' for them -- so WHERE an element lived decided WHAT
    power-on treatment it got. That is how a memory ended up with an invented `val(mem(A), 0, 0)`
    in the design layer (a claim no synthesised array makes, and one a property could not
    quantify over) while a lane register got a comment telling the reader to do it by hand.
    Where an element lives is now `_xinit_form`, and it has nothing to do with what its
    power-on value is: state is state.

    The ORDER of the tests is part of the contract, and so is the ORDER of the two budget
    tests: `width * join > XINIT_CAP` is checked FIRST so `2 ** width` is only ever computed for
    a width that is small (both here and in the Lean model's kernel reduction).

    Mirrored in Lean as `Xinit.kind`, checked against THIS function on every element the
    translator really classifies AND over the whole bounded input space
    (proofs/gen_xinit_lean.py -> XinitTable.lean)."""
    if has_reset:
        return "skip"
    if not four_state:
        return "two_state"
    if is_enum:
        return "enum_pool"
    if width * max(join, 1) > XINIT_CAP:
        return "wide"
    if cells * 2 ** width > XINIT_ATOM_CAP:
        return "wide"
    return "choice"


def _xinit_form(is_mem: bool, is_lane: bool) -> str:
    """WHERE a power-on treatment applies -- orthogonal to WHICH treatment it is.

      'addressed' -- one rule over the address domain, covering every cell of an array;
      'lane'      -- one rule over the lane index, covering every lane;
      'plain'     -- a single signal.

    Kept SEPARATE from `_xinit_kind` deliberately (see that function): conflating the two is
    the defect F4 removed."""
    if is_mem:
        return "addressed"
    if is_lane:
        return "lane"
    return "plain"


def _xinit_elements(design: Design, bitvec: bool = True, text: str = "") -> list[_XElem]:
    """Every STATE element of one design, classified for power-on -- registers, array cells,
    vectored-flop lanes, and latches (explicit and inferred).

    Walking construct kinds is what produced F12 (an inventory that listed registers and
    memories and silently omitted latches), so this walk is not the authority on what state
    EXISTS: `xinit_uncovered` re-derives the state vector from the EMITTED RULES and reports
    anything this function did not consider. This walk supplies the METADATA -- width, cell
    count, enum members, address arity -- which the rules alone do not carry. Same split as
    `state_inventory.render`, and for the same reason.

    First occurrence wins, so a construct reachable by two routes (an inferred latch appears
    both in `inferred_latches` and, hold-only, in `latches`) is classified once."""
    four = {s.name: s.irtype.four_state for s in design.signals}
    widths = {s.name: s.irtype.width for s in design.signals}
    sig_of = {s.name: s for s in design.signals}
    an = analyze(design, bitvec=bitvec)          # the SAME analysis the emitter ran (per-bit registers)
    shapes = an.shape
    lane_w = dict(design.lane_elem_w)
    lanes = set(design.lane_dims) | {v.q for v in design.vffs}
    # A register the ANALYSIS chose for the per-bit representation (`--bitvec`'s
    # `bitvec_signals`: a wide word whose sole driver is bit-structural, e.g. a shift register
    # `q <= {q[6:0], d}`) is held as per-bit atoms `q(I)` (or `q(I, J)` for a wide-element lane),
    # not as the word. Its power-on must be given in THAT form: a word-level `val(q, 0, 0)` never
    # reaches the bits (the bridge for an internal lane signal assembles lanes INTO the word), so
    # the register was dark until every bit had been written once -- eight cycles of vacuous
    # properties for an 8-bit shift register, with `--init-zero` on. The frontend does not know
    # this shape (it is the analysis's decision), so it is folded in here.
    bitvec = set(an.bitvec_signals)
    lanes |= bitvec
    # the JOIN each family is read at, off the emitted rules (see `_xinit_kind`); with no text
    # (a caller that has none) every family is budgeted at its own width -- the pre-join rule
    joins = family_join(text) if text else {}
    mems = {m.name for m in design.mems}
    # A COMBINATIONAL or read-only array is driven at every instant, so it is not sequential
    # state and needs no power-on value -- the same test `state_inventory` applies, so the two
    # artifacts agree on what a pins check must demand.
    mem_clocked = {w.mem for w in design.mem_writes if w.clock}

    out: list[_XElem] = []
    seen: set[str] = set()

    def _int(x, dflt: int = 1) -> int:
        return x if isinstance(x, int) else dflt

    def _prod(dims) -> int:
        n = 1
        for d in dims:
            n *= _int(d)
        return n

    def add(name, kind_args, form, width, dims=(), labels=(), avars=(), what="", gate=None) -> None:
        if name in seen:
            return
        seen.add(name)
        j = joins.get(name, 1)
        out.append(_XElem(name, _xinit_kind(*kind_args, join=j), form, width,
                          _prod(dims), tuple(dims), tuple(labels), tuple(avars), what, gate, j))

    def _lane_extent(name: str, lane_domain: str | None, w: int) -> tuple:
        """A lane register's per-index extents, or () if they cannot be determined.

        TWO independent sources, and neither covers the other: an ARRAY OF INSTANCES publishes
        its extents as `lane_domains[owner]` and carries no per-lane element width, while a
        genvar/packed lane register carries `lane_elem_w` and no lane domain. Deriving the
        count from width/element alone gave `inst_array_demo`'s 4-lane `y` ONE lane (its
        `lane_elem_w` is absent, so the element width defaulted to the whole word) -- a power-on
        choice covering lane 0 and silently leaving lanes 1..3 dark. Returning () rather than
        guessing 1 is the difference between a visible gap and that."""
        if lane_domain and lane_domain in design.lane_domains:
            return tuple(design.lane_domains[lane_domain])
        nd = _multi_level(name)
        if nd:
            return nd
        ew = _int(lane_w.get(name, 0), 0)
        if ew and w % ew == 0 and w // ew >= 1:
            return (w // ew,)
        return ()

    def _multi_level(name: str) -> tuple:
        """The per-level extents of a register written in a NESTED generate (`g[i][j] <= ..` on
        `logic [R-1:0][C-1:0] g`): its atoms are `g(I, J)`, so its power-on must be spelled
        `g(L1, L2)` over both levels -- the flat `g(L), L = 0..15` it got named atoms no rule
        reads, and a 4x4 flop bank was dark from T=0 in both modes (F38, 2026-09-03)."""
        levels = _int((getattr(design, "lane_dims", {}) or {}).get(name, 1), 1)
        pd = tuple(getattr(design, "packed_dims", {}).get(name, ()) or ())
        if levels >= 2 and len(pd) >= levels:
            return tuple(int(x) for x in pd[:levels])
        return ()

    for it in design.seq:                                  # clocked registers (incl. lane regs)
        if it.combinational or it.reg in mems:
            continue                                       # the array walk below owns the cells
        w = _int(widths.get(it.reg, 1))
        is_lane = it.reg in lanes
        if it.reg in bitvec:                                # per-bit atoms: one lane per BIT
            lew = _int(lane_w.get(it.reg, 1), 1)
            dims = _multi_level(it.reg) or ((w // lew, lew) if lew > 1 and w % lew == 0 else (w,))
        else:
            dims = _lane_extent(it.reg, it.lane_domain, w) if is_lane else ()
        n = _prod(dims) if dims else 1
        ew = max(1, w // n) if is_lane else w               # bits of ONE lane
        is_enum = (shapes.get(it.reg) == Shape.TAG
                   and bool(_enum_labels(design, sig_of.get(it.reg))))
        # The per-lane / per-bit register's budget is its element width TIMES the join the
        # emitted rules make over its atoms (the word bridge reads every lane / bit in one
        # body) -- `_xinit_kind`'s `join`, read off the rules by `family_join`. It used to be
        # special-cased for the per-bit register alone; a 4-lane x 8-bit lane register (2^32
        # in its bridge) fell through the same hole.
        add(it.reg, (it.reset is not None, four.get(it.reg, False), is_enum, ew, n),
            _xinit_form(False, is_lane), ew, dims,
            _enum_labels(design, sig_of.get(it.reg)) or (),
            what=("per-lane register" if is_lane else "register"))

    mem_reset = {w.mem for w in design.mem_writes if getattr(w, "reset", None) is not None}
    for m in sorted(design.mems, key=lambda x: x.name):    # array cells
        if m.name not in mem_clocked:
            continue
        dims = m.dims or (m.depth,)
        ew = _int(getattr(m.elem, "width", 1))
        avars = ("A",) if len(dims) == 1 else tuple(f"A{p + 1}" for p in range(len(dims)))
        # An array MAY carry a reset -- `if (!rst_n) for (i...) tab[i] <= C;` resets every cell, and
        # that is how an array of REGISTERS is written (VerilogEval's gshare does it to its PHT).
        # This used to read "an array carries no reset in synthesizable RTL, so has_reset is False by
        # construction". That was wrong, and it was load-bearing: once the reset started lowering
        # (F25) the power-on layer still pinned every cell to 0 at T=0 beside the reset's own force,
        # and every cell was multi-valued. An array whose cells a reset drives takes its power-on
        # from that reset, exactly like a register.
        has_rst = m.name in mem_reset
        add(m.name, (has_rst, bool(getattr(m.elem, "four_state", False)), False, ew, _prod(dims)),
            _xinit_form(True, False), ew, dims, avars=avars, what="array cell")

    for v in sorted(design.vffs, key=lambda x: x.q):       # vectored-flop lanes
        # a VFF states its own lane count and per-lane width, so its extent needs no inference.
        add(v.q, (False, four.get(v.q, True), False, _int(v.width), _int(v.lanes)),
            _xinit_form(False, True), _int(v.width), (_int(v.lanes),),
            what="vectored-flop lane")

    for il in sorted(design.inferred_latches, key=lambda x: x.lhs):
        w = _int(getattr(il, "width", widths.get(il.lhs, 1)))
        add(il.lhs, (False, four.get(il.lhs, False), False, w, 1),
            _xinit_form(False, False), w, what="inferred latch")

    for la in sorted(design.latches, key=lambda x: x.q):   # explicit level-sensitive latches
        w = _int(widths.get(la.q, 1))
        # transparent while `en` is 1 (active-low enables are refused at intake), so the latch
        # is OPAQUE -- and its power-on fact applies -- only when `en` is 0 at t=0
        add(la.q, (False, four.get(la.q, False), False, w, 1),
            _xinit_form(False, False), w, what="latch", gate=(la.en, 0))

    for ed in sorted(design.edges, key=lambda x: x.lhs):   # $rose / $fell sampled-value edges
        # An edge function is not a register -- it holds nothing -- but its value at `T+1` is
        # determined by instant `T`, which is what makes it state and what the completeness
        # check sees. At the FIRST tick there is no previous sample, so IEEE 1800 reads it as
        # x: exactly the unknown a power-on choice is for. The emitter already WARNS that it is
        # unbound at T=0; before F4 that warning was all there was, and the signal was simply
        # dark there.
        #
        # `four_state` is asserted rather than looked up, and that is deliberate: the unknown
        # comes from there being NO previous sample at all, not from how the sampled signal was
        # declared, so a `$rose` on a 2-state `bit` is just as unknown at the first tick.
        add(ed.lhs, (False, True, False, 1, 1), _xinit_form(False, False), 1,
            what="sampled-value edge (no previous sample at the first tick)")

    return out


def xinit_uncovered(design: Design, text: str, bitvec: bool = True) -> list[str]:
    """State elements the EMITTED RULES carry that the power-on walk never considered.

    The teeth behind `_xinit_elements`. That walk enumerates CONSTRUCT KINDS, and this project
    has now paid three times for a list maintained that way -- a rule reaching registers but
    not memory cells, an x-init companion covering registers only, and a state inventory that
    omitted latches. So membership is arbitrated by the one thing that cannot go stale: a
    signal whose value at `T+1` is determined by instant `T` IS state, read straight off the
    emitted program (`state_inventory.state_signals`).

    An element here has NO power-on policy at all -- not a choice, not even a comment saying
    why it does not get one. Since F4 the design layer supplies no initial state either, so
    such an element is dark at `t = 0` and every property over it passes VACUOUSLY. That is a
    PROBLEM, not a warning: the same failure mode as F2, F7 and F10.

    A state TERM is matched against the walk's element names two ways, because a term may or
    may not carry an index: `u_cnt(q)` is a flattened register and matches whole, while
    `u_rf(mem(A))` is one cell of the family `u_rf(mem)` and matches after the innermost index
    list is dropped. Matching on the root symbol instead would collapse every element of one
    flattened instance onto the instance name, and a covered sibling would then vouch for an
    uncovered one."""
    elems = _xinit_elements(design, bitvec, text)
    names = {e.name for e in elems}
    forms = {e.name: e.form for e in elems}

    def uncovered(t: str) -> bool:
        if t in names:
            return False
        fam = state_family(t)
        if fam not in names:
            return True
        # The FORM must match too: a state term WITH an index (`q(I)`, per-bit or per-lane
        # atoms) whose family the walk covers as a PLAIN word is not covered -- the walk's
        # power-on pins the word, and nothing derives the atoms the rules actually hold.
        return fam != t and forms.get(fam) == "plain"

    return sorted(t for t in state_terms(text) if uncovered(t))


def _xinit_target(e: _XElem, inst: str | None) -> tuple[str, str, str]:
    """WHERE one element's power-on rule applies: its head TERM, the body GUARD that fans the
    rule over the family, and a human span for the comment.

    The term goes through `_lane_term`, the same LEAF injection the design rules use, so a
    hierarchy-qualified name composes (`u_rf(mem)` + `A` -> `u_rf(mem(A))`) instead of becoming
    the invalid curried `u_rf(mem)(A)`. Sharing the builder is the point: a second copy is how
    the companion and the design would drift into naming different atoms, and a power-on choice
    for an atom no rule reads is silently no power-on at all."""
    if e.form == "addressed":
        ix = ", ".join(e.avars)
        dom = f"addr({inst}, " if inst else "addr("
        return _lane_term(e.name, ix), f" :- {dom}{e.name}, {ix})", f"{e.cells} cell(s)"
    if e.form == "lane":
        # the lane extent INLINE rather than a `lane(owner, L)` literal: an array of instances
        # publishes that domain fact but a genvar lane register does not (its index is bound by
        # the operand read), and one self-contained shape works for both.
        lv = ["L"] if len(e.dims) == 1 else [f"L{i + 1}" for i in range(len(e.dims))]
        rng = ", ".join(f"{v} = 0..{n - 1}" for v, n in zip(lv, e.dims, strict=True))
        return _lane_term(e.name, ", ".join(lv)), f" :- {rng}", f"{e.cells} lane(s)"
    return e.name, "", ""


def _xinit_lines(design: Design, inst: str | None, bitvec: bool = True, text: str = "") -> list[str]:
    """Choice (or guidance-comment) lines for one design's unknown power-on state.
    ``inst`` = the instance path for modular val/4 atoms, None for flat val/3."""
    q = (lambda t, rest: f"val({inst}, {t}{rest}") if inst else \
        (lambda t, rest: f"val({t}{rest}")
    out: list[str] = []
    for e in _xinit_elements(design, bitvec, text):
        if e.kind == "skip":
            continue
        if e.form == "lane" and not e.dims:
            # the extent could not be determined from either source (`_lane_extent`). Say so
            # rather than emit a range: a wrong extent opens SOME lanes and leaves the rest
            # dark, which reads exactly like a covered element.
            out.append(f"% {e.name}: unreset {e.what} whose LANE EXTENT this tool could not "
                       f"determine -- open the lanes in the scenario "
                       f"({{ {q(_lane_term(e.name, 'L'), ', V, 0)')} : V = 0..{2 ** min(e.width, 8) - 1} }}"
                       f" = 1 :- L = 0..N-1)")
            continue
        # WHERE the treatment applies. The head TERM and the body GUARD are the only things the
        # form changes -- every kind below renders the same whether it is a signal, a cell or a
        # lane, which is what makes "state is state" true of the code and not just of the prose.
        term, guard, span = _xinit_target(e, inst)
        where = f" ({span})" if span else ""
        if e.kind == "two_state":
            out.append(f"% {e.name}: unreset but 2-STATE {e.what}{where} -- LRM 6.8 default is 0, "
                       f"not x; supply {q(term, ', 0, 0)')}{guard} in the scenario if the type's "
                       f"default is intended")
        elif e.kind == "enum_pool":
            pool = "; ".join(q(term, f", {l}, 0)") for l in e.labels)
            out.append(f"{{ {pool} }} = 1{guard}.   % {e.name} powers on UNKNOWN: any enum state")
        elif e.kind == "wide":
            # the cost is the JOIN: a rule reading `join` of the element's atoms at once grounds
            # over 2^(width * join) combinations (the word bridge over a lane/per-bit register)
            cost = (f"2^{e.width * e.join} ({e.join} x {e.width}-bit atoms joined in one rule)"
                    if e.join > 1
                    else f"{e.cells} x 2^{e.width}" if e.cells > 1 else f"2^{e.width}")
            out.append(f"% {e.name}: unreset {e.what}{where}, {e.width}-bit -- exact-X "
                       f"enumeration infeasible ({cost} values); seal it behind a boundary "
                       f"predicate (control/data separation) or use the completion->Lean "
                       f"forall route")
        else:
            out.append(f"{{ {q(term, ', V, 0)')} : V = 0..{2 ** e.width - 1} }} = 1{guard}.   "
                       f"% {e.name} powers on UNKNOWN (no reset): one answer set per "
                       f"{'cell ' if e.form == 'addressed' else 'lane ' if e.form == 'lane' else ''}"
                       f"value")
    return out


def _xinit_header(top: str, modular: bool) -> list[str]:
    inc = f"clingo <outdir>/*.lp  (this file composes with the others)" if modular else           f"clingo {top}.lp scenario.lp {top}__xinit.lp"
    return [
        f"% __xinit.lp for `{top}` -- EXACT-X power-on state (on by default; --no-x-init omits).",
        "%",
        "% A 4-state register with no reset powers on UNKNOWN (IEEE 1800: x). This tool does not",
        "% push an x token through the logic -- 4-state simulation approximates unknownness in",
        "% BOTH directions (notes/design/X_SEMANTICS.md, witnessed in examples/rtl2asp/x_semantics_lab/).",
        "% Instead each unknown is a CHOICE over its domain: one answer set per power-on value.",
        "%   * a property checked with the require-the-violation polarity is therefore proven",
        "%     (UNSAT) or refuted (SAT) over EVERY power-on value at once;",
        "%   * a scenario fact val(reg, V, 0) SATISFIES the choice, so pinning a concrete value",
        "%     still works and existing scenarios compose unchanged.",
        f"%   solve:  {inc}",
        "",
    ]


def dontcare_lines(design: Design, text: str) -> list[str]:
    """The boundary choices for every `x`-valued assignment the design DECLARED.

    The design layer emits `dontcare_at(Sig, T) :- <the arm's guards>.` -- a value-free statement of
    WHERE it is unconstrained -- and this turns each into the choice that says what unconstrained
    MEANS: any value of the signal's width, one answer set per value. Keeping the choice out of the
    design file is hard rule 3 (the design layer is positive-definite; choices are the boundary
    layer's), and it is the same split power-on uses.

    Read off the EMITTED TEXT rather than from a list the emitter also keeps, so a declaration that
    reaches the program is the one that gets a choice -- the F12/F4 discipline.

    An ENUM's domain is its MEMBER POOL, never 2^width (the Fix 86 lesson); a signal too wide to
    enumerate gets guidance instead of a grounding blow-up, like `wide` power-on."""
    sigs: list[str] = []
    for ln in text.splitlines():
        if ln.startswith("dontcare_at("):
            nm = ln[len("dontcare_at("):].split(",", 1)[0].strip()
            if nm not in sigs:
                sigs.append(nm)
    if not sigs:
        return []
    width = {sg.name: sg.irtype.width for sg in design.signals}
    enum_of = {sg.name: sg.enum_type for sg in design.signals if sg.enum_type}
    members = {en.name: [lab for lab, _v in en.members] for en in design.enums}
    out = ["", "% ---- DON'T-CARE values: where the RTL assigned `x`, the design constrains nothing.",
           "% Each is one answer set per value, so a property must hold for EVERY resolution --",
           "% never a value invented on the design's behalf (notes/design/X_SEMANTICS.md)."]
    for nm in sigs:
        base = nm.split("(", 1)[0]
        if base in enum_of and enum_of[base] in members:
            pool = "; ".join(members[enum_of[base]])
            out.append(f"{{ val({nm}, V, T) : V = ({pool}) }} = 1 :- dontcare_at({nm}, T).   "
                       f"% unconstrained: any MEMBER of {enum_of[base]}")
            continue
        w = width.get(base)
        if w is None:
            continue
        if w > XINIT_CAP:
            out.append(f"% {nm} is unconstrained where `dontcare_at({nm}, T)` holds, but {w} bits is "
                       f"{2 ** 20}+ values -- enumerating it would not ground. Constrain it in the "
                       f"scenario, or read the datapath symbolically.")
            continue
        out.append(f"{{ val({nm}, V, T) : V = 0..{2 ** w - 1} }} = 1 :- dontcare_at({nm}, T).   "
                   f"% unconstrained: any {w}-bit value")
    return out


def xinit_lp(design: Design, bitvec: bool = True, text: str = "") -> str | None:
    """The flat-mode companion file, or None when the design leaves nothing unknown. ``text``
    is the emitted design program: the join each family is read at comes off its rules."""
    lines = _xinit_lines(design, None, bitvec, text) + dontcare_lines(design, text)
    if not lines:
        return None
    return "\n".join(_xinit_header(design.name, False) + lines) + "\n"


def xinit_modular(modular: dict, bitvec: bool = True, files: dict | None = None) -> str | None:
    """The modular companion: every unreset state element INSTANCE, val/4-qualified like the
    scenario stub."""
    specs, tree = modular["specs"], modular["tree"]
    body: list[str] = []
    for n in tree:
        body += _xinit_lines(specs[n["spec"]], n["path"], bitvec,
                             (files or {}).get(f"{n['spec']}.lp", ""))
    if not body:
        return None
    return "\n".join(_xinit_header(modular["top"], True) + body) + "\n"


def _init_zero_lines(design: Design, inst: str | None, bitvec: bool = True) -> list[str]:
    """CONCRETE power-on state: every unreset state element pinned to 0 at T=0.

    The TESTING half of the F4 split. The design `.lp` is the transition relation and carries
    no initial state, so a property can quantify over power-on rather than inherit one baked-in
    start -- but a test wants ONE model, fast and debuggable, and a proof wants the symbolic
    range. Those are different jobs and neither belongs in the translation. `__xinit.lp` is the
    symbolic artifact; this is the concrete one, and each fact SATISFIES the matching choice,
    so composing both narrows to this value and the model is unique again.

    Zero is ARBITRARY. It is not what the hardware does -- an uninitialised array or unreset
    register reads x -- and it is not a default this tool is entitled to pick. It is here
    because a test has to name SOME value and zero is the conventional one to name. That is the
    whole justification, and it is why the file is OPT-IN (`--init-zero`) and never composed
    unless asked for: a tool that quietly supplies zeros has gone back to inventing power-on
    state, which is the defect F4 removed, one filename over.

    An element the choice file only COMMENTS on (2-state, or too wide/large to enumerate) is
    pinned here too: this file's job is a complete concrete start, and the reasons not to
    enumerate 2^w symbolically do not apply to one ground fact."""
    q = (lambda t, v: f"val({inst}, {t}, {v}, 0)") if inst else (lambda t, v: f"val({t}, {v}, 0)")
    out: list[str] = []
    for e in _xinit_elements(design, bitvec):
        if e.kind == "skip" or (e.form == "lane" and not e.dims):
            continue          # nothing to pin, or no extent to pin it over (see `_xinit_lines`)
        # an enum's zero is its FIRST MEMBER, not the integer 0: the signal's values are tags,
        # and `val(st, 0, 0)` would name a value the design's rules never mention.
        zero = e.labels[0] if e.kind == "enum_pool" and e.labels else "0"
        term, guard, _span = _xinit_target(e, inst)
        if e.gate is not None:                      # a latch: pin it only while it is OPAQUE at t=0
            gsig, gval = e.gate
            glit = f"val({inst}, {gsig}, {gval}, 0)" if inst else f"val({gsig}, {gval}, 0)"
            guard = f"{guard}, {glit}" if guard else f" :- {glit}"
        out.append(q(term, zero) + guard + ".")
    return out


def _init_zero_header(top: str, modular: bool) -> list[str]:
    inc = ("clingo <outdir>/*.lp  (this file composes with the others)" if modular else
           f"clingo {top}.lp scenario.lp {top}__init0.lp")
    return [
        f"% __init0.lp for `{top}` -- CONCRETE power-on state (all zeros; --init-zero writes it).",
        "%",
        "% The design .lp is the TRANSITION RELATION and carries no initial state (F4). This file",
        "% supplies one, for TESTING: one model, deterministic, debuggable. Each fact satisfies",
        "% the matching __xinit.lp choice, so composing both narrows to this value.",
        "%",
        "% Zero is a convenience, NOT hardware: an uninitialised array or unreset register reads",
        "% x. Replace this file with real power-on values when that matters, or drop it and let",
        "% __xinit.lp range over every power-on state.",
        f"%   solve:  {inc}",
        "",
    ]


def init_zero_lp(design: Design, bitvec: bool = True) -> str | None:
    """The flat-mode concrete-init file, or None when the design has no unreset state."""
    lines = _init_zero_lines(design, None, bitvec)
    if not lines:
        return None
    return "\n".join(_init_zero_header(design.name, False) + lines) + "\n"


def init_zero_modular(modular: dict, bitvec: bool = True) -> str | None:
    """The modular concrete-init file: every unreset state element INSTANCE, val/4-qualified."""
    specs, tree = modular["specs"], modular["tree"]
    body: list[str] = []
    for n in tree:
        body += _init_zero_lines(specs[n["spec"]], n["path"], bitvec)
    if not body:
        return None
    return "\n".join(_init_zero_header(modular["top"], True) + body) + "\n"


def _stub_init(inst: str, name: str, shape: Shape | None, sig, design: Design) -> str:
    """One T=0 register-init GROUND fact (value 0 / first tag). ADDRESSED/INDEXED are emitted
    commented (they need a concrete address / lane index)."""
    note = _shape_note(shape, sig, design) if sig is not None else "memory"
    if shape == Shape.TAG:
        v = (_enum_labels(design, sig) or ("tag",))[0]
        line = f"val({inst}, {name}, {v}, 0)."
    elif shape == Shape.INDEXED:
        return f"% val({inst}, {name}(L), 0, 0).   % {note}: one fact per lane index L"
    elif shape == Shape.ADDRESSED:
        return f"% val({inst}, {name}(A), 0, 0).   % memory: one fact per address A"
    else:
        line = f"val({inst}, {name}, 0, 0)."
    return f"{line:<44}% {note} @ T=0"


def _stub_observe(top: str, sig, shape: Shape | None) -> tuple[str, str]:
    """(rule, show-name) observing one top output as obs_<sig>."""
    pred = f"obs_{sig.name}"
    if shape == Shape.TAG:
        return f"{pred}(T, G) :- val({top}, {sig.name}, G, T).", f"{pred}/2"
    if shape == Shape.INDEXED:
        return f"{pred}(T, L, V) :- val({top}, {sig.name}(L), V, T).", f"{pred}/3"
    return f"{pred}(T, V) :- val({top}, {sig.name}, V, T).", f"{pred}/2"


def scenario_stub(modular: dict, k: int = 8, primary_clock: str | None = None) -> str:
    """Emit a ready-to-edit scenario SKELETON for a modular translation: the run length, a T=0 init
    GROUND fact per register instance, a GROUND stimulus fact per top input *per cycle*, and an
    observe predicate per top output -- all in the right ``val(Inst, …)`` shape (with a field
    legend), so authoring is fill-in-the-value, not derive-the-shape. Stimulus is ground facts (not
    rules over all T), so values are set per cycle and never double-drive. ``modular`` is the dict
    from ``PyslangFrontend.parse_modular``."""
    specs, tree = modular["specs"], modular["tree"]
    top, clk = modular["top"], primary_clock or modular["topclk"] or "clk"
    shapes_of = {key: analyze(d).shape for key, d in specs.items()}

    top_node = next((n for n in tree if n["parent"] is None), None)
    top_design = specs[top_node["spec"]] if top_node else None

    out: list[str] = [
        f"% Scenario STUB for the modular translation of `{top}` (--mode modular).",
        "% Signals are INSTANCE-qualified: val(Inst, Sig, ...). The top instance id is the top",
        f"% module name `{top}`; submodule state lives at its instance path (e.g. u_lane0(u_acc)).",
        "%",
        *_legend(),
        "%",
        f"%   compose & solve:  clingo <outdir>/*.lp {top}__scenario_stub.lp",
        f"#const k = {k}.",
        f"time({clk}, 0..k).",
        "",
        "% --- initial register state: one GROUND T=0 fact per register instance ---",
    ]

    init_lines: list[str] = []
    for n in tree:
        d = specs[n["spec"]]
        sh = shapes_of[n["spec"]]
        for s in [s for s in d.signals if s.is_reg]:
            init_lines.append(_stub_init(n["path"], s.name, sh.get(s.name), s, d))
        for m in d.mems:
            init_lines.append(_stub_init(n["path"], m.name, Shape.ADDRESSED, None, d))
    out += (init_lines or ["% (no registers — purely combinational)"])

    out += ["", f"% --- top inputs: one GROUND fact per cycle (T=0..{k}); set each value ---"]
    if top_design is not None:
        sh = shapes_of[top_node["spec"]]
        ins = [s for s in top_design.signals if s.direction == "input" and s.name != clk]
        for s in ins:
            out += _stub_input(top, s, sh.get(s.name), top_design, k)
        if not ins:
            out.append("% (no input ports)")

    out += ["", "% --- observe top outputs (these stay RULES: they derive obs_ from val) ---"]
    if top_design is not None:
        sh = shapes_of[top_node["spec"]]
        outs = [s for s in top_design.signals if s.direction == "output"]
        rules, shows = [], []
        for s in outs:
            rule, show = _stub_observe(top, s, sh.get(s.name))
            rules.append(rule)
            shows.append(f"#show {show}.")
        out += rules or ["% (no output ports)"]
        if shows:
            out.append(" ".join(shows))
    return "\n".join(out) + "\n"
