"""Signal-shape and per-bit (bitvec) classification — the analysis the emitter consumes.

This is a structural refactor of the original monolithic ``stage2_analysis.analyze``: the six
classification phases are now explicit, named transfer functions over a mutable ``_State``, and the
per-bit *bridge direction* is carried as first-class data (``bitvec_word_form``) rather than
re-derived at emit time. That last point is the lesson of Fix 42 — a signal pulled into the per-bit
set by group-closure but emitted in word form needs the OPPOSITE bridge direction, and inferring
that from a flag at emit time is where the original bug lived.

Semantics are identical to the original (guarded by scripts/analysis_parity.py and the .lp byte
parity gate). The phases, in order:

  1. base_shapes      — width (BIT/WORD) + memory family (ADDRESSED) + enum (TAG)
  2. indexed_lanes    — vectored-flop / generate-for lane signals, propagated over lane groups
  3. bitvec_trigger   — wide WORD signals with a sole bit-structural comb driver (+ group closure)
  4. bitvec_seqshift  — sequential + shift-of-bitvec fixed point (mutually dependent → run together)
  5. word_consumers   — wide-lane bitvec signals read as per-lane words downstream
  6. word_form        — bitvec signals whose sole driver is NOT bit-structural (decompose bridge)
"""

from __future__ import annotations

from dataclasses import dataclass, field

from ..ir.expr import BinOp, BitSel, Concat, Cond, Const, EnumCast, EnumVal, Expr, LaneIdx, MemRef, Ref, SExt, Slice, Tag, UnOp
from ..ir.nodes import Design
from ..ir.types import Shape

# Bitwise operators that act element-wise (per lane); arithmetic/compare/reduction do not.
_LANE_OPS = {"and", "or", "xor"}

# Word-level ops: produce a packed integer result; reading an INDEXED operand requires val(sig(I),V,T).
# Must stay in sync with _WORD_OPS in stage3_emit.py.
_WORD_OPS = frozenset({
    "add", "sub", "mul", "div", "mod", "sidiv", "simod",
    "and", "or", "xor", "shl", "shr", "ashr", "pow", "clz",
})

# Comparison ops: in a lane-AND context, operands are read as per-lane words.
_CMP_OPS = frozenset({"eq", "ne", "lt", "le", "gt", "ge", "llt", "lle", "lgt", "lge"})

_SHIFT_OPS = ("shl", "shr", "ashr")


# ---------------------------------------------------------------------------
# Expression predicates (pure; no state)
# ---------------------------------------------------------------------------

def _refs_in(e: Expr) -> set[str]:
    """Collect all Ref.name values in an expression tree (any depth)."""
    if isinstance(e, Ref):
        return {e.name}
    if isinstance(e, (Const, Tag, LaneIdx)):
        return set()
    if isinstance(e, (BinOp,)):
        return _refs_in(e.left) | _refs_in(e.right)
    if isinstance(e, (UnOp, SExt, EnumCast, EnumVal)):
        return _refs_in(e.operand)
    if isinstance(e, (Slice, BitSel)):
        return _refs_in(e.base)
    if isinstance(e, Concat):
        out: set[str] = set()
        for part, _ in e.parts:
            out |= _refs_in(part)
        return out
    if isinstance(e, Cond):
        return _refs_in(e.sel) | _refs_in(e.a) | _refs_in(e.b)
    if isinstance(e, MemRef):
        out = set()
        for addr in e.addrs:
            out |= _refs_in(addr)
        return out
    return set()


def _flatten_logand(e: Expr) -> list[Expr]:
    """Flatten a chain of logand into its conjuncts (mirrors stage3_emit._flatten_logand)."""
    if isinstance(e, BinOp) and e.op == "logand":
        return _flatten_logand(e.left) + _flatten_logand(e.right)
    return [e]


def _is_lane_and_rhs(e: Expr) -> bool:
    """True if e is a logand-of-lane-conjuncts (comparison or bit-ref per lane).
    In that context, comparison operands are read as per-lane words (Path C)."""
    parts = _flatten_logand(e)

    def _ok(p: Expr) -> bool:
        if isinstance(p, Ref):
            return True
        if isinstance(p, UnOp) and p.op == "lnot" and isinstance(p.operand, Ref):
            return True
        return isinstance(p, BinOp) and p.op in _CMP_OPS

    return all(_ok(p) for p in parts)


def _lane_refs(e: Expr) -> set[str] | None:
    """If ``e`` is a pure per-lane (bitwise) expression over signal refs, return the set of
    refs it touches; else None. A copy (bare Ref) is the trivial case. A Const or any
    word-level op (add/compare/slice/mux) makes the expression non-per-lane -> None."""
    if isinstance(e, Ref):
        return {e.name}
    if isinstance(e, UnOp) and e.op == "not":
        return _lane_refs(e.operand)
    if isinstance(e, BinOp) and e.op in _LANE_OPS:
        left, right = _lane_refs(e.left), _lane_refs(e.right)
        return None if left is None or right is None else left | right
    return None


def _is_bitstructural(e: Expr) -> bool:
    """True when ``e`` is a *structural* bit-assembly RHS the per-bit emitter can lower to compact
    range-guarded per-index rules: a concatenation (incl. replication), a sign-extension, a constant
    slice/bit-select of a signal, or a Cond(sel, a, b) where both arms are bitstructural (masked-mux
    of two per-bit expressions, e.g. sf?srcA:sign_ext_concat). These are the shapes that produce
    O(N^2) @shl/@bor chains in the word model and compact O(1)-rule ranges in the per-bit model."""
    if isinstance(e, (Concat, SExt)):
        return True
    if isinstance(e, Slice) and isinstance(e.base, Ref):  # noqa: SIM103
        return True
    if isinstance(e, Cond):                              # masked-mux of two bitvec arms
        def _ok(x: Expr) -> bool:
            return isinstance(x, Const) or _is_bitstructural(x)
        return _ok(e.a) and _ok(e.b)
    return False


def _is_shift_of_bitvec(e: Expr, bitvec_signals: set[str]) -> bool:
    """y = x << n / x >> n / x >>> n where x is (a slice of) a per-bit signal: an index remap."""
    return (
        isinstance(e, BinOp) and e.op in _SHIFT_OPS and (
            (isinstance(e.left, Ref) and e.left.name in bitvec_signals)
            or (isinstance(e.left, Slice) and isinstance(e.left.base, Ref)
                and e.left.base.name in bitvec_signals)
        )
    )


# ---------------------------------------------------------------------------
# Result object (unchanged public shape) + working state
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Analysis:
    shape: dict[str, Shape]
    # --bitvec (phase 1): wide signals chosen for the per-bit representation, and their total widths.
    # Empty unless bitvec=True. The emitter folds these into its lane bookkeeping (lane_dims=1,
    # lane_elem_w=1) so the existing lane<->word bridge and per-lane rules apply.
    bitvec_signals: frozenset[str] = frozenset()
    bitvec_width: dict[str, int] = field(default_factory=dict)
    # --bitvec phase 5: wide-lane bitvec signals (lane_elem_w>1) that have at least one downstream
    # rule reading val(sig(I),V,T) as a word (e.g. @add, comparison, non-bitvec lane register capture).
    # For signals NOT in this set, no inner bridge is needed; val(sig(I,J),B,T) is the complete model.
    bitvec_word_consumers: frozenset[str] = frozenset()
    # --bitvec phase 1 supplement: bitvec signals whose sole comb driver is NOT bit-structural (e.g.
    # a Cond with a word-op arm, pulled into bitvec_signals via group-closure propagation). The emitter
    # produces val(sig, V, T) (word form) for these — the lane<->word bridge must decompose word→per-bit
    # rather than assemble per-bit→word, or per-bit atoms would never be derived. (Fix 42.)
    bitvec_word_form: frozenset[str] = frozenset()


WORD_BRIDGE_BUDGET_BITS = 20      # 2^20 ground instances of ONE rule is where "slow" becomes "never"
                                  # (scripts/scenario_budget.py's DEFAULT_BUDGET_BITS, the same number)


class Shapes(dict):
    """The shape map, plus two facts the emitter's word reader needs and cannot recover from the
    shape alone -- carried on the map itself so every one of the reader's forty-odd call sites
    sees them without a new argument (the Fix-42 lesson: a bridge fact is first-class data).

    ``bit_atoms``: the signals whose per-lane atoms are single BITS at one index level
    (``val(sig(k), B, T)``, k the bit position) -- every per-bit signal of element width 1 and
    every one-level lane of 1-bit elements. For these, a constant slice or bit select can be read
    from the bits directly instead of from the assembled word.

    ``budget_bits``: the grounding budget. The word of a per-bit signal is ASSEMBLED from its
    bits by one rule joining all of them, 2^N instances when the bits are not fixed at grounding
    (any register-derived signal): 20 bits is a million, 36 bits never finishes (F32, 2026-09-03).
    Above the budget the word is not assembled; a slice reads the bits; a whole-word read is
    refused by name."""
    bit_atoms: frozenset = frozenset()
    budget_bits: int = WORD_BRIDGE_BUDGET_BITS


@dataclass
class _State:
    """Mutable working state threaded through the phases; frozen into an Analysis at the end."""
    design: Design
    bitvec: bool
    shape: dict[str, Shape] = field(default_factory=dict)
    indexed: set[str] = field(default_factory=set)
    groups: list[set[str]] = field(default_factory=list)          # lane-equivalence groups
    bitvec_signals: set[str] = field(default_factory=set)
    bitvec_width: dict[str, int] = field(default_factory=dict)
    word_consumers: set[str] = field(default_factory=set)
    word_form: set[str] = field(default_factory=set)
    # caches
    by_name: dict = field(default_factory=dict)
    drivers: dict[str, list[Expr]] = field(default_factory=dict)  # comb lhs -> its RHS(es)
    regs: set[str] = field(default_factory=set)
    lane_elem_w: dict[str, int] = field(default_factory=dict)

    def _wide_word(self, name: str) -> bool:
        """A concrete-width (>1) signal currently classified WORD — the per-bit candidate gate."""
        s = self.by_name.get(name)
        return (s is not None and isinstance(s.irtype.width, int) and s.irtype.width > 1
                and self.shape.get(name) == Shape.WORD)


# ---------------------------------------------------------------------------
# Phase 1 — base shapes
# ---------------------------------------------------------------------------

def _phase_base_shapes(st: _State) -> None:
    for s in st.design.signals:
        if s.enum_type is not None:
            st.shape[s.name] = Shape.TAG  # enum -> symbolic tag value, val(s, <label>, T)
            continue
        w = s.irtype.width
        st.shape[s.name] = Shape.BIT if (isinstance(w, int) and w == 1) else Shape.WORD
    for m in st.design.mems:
        st.shape[m.name] = Shape.ADDRESSED


# ---------------------------------------------------------------------------
# Phase 2 — INDEXED (lane) shape
# ---------------------------------------------------------------------------

def _phase_indexed_lanes(st: _State) -> None:
    """Seed from every vectored-flop port (read/written per-lane) and generate-over-vector signal,
    then propagate over lane-equivalence groups: each per-lane comb item ties {lhs} ∪ {its refs}
    into one group (a copy/bridge bare Ref, or a bitwise op q & mask). If any member of a group is
    indexed, the whole group is. Word-level ops (add/compare) are not groups, so the lane shape
    never leaks across a reshape seam.

    A READ operand is absorbed only if it can BE a lane vector: its declared width equals a lane
    peer's. Read bitwise against a lane at any other width it is a BROADCAST -- read whole in
    every lane, `val(en, V, T)` -- not a per-lane atom. `for(i) y[i] = a[i] & en` (scalar `en`)
    and `y[i] = a[i] & mask` (an element-wide `mask` against W>1 element lanes) used to absorb
    `en` / `mask` and emit `val(en(I), ..)`, which nothing derives: `y` had NO value at any
    instant, with exit 0 and `coverage: OK`. The register path never had the hole (a scalar
    enable renders `val(en, 1, T)`); this makes the comb path agree. The LHS of a lane-shaped
    item is exempt: a condition hoisted inside a lane body (`c4 = alloc_we[e]`) is declared at
    ELEMENT width yet is per-lane by construction. Unknown widths keep the legacy absorption."""
    for v in st.design.vffs:
        st.indexed |= {v.en, v.d, v.q}
    st.indexed |= set(st.design.lane_signals)
    group_lhs: list[str] = []
    for c in st.design.comb:
        refs = _lane_refs(c.rhs)
        if refs is not None:
            st.groups.append({c.lhs} | refs)
            group_lhs.append(c.lhs)

    def _width(n: str) -> int | None:
        s = st.by_name.get(n)
        w = s.irtype.width if s is not None else None
        return w if isinstance(w, int) else None

    ldims = getattr(st.design, "lane_dims", {}) or {}
    pdims = getattr(st.design, "packed_dims", {}) or {}

    def _rank(n: str) -> int:
        """How many index LEVELS a signal's lanes have: a nested generate's `g(I, J)` is two, a
        packed `logic [R-1:0][C-1:0]` declared as such is two, everything else one."""
        return max(ldims.get(n, 1), len(pdims.get(n, ())) or 1)

    def _is_broadcast(m: str, peers: set[str], lhs: str) -> bool:
        # a member whose lanes have a DIFFERENT NUMBER OF LEVELS than its peers' is a WORD,
        # never a lane peer -- even as the item's own LHS: `assign w = ul;` with `ul` a two-level
        # lane pulled the 9-bit `w` in as nine one-level lanes, `val(w(I), V, T) :- val(ul(I, J),
        # V, T)`, every w(I) took three values and the modular program was UNSAT (the 2-D
        # torus's pack, 2026-09-03). As a word, `w` is the copy of ul's assembled word.
        peer_ranks = {_rank(p) for p in peers if p != m}
        if bool(peer_ranks) and _rank(m) not in peer_ranks:
            return True
        if m == lhs:                 # this item DEFINES m from a lane -> per-lane, whatever its width
            return False
        wm = _width(m)
        if wm is None:
            return False
        peer_ws = {_width(p) for p in peers} - {None}
        return bool(peer_ws) and wm not in peer_ws

    _closure(st.indexed, st.groups, _is_broadcast, group_lhs)
    for n in st.indexed:
        st.shape[n] = Shape.INDEXED


def _closure(seed: set[str], groups: list[set[str]], reject=None,
             group_lhs: list[str] | None = None) -> None:
    """Grow ``seed`` in place: any group that touches it is absorbed whole. Monotone → terminates.
    ``reject(member, seed_peers_in_group, group_lhs)`` -> True keeps that member OUT (a
    broadcast, see ``_phase_indexed_lanes``); a rejected member stays out of every group so it
    is never both a whole read and a lane atom."""
    excluded: set[str] = set()
    changed = True
    while changed:
        changed = False
        for k, g in enumerate(groups):
            live = g - excluded
            if not (live & seed) or live <= seed:
                continue
            if reject is not None:
                lhs = group_lhs[k] if group_lhs is not None else ""
                for m in live - seed:
                    if reject(m, live & seed, lhs):
                        excluded.add(m)
                live = g - excluded
                if live <= seed:
                    continue
            seed |= live
            changed = True


# ---------------------------------------------------------------------------
# Phase 3 — bitvec trigger + group closure
# ---------------------------------------------------------------------------

def _phase_bitvec_trigger(st: _State) -> None:
    """The NARROW per-bit trigger: a wide WORD signal (or wide-element lane signal from a
    generate-for) whose sole combinational driver is bit-structural is chosen for per-bit rep.
    Then pull bit-parallel neighbours in through the same lane-equivalence groups (a bitwise chain
    over a chosen signal is itself per-bit)."""
    for name, rhss in st.drivers.items():
        s = st.by_name.get(name)
        if s is None or len(rhss) != 1:            # unknown / multi-driver -> leave word
            continue
        w = s.irtype.width
        if not (isinstance(w, int) and w > 1):     # 1-bit or symbolic-width -> not a bitvec win
            continue
        elem_w = st.lane_elem_w.get(name, 1)
        is_wide_lane = name in st.indexed and elem_w > 1  # wide per-lane: generate-for, W>1 element
        if (name in st.regs
                or (name in st.indexed and not is_wide_lane)   # 1-bit/VFF lanes: already fine
                or (st.shape.get(name) not in (Shape.WORD, Shape.INDEXED))
                or (s.is_port and not is_wide_lane)  # ports excluded except wide-lane (generate-driven)
                or "(" in name):       # functor-shaped (struct field / hierarchy / lane) -> skip
            continue
        if _is_bitstructural(rhss[0]):
            st.bitvec_signals.add(name)
            st.bitvec_width[name] = w

    # group closure: reuse the phase-2 lane groups. A bitwise chain over a chosen signal is per-bit.
    seeded = set(st.bitvec_signals)
    changed = True
    while changed:
        changed = False
        for g in st.groups:
            if (g & seeded) and not (g <= seeded):
                for m in g - seeded:
                    sm = st.by_name.get(m)
                    if (sm is not None and m not in st.regs and st.shape.get(m) == Shape.WORD
                            and isinstance(sm.irtype.width, int) and sm.irtype.width > 1):
                        st.bitvec_width.setdefault(m, sm.irtype.width)
                seeded |= g
                changed = True
    st.bitvec_signals = {m for m in seeded if m in st.bitvec_width}
    for n in st.bitvec_signals:
        st.shape[n] = Shape.INDEXED


# ---------------------------------------------------------------------------
# Phase 4 — sequential + shift-of-bitvec fixed point
# ---------------------------------------------------------------------------

def _phase_bitvec_seqshift(st: _State) -> None:
    """The sequential and shift-of-bitvec triggers are mutually dependent:
      - a register q <= shifted_comb needs shifted_comb in bitvec_signals (shift pass first);
      - a shift comb y = reg << n needs reg in bitvec_signals (seq pass first).
    Neither ordering alone is complete, so run BOTH to a shared fixed point. Each pass is monotone
    (only adds), so the loop terminates when a full round adds nothing."""
    regs_with_reset = {it.reg for it in st.design.seq if it.reset is not None}

    def _add(name: str, w: int) -> None:
        st.bitvec_signals.add(name)
        st.bitvec_width[name] = w
        st.shape[name] = Shape.INDEXED

    def _seq_pass() -> bool:
        added = False
        for it in st.design.seq:
            if it.combinational:
                continue
            name = it.reg
            s = st.by_name.get(name)
            if s is None:
                continue
            w = s.irtype.width
            if not (isinstance(w, int) and w > 1):
                continue
            if (name in st.bitvec_signals or name in st.indexed or st.shape.get(name) != Shape.WORD
                    or name in regs_with_reset               # phase 1: skip regs with reset paths
                    or (s.is_port and s.direction == "input") or "(" in name):
                continue
            # A branch D-input qualifies if bit-structural, a copy of a bitvec signal, or a shift of a
            # bitvec signal. Exclude self-refs (hold branches) and Tag (enum state).
            for br in it.branches:
                e = br.value
                if isinstance(e, (Tag, Ref)) and (not isinstance(e, Ref) or e.name not in st.bitvec_signals):
                    continue
                qualifies = (_is_bitstructural(e)
                             or (isinstance(e, Ref) and e.name in st.bitvec_signals)
                             or _is_shift_of_bitvec(e, st.bitvec_signals))
                if qualifies:
                    _add(name, w)
                    added = True
                    break
        return added

    def _shift_pass() -> bool:
        # A comb signal y = x << n where x is a bitvec signal is itself bit-structural (index remap).
        added = False
        for name, rhss in st.drivers.items():
            if len(rhss) != 1 or name in st.bitvec_signals:
                continue
            s = st.by_name.get(name)
            if s is None:
                continue
            w = s.irtype.width
            if not (isinstance(w, int) and w > 1):
                continue
            if (name in st.regs or name in st.indexed or st.shape.get(name) != Shape.WORD
                    or s.is_port or "(" in name):
                continue
            if _is_shift_of_bitvec(rhss[0], st.bitvec_signals):
                _add(name, w)
                added = True
        return added

    while _seq_pass() | _shift_pass():   # non-short-circuit: run BOTH each round
        pass


# ---------------------------------------------------------------------------
# Phase 5 — wide-lane word consumers
# ---------------------------------------------------------------------------

def _phase_word_consumers(st: _State) -> None:
    """Classify wide-lane bitvec signals (lane_elem_w > 1) by whether they have word consumers.
    A word consumer reads val(sig(I),V,T) — the per-lane WORD form — rather than per-bit. Only
    wide-lane signals matter; scalars always have lane_elem_w=1 and no inner bridge."""
    wide_lane_bitvec = {name for name in st.bitvec_signals if st.lane_elem_w.get(name, 1) > 1}
    if not wide_lane_bitvec:
        return
    # comb: INDEXED lhs with a word-op context reads sources as per-lane words.
    # Paths A (Ref copy), B (word-op BinOp/UnOp), C (lane-and-compare) trigger word reads.
    # Paths that do NOT: bitvec Cond/Concat/SExt/Shift — these go through _emit_bitvec.
    for c in st.design.comb:
        if st.shape.get(c.lhs) != Shape.INDEXED:
            continue
        rhs = c.rhs
        is_word_ctx = (
            isinstance(rhs, Ref)                                        # Path A: copy
            or (isinstance(rhs, BinOp) and rhs.op in _WORD_OPS)        # Path B: word arithmetic
            or (isinstance(rhs, UnOp) and rhs.op in ("not", "neg"))     # Path B: word unary
            or _is_lane_and_rhs(rhs)                                    # Path C: lane comparisons
        )
        if is_word_ctx:
            st.word_consumers |= _refs_in(rhs) & wide_lane_bitvec
    # seq: non-bitvec INDEXED registers read D-inputs via _word_body(lane_ctx=True).
    # Bitvec INDEXED registers use _emit_bitvec → read per-bit; NOT word consumers.
    for it in st.design.seq:
        if it.combinational or st.shape.get(it.reg) != Shape.INDEXED:
            continue
        if it.reg in st.bitvec_signals:
            continue  # bitvec reg reads D-input per-bit via _emit_bitvec
        for br in it.branches:
            st.word_consumers |= _refs_in(br.value) & wide_lane_bitvec


# ---------------------------------------------------------------------------
# Phase 6 — word-form set (the bridge-direction bit; Fix 42)
# ---------------------------------------------------------------------------

def _phase_word_form(st: _State) -> None:
    """bitvec signals whose sole comb driver is NOT bit-structural. Group-closure (phase 3) can pull
    a signal into bitvec_signals even when its own RHS is a word-op or non-flattenable Cond. For
    these, _emit_comb produces val(sig, V, T) (word form), so the bridge must decompose word→per-bit,
    not assemble per-bit→word. Exclusions — emitter does NOT produce word form for these:
      - bit-structural RHS (Concat/SExt/Slice/Cond-of-bitvec): _emit_bitvec path (per-bit)
      - Ref copy: emits val(sig(I),V,T) :- val(src(I),V,T) (per-bit copy)
      - shift-of-bitvec: _emit_comb takes the BinOp shift branch → per-bit index-remap"""
    for name in st.bitvec_signals:
        rhss = st.drivers.get(name, [])
        if len(rhss) != 1:
            continue  # multi-driver or no-driver: word form (no single per-bit path)
        rhs = rhss[0]
        if _is_bitstructural(rhs):
            continue
        if isinstance(rhs, Ref):
            continue
        if _is_shift_of_bitvec(rhs, st.bitvec_signals):
            continue
        # A BITWISE driver over refs (`m = t | k`, `r2 = c & t`, `~x`) is per-lane by nature: the
        # emitter lowers it per lane (`val(m(I), ..) :- val(t(I), ..), val(k(I), ..)`), so its bridge
        # must ASSEMBLE. It used to be word-form here, which gave it a DECOMPOSE bridge from a word
        # rule that was never emitted -- an OUTPUT port so driven (`assign r2 = c & t`) had per-bit
        # atoms and NO word value: a property over `val(r2, V, T)` passed vacuously, exit 0 (found by
        # the spec2rtl lane arbiter's print, 2026-08-18; `test_lane_roll_over_a_partial_index_set`
        # `wf3`/`wf4`). Word-form is now exactly the drivers the emitter renders as a WORD.
        if _lane_refs(rhs) is not None:
            continue
        st.word_form.add(name)


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def analyze(design: Design, *, bitvec: bool = False) -> Analysis:
    st = _State(design=design, bitvec=bitvec)
    st.by_name = {s.name: s for s in design.signals}
    st.regs = {s.name for s in design.signals if s.is_reg}
    st.lane_elem_w = dict(design.lane_elem_w)
    for c in design.comb:
        st.drivers.setdefault(c.lhs, []).append(c.rhs)

    _phase_base_shapes(st)
    _phase_indexed_lanes(st)
    if bitvec:
        _phase_bitvec_trigger(st)
        _phase_bitvec_seqshift(st)
    _phase_word_consumers(st)
    if bitvec:
        _phase_word_form(st)

    shape = Shapes(st.shape)
    design_lane_dims = getattr(st.design, "lane_dims", {}) or {}
    shape.bit_atoms = frozenset(
        {n for n in st.bitvec_signals if st.lane_elem_w.get(n, 1) == 1}
        | {n for n, sh in st.shape.items()
           if sh == Shape.INDEXED and st.lane_elem_w.get(n, 1) == 1 and design_lane_dims.get(n, 1) == 1})
    return Analysis(
        shape=shape,
        bitvec_signals=frozenset(st.bitvec_signals),
        bitvec_width=st.bitvec_width,
        bitvec_word_consumers=frozenset(st.word_consumers),
        bitvec_word_form=frozenset(st.word_form),
    )
