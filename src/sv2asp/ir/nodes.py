"""IR nodes: the normalized netlist + behavior model.

A thin model mirroring catalog vocabulary, built once by the frontend in source
order and frozen. Stage 2 produces a separate analysis result (it does not mutate
these nodes). Every node carries a source location for provenance + coverage.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from .expr import Expr
from .types import ElementType, IRType, Width


@dataclass(frozen=True)
class Loc:
    """A source location: file + 1-based line + the trimmed source line text."""

    file: str
    line: int
    text: str = ""


@dataclass(frozen=True)
class Param:
    """A parameter/localparam. ``value`` set for base params; ``expr`` for derived."""

    name: str
    value: int | None
    expr: Expr | None
    loc: Loc


@dataclass(frozen=True)
class Signal:
    """A scalar/vector signal (net or variable). Memories are ``Mem`` instead."""

    name: str
    irtype: IRType
    is_reg: bool  # assigned by a sequential process
    is_port: bool
    direction: str | None  # "input" | "output" | None
    initial: Expr | None  # declaration initializer (T=0 fact), if any
    loc: Loc
    enum_type: str | None = None  # name of the enum type if this signal is an enum (TAG shape)


@dataclass(frozen=True)
class Enum:
    """An enum type: its name and members (label, encoding). Drives the tag-shape schema."""

    name: str
    members: tuple[tuple[str, int], ...]  # (lowercased label, value)


@dataclass(frozen=True)
class Mem:
    """An unpacked array (addressed family of cells, catalog Section 3.5/2.9). ``dims`` holds the
    per-dimension cell counts outer-first (a 2-D array ``q[0:N][0:M]`` -> ``(N+1, M+1)``); ``depth``
    and ``addr_width`` describe the OUTER dimension (1-D back-compat). Empty ``dims`` == ``(depth,)``."""

    name: str
    elem: ElementType
    addr_width: Width
    depth: int
    loc: Loc
    dims: tuple[int, ...] = ()


@dataclass(frozen=True)
class Clock:
    """A clock domain of the design — collected up front so every stage knows the full clock structure.
    A FREE clock is a plain input (``derived=False``); a GATED clock from an ICG primitive is
    ``derived=True`` with its ``base`` clock and 1-bit ``gate`` signal (see ``DerivedClock``)."""

    name: str
    derived: bool = False
    base: str | None = None     # for a gated clock: the base clock it is gated from
    gate: str | None = None     # for a gated clock: the 1-bit gate signal


@dataclass(frozen=True)
class DerivedClock:
    """A derived clock domain (catalog §6.7). Two kinds:

    ``kind="gate"`` — the ICG clock-gating primitive: ``name`` ticks exactly when ``base``
    ticks AND the 1-bit ``gate`` signal is high; emitted as
    ``time(name, T) :- time(base, T), val(gate, 1, T).``

    ``kind="rise"`` (F27) — an INTERNAL-SIGNAL clock: a register output used as a clock
    (``always_ff @(posedge divided_clock)``). ``name`` ticks exactly across its own 0→1
    transitions on the driving domain's axis; ``gate`` is unused; emitted as
    ``time(name, T) :- time(base, T), val(name, 0, T), val(name, 1, T+1).``

    Either way a flop on ``name`` advances only on those ticks and HOLDS between them via
    the master-tick multi-clock linkage (``no_tick``)."""

    name: str
    base: str
    gate: str
    loc: Loc
    kind: str = "gate"


@dataclass(frozen=True)
class Reset:
    """Reset metadata. ``kind`` in {sync, async}; ``active`` in {low, high}."""

    signal: str
    active: str
    kind: str


@dataclass(frozen=True)
class EdgeItem:
    """A sampled-value EDGE function -- ``$rose(x)`` / ``$fell(x)``.

    Its value at an instant depends on the sampled signal at TWO adjacent clock ticks, so it is
    neither a ``CombItem`` (same instant) nor a ``SeqItem`` (a register carrying its own state):
    ``$rose(x)`` holds at ``T+1`` exactly when ``x`` reads 0 at ``T`` and 1 at ``T+1``.

    At the FIRST tick there is no previous sample, so the result is deliberately UNBOUND there --
    SystemVerilog's own answer (the previous sampled value is `x`). That partiality is announced,
    not hidden (TRANSLATION_SPEC S3.3)."""

    lhs: str        # the synthesized 1-bit signal carrying the edge
    sig: str        # the sampled signal
    rising: bool    # True = $rose, False = $fell
    clock: str      # the clock domain whose ticks define "the previous sample"
    loc: Loc


@dataclass(frozen=True)
class CombItem:
    """A continuous/combinational assignment ``lhs = rhs`` at time T.

    ``lane_hi`` is the EXCLUSIVE upper bound of the loop/generate that produced a lane-rolled
    assignment, when that range is narrower than the target array's address domain. The
    emitted rule must then guard the lane variable (`I < lane_hi`): `addr(y, I)` ranges over
    the whole ARRAY, but a `for (i=0;i<3;i++)` over `y[0:7]` drives only lanes 0..2 and must
    leave the rest undriven. ``None`` = the loop covers the whole domain (no guard needed).
    ``lane_lo`` is the loop's START (inclusive): `for (i = 1; ...)` writes lanes `lane_lo ..
    lane_hi-1`, and the rule's domain literal is `I = lane_lo..lane_hi-1`. Zero (the default) is
    the canonical loop; a partial range with a non-zero start used to be refused, before that
    it was rolled over every lane (0b L4)."""

    lhs: str
    rhs: Expr
    loc: Loc
    lane_hi: int | None = None
    lane_lo: int = 0
    lane_step: int = 1   # the loop's stride: `i += 2` writes lo, lo+2, .. -- `(I - lo) \ step = 0`
    lane_off: int = 0    # `y[i+1] = ..`: the head lane is I+off (the carry-chain shape `c[i+1] = ..`)


@dataclass(frozen=True)
class Branch:
    """One priority arm: fire ``value`` when all ``guards`` and ``tag_guards`` hold.

    A guard is (signal_name, polarity) — the required 1-bit value. A tag_guard is
    (signal_name, tag) — the enum signal must equal that tag (a ``case`` arm match).
    The frontend folds in the full path condition (else-branches carry the negated guard),
    so a register's branches are mutually exclusive and need no implicit-hold complement.
    """

    guards: tuple[tuple[str, int], ...]
    value: Expr
    tag_guards: tuple[tuple[str, str], ...] = ()
    neg_matches: tuple[tuple[str, str], ...] = ()  # selector != value (a case `default` arm)
    loc: Loc | None = None  # source line of THIS branch's assignment (per-branch provenance); a
    #                         register driven across several if/case arms attributes each rule to its line


@dataclass(frozen=True)
class SeqItem:
    """A clocked register update with optional reset and a priority branch chain."""

    reg: str
    clock: str
    reset: Reset | None
    branches: tuple[Branch, ...]
    has_hold: bool
    loc: Loc
    reset_value: int | str = 0  # value assigned by the reset branch (captured from RTL); a str is an enum TAG
    combinational: bool = False  # always_comb: emit at T (no clock/T+1/hold), not a register
    lane_domain: str | None = None  # owner of the lane domain when this is an INDEXED (array) reg
    # The index range of the loop/generate that lane-rolled this register (`for (i = lo; i < hi;
    # i++) q[i] <= ..`): the emitted rules take the domain literal `I = lane_lo..lane_hi-1`, so a
    # PARTIAL loop drives only its own lanes. ``lane_hi`` None = the loop covers the whole lane
    # domain of the register (no literal needed unless nothing else binds I). Before these
    # existed, a partial sequential lane loop over a packed vector was rolled over EVERY lane.
    lane_hi: int | None = None
    lane_lo: int = 0
    lane_step: int = 1
    lane_off: int = 0


@dataclass(frozen=True)
class MemWrite:
    """A clocked memory write, gated by ``guards`` (catalog Section 2.9).

    For a whole-cell write ``data`` is the new cell value. For a struct-array FIELD write
    (``arr[i].f <= v``) ``rmw_slices`` holds the written slices ``[(off, w, val), ...]`` and the
    emitter computes a read-modify-write of the cell (untouched bits retain), ``cell_width`` is the
    cell's bit width."""

    mem: str
    addrs: tuple[Expr, ...]      # one Expr per unpacked dimension (q[i] -> 1, q[i][j] -> 2)
    data: Expr
    guards: tuple[tuple[str, int], ...]
    clock: str
    loc: Loc
    rmw_slices: tuple = ()       # field writes into the cell -> read-modify-write
    cell_width: int = 0
    lane_rolled: bool = False    # a `for`/`while` write q[i]<=.. lane-rolled over addr(mem, I[, J])
    lane_hi: tuple[int | None, ...] = ()   # per-dim exclusive bound for a PARTIAL loop (None = full)
    lane_lo: tuple[int, ...] = ()          # per-dim START of the loop (`for (i = 1; ..)`; () = all 0)
    reset: tuple | None = None             # F16: (rst_signal, released_polarity, cell_reset_value) when the
    #                                        write sits in an async-reset block whose reset arm clears the cells


@dataclass(frozen=True)
class MemRead:
    """A memory read into ``lhs``. ``sync`` False = combinational read."""

    lhs: str
    mem: str
    addrs: tuple[Expr, ...]
    sync: bool
    loc: Loc


@dataclass(frozen=True)
class MuxItem:
    """Encoded select: out = arms[sel]  (a case/mux over the word ``sel``)."""

    out: str
    sel: str
    arms: tuple[Expr, ...]   # arms[i] drives out when sel == i
    loc: Loc
    #: ONE-HOT selector (VCMUX): arm i is guarded by `sel == 2**i` rather than `sel == i`, and
    #: an all-zero selector drives 0. Single-valuedness holds for the same reason as the binary
    #: mux -- the guards are distinct selector VALUES -- and the covered set is the one-hot
    #: codes plus zero, which is what the partiality warning counts.
    onehot: bool = False


@dataclass(frozen=True)
class VffItem:
    """Vectored flop (the ``VFF`` primitive): ``lanes`` independent per-lane flops with per-lane enable.

    Functor lane shape (catalog §4.6): each lane is a functor signal ``q(I)`` -- val(q(I), V, T). The
    per-lane value V keeps its OWN shape: at ``width == 1`` it is the bit; at ``width > 1`` it is the
    whole ``width``-bit WORD (one rule shape either way, and word arithmetic on a lane works). en is
    per-lane (val(en(I), 1, T)). The lane domain is qualified by the INSTANCE name ``inst``
    (``lane(inst, I)``) -- the entity that owns the lanes and is unique by construction -- not the
    output net (a proxy that can collide when two instances drive slices).
    """

    q: str
    d: str
    en: str
    clock: str
    lanes: int
    inst: str
    loc: Loc
    width: int = 1   # per-lane bit width; >1 -> the per-lane value V is a W-bit word (lane_shape marker)


@dataclass(frozen=True)
class CellInfo:
    """A structural instance in the netlist: its name, the cell/module type it instantiates, the
    net(s) it drives, and the enclosing module/instance. Pure provenance -- behaviour is the flattened
    Comb/Seq/Mux/Vff items; this manifest just records the instance->celltype->driven-net structure that
    flattening otherwise discards (emitted as ``cell/3`` + ``cell_out/2``)."""

    inst: str                 # instance name; path-qualified u_sub(u_inner) when nested
    cell_type: str            # lowercased SV cell/module name (a valid clingo constant)
    outs: tuple[str, ...]     # output net(s) this instance drives (0..N)
    parent: str               # enclosing module name (top) or qualifying instance functor (nested)


@dataclass(frozen=True)
class LatchItem:
    """A LEVEL-SENSITIVE latch (`LATA` / `LATB`), emitted as two rules:

        val(q, V, T)   :- val(en, 1, T), val(d, V, T).      -- transparent, SAME time index
        val(q, V, T+1) :- val(en, 0, T+1), val(q, V, T).    -- opaque, hold across the boundary

    Both guards read `en` at the instant the head is derived (DESTINATION-gating), so they are
    complementary by construction and the schema is single-valued with no clock hypothesis —
    the same argument as the async-reset flop. Proven in `Latch.lean`.

    NOT a flop: a transparent latch has ZERO delay. `Latch.flop_is_latch_delayed` shows the
    old flop modelling was this schema shifted by exactly one cycle on every trace, which is a
    different circuit rather than a conservative approximation."""

    q: str
    d: str
    en: str
    inst: str
    loc: Loc
    #: Emit ONLY the hold rule. An INFERRED latch's transparent half is already emitted by the
    #: ordinary combinational path (`val(y, V, T) :- <guard>, <driver>` -- that IS the driven
    #: case), so all that is missing is the retention. Emitting the transparent rule again would
    #: duplicate it, and emitting `d` as a signal name would be wrong: for an inferred latch
    #: there is no single data net, the value comes from whatever the block computes.
    hold_only: bool = False


@dataclass(frozen=True)
class InferredLatch:
    """An INFERRED latch: an `always_comb` target whose bits are not all driven on every path.

    SystemVerilog says the undriven bits RETAIN their value, which is a latch. Rather than
    refuse the design, it is translated with the latch semantics proven in `Latch.lean` and
    reported LOUDLY -- the same policy as the incomplete selector (D4) and the combinational
    loop (T2): translate faithfully, never invent a value, and make the reader see it.

        % INFERRED LATCH: bits [7:4] of y are not assigned on every path -- they HOLD.
        val(y, 0, 0).                                  -- no reset: default power-on, as registers get
        val(y, Vn, T+1) :- val(y, Vo, T), T < k, <driven at T+1>,
                           Vn = (Vo & KEEP) | <driven regions>.

    The hold crosses a time index (`T` -> `T+1`), so it is NOT a combinational loop and the
    tightness detector correctly leaves it alone."""

    lhs: str
    width: int
    keep: int              # mask of bits that HOLD (not driven on every path)
    bits: str              # human-readable bit list, e.g. "7:4"
    value: Expr            # the RMW value: (prior & keep) | driven regions
    loc: Loc
    #: For a GUARDED slice, one (guard-literals, value) pair per combination of the guarded
    #: slices firing — emitted as one rule each, the guards read at `T+1`. Splitting the rule is
    #: what removes the `guard ? val : lhs[region]` conditional, whose hoisted temp read `lhs`
    #: at the head's own instant and formed a combinational loop (Fix 83). Empty ⇒ the single
    #: unguarded rule built from `value`.
    variants: tuple = ()


@dataclass(frozen=True)
class Design:
    """The whole translation unit (one flat module for M1)."""

    name: str
    params: tuple[Param, ...]
    signals: tuple[Signal, ...]
    mems: tuple[Mem, ...]
    clocks: tuple[Clock, ...]
    resets: tuple[Reset, ...]
    comb: tuple[CombItem, ...]
    seq: tuple[SeqItem, ...]
    mem_writes: tuple[MemWrite, ...]
    mem_reads: tuple[MemRead, ...]
    muxes: tuple[MuxItem, ...] = ()
    latches: tuple[LatchItem, ...] = ()
    inferred_latches: tuple[InferredLatch, ...] = ()
    vffs: tuple[VffItem, ...] = ()
    lane_signals: tuple[str, ...] = ()  # genvar-indexed signals (INDEXED shape seed, §4.6)
    lane_dims: dict[str, int] = field(default_factory=dict)  # lane signal -> # of lane indices (1, 2, ...)
    lane_elem_w: dict[str, int] = field(default_factory=dict)  # lane signal -> per-lane element bit width
    lane_domains: dict[str, tuple] = field(default_factory=dict)  # array-inst lane owner -> per-dim counts (ni[,nj])
    enums: tuple[Enum, ...] = ()        # enum types (drive the tag-shape schema, §3.6)
    cells: tuple[CellInfo, ...] = ()    # structural instance manifest (cell/3 + cell_out/2, §4.1)
    packed_dims: dict[str, tuple[int, ...]] = field(default_factory=dict)  # packed multi-D signal ->
    #   declared per-dimension widths, outer-to-inner (logic[3:0][7:0] -> (4, 8)); the type/3 width is
    #   the flattened product. Only signals with >=2 packed dims (a true matrix), for packed_dims schema.
    flagged: tuple[tuple[Loc, str], ...] = field(default_factory=tuple)
    #: LOUD ADVISORIES that are NOT coverage problems. The construct is fully and faithfully
    #: translated -- nothing dropped, nothing mistranslated -- but the RESULT has a property
    #: the reader must know about. Today: a selector whose arms do not cover it, leaving the
    #: output unbound on the uncovered values (so a property over it can pass vacuously).
    #: Separate from `flagged` because rule 2 is about constructs being silently missed, and
    #: nothing is missed here; `--strict-warnings` promotes these to a non-zero exit for shops
    #: whose RTL rules require a `default` on every case.
    warned: tuple[tuple[Loc, str], ...] = field(default_factory=tuple)
    derived_clocks: tuple[DerivedClock, ...] = ()   # gated clocks from ICG primitives (§6.7)
    edges: tuple[EdgeItem, ...] = ()   # $rose/$fell sampled-value edge functions
    stub_rules: tuple[str, ...] = ()   # verbatim ASP lines from project-local functional stubs (sources.json `stubs`)
