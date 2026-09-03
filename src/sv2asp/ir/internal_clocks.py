"""F27: INTERNAL-SIGNAL CLOCKS, classified at the one place every Design is built.

A register clocked by a net the design computes (``always_ff @(posedge divided_clock)``
with ``divided_clock`` a flop output) used to lower against a time axis nothing emits: the
register silently held its power-on value forever, at exit 0 under --strict-coverage --
the fail-loud guarantee (hard rule 2) broken. Both emitters consume this IR, so the
classification lives here, in the frontend, exactly like ``x_misused`` -- putting it in one
emitter is the two-emitter split producing the same bug class again.

Classified: the internal net becomes an EDGE-DERIVED clock (``DerivedClock`` with
``kind="rise"``), lowering through the same section-6.7 machinery as ICG gating -- a
conditional time axis (ticks exactly across the net's own 0->1 transitions on the driving
domain's axis) plus the ``no_tick`` off-edge holds. The driving domain is found by chasing
the net's register driver to a primary clock, through chains of divided clocks.

Refused BY NAME (a ``flagged`` entry -> a loud coverage problem, never silence): a clock
with no register driver (a combinationally derived / gated-by-logic clock: its edges are
sub-cycle, which this per-cycle model cannot represent -- use an ICG primitive for gating);
a clock wider than one bit; a driver chain that never reaches a primary clock. One stated
limit: the IR carries no edge polarity, so an internal clock is modeled on its RISING
edges (the corporate posedge convention); an internal negedge-clocked register is not yet
distinguishable here and is recorded as owed in notes/WORKLIST.md under F27.
"""
from __future__ import annotations

import dataclasses

from .nodes import Clock, Design, DerivedClock


def classify_internal_clocks(design: Design) -> Design:
    # "primary" = an INPUT PORT used as a clock. design.clocks cannot be the test: its builder
    # registers every clock NAME a register uses as a free Clock -- including the internal net
    # this pass exists to catch (that assumption is F27's root).
    primary = {s.name for s in design.signals if s.is_port and s.direction == "input"}
    derived_known = {dc.name for dc in design.derived_clocks}
    widths = {s.name: s.irtype.width for s in design.signals}
    drivers = {it.reg: it for it in design.seq if not it.combinational and it.clock}

    used: dict[str, object] = {}
    for it in design.seq:
        if not it.combinational and it.clock:
            used.setdefault(it.clock, it.loc)
    for w in design.mem_writes:
        if w.clock:
            used.setdefault(w.clock, w.loc)
    for it in design.vffs:
        if it.clock:
            used.setdefault(it.clock, it.loc)
    for ed in design.edges:
        ck = getattr(ed, "clock", None)
        if ck:
            used.setdefault(ck, ed.loc)

    new_dcs: list[DerivedClock] = []
    flags: list[tuple] = []
    for c in sorted(used):
        if c in primary or c in derived_known:
            continue
        loc = used[c]
        drv = drivers.get(c)
        if drv is None:
            flags.append((loc, f"clock '{c}' is an internal signal with NO register driver: a "
                               f"combinationally derived clock's edges are sub-cycle, which this "
                               f"per-cycle model cannot represent (F27; gate clocks with an ICG "
                               f"primitive instead)"))
            continue
        if widths.get(c, 1) != 1:
            flags.append((loc, f"clock '{c}' is {widths.get(c)} bits wide: a clock is one bit (F27)"))
            continue
        base, seen = drv.clock, {c}
        ok = True
        while base not in primary:
            if base in seen or not base:
                flags.append((loc, f"clock '{c}': its driver chain never reaches a primary clock "
                                   f"(stuck at '{base}') (F27)"))
                ok = False
                break
            seen.add(base)
            bdrv = drivers.get(base)
            if bdrv is None:
                flags.append((loc, f"clock '{c}': the chain passes through '{base}', which has no "
                                   f"register driver (F27)"))
                ok = False
                break
            base = bdrv.clock
        if ok:
            new_dcs.append(DerivedClock(name=c, base=base, gate="", loc=drv.loc, kind="rise"))

    if not new_dcs and not flags:
        return design
    reclassified = {dc.name for dc in new_dcs}
    clocks = tuple(c for c in design.clocks if c.name not in reclassified) \
        + tuple(Clock(dc.name, derived=True, base=dc.base, gate=dc.gate) for dc in new_dcs)
    return dataclasses.replace(
        design,
        derived_clocks=tuple(design.derived_clocks) + tuple(new_dcs),
        clocks=clocks,
        flagged=tuple(design.flagged) + tuple(flags))
