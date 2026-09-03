"""The flat → per-instance rule seam (the "RuleSink").

Modular emission reuses the SAME flat emitters (`_emit_comb`/`_emit_seq`/`_emit_bitvec`/
`_emit_lane_word_bridge`) that produce the flat `.lp`; every behavioural rule is written exactly
once. A single documented transform then *lifts* each flat rule line into instance-parameterised
form — this module is that transform, extracted and named.

Design note (why this shape, not a per-emitter sink): the modular set does not re-derive any rule.
The flat emitters emit local-named rules into an `_Out`; :func:`instance_index` rewrites each rule
line so every per-instance predicate gains the leading ``Inst`` term and the rule is guarded by
``isa(Inst, spec)``. Making the lift a line transform (rather than threading an ``Inst`` parameter
through ~15 emit functions) is what keeps flat and modular byte-identical by construction: they run
the identical emit code and differ only by this one, legible post-pass. Provenance comments and
blank lines pass through untouched (hard rule 7).
"""

from __future__ import annotations

import re

# per-instance predicates: the value atom, the memory address DOMAIN, the per-cell HOLD, and the
# array-instance LANE domain all carry the leading instance term Inst (per-instance state).
_VAL_RE = re.compile(r"\bval\(")
_TIME_RE = re.compile(r"\btime\(([a-z]\w*), T\)")   # a real clock (lowercase), not the `_` wildcard
_ADDR_RE = re.compile(r"\baddr\(")
_MEMHOLD_RE = re.compile(r"\bmem_hold\(")
# the multi-port joint hold's per-port condition -- per-instance for the same reason mem_hold is:
# two instances of one module must not share it, or one instance's idle port would hold the other's cells
_MEMNOWRITE_RE = re.compile(r"\bmem_nowrite\(")
_LANE_RE = re.compile(r"\blane\(")


def instance_index(line: str, spec: str, derived: frozenset[str] = frozenset()) -> str:
    """Rewrite a flat (local-named) rule into the instance-parameterised form: every `val(s,…)`
    becomes `val(Inst, s,…)`, the rule is guarded by `isa(Inst, spec)`, and a real clock `time(clk,T)`
    becomes `clkof(Inst, CK), time(CK, T)` so the instance's clock domain is resolved by the manifest.
    A DERIVED (gated) clock `time(gclk,T)` is per-instance, so it becomes the functor clock
    `time(gclk(Inst), T)` instead (defined by its own rule -- see _spec_rules).

    The instance variable is `Inst`, NOT `I`: `I`/`J`/`K`… are the flat emitter's lane/ADDRESS index
    variables (lane-rolled and multi-dim memory: `val(q(I,J),…) :- addr(q, I, J)`). A single-letter `I`
    instance term would UNIFY with the lane `I` (`val(I, q(I,J),…) :- isa(I,m), addr(I, q, I, J)`),
    silently breaking every lane-rolled / multi-dim construct. `Inst` can never collide."""
    head, _, body = line[:-1].partition(" :- ")     # drop trailing "."

    def _qual(s: str) -> str:
        # Prepend the instance term Inst to every per-instance PREDICATE -- and only at
        # ATOM position (paren depth 0). The regex form rewrote every occurrence, so a
        # design NET named after a reserved predicate was mangled INSIDE value terms:
        # a lane register named `addr` became the atom-term `addr(Inst, I)`, silently
        # disconnected from its init companion and every projection -- in modular only,
        # a flat/modular divergence of exactly the class hard rule 1 exists to stop
        # (found by the miss-queue regeneration's round trip, 2026-08-31).
        names = ("val", "addr", "mem_hold", "mem_nowrite", "lane")
        out, depth, i = [], 0, 0
        while i < len(s):
            c = s[i]
            if depth == 0 and (i == 0 or not (s[i-1].isalnum() or s[i-1] == "_")):
                for nm in names:
                    if s.startswith(nm + "(", i):
                        out.append(nm + "(Inst, ")
                        i += len(nm) + 1
                        depth += 1
                        break
                else:
                    if c == "(":
                        depth += 1
                    elif c == ")":
                        depth -= 1
                    out.append(c)
                    i += 1
                continue
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
            out.append(c)
            i += 1
        return "".join(out)

    head = _qual(head)
    body = _qual(body)
    for gc in derived:    # gated clock -> per-instance functor clock (BEFORE the generic clkof rewrite)
        body = re.sub(rf"\btime\({re.escape(gc)}, T\)", f"time({gc}(Inst), T)", body)
    # a real clock time(clkN, T) -> clkof(Inst, clkN, CK), time(CK, T): the per-port resolution KEEPS the
    # clock formal name (clkN), so a module with several internal clocks resolves each one independently.
    body = _TIME_RE.sub(r"clkof(Inst, \1, CK), time(CK, T)", body)
    guard = f"isa(Inst, {spec})"
    return f"{head} :- {guard}, {body}." if body else f"{head} :- {guard}."
