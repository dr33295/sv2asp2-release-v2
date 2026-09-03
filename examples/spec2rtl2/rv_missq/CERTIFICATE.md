# The miss queue's certificate — the regeneration run

What the proof establishes, on the artifacts in this folder, on 2026-08-31. The raw runner
reports sit beside this file: `certificate.log` (the contract of record) and
`certificateFv.log` (the second producer). Reproduce either with

    PYTHONPATH=src python -m sv2asp.aspfirst2 refine spec.lp l1.lp --induct 1

run from this directory (the linkage `l1.inv.lp` is found beside the design).

## What was proven

**Base.** From reset, no monitor can fire on ANY input sequence within the window. The
machine comes up empty (`emptyUnderReset`, `quietUnderReset` are judged where reset is
asserted, the file-level exemption in force).

**Induction, normal form, K=1.** Every slot register freed at T=0 — the four `valid`,
`dem`, `want`, `infl`, `fill` bits per slot and the one-hot pointer as free booleans, the
three payloads (`addr`, `entryTag`, `line`) as free tokens — inputs free at every instant,
reset held released, the whole monitor set assumed over the window and a violation demanded
at the next instant: **UNSAT**. With the base, all forty-four monitors hold for ALL time:

- the seventeen property claims (allocation, lift, merge, stall, the ready biconditionals,
  the answered-within-depth window, phase exclusion, one-entry-per-line, the bounds, the
  reset pair);
- the behaviour event monitors (askMemory, enquiryTaken, receiveFill, forwardDemand,
  finishPrefetch, redirect);
- the synthesized frame family (`*Disturbed`: no window changes without its writer) and the
  entry lifecycle pair (`entryAppeared`, `entryVanished`);
- the five single-valuedness monitors (`*NotSingleValued`), added 2026-09-02. Each says a
  window holds ONE value at an instant. That was true here all along — every window is
  mounted from exactly one `val/3` atom, which the translator's schema makes single-valued —
  but it was true by accident rather than by statement, and a linkage mounting one window
  from two rules would have broken it silently in the MASKING direction: a claim asks
  whether SOME value matches, so a spurious second value satisfies a claim the design
  violates. All five proved inductive at K=1 with no invariant and no increase in K, which
  is what "true by construction here" looks like when it is finally checked.

**No ghost state, no invariants.** The induction closed with nothing asked for: the linkage
is pure derived views of the design's flops, and no confining claim had to be added. (The
first run's `entryInOnePhase` cargo has no descendant here.)

**Scenarios.** All six — lift, merge, demand-beats-prefetch, reserve refusal, repeat-demand
stall, and the input-free start — are POSSIBLE on this design and their expectations cannot
be violated: the anti-vacuity half of the certificate.

**Both producers agree.** The same design is certified by the contract of record
(`spec.lp`, compiled from `rvMissq.cnl` + `rvMissq.yaml`) and independently by the FV
stand-in's hand-written contract (`specFv.lp`) — and the sabotaged designs fail BOTH: the
wrong-tag defect (a claims-level lie) and the ungated-fillhit defect (a behaviour-level
one, caught by each contract's frames). That is the two-producer differential the route's
verdict-parity gates run on every suite pass (`test_v2_cnl_corpus_gate`,
`test_v2_dsl_verdict_differential_on_the_missq`, `test_v2_rv_missq_fetch_queue_certificate`).
The linkage mounts both vocabularies on the same flops — `entryExists`/`entryValid`,
`forwarded`/`forwardOf` — so the two contracts read one state and cannot be told different
stories.

## What is different from the first run's certificate

The design under proof changed shape twice, at the user's direction, and the certificate
re-closed at K=1 with no help:

1. **Lanes under the `depth` parameter** with every scan a chain — including the rotating
   arbiter, reformulated from the binary-pointer square to the textbook chain form
   (one-hot pointer, thermometer, wrap half, ring closed through a boundary member;
   all-zeros power-on read as pointer-at-0), written ONCE and instantiated for BOTH
   ports: the forward side and — after the user's review caught the asymmetry — the
   memory-request side too, whose `choose fairly among eligible entries` obligation the
   first design met with fixed lowest-index priority that could starve a high slot. The
   bounded-rotation fact is proven at every depth in Lean (`RouteLean.Rotation.reaches`);
   CHECKING the fairness obligation in the certificate remains the recorded Phase-3 item.
2. **The `xxM1` staging convention**: the 1-bit slot state in sum-of-products hold/set
   form (`set | (hold & ~clear)`), the payloads as single-level muxes, and only `valid`
   and the two pointers carry reset. The frames and the lifecycle monitors are unchanged
   in meaning — they read windows, not flop idioms. The popcount chains add the valid
   bit directly (`liveCnt[i-1] + valid[i]`), the idiomatic zero-extend.

## The reset story, told honestly (the user's review, 2026-08-31)

The first certificates ran the induction step with **reset held released** — the runner's
default, and its report says so in one line ("reset held released: resetN"). That line
carries a consequence easy to miss: the two reset-exempt monitors (`emptyUnderReset`,
`quietUnderReset`) are judged only where reset is ASSERTED, so a step that never asserts
reset can never fire them — they were **vacuous in the step**, green for the wrong
reason, and the only reset instant ever exercised was the base's power-on. The user's
review found the state that vacuity was hiding: `infl` is not a reset register, so a
mid-operation reset left a stale in-flight bit in an invalid slot and the raw count read
it — `inFlightCount != 0` under reset.

Two things fixed it, and the strong run proves the fix rather than asserting it:

1. **The counts are valid-gated** (`inflCnt` sums `valid[i] & infl[i]`): the window means
   "existing entries whose enquiry is in flight", and an invalid slot's stale bit is not
   an entry — the same gating the per-entry `inFlight` window always had. The window and
   its counter now agree about what exists.
2. **The certificate gained a strong half** (`certificateFreeReset.log`, and the suite
   gate asserts it): the induction re-run with `--free-reset`, so reset can assert at any
   step instant and the reset monitors genuinely bind — and the whole set is INDUCTIVE at
   K=1. Scenarios are deliberately excluded from the strong half: a reset asserted in the
   middle of a directed story cancels the story by definition, which the freed solver
   demonstrates and which is not a design defect.

On the stalled-enquiry question the review also raised: `memoryRequestAddress` may change
while `memoryRequestReady` is low, and that is the ARCHITECTURE, not an oversight — the
signature declares `payload: reprioritisable` on `memoryRequest` (marked as a departure
from the usual readyValid rule, with the integrator's obligation to sample on the
handshake), and P14c states it in English: an enquiry is an OFFER, re-prioritisable until
taken. The `demandFirst` promise *requires* exactly this preemption — a demand arriving
while a prefetch's enquiry stalls must take the port, which a held-payload interface
would forbid.

## What the certificate does not claim

The `memoryEventuallyAnswers` assumption is an `s_eventually` obligation on the
environment, not a rule — the compiler refuses to lower it, by design, and the bounded
answered-within-depth property is what stands in the proof. The certificate is at the
built configuration (depth 4, reserve 1, two outstanding fetches); size-independence
arguments live where they are named, in Lean. The printed RTL's agreement with this design
is the round-trip's claim, at the rtl rung, not this one.
