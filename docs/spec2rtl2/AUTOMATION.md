# What is automated, and what is still to be done

This document answers two questions a newcomer to the route asks on day one: *which parts
of the journey from English to proven RTL does a machine do for me?* and *what remains
open?* It is written for a person, not a changelog: each entry says what the thing does
and why it exists, and the open items say where their full record lives. Status is as of
2026-09-01; the worklist (`notes/WORKLIST_SPEC2RTL.md`) is the living tracker this
document summarizes.

The principle behind the whole list: **every mechanical arrow of the route has a command
that performs it and a gate that fails loudly when it goes wrong.** The arrows that are
*not* mechanical — deciding what the block should do, approving each artifact, writing
the design — belong to a person or a model-in-the-loop on purpose, and no item below
proposes to automate them away.

---

## 1. The front end: from controlled English to the contract

**One command:**

    python -m sv2asp.aspfirst2 compile <block>.cnl <block>.yaml -o spec.lp

What it does, in order — each step once a manual act, now mechanical:

| step | what the machine does |
|---|---|
| the sigil check | every structural keyword must carry its `@`; a bare `when` is refused with the exact spelling to use, an unknown `@wehn` is refused by name |
| desugaring | the controlled English becomes the symbolic core, written beside the source as `<block>.cnl.core` — generated, committed, diffable, never hand-edited |
| the cross-file checks | names resolve against the signature, verbs match protocols, drives respect direction, fields are real ports — plus the semantic checks (scope, lifetime, correspondence, a variable bound twice) |
| the lowering | claims become `failType` monitors stamped at their determination instants; behaviours become event monitors plus synthesized hold-otherwise frames; scenarios become constrained starts; nothing lowers silently — every refusal is printed by name |
| the frame rule | every window a behaviour WRITES gets a hold-otherwise monitor keyed by its own shape — no key for a scalar, the position for an indexed window, the object plus its lifetime for an object — with the licence specific to the position written; a window only READ is a derived view of the design and is not framed |
| the reset exemption | a clause NAMING the reset is judged at every instant rather than silenced by the file's `disable iff`, in a behaviour as well as a property — the rule of Chapter 33 rather than one spelling of it |
| single-valuedness | every value-carrying window gets a `<window>NotSingleValued` monitor: a linkage mounting one window from two rules is named, rather than silently satisfying claims it violates (a claim asks whether SOME value matches). A monitor and not a constraint, because a constraint would make a multi-valued linkage UNSAT, which reads as "no counterexample" |
| the signature's enumerations | every enumerated field is refused by name against its domain -- `role`, `active`, `direction`, and the reset's `polarity`/`edge`/`synchronous`/`discipline` -- including the three the compiler does not read yet; and `compile` echoes the resolved reset sense, so a polarity spelled correctly and simply wrong is visible to the reader |
| the domain rules | a subscript AND a quantifier must name a declared `@index` (or, for a quantifier, a kind objects are created of); an unknown kind would otherwise read as an object kind and quantify over a population nothing mounts, making every claim under it vacuous rather than refused |
| the shape rules | a port declares whether it is a vector or an ARRAY (`elements` beside `width`), and the declaration — never inference — decides whether `data[J]` is bit J (a boundary) or element J (an addressed read); an undeclared subscript domain, and one whose extent disagrees with the port, are both refused |
| the mount manifest | the windows the design must give glass to are printed, because quantifying over entries silently demands them and nothing in the source text says so |
| the grounding check | `compile` GROUNDS the contract it just wrote and fails if clingo reports an error -- because an unsafe rule does not merely fail, it stops grounding and takes the whole program down, so a clean compile could hand back an artifact nothing downstream can run |
| the wellformedness guard | the emitter refuses its own output if a helper negates its own head or one name is defined by two lowerings — the collision class caught once by reading, now caught every time by machine |

The generated names are for people (`allocateDemandCreated`, `RAddress`), the sentence
patterns live in the single grammar source (`lib/dsl/grammar.ebnf`) that the compiler
derives its matchers from, and Chapter 35 of the methodology renders that source
verbatim, drift-gated.

## 2. The verification: the certificate and its report

**One command** — the entry's `verify.json` carries the whole certificate as data, with
per-step `log` keys writing each report into the entry folder:

    python -m sv2asp.aspfirst2 certificate <entry>     # everything that proves
    python -m sv2asp.aspfirst2 verify      <entry>     # ... plus the round trip

(the underlying pieces remain available individually: `lint <design>.lp` and
`refine <spec>.lp <design>.lp --induct K [--free-reset]`)

The certificate is FOUR runs, in the order the skill teaches (each a paid-for lesson):

1. **The standard run** — base from reset plus the normal-form induction step at K.
2. **The strong half** (`--free-reset`) — the step with reset free at every instant, where
   the reset-exempt monitors genuinely bind. The runner itself now refuses the vacuous
   claim: with the reset pinned, those monitors are reported `NOT EXERCISED in this step`
   and excluded from the inductive list, never shown as proven while unfireable.
3. **The second configuration** — the design regenerated at an off-default point and the
   contract's `#const` lines rewritten to match. A design parameterized in name only —
   a baked threshold, a shearable width — dies here and nowhere else, so the gate also
   requires the off-default contract to *reject* the default design (the point must
   discriminate, or it proves nothing).
4. **Reading the exclusions** — the report's boundary lines ("reset held released",
   "NOT EXERCISED", "bounded-only") are part of the verdict. This run is a person's, on
   purpose: it is where the claim's edges are understood.

## 3. The RTL: print and round trip

**The commands:**

    python -m sv2asp.aspfirst2 print     <design>.lp -o <block>.sv
    python -m sv2asp.aspfirst2 roundtrip <design>.lp <scenario>.lp --sim auto     # Verilator first, else Icarus; --verilator / --icarus name one

The print carries the conventions of methodology §27.1 mechanically — parametric honestly
(every size comparison a parameter expression, derived widths as `localparam` no override
can shear), grouped `generate for` blocks, the `xxM1` hold/set staging with flops as
`xx[i] <= xxM1[i]`, human names with zero hoisted wires, no sigil in any identifier. The
round trip is what holds the printer to all of it while keeping it honest: the printed
file is translated back by the independent translator and compared against the authored
model value for value, with the simulator arbitrating every definite sample (Verilator
under the two-fill rule, methodology 27.5, or Icarus under 4-state x).

## 4. The ladder: automated gating, human approval

    python -m sv2asp.aspfirst2 ladder {status|init|built|explained} <entry>

The machine enforces the process: no rung begins until the one before is approved, every
approval pins the artifact's digest, and an edit after approval reverts the rung to
stale. What the machine deliberately cannot do is approve — there is no command for it;
a person edits `ladder.yaml`. That asymmetry *is* the ladder.

## 5. The standing gates: verified again on every suite run

These are not one-time checks; `pytest tests/test_aspfirst2.py` re-proves all of them on
every pass, and `tests/test_translate.py` guards the translator underneath:

- **the corpus gate** — the user's structured-English miss queue compiles end to end and
  certifies the real design, with both sabotage families red;
- **the two-producer parity** — the compiled contract and the hand-written FV contract
  certify the same design and both reject the sabotaged ones (a per-entry fixture, not a
  route requirement);
- **the Stage-5 differential** — an independent reference interpreter agrees with the
  generated contract under clingo on every (monitor, instant) verdict over random traces,
  with a dropped monitor and a mistranslated bound both caught;
- **the grammar's single source** — the core slice builds the lark parser, the surface
  slice builds the desugarer's matchers, the methodology renders both, drift is a build
  error, and every surface pattern carries an executable example the gate runs;
- **the contract wellformedness, sigil, and traceability gates**; the **two-point** and
  **strong-half** certificate assertions; the **Lean build** with its axiom audit
  (`RouteLean/Claims.lean`: each monitor schema proven faithful to its trace denotation;
  `RouteLean/Rotation.lean`: the rotation bound at every depth);
- **the documentation gates** — every markdown link resolves, every document is in the
  doc map.

### Print parity, with the second configuration

The four-run certificate's second configuration certifies the ASP at an off-default point.
Since 2026-09-02 it also PRINTS both configurations and requires them to differ only in the
parameter defaults — because a parameterisation can be lost between the ASP and the print, and
"this module honours its parameter" is a property of the printed RTL. It is automatic (opt out
with `"print_parity": false`) and it found a real fake-parameterised module on its first run.

### The schema, printed by the tool that enforces it

`sv2asp2 schema` prints what a design may contain, what a contract contains, and what a
linkage looks like — the generation target for whoever writes the design, model or person.
It is derived from `load.FACT_PREDS`, `model.CELLS` and `emit._ROLES`, so it cannot describe
a language the tool does not accept, and two gates keep the prose honest: every fact and
cell must carry a gloss, and every predicate and verdict name the corpus contract emits must
fall into a documented part of it.

## 6. What a person (or the model in the loop) still does — on purpose

Resolving the English and approving each rung; writing the design against the contract
and reading the counterexamples the certificate hands back; deciding architecture
(an offer that may be re-prioritised, a count that gates on validity); and reading
reports' exclusion lines as the boundary of every claim. None of these are automation
gaps. They are the route.

---

## 7. The tracker: what is to be done

**Since 2026-09-02 the ledger of record is `CHANGES.yaml`**, beside this file: one entry per
tool change with its reason, gated so a "fixed" entry must name a real test. The table below
is kept as the narrative; the ledger is what a build checks.

In priority order. Each item's full record lives where the last column says.

| # | item | why it matters | status | record |
|---|---|---|---|---|
| 1 | ~~the `certificate` command + the `verify` manifest~~ | **DONE (2026-09-01)**: `verify.json` carries the whole flow as data — the standard run, the strong half (`induction_only`), parity producers, the discriminating `second_points` block, the round trip — with per-step `log` keys writing reports into the entry; `sv2asp2 certificate <entry>` runs everything that proves, `sv2asp2 verify <entry>` adds the round trip; the suite gate runs the manifest on a copy | done | `flow.py`'s schema docstring; the entry's `verify.json` |
| 1b | **the user distribution** — `scripts/build_dist.py` assembles the workspace layer (bootstrap, skill, route docs, worked examples, config template) and gates it: nothing withheld, no clone instructions, no dangling pointers | a withhold list that is only a convention gets violated by a locally-reasonable edit — the book's setup chapter told readers to clone the private repo | **DONE (2026-09-01)** for the workspace layer, gated by `test_v2_user_distribution_is_safe_to_ship`; the ENGINE's wheel is open, blocked on resource resolution (repo-relative `parents[4]` paths must become `importlib.resources`) | `scripts/build_dist.py`; `notes/MAINTAINER.md` |
| 1c | **`--report FILE`** — every verb writes an issue report: tool version, the resolved toolchain, the command, the exit status, the output — and nothing from the user's design | a gap must travel back to the maintainer without the block travelling with it; "which clingo, from where" is the question users answer least reliably | **DONE (2026-09-01)**, gated by `test_v2_issue_report_captures_environment_not_the_design` | `__main__.py`'s `_run_reported`; SUITE.md §C.4 |
| 1d | **the self-contained distribution** — `build_dist.py --runnable` produces the working folder (tool, libraries, `setup.sh`, docs, skill, one worked entry per route), maintained as the orphan `distribution` branch | a recipient needs a folder they can work in, with an environment step that assumes nothing about their machine | **DONE (2026-09-01)**: verified in a clean environment (conda unset, system Python 3.14, fresh `.venv`) — setup completes, `doctor` READY, the miss queue's whole certificate green from inside the folder; gated by the shipping test | `scripts/build_dist.py`; `notes/MAINTAINER.md` |
| 2 | ~~**the second block through the language**~~ | only a real block forces the design correctly, and this one did: a framing receiver (an FSM phase, a bit counter, an indexed array) went through the language IN THE FIELD and cost **eleven** language and compiler changes — enum members as values, a scalar state assignable from an expression, `@index` and `@every <kind> <VAR>:`, `@during reset` reading the file's own reset, `next(P)`, port `elements`, and the target/source instant rule that makes a counter satisfiable | **DONE (2026-09-02)** for the language; the two committed corpus blocks still share objects and opaque comparisons, so item 2b holds the residue | LEARNINGS.md; `dsl/cnl.py`, `dsl/emit.py` |
| 2d | **the effect surface derived, not described** — the controlled English's effect shapes generated from `lib/dsl/grammar.ebnf` the way its condition patterns already are | the conditions are single-source in both directions (a production with no handler, or a handler with no production, is refused at import) while the effect shapes are prose beside code that can drift from them, with no gate; a reader who assumes the whole surface is gated trusts the wrong half | open | `lib/dsl/grammar.ebnf` (the surface section says so); SUITE A.7 |
| 2c | **the never-fired report over the compiled contract** — name every monitor that no execution can satisfy the body of | the reset-exemption defect produced monitors that were structurally dead, and the count of monitors looked right; Chapter 33 says the report is what makes an implicit exemption safe, and it runs today over the hand-written contract | open — raised in priority by the second block's G12 | Chapter 33; `LEARNINGS.md` |
| 2b | **a third corpus entry with NO objects** — the framing receiver, or an equivalent | every defect in the three-day sequence survived because both committed blocks are object-shaped and compare opaque tokens; a gate only discriminates against a shape it contains, and the language's newest half is exercised today only by unit tests | open — the frontier, and the direct successor of item 2 | LEARNINGS.md ("generalising from one example's incidental shape"); worklist |
| 3 | **fairness checking (Phase 3)** — a bounded-service property for the fetch side, tied to `Rotation.reaches` | `choose fairly` is stated on two behaviours; the forward side has its bounded property (`demandForwardedAfterFill`), the fetch side now rotates but nothing certifies it | open | worklist; CERTIFICATE.md |
| 4 | **the hoisted-ternary-in-generate translator defect (F30)** — a ternary ARM hoisted inside a for-generate loses its genvar: `_hoist_bit_arms` lifts any non-trivial arm without the lane-index guard the register path has | **NO LONGER LOUD since F29** (2026-09-02): the refusal that surfaced it as a dark read was the one F29 removed, so the head translates the shape at exit 0 with wrong rules — hard rule 2 violated until fixed. Found by bisecting a round trip that timed out (the wrong rules make a 2^64 join) | **DONE (2026-09-02, F30)**: a temp hoisted inside a generate that reads a lane is a lane by construction, on every path -- the reporter's round trip went from a 300 s timeout to `ROUNDTRIP: OK` with Icarus agreeing on all 1300 definite samples | `notes/WORKLIST.md` F30 |
| 5 | **behaviours, frames and scenarios in the Stage-5 differential** | the reference interpreter covers the property layer; the behaviour monitors are compared only through designs today | open | `dsl/interp.py`'s docstring; worklist |
| 6 | **the per-construct denotational semantics in Lean** — quantifiers and behaviours, beyond the claim schemas | `Claims.lean` proves the three monitor schemas faithful; the larger half of Stage 6 is the construct-by-construct meaning | open | TRANSLATION.md §6; LEAN.md |
| 7 | **`choose fairly` beyond recording** in the compiler — the obligation lowered to a checkable form | today the compiler records the annotation; item 3 is the design-side half of the same debt | open | TRANSLATION.md; `dsl/cnl.py` |

Recently closed, for orientation: the reset-vacuity class (the runner's `NOT EXERCISED`
bucket plus the strong half), the parameter class (the two-point certificate; derived
`COUNTWIDTH`), the sigil rule and the single grammar source, the human-RTL print
conventions, F28 and the lane-conjunct generalization, and the miss queue itself —
rebuilt through all seven rungs, every rung user-approved.
