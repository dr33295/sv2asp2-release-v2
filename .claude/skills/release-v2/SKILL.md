---
name: release-v2
description: Build a block with the RELEASED spec2rtl v2 tool starting DIRECTLY from a hand-written ASP contract (spec.lp) -- no signature compiler, no controlled English -- then the linkage, the design, the certificate, the print and the round trip, every rung under the human-gated ladder. Use when the block is specified by a person writing spec.lp; /spec2rtl-dsl is the same route with the controlled-English front end.
---

# release v2 — the direct-ASP procedure for the released tool

**You start at `spec.lp`.** The specification in force (`SPECIFICATION.md`) is resolved by a
person; the contract is written by a person or by you, BY HAND, in the tool's own ASP
vocabulary; everything after it is the v2 route unchanged. This skill is the operating
procedure for that path with the released tool (`sv2asp2`). For a block that starts from the
controlled English use `/spec2rtl-dsl`; the two routes meet at `spec.lp` and share every rung
below it.

**The governing document is `docs/spec2rtl2/ROUTE_METHODOLOGY.md`, Chapter 0 first.** This
file is the procedure, not the reasoning. `docs/spec2rtl2/GETTING_STARTED.md` is the guide
for a hardware engineer meeting the route cold; `docs/spec2rtl2/SUITE.md` Part C is the
command reference.

## The tool, and where work happens

Run the tool from the block's WORKING FOLDER beside the tools folder -- the folder the
release was unpacked into (`sv2asp2-release-v2`, say), never inside it:

```
../sv2asp2-release-v2/.venv/bin/python -m sv2asp.aspfirst2 <verb> ...   # or `sv2asp2 <verb>` after activating
sv2asp2 doctor                                                 # the toolchain: python, clingo, a simulator (verilator preferred, or iverilog), lean
sv2asp2 schema                                                 # THE ASP YOU MUST WRITE: facts, primitives, contract vocabulary, linkage
```

Nothing is written into the tools folder. A refusal is information: change the input, never
the installed tool. A gap in the tool goes back to the maintainer with `--report issue.txt`
(every verb takes it) and a minimised probe of your own.

## The ladder governs everything

Every artifact is a rung: `specification, signature, dsl, contract, design, certificate, rtl`.
Build it, explain it in plain language, **STOP and wait for the user to approve** before the
next. Approvals carry the artifact's digest; a later edit reverts the rung.

```
sv2asp2 ladder status <entry>
sv2asp2 ladder built <entry> <step>
sv2asp2 ladder explained <entry> <step> --note '...'
```

**Never set `approved`**: the user edits `ladder.yaml`. On this route the `signature` rung is
still built (the `<block>.yaml` is the symbol table a reader needs, and `role` is the
control/data split even when no compiler reads it), and the `dsl` rung is explained as
"contract written by hand" for the user to approve as such -- the ladder has no skip today.

## The order of work

1. **Resolve the English first.** Adversarial misreading pass; every ambiguity, silence and
   contradiction resolved and recorded; `SPECIFICATION.md` in force with every checkable
   sentence tagged with the rule that will check it (`checked by \`name\``).

2. **The signature, `<block>.yaml`.** Wires, widths, parameters, the reset's polarity; `role:
   opaque` for payloads (a token compared only through the equality theory, never enumerated),
   `numeric` for a value with a domain. Validate: `python -m sv2asp.aspfirst2.dsl.signature
   <block>.yaml`.

3. **The contract, `spec.lp`, by hand -- the route's proof anchor.** Read `sv2asp2 schema`
   before writing a line: it prints the contract's vocabulary as the tool accepts it.
   - **Over external symbols only**: the ports directly, plus DECLARED windows for what the
     ports do not expose. A window is a name, a domain and a prose meaning; the spec never
     defines it -- the design's linkage will. No spec-side ghost state outside `refmodel`
     (the lint refuses it; gating is per rule and literal). A rule gated under `refmodel` is
     live in the bounded legs (base, scenarios, delivery obligation) and absent from the step.
   - **A delivered DATA value is an OBLIGATION, not a property**: `model(Port, Want, T) :- ...`
     with `obligation_span(N)` (the lookback the expected term needs). The runner solves the
     span window once and compares the design's delivered term with `Want`: the same term is
     DISCHARGED BY IDENTITY, a different term is OWED to Lean (recorded, never a failure), two
     different concrete values are a VIOLATION with a table. For a WIDE value (a 64-bit
     product) gate the `model` rule and its `expected` helper under `refmodel`, so the wide
     term grounds in the delivery leg only and never in the step.
   - **One named failure per kind of wrongness**: `failType(Name, T) :- ...` (or `bad`; one
     vocabulary). A run deriving a failure says which way you are wrong. Goals for everything
     that must stay reachable.
   - **`live(T)` guards every monitor.** With a reset, `live(T) :- val(reset, off, T).`;
     with NO reset, `live(T) :- gtime(T).` -- every instant is judged. The runner refuses a
     contract in which no instant can be live, because a monitor that cannot fire certifies
     anything.
   - **Sample a port ONCE per rule.** Each `val(q, Q, T)` literal is a sample the grounder
     joins over the port's whole domain: k samples of a 9-bit port in one rule ground as 512^k.
     Bind the port once and read its bits through `pval(bit(Q, i), B)`.
   - **No derived arithmetic in the step vocabulary**: flags and wrap-bit pointers, not
     counts; one-step relations over linked symbols, not history ghosts. A quantity compared
     only against constants is a predicate. A counter that is not small is datapath.
   - **State what must be single-valued** as a MONITOR (`<window>NotSingleValued`), never as a
     constraint: a constraint excludes the multi-valued runs and UNSAT reads as "no
     counterexample".
   - **Frames are monitors too**: a window some behaviour writes gets a hold-otherwise rule
     (a change with no licensed cause is a named failure); a window only read is a derived
     view and is not framed.
   - **Scenarios**: a constrained abstract start and an expectation, no stimulus; a universal
     scenario is lowered per position. Every scenario must be SAT on the design -- a certificate
     with no scenario output is suspect before it is celebrated.
   - `sv2asp2 compile` is not on this route; `sv2asp2 lint` and the contract's own grounding
     (`clingo --text spec.lp`) are the checks. Keep the contract byte-stable: it is the anchor
     every later rung is proved against.

4. **The design, `l1.lp`, and its linkage, `l1.inv.lp`.** The design language is what
   `sv2asp2 schema` prints; read the refusals as the extension surface.
   - **State comes from cells** (`ff`, `arff`, `farray`, `spram`); combinational logic is
     `def(net, expr)`; FSM tables are guarded rules. Parameters are `param` expressions;
     every threshold a parameter EXPRESSION (`lt(count, k(depth, w), w)`), never a baked
     number -- the second-configuration certificate run catches a module parametric in name
     only.
   - **Write a regular structure with the axes it has.** A grid is `net_lane(g, (side,
     side), 1)` with members `g(r, c)`; `def_lane(y, (R, C), e)` binds one variable per axis
     and each axis wraps on its own (`q(R - 1 \ side, C)`, the offsets and blocks as
     parameters); its state is `inst_lane(uG, ff, (side, side))` with pins on the grid's
     lanes; a flat wide port is read per cell as `bit(data, add(mul(R, side), C))`; `pack(L)`
     is a lane as one word, row-major. Never linearise a grid onto one index: it puts row-major
     order into every neighbour expression and hides the locality the induction needs.
   - **The linkage mounts every declared window** on the design's flops, defined at every
     instant (head at `T`). An unmounted window makes its monitors vacuous; the lint reports
     what is demanded and not mounted. A window mounted from two rules is reported
     `NotSingleValued` -- fix the linkage, not the claim.
   - **Gated datapaths** declare `opaque_datapath.`; **units** are proven standalone first
     (`sv2asp2 contract <m>.lp --induct K`) and assumed in the composed step.
   - Read the design back: `sv2asp2 expand l1.lp` shows it in the translator's emitted schema.

5. **The certificate.** Write `verify.json` -- the manifest is the entry's declaration of what
   its certificate IS -- and run it once when the artifact is believed done:

```
sv2asp2 certificate <entry>            # the standard run, the strong half (--free-reset, induction only),
                                       # any parity producers, the second configuration with its
                                       # discrimination check; logs where the manifest's `log` keys say
```

   The standard run is `refine spec.lp l1.lp --induct K`: LIVE must be possible, the base from
   reset with free inputs, the normal-form step (state free, properties assumed over the
   window), the scenarios, the delivery obligations. Start at K = 1; a failed step is an
   INVARIANT REQUEST -- read the counterexample table, raise K toward the deepest reference,
   only then write the confining claim into `l1.inv.lp`. Iterate with the one solve the change
   needs, never with the whole certificate (the budget rule: a step that takes more than low
   minutes is enumerating something; `Solving: 0.00s` at a timeout means grounding -- profile
   before waiting).

6. **The print and the round trip.**

```
sv2asp2 print l1.lp -o <block>.sv
sv2asp2 roundtrip l1.lp roundtrip_scenario.lp --sim auto     # Verilator first, else Icarus (--verilator/--icarus name one); --both-modes adds flat; --incremental when the translated side cross-products
```

   The printed RTL is the deliverable: parametric where the design is, grouped generate
   blocks, `xx[i] <= xxM1[i]` flops, no hoisted wires. The round trip translates the print back
   and compares every net at every instant against the authored program, with the simulator arbitrating
   (Verilator: compiled once, run under the all-zeros and all-ones power-on fills, a sample definite only
   where both agree -- the 2-state stand-in for x; Icarus: x is not definite);
   a comparison over zero samples is a failure by name. Then `sv2asp2 verify <entry>` runs the
   whole flow from the manifest, and the `rtl` rung is explained.

## Explain reasoning to humans

Every read-back explains WHY: the alternatives rejected and what rejecting them bought, jargon
expanded at first use. A design ships with a `DESIGN.md` in this form and the entry with a
`CERTIFICATE.md` saying what is proved, what is bounded-only, and what it cost.

## Run only what the change needs

An edit to the contract runs that contract's lint and one solve; a design edit runs the step
the edit could affect; the certificate runs once when the artifact is believed done. Read gate
exit codes directly, never through a pipe; verify a claim before a message claims it.

## Traps this route has paid for

- **A guard nothing derives certifies anything.** If every scenario reports "no compliant
  state", stop: nothing above that line means anything. The runner's first line, `live: OK`,
  is the check.
- **Transitions are behaviours; invariants are properties.** "At the next edge X is Y" reads
  its sources NOW and writes next; a rule with both sides at `T+1` says something else.
- **A port sampled twice in one rule is a product join** (see step 3); a 36-bit word assembled
  from its bits is a 2^36 join if the bits are free at grounding -- the translator now leaves
  an unread word unassembled and names the cost of a read one, but a hand contract can still
  read a whole wide word: read bits, or a window.
- **Opaque compares are equality-theory, never token identity**; `$stable` on a payload means
  every payload wire through the theory.
- **A helper is a definition** written once at plain `T`, called at whatever instant the use
  needs; body-at-`t`/head-at-`T` double-shifts, both-at-`t` reads as ghost state.
- **A safety binder is the identity domain, never the existence window**: demanding that an
  entry exists inside a helper whose content is "the entry is gone" makes the escape
  underivable.
- **Fairness is architecture**: a per-entry bound rests on the arbitration rotating; the
  parametric fact lives in Lean, because clingo grounds and cannot be given "for every depth".
- **N copies of one unit over a regular relation** (a grid, a lane of stages, a ring): certify
  the UNIT in clingo with its neighbours as free inputs, state the lift in Lean for every N, tie
  the generated design to the unit mechanically. Do not hand the grounder a contract over N
  cells; the time it spends looks like a scaling problem when it is a wrong-engine problem.
- **The reset exemption**: a property that names the reset is judged at every instant
  (`gtime`), and the standard step pins the reset -- `NOT EXERCISED` there is expected; the
  strong half (`--free-reset`) is where it binds.
- **A refusal whose advice is refused is a gap wearing a message**: report it.

## If you see X, do Y

| you see | it means | do |
|---|---|---|
| `live: OK` | some instant can be judged; the monitors can fire | read on |
| `FAIL live: NO instant can be live` | nothing derives `live(T)`: a reset the design never releases, or a reset-less contract without `live(T) :- gtime(T).` | fix the contract or the design; nothing below this line means anything until it passes |
| `base: a property fires from reset -- bad(X, t)` | a real counterexample within K live steps | read the table like a waveform; the design is wrong, or the claim is stronger than the English |
| `NOT inductive` + an invariant request | the property set cannot close by itself | raise K toward the deepest reference; only then the confining claim |
| `scenario S: no compliant state satisfies ...` (one scenario) | the situation is impossible under the properties | the scenario, or a property over-constrains |
| every scenario "no compliant state" | `live` is empty, or the linkage mounts nothing | see `live`; check every declared window is mounted |
| `failType(<window>NotSingleValued, ..)` | the linkage mounts the window from more than one rule | fix the linkage, not the claim |
| `WARNING (BUDGET: the word of X ...)` / `NOT assembled` | a wide per-bit word is (or is not) built from its bits; the cost is named | pinned runs are fine; a free power-on will explode -- read bits, or a window |
| `TIMEOUT` with `Solving: 0.00s` | grounding, not search: something is enumerated | profile (`gringo --text \| sed -E 's/[(:].*//' \| sort \| uniq -c \| sort -rn`), then digits, tokens, or `opaque_datapath.` |
| `DARK READ: X is READ but never DERIVED` (round trip) | the print does not translate back completely | a translator gap: `--report`, and a minimised probe |
| `FAIL obligations: no model instance is derivable at the window's end -- UNREACHABLE` | no `model(...)` atom exists at the span's last instant: the `delivered` condition never holds within `obligation_span`, or the span is shorter than the lookback | check the span against the deepest `T-k` in the rule; check the enabling condition can hold from a free start |
| `VERILATOR COMPARED NO DEFINITE SAMPLE` / `ICARUS COMPARED ...` | the bench matched nothing (a naming mismatch, or every sample power-on dependent) | not a round trip; report it |
| `verilator: N sample(s) not definite -- skipped` | those values depend on unreset state (the two power-on fills disagree); Icarus would print x there | expected for unreset memory cells; if a RESET register appears here, its reset is not reaching the print |
| `the printed RTL is NOT parametric` | the two configurations differ beyond the parameter defaults | author every threshold as a parameter expression; sweep the print for numbers |
| `inferred latch` on the round trip | the print's guards are not visibly total | guard on the enum tag, one `case` over every member |

## Where things are

| what | where |
|---|---|
| **the ASP you must write** | `sv2asp2 schema` |
| the methodology (Chapter 0 first) | `docs/spec2rtl2/ROUTE_METHODOLOGY.md` (+ PDF) |
| the guide from zero, the command reference | `docs/spec2rtl2/GETTING_STARTED.md`, `docs/spec2rtl2/SUITE.md` Part C |
| a hand-written contract beside its compiled twin, and a complete entry | `examples/spec2rtl2/rv_missq/` (`specFv.lp` is the hand contract; `verify.json`, `ladder.yaml`, `CERTIFICATE.md`) |
| the small hand-written entry | `examples/spec2rtl2/fifo/` (`spec.lp`, `l1.lp`, `l1.inv.lp`, `DESIGN.md`) |
| the controlled-English route this shares its rungs with | `.claude/skills/spec2rtl-dsl/SKILL.md` |
| every tool change, with its reason and its gate | `docs/spec2rtl2/CHANGES.yaml` |
