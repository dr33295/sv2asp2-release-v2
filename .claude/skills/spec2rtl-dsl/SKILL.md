---
name: spec2rtl-dsl
description: Build a spec2rtl entry through the SPECIFICATION LANGUAGE — English resolved, then a signature (.yaml) and the specification in CONTROLLED ENGLISH (.cnl, desugared to a committed symbolic core), checked and compiled to the ASP contract — the route's permanent proof anchor — then the v2 design/induction/print route unchanged, every step under the human-gated ladder. Use for any entry starting from the language; /spec2rtl-v2 remains the direct-ASP procedure it builds on.
---

# spec2rtl through the DSL — operating procedure

**Read first: `docs/spec2rtl2/ROUTE_METHODOLOGY.md`** — Chapter 0 is the route end to end,
Part II is the language, Chapter 33 the four semantic decisions, Chapter 34 the depth
question. **`docs/spec2rtl2/TRANSLATION.md`** is the compiler's contract. This file is the
procedure and the traps, not the reasoning. The worked entry is
`examples/spec2rtl2/rv_missq/` — read it beside this.

## The ladder governs everything

Every artifact is a rung: `specification, signature, dsl, contract, design, certificate,
rtl`. Build it, explain it in plain language, **STOP and wait for the user to approve**
before the next. Approvals carry the artifact's digest, so a later edit reverts the rung —
that is the mechanism working, not an obstacle.

```
python -m sv2asp.aspfirst2 ladder status <entry>
python -m sv2asp.aspfirst2 ladder built <entry> <step>
python -m sv2asp.aspfirst2 ladder explained <entry> <step> --note '...'
```

**Never set `approved`.** The tool has no command for it; the user edits `ladder.yaml`.

## The order of work

1. **Resolve the English first** (unchanged from v2): adversarial misreading pass,
   resolutions recorded, `SPECIFICATION.md` in force with every checkable sentence tagged.

2. **The signature, `<block>.yaml`** — the compiler's SYMBOL TABLE: interfaces with
   `protocol` (readyValid/validOnly) and `side`, ports with `role`, parameters, the reset.
   Validate it: `python -m sv2asp.aspfirst2.dsl.signature <block>.yaml` — refusals are by
   name, unknown keys are hard errors.
   - **Every enumerated value is checked and the spelling is EXACT** — `role`, `active`,
     `direction`, and the reset's `polarity` / `edge` / `synchronous` / `discipline`. The
     polarity is the one to get right: it decides which way `disable iff` runs for every
     monitor, so a near-miss would not be a refusal but a DIFFERENT specification, with
     each claim judged exactly where it should have been silenced. `compile` echoes the
     resolved sense — `reset resetN: active_low -- claims are judged where resetN == 1` —
     so read that line, because a polarity spelled correctly and simply wrong is only
     visible there.
   - **`role` is the control/data split.** `opaque` = a token, compared only through the
     equality theory, never enumerated; `numeric` = a value with a domain. A 26-bit address
     marked numeric is 67 million values in the grounder.
   - **An inverted-sense control wire declares `active: low`** (a FIFO's `full` is push's
     ready read the other way up).
   - **A re-prioritisable payload declares `payload: reprioritisable`**, with the
     integrator's obligation in the description (sample on the handshake, not on valid).
   - **A block with no reset is legitimate** — a pure transition relation, judged at every
     instant. The certificate's first line, `live: OK`, says the monitors can fire at all;
     if instead EVERY scenario reports "no compliant state", stop: nothing above that line
     means anything.
   - **Is the block N copies of one unit over a regular relation** (a grid, a lane of
     identical stages, a ring)? Then specify the UNIT: certify it in clingo with its
     neighbours as free input ports, state the lift in Lean for every N, and tie the
     generated design to the unit mechanically (methodology 34.6). Do not write a contract
     that quantifies over N cells and hand it to the grounder — it will not finish, and the
     time it spends looks like a scaling problem when it is a wrong-engine problem.
   - **And write the WIRING as lanes with the AXES the structure has, never as a
     generator's unrolled cells.** A grid is `net_lane(g, (side, side), 1)`, members
     `g(r, c)`; a torus is eight `def_lane(up, (R, C), q(R - 1 \ side, C))`-style lines,
     one wrap per axis, no row base, with the offsets and blocks as PARAMETERS, so the print
     is parametric where the wiring is (methodology 27.3); the grid's state is
     `inst_lane(uG, ff, (side, side))` with its pins on the grid's lanes. Linearising onto one index hides
     the locality the induction needs and puts row-major order into every neighbour
     expression; a generator that bakes literal indices per cell prints a module that is
     parametric in name only, and print parity will say so in thousands of lines.
   - **Parameter defaults ARE the built entry's configuration**, because the contract is
     compiled at them. Defaults that disagree with the design have the contract judging it
     by another block's arithmetic — a depth-8 contract calls a full depth-4 queue empty,
     then blames the design for the difference.
   - **An ARRAY port declares `elements` beside `width`** — `width` is one element's
     width, `elements` how many — because the shape decides what a subscript MEANS:
     `data[J]` is element J on an array port and bit J on a flat one. Declare it and a
     claim can speak of element J, compared whole as a token; leave it out and every
     subscript is a bit.

3. **The specification, `<block>.cnl`** — CONTROLLED ENGLISH, the surface a person
   actually writes (Chapter 35). Sentences drawn from the frozen patterns, one meaning
   each; a sentence outside them is refused by name, never guessed at. The desugarer
   writes the symbolic core BESIDE it as `<block>.cnl.core` — generated, committed,
   diffable, **never hand-edited** (the archived `rvMissq.spec` is why: two hand copies
   of one meaning drift). The surface rules that recur:
   - **Articles are quantifiers.** `a`/`an` in trigger position means EACH such instance;
     `the` claims uniqueness and needs the license that makes it true.
   - **`already` is refused as noise; `still` means persistence** (`E @still exists` is a
     real conjunct, and the lift scenario needed it).
   - **The eighteen STRUCTURAL keywords carry a required `@` sigil** — `@when`,
     `@then`, `@given`, `@while`, `@once`, `@must`, `@never`, `@may`, `@within`,
     `@next`, `@every`, `@exactly`, `@still`, `@choose`, `@before`, `@during`,
     `@eventually`, `@always` — so the sentence's skeleton is visible and a typo fails AS a
     keyword: a bare `when` is refused with the exact spelling, an unknown `@wehn`
     refused by name. Grammatical words (articles, connectives, verbs) stay plain;
     `sv2asp2 keywords` prints the vocabulary with the structural words marked. The sigils
     strip before desugaring, so the core is untouched by the rule — and the sigil STOPS
     AT THE SURFACE: it must never appear in any generated name (core, contract, design,
     or RTL identifiers). The `@` in printed SystemVerilog's `always_ff @(posedge clk)`
     is SV's own event-control syntax, not a sigil — never "fix" it.
   **When the block's state is not objects** — an FSM phase, a counter, an array of bits
   rather than a population of slots — these are the constructs to reach for:
   - **`@state phase : enum { idle, receiving, … }`, and members are values**:
     `phase == presenting` compares the NAME. Magic numbers are not the alternative to
     this; they are the symptom of it missing.
   - **A scalar state is assignable in an effect**: `@next cycle phase is receiving`, and
     the right-hand side may be an expression — `@next cycle bitIndex = bitIndex + 1`, so
     a counter can advance. **An effect's TARGET is next cycle and its SOURCES are read
     NOW**, including a subscript: which position gets written is decided by the index at
     the event, not by what the index will hold afterwards.
   - **`@index bit : dataBits` declares a domain**, and `@every bit J:` ranges over it —
     in a `@behavior` and a `@scenario` as well as a `@property` — a per-position CLAIM, a
     per-position EFFECT ("for every bit, hold it unless this is its turn") and a
     per-position REACHABILITY QUESTION ("every data bit is one, then a stop bit") are all
     writable. In a scenario the reading is UNIVERSAL: the story is reached only when no
     position violates the expectation, never when one happens to satisfy it. The
     quantifiers are not limited to the built-in `entry`. **A domain must be declared
     whether a subscript or a quantifier names it**, and the quantifier is the half that
     matters: an undeclared kind reads as an OBJECT kind, so the claim asks for a window
     nothing mounts and is then vacuously true rather than refused.
   - **`@during reset` uses YOUR reset**, in your polarity, read from the file's own
     `disable iff` line — and the exemption follows the reset being NAMED, not that
     phrase: `@when reset == 1` is exempt too, in a `@behavior` as well as a `@property`.
   - **`@then @next cycle Q` in a `@property`** — so a requirement that is both
     reset-exempt and about the following cycle ("after a reset cycle the phase is idle")
     has a spelling. Every consequent of one claim carries it or none does.
   - **`@always <condition>`** is a property with no trigger — "the state is always one of
     the three" — instead of a tautological `@when` that tells a reader nothing.
   - **`next(P)`** is the pointer relation, not the `@next` marker.

   The symbolic core notation's grammar single source is `lib/dsl/grammar.ebnf` — the
   notation people READ when reviewing a core. lark builds the parser from a mechanical
   translation (dsl/ebnf.py) at import, and the methodology's grammar block renders the
   EBNF itself, so both consumers are mechanical and the source stays legible. The
   semantic rules that carry Chapter 33:
   - **An object is a SLOT.** Quantifiers range over what exists NOW; `exists(E)` is a
     window the design must mount whether or not you write it. A claim mentioning an object
     at two instants says whether it still exists at the later one, or the entry that
     REPLACED it can discharge its obligation.
   - **A `some` with a scope binds a witness; without one it is a proposition.** The scope
     encloses the WHOLE rule the witness takes part in — trigger and effects. Written
     inside-out, "every demand requires a matching prefetch to exist" reads perfectly and
     is unsatisfiable on an empty queue.
   - **A block scope (`each entry E:`) makes several claims about the SAME object** — the
     shared subject lives in the file, not the reader's head.
   - **`send on IFACE as D answering E`** — one clause, three bindings (valid, corresponds,
     forwarded). The design names which object it answers; the spec never establishes it.
   - **A property naming the reset signal is exempt** from the file's `disable iff`; the
     never-fired report is what makes that safe.
   - **Pointers are vocabulary, not arithmetic**: `pointer(N)` with `next`, `address`,
     `opposite`. A derived count is enumeration in disguise — declare the counter a window
     and let the design carry or derive it.

4. **Check both files**: the cross-file checks (names resolve, verbs match protocols,
   drives respect direction, fields are real ports) and the semantic checks (scope,
   lifetime, correspondence, shadowing — `E` bound twice in one rule means the entry the
   trigger tested is not the entry the rule acts on). Every finding is by name; fix it
   before compiling.

5. **Compile**: `Emitter(spec, signature).contract_file()` → the contract (a `.cnl` is
   taken directly; the core is written beside it). Read it — the comparison against
   anything hand-written is on VERDICTS, never text. Know what it is:
   - **The whole surface lowers**: claims, behaviours (an event monitor plus a
     hold-otherwise frame monitor synthesized from the behaviour's writers), and
     scenarios. The generated contract also carries the equality theory's concrete half,
     guarded so it loads only when the design declares `data()`.
   - **The checks run here too**, so a malformed specification is caught by the command
     you actually type; `compile` exits non-zero when anything is reported.
   - **And `compile` GROUNDS what it emits.** A contract that clingo cannot read is worse
     than one that says the wrong thing, because clingo does not skip an unsafe rule — it
     stops grounding and takes the whole program with it, so nothing downstream runs at
     all. Safety is syntactic, so the check needs no design and costs a fraction of a
     second. `PROBLEM: the emitted contract does not ground` is a tool defect, not yours:
     `--report` it.
   - **The contract it produces is the PROOF ANCHOR** — the layer every certificate and
     every design iteration runs against. Today an entry's contract of record is the FV
     stand-in's; the compiler is a second PRODUCER of the same layer, and the corpus gate
     holds both producers to the same verdicts on the same designs, sabotages included.
   - **The names are for people**: every auxiliary atom is named for its declaration
     and role (`allocateDemandCreated`, `forwardIsCorrectBody`), every value variable
     for what it samples (`RAddress`, `LiveEntries`) — no numbered gensyms. The emitter
     REFUSES its own output if a helper negates its own head or one name is defined by
     two lowerings — the collision guard.
   - `s_eventually` is refused BY DESIGN — reduce it to a bound, a ranking, or
     work-conservation before compiling.
   - The header prints the claim set's **deepest temporal reference** — the K to raise
     toward when a step fails.
   - **Read the two lines it prints before the contract.** `reset <name>: <polarity> --
     claims are judged where <name> == <n>` is the resolved sense of the file's
     `disable iff`, and it is the only place a polarity that is spelled correctly and
     simply wrong becomes visible. `window demanded of the design: X` is the mount
     manifest — every X must appear in the linkage, or the claims reading it derive
     nothing and go quietly vacuous.

6. **Design + linkage** — **run `sv2asp2 schema` FIRST if you are writing either by hand.**
   It prints the generation target: every fact `l1.lp` may contain with its arity (the list
   is exhaustive — anything outside it is refused by name), every primitive with its pins
   and parameters, the contract's own vocabulary, and the linkage shape with the three rules
   that matter (mount every demanded window; gate a field on its object's existence; ONE
   source per window). `--design`, `--contract`, `--linkage` select a section. It is derived
   from the tables the tool enforces, so it cannot describe a language the tool does not
   accept. The design section also lists EVERY expression operator with its argument order
   — the vocabulary `def(x, …)` is written in, `pack(L)` included.
   **Named states: declare the register `arch_reg(st, enum(st))` with `enum_member(st, name,
   value)` facts, and any intermediate that carries a state `net(x, enum(st))`** — a
   plain-width net is refused
   (`width_mismatch(x, W, enum(st))`), which is correct and easy to misread as "enums are
   unsupported". The register's reset is a bare member LABEL, `iparam(u, reset_value, none)`
   (`enum_reg_reset_not_tag` refuses a number or `tag(...)`). Declared enum-typed, the print
   carries the NAMES: `st_t st;`, `st <= none;`, `st_t'(d ? one : none)`, `st == two`.
   **A lane as one word is `pack(L)`** — member 0 the LSB. A `net_lane` exists only as its
   members, so a port fed by a lane needs this rather than the bare name; it prints as
   `assign out_byte = cap;`, one line and parametric, where the alternative was a weighted
   sum whose baked per-element weights made the module lie about honouring its parameter.
   **A module name with a leading capital is QUOTED**: `module("TopModule").` prints as
   `module TopModule`. ASP reads a bare leading capital as a variable, so quoting is the
   only escape — and renaming it lowercase instead would print the wrong SystemVerilog
   module name silently, which is a loud failure traded for a quiet one.
   Plus one rule: **a window's name is the name the
   specification declares.** The compiler never renames; the linkage is where vocabularies
   meet — mount `entryExists`, `forwarded`, `corresponds` on the design's own selection
   signals, beside whatever names a hand-written contract used. Derived views of one flop
   cannot disagree.

7. **Certificate — FOUR runs, ONE command.** Write the entry's `verify.json` (the flow
   as data — see `flow.py`'s schema) and run `python -m sv2asp.aspfirst2 certificate
   <entry>`; `verify <entry>` adds the round trip. The manifest's `log` keys write each
   report into the entry folder. What the manifest must carry, in order, none optional
   (each a paid-for lesson):
   1. **The standard run**: `refine <contract> <l1> --induct K`, starting at K=1.
   2. **The strong half**: the same induction with `--free-reset`. The standard step PINS
      the reset, so every reset-exempt monitor is vacuous there — the runner now says so
      (`NOT EXERCISED in this step`) and refuses to list them as inductive; the strong
      half is where they bind. Scenarios stay under released reset: a mid-story reset
      cancels the story by definition.
   3. **The second configuration**: regenerate the design at an off-default point (for
      the missq: depth 2) and run the standard certificate against the contract with its
      `#const` lines rewritten to match. A design parameterized in name only — baked
      thresholds, a sheared width — dies here and nowhere else, because the default-point
      certificate is structurally blind to it. Assert the point DISCRIMINATES (the
      off-default contract must reject the default design).
   3b. **Print parity, automatic with the second point.** Both configurations are PRINTED
      and must differ only in the parameter defaults. The second point certifies the ASP,
      and a parameterisation can be lost between the ASP and the print — a block passed at
      `dataBits=3` while its printed module carried eight hardcoded `assign byteUpTo[i]`
      lines. "This module honours its parameter" is a property of the printed RTL, so the
      check reads printed RTL.
   4. **Read the report's exclusion lines as the boundary of the claim** — "reset held
      released", "NOT EXERCISED", "bounded-only" are part of the verdict, not boilerplate.
   **When the step fails, the remedies are ORDERED**: read the counterexample (usually
   the abstraction's excess, sometimes a compiler defect); raise K toward the printed
   deepest reference; ONLY THEN write the confining claim. **And after fixing anything,
   re-measure whether earlier remedies are still needed** — an invariant added during a
   misdiagnosis survives as cargo under a justification that is no longer true, and only
   measurement finds it.

8. **Print, round trip** (`--sim auto`: Verilator first, else Icarus), entry bookkeeping, catalogue row, and a gate in
   `tests/test_aspfirst2.py` whose sabotage is a REAL defect this entry found. **The
   printed RTL has conventions** (methodology 27.1): parametric honestly — every size COMPARISON a parameter expression
   (`liveCount < COUNTWIDTH'(DEPTH)`), never a baked number; grouped generate-for blocks
   (a slot's logic together, not one block per net); the `xxM1` staging with the hold
   term visible and flops as `xx <= xxM1`; human names with no hoisted wires and no
   sigil in any identifier.

**A window holds ONE value at an instant, and the compiler checks it** — a
`<window>NotSingleValued` monitor per value-carrying window, so a linkage that mounts one
window from two rules (a one-hot phase with both bits high) is reported by name. You do not
transcribe "the phase is exactly one of these" — and when `SPECIFICATION.md` carries that
sentence, TAG IT to `<window>NotSingleValued`, so the clause has a rule to cite like every
other checkable sentence. The reason it is
a monitor and not a constraint: a constraint would exclude the multi-valued runs, so a
genuinely multi-valued linkage would come back UNSAT, and UNSAT reads as "no counterexample".
A window you declare `set of KIND` is legitimately many-valued and exempt.

**You do not write hold conditions, and you should CHECK that you got them.** A behaviour
says what happens when its event occurs and, on its own, nothing whatever about the cycles
when it does not — so the compiler adds a hold-otherwise FRAME monitor per window: a change
with no licensed cause is a named failure, and the licence is specific to the position
written. That is what pins a captured byte to the line between the cycle it arrived and the
cycle it is presented, and it is why "X does not change until Y" usually needs no clause of
its own. Read the generated contract for `<window>Disturbed` and satisfy yourself the ones
you expected are there — **only a window some behaviour WRITES is framed**, because a window
the specification merely reads is a derived view of the design rather than state the
specification controls.

## Traps paid for by this route

- **Transitions are behaviours; invariants are properties.** "At the next edge, X is Y" is a
  behaviour: its effect reads the sources NOW and writes the target next. A property's
  `@then @next cycle x == y` puts BOTH sides at the next instant and says something else.
  Getting this wrong compiles clean, and a block whose central rule was transcribed as a
  property sat green for a session.
- **A port read several times in one claim is sampled once** — the compiler's job, not
  yours. Write the neighbourhood the natural way; do not route reads through a window to
  make the grounder finish.
- **Opaque compares are equality-theory, never token identity** — identity across instants
  is false by construction (every input a fresh token), and identity between design and
  contract lets each judge the same pair differently. `$stable` on a payload means every
  payload wire of the interface, through the theory.
- **The failure stamp is the determination instant** — where the wrongness appears (`T+1`
  for `|=>`, `T+b` for a window), matching hand-written contracts. Verdict comparisons must
  never assume stamps align; that difference was found only by a person reading two reports.
- **A helper is a definition**: written once at plain T, head and body, called at whatever
  instant the use needs. Both shortcuts fail — body-at-t/head-at-T double-shifts every
  call; both-at-t reads as ghost state.
- **A safety binder must be the IDENTITY domain, never the existence window** — demanding
  `entryExists(E)` inside a helper whose content is "the entry is GONE" makes the escape
  underivable, and the lifetime clause fires on every correctly-freed entry.
- **Fairness is architecture**: a per-entry bound (`##[1:depth]`) rests on the arbitration
  rotating, not on the forwarding path — fixed priority starves above the measured depth,
  and the parametric fact lives in Lean (`RouteLean.Rotation.reaches`), because clingo
  grounds and cannot be given "for every depth".
- **A module parameterized in name only**: the header can carry `#(parameter DEPTH)`
  while the thresholds compare against baked defaults — author every threshold as a
  parameter expression (`lt(count, k(depth, w), w)`), and sweep the print for numbers.
  The second-configuration certificate run is the mechanical catch.
- **A derived quantity is a parameter EXPRESSION, never a defaulted free parameter** —
  `param(countWidth, log2(add(depth, 1)))` prints as a `localparam` no override can
  shear; a defaulted `COUNTWIDTH = 3` beside `DEPTH = 8` collapses every threshold.
- **A window and its counter gate alike**: two derived views of one fact must agree
  about what exists — `inFlight(E)` was valid-gated while `inFlightCount` summed raw
  bits, and a stale bit in an invalid slot counted as an entry under reset.
- **The two-producer fixture is per-entry, not a route requirement**: the miss queue
  keeps `specFv.lp` (the FV stand-in's hand contract) for its parity gates, but new
  modules need not have one — the compiler's entry-independent evidence is the Stage-5
  differential and the Lean schema meanings.
- **A gap goes back to the maintainer, never around**: re-run with `--report issue.txt`
  (every verb takes it) and send that file — tool version, resolved toolchain, command,
  output, nothing from the design. Never patch the installed tool: a certificate from a
  modified tool means nothing.
- **Gate exit codes are read directly, never through a pipe**; a claimed edit is verified
  before its commit message claims it.

## If you see X, do Y

| you see | it means | do |
|---|---|---|
| `PROBLEM: line N: [rule] ...` | a check refused the pair of files; `compile` exits non-zero | fix by name — every finding says what is wrong and why it matters. Never work around it |
| `the printed RTL is NOT parametric` | printing at the two configurations changes more than the parameter defaults, so the module carries a parameter it does not honour | look at the named lines: something is baked per element. Usually the DESIGN, not the printer — a construct whose body differs per index cannot roll into a `generate for` |
| `PROBLEM: the emitted contract does not ground` | the compiler produced an artifact clingo will not read — an unsafe rule stops grounding and takes the whole program down | a TOOL defect, not a specification one: `--report` it. Nothing downstream can run until it is fixed, so there is no working around it |
| `PROBLEM: the sigil rule: line N: ...` | a structural keyword is missing its `@`, or a word is not in the vocabulary | the message gives the exact spelling; `sv2asp2 keywords` lists what exists |
| `PROBLEM: <decl>: no frozen pattern covers the condition: '...'` | the sentence is outside the controlled English | rephrase within the patterns. If the sentence is legitimate and has no spelling, that is a gap: `--report` it |
| `PROBLEM: <file>.yaml: ...` (no line, no rule) | the SIGNATURE was refused, before the specification was even read | an enumerated field is out of domain, or a reset declares no polarity. The message lists the valid values; the spelling is exact |
| `REFUSED: <decl>: ...` | the construct is outside the language, not outside the tool's abilities | rephrase within the frozen patterns. If the sentence is legitimate and has no spelling, that is a gap: `--report` it |
| `window demanded of the design: X` | the specification asked the design for a view it must mount | add X to the linkage. A demanded window nobody mounts derives nothing, and the claims reading it go quietly vacuous |
| `NOT EXERCISED in this step` | the monitor is reset-exempt, and the standard step pins the reset | expected — the strong half (`--free-reset`) is where it binds. It is NOT inductive until that run says so |
| `NOT inductive` + an invariant request | the property set cannot close by itself yet | the ORDERED remedies: read the counterexample, raise K toward the printed deepest reference, and only then write the confining claim |
| `failType(<window>NotSingleValued, ...)` | the linkage mounts that window from more than one rule, so it holds two values at an instant | fix the LINKAGE, not the claim — a multi-valued window silently SATISFIES claims the design violates, because a claim asks whether some value matches. If the window is genuinely many-valued, declare it `set of KIND` |
| a monitor that never fires in any scenario | usually a dead body, not a satisfied claim | check it is not asking for something underivable — a guard needing the reset both ways, a window nothing mounts, a quantifier over an undeclared kind |
| a scenario over `@every <kind> V:` is not reachable | the reading is UNIVERSAL by design — ONE position failing the expectation is enough | find the position, not the scenario: the story is reached only when none violates, which is what makes "every data bit is one" mean what it says |
| the certificate is green on the first try, with no scenario output | suspect vacuity before celebrating | the scenarios must be SAT; a base that proves everything proves nothing |
| `inferred latch` on the round trip | the print's guards are not visibly total | guard on the enum tag, so the print is one `case` over every member |

## Where things are

| what | where |
|---|---|
| **the ASP you must generate** | `sv2asp2 schema` (design facts, primitives, contract vocabulary, linkage) |
| the surface's vocabulary | `sv2asp2 keywords` |
| the methodology (Chapter 0 first) | `docs/spec2rtl2/ROUTE_METHODOLOGY.md` (+ PDF) |
| the compiler's contract | `docs/spec2rtl2/TRANSLATION.md` (+ PDF) |
| the grammar's single source | `lib/dsl/grammar.ebnf` (`dsl.grammar`; `--lark` shows the derived parser input) |
| the front end | `src/sv2asp/aspfirst2/dsl/` (signature, parse, check, expr, emit) |
| the worked entry | `examples/spec2rtl2/rv_missq/` (all seven rungs + `CERTIFICATE.md`) |
| the direct-ASP procedure this builds on | `.claude/skills/spec2rtl-v2/SKILL.md` |
| the route worklist | `notes/WORKLIST_SPEC2RTL.md` |
| every tool change, with its reason and its gate | `docs/spec2rtl2/CHANGES.yaml` (open = worklist, fixed = changelog) |
