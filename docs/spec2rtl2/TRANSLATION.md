# The translation grammar — from the signature and the specification to `spec.lp`

This document was written as a plan and is kept as the compiler's CONTRACT. The plan has
since been executed: the signature loader, the structural and semantic checks, the claim
and behaviour emitters, scenarios, and the controlled-English surface on top (the
methodology's Chapter 35) are built and gated, and the worklist records each phase with
its witnesses. What remains normative here is unchanged by that: what the compiler must
do, construct by construct; what "the translation is correct" has to mean, and why the
obvious bar is the wrong one; and the staged order, whose gates are now the record of how
it was built rather than a promise about how it would be.

## 1. What is new, and what is untouched

The route's essence is unchanged: **an ASP contract, a design, induction, and RTL out the
far end.** What changes is only where a person starts.

When this plan was written, an author's first act was to write `spec.lp` by hand — the
contract, in ASP. That is the hardest and most specialised thing the route asks of anyone:
it demands the wrap-bit pointer trick, the knowledge that a counter is enumeration in
disguise, the discipline to state a frame condition as a monitor rather than a model. The
language and the signature replace **that authoring act**, and nothing after it. One
further layer has since been added on top: the symbolic notation itself is not
hand-written either — it is generated from a CONTROLLED ENGLISH surface (the methodology's
Chapter 35), so what a person writes is sentences, and what this document describes is
what those sentences become.

```
   SPECIFICATION.md              English, in force
          |
          v
   <block>.cnl  +  <block>.yaml   controlled English + the signature -- what a person writes
          |
          |   desugar (mechanical)
          v
   <block>.cnl.core               the symbolic core -- generated, committed, never hand-edited
          |
          |   compile
          v
        spec.lp                   THE ASP CONTRACT -- the route's proof anchor. Today an
          |                       entry's contract of record is the FV stand-in's; this
          |                       chain is a second PRODUCER of the same layer, held to
          |                       verdict parity against it
          |
   =======|=================================================  from here, v2 exactly as it is
          v
   l1.lp  +  l1.inv.lp        the design, and its linkage mounting the spec's windows
          |
          v
   refine spec l1 --induct K       lint, base, step, scenarios, delivery obligations
          |
          v
   print  ->  roundtrip --icarus  ->  RTL
```

**The compiler emits one file: `spec.lp`.** Not the design, not the linkage, not a
stimulus — v2's certificate takes no stimulus at all — and not an `l0`, which v2 keeps only
as a diagnostic rung.

**RTL is never generated from the DSL. The route always goes through ASP.** This is a
standing rule, not an artefact of what happens to be built yet, so it is worth stating with
its reason. The compiler's whole output is the contract. The design is a separate artifact,
authored in the ASP authoring form, and SystemVerilog comes from printing *that* — the path
that already has a proven printer, an independent translator reading it back, and a simulator
arbitrating between them.

The independence that matters here is not authorial — the same model often writes both the
specification and the design — but **mechanical**: the certificate does not ask who wrote the
design, it asks whether any execution of it can violate any property of the contract, and
clingo answers. What would destroy that is a shared mechanical derivation: RTL emitted from
the same specification by the same compiler would carry any front-end misreading identically on
both sides, and the comparison would pass while saying nothing.

The honest limit, which is why §5 exists: authoring the design does not protect against a
*compiler* defect. A mistranslated specification is faithfully implemented and faithfully
certified. That is why the generated `spec.lp` is committed and readable, and why this
translation needs a correctness argument of its own.

### 1.1 Why the linkage is not the compiler's to write

The specification declares its windows as free vocabulary: a name, a domain, a prose
meaning. The **linkage** — `pointer_push(P, T) :- val(write_pointer, P, T).` — names *this
design's* registers, and no design exists when the specification is written. So the linkage
belongs to the level, is written with the level, and the compiler cannot produce it.

What the compiler can and should produce is the **mount manifest**: the list of windows this
contract requires, with their arities and meanings, so a level's author knows exactly what
must be given glass. That matters more than it sounds, because of the failure mode the
methodology names: **an unmounted window makes its monitors silently vacuous** — a monitor
over `cell_value` on a level that never defines `cell_value` can never fire, and "never
fires" is indistinguishable from "always satisfied." A generated manifest is the input the
window-with-no-glass check wants.

## 2. The signature is the compiler's symbol table

The specification names no wires. `request.valid(R)` is not a signal, and `R.address` is
not a field of anything the specification declares. Both resolve through the signature.

So the signature is not documentation sitting beside the specification. **It is the symbol
table**: without it the specification denotes nothing, and the compiler reads both files or
neither.

### 2.1 What each part decides

| signature section | what it fixes |
|---|---|
| `parameters` | a `#const` at the head of `spec.lp`, and every domain derived from it — `depth` is the miss queue's slot count and the FIFO's pointer modulus |
| the clock | the time axis the whole contract is indexed by |
| the reset | `live(T) :- val(reset_n, 1, T).` — the predicate `disable iff` expands into — plus the reset properties at both ends of the release edge |
| `interfaces` — `protocol` | which verbs exist. `readyValid` gives the derived event `accepted(T) :- live(T), val(x_valid,1,T), val(x_ready,1,T).`; `validOnly` has no acceptance to define |
| `interfaces` — `side` | direction: a property may require a `sends` output to take a value; a `receives` input is the environment's |
| `ports` — `role` | **the control/data split**. `opaque` means a token: comparisons go through `boundary(eq(A,B),1)` and are read back as `pval`, never enumerated. `numeric` means an ordinary value with a domain |
| `ports` — `width` | that domain |

The `role` row carries the cost. Declaring `requestAddress` as `opaque` is what lets a
26-bit line address be compared without a 2^26 domain ever being built — and in the v2 miss
queue it is exactly what keeps the address comparisons linear in `depth`. That decision is
made once, in the signature, instead of remembered at every use.

### 2.2 The expansion, concretely

| written in the specification (core form) | compiled, through the signature, to |
|---|---|
| `request.valid(R)` | `val(request_valid, 1, T)` |
| `R.address` | `val(request_address, A, T)` — `opaque`, so `A` is a token |
| `R.isDemand == 1` | `val(request_is_demand, 1, T)` — `numeric`, an ordinary value |
| `accepted(R)` | the derived event `accepted(T)`, from `protocol: readyValid` |
| `fill.arrives(F)` | `filling(T) :- live(T), val(fill_valid, 1, T).` — `validOnly`, no ready conjunct exists to write |
| `E.address == F.address` on opaque roles | a `boundary(eq(A,B),1)` declaration plus a `pval(eq(A,B),1)` read |
| `disable iff (!resetN)` | the `live(T)` guard on every rule |

### 2.3 The checks that exist only because there are two files

Each is a genuine cross-file check, and none is possible from either file alone: every name
resolves; every verb matches its protocol (`accept` on a `validOnly` interface is an error,
not a modelling choice — the wires do not exist); every drive respects direction; every
field access type-checks, so a misspelled `R.tag` is refused rather than quietly becoming a
fresh free variable that makes some property vacuously true; widths agree; and every output
port is constrained by some property or carries a written don't-care.

The last deserves its own line, because version 1 paid for it: **an output nothing
constrains and an output deliberately left free produce identical artifacts.** There is no
way to tell them apart by looking at the result, so the check has to be structural, and a
declared port list is what makes it mechanical.

## 3. What the compiler emits, construct by construct

### 3.0 What the four semantic decisions demand of the compiler

The decisions of the methodology's Chapter 33 were made after this plan was first written,
and they change what the front end must do. They are collected here because three of the four
are things a compiler *would otherwise have decided by accident* — and a decision taken by
accident becomes the language's real semantics without anyone reviewing it.

**An object is a slot, and existence is a window.** Every quantifier ranges over the objects
that exist at the instant it is evaluated, so every quantifier is silently asking the design
which slots are live. The compiler therefore emits an `exists` window **whether or not the
author wrote one**, and puts it in the mount manifest. This is the clearest case of the
general point: nobody writes `exists(E)` in an ordinary rule, so nothing in the source text
tells you the demand is there — only the semantics does.

**Scope is syntactic, so scope errors are cheap to catch.** A variable used outside its
quantifier's scope is refused by name (well-formedness 10a). This needs no solver and no
analysis: it is a property of the parse tree, and it is the one place where the compiler can
say *"you probably meant `each entry E ( … )`"* and be right nearly always.

**Lifetime is a shape check, not a proof.** A claim mentioning a bound object under a delay
must mention `exists` there too (10b). Also purely syntactic — and it closes a hole that a
solver would never report, because the resulting contract is perfectly satisfiable, just
about the wrong thing.

**Correspondence is a manifest entry.** `send on IFACE answering E` compiles to a declared
window naming which object each send serves, mounted by the level's linkage on the design's
own selection signal (10c). The compiler never *establishes* the relation — that would be
specification-side state, and an assertion where a check belongs.

**The reset exemption is a rule about which properties the `disable iff` reaches.** A property
mentioning the reset signal is exempt. The compiler applies that automatically; what makes it
safe is not the rule but the report (10d), and the report is the compiler's obligation too:
it must emit whatever the runner needs in order to say which properties could never have
fired.

Three of these four exist because the failure is **silence**. That is worth restating in a
document about a compiler, because a compiler is exactly the place where a silent decision
gets made once and applied for ever.

### 3.1 `@state` and `@define` — windows, never notebooks

`@state held : transaction of input` does **not** become specification-side storage. It
becomes a **declared window**: a name, an arity, a domain, a prose meaning, and an entry in
the mount manifest. `@define` becomes either a port-only helper (no state, computed from the
interface) or another declared window.

This is the hard rule, and it is the one the previous draft of this document got wrong:
**the compiler never emits specification-side state.** v2's lint refuses it outside a
`refmodel` gate, so a compiler that emitted it would produce contracts the route rejects —
and rightly, since a notebook must be initialised, proven consistent with the design in
every reachable state, and enumerated by the grounder.

### 3.2 `@property` — one named `bad` per kind of wrongness

Each temporal form has one instant-indexed reading and one rule schema, and every one of
them lands as a `bad/2`:

| DSL | generated ASP |
|---|---|
| `P \|-> Q` | `bad(name, T) :- live(T), P(T), not Q(T).` |
| `P \|=> Q` | `bad(name, T+1) :- live(T), live(T+1), P(T), not Q(T+1).` |
| `P \|-> ##N Q` | as above with the head at `T+N`, liveness on each instant between |
| `P \|-> ##[a:b] Q` | a witness helper over `K = a..b`, then `bad` when no witness exists |
| `P \|-> Q until R` | `bad(…, T+K)` guarded by a no-R-yet helper |
| `$stable(x)` | `val(x, V, T-1), val(x, V, T)` |
| `$rose(x)` / `$fell(x)` | the two-instant pattern |
| `some X where P: Q` | a variable guarded by the index and `P` |
| `each X where P: Q` | the same, with the violation head per `X` |
| `each X ( P \|-> Q )` | one rule with `X` bound across both halves — the scoped form |
| `each X:` block | the same binding, shared by every claim in the block |
| `exists(X)` | the existence window, emitted whether or not it is written |

The name is not decoration. A certificate that fails names the `bad` that fired and the
instant, so the name is the first line of the diagnosis — which is why the DSL requires
every property to carry one.

### 3.3 `@behavior` — an event monitor and a hold-otherwise monitor

This is where the previous draft was most wrong, and the correction makes the compiler much
simpler.

A behaviour is not a model the specification runs. It is a **judgement on the design**, and
it compiles to two monitors:

```prolog
% the event: the trigger fired, so the window must show the consequence
bad(pointer_push_wrong, T+1) :- accepted_push(T), live(T+1), pointer_push(P, T),
                                Q = (P + 1) \ (2*depth), not pointer_push(Q, T+1).

% the frame: nothing fired, so nothing may have changed
bad(pointer_push_wrong, T+1) :- live(T), live(T+1), not accepted_push(T),
                                pointer_push(P, T), not pointer_push(P, T+1).
```

**So the frame rule is not the frame problem here.** There are no inertia rules, no
successor-state axioms, and no stratification question, because the compiler is not
building a transition relation — the design is the transition relation, and the frame
condition is one extra monitor per state symbol saying *if nothing caused a change, a change
is wrong*. The FIFO's `cell_disturbed` is literally this rule, hand-written.

The compiler's obligation is completeness of the trigger disjunction: the frame monitor's
`not <trigger>` must cover **every** behaviour that writes that symbol, or the contract
forbids a change the specification allows.

**And the frame has a KEY, which the declaration supplies.** The question is the same for
every window — did this change with no cause that licensed it? — but it must be asked *of
something*, and what varies is what the answer is indexed by. A scalar window (a phase, a
counter) has no key. A window indexed by a declared domain is keyed by the position, which
ranges over the declared extent. A field or flag of an object is keyed by the object, and
only that case carries the guard that the object exist at both instants — because only that
case has a lifetime, and without the guard allocation and death would be reported as frame
violations.

Two consequences the compiler must get right, each of which fails silently:

- **A licence is specific to its key.** When a behaviour writes one position — capture the
  line into the bit the counter points at — the licence records *which* position, read at
  the instant the event happened. Licensing every position instead emits the same monitor,
  reads correctly to a reviewer, and forbids nothing.
- **Only a window some behaviour WRITES is framed.** A window the specification merely reads
  is a derived view of the design rather than state the specification controls; framing the
  miss queue's `liveEntries`, which is the count of what exists, would forbid a change no
  requirement ever claimed to govern.

This is written out because the rule was first implemented for the object case alone, with
the object baked into three separate places — the patterns deciding which windows an effect
writes, the existence guards, and the arity of the emitted atoms. A block whose state was a
phase, a counter and an indexed array got **no frame monitors at all**, with no refusal: it
compiled, reported every monitor it had, and certified green while nothing forbade the design
from changing a captured bit between the cycle it arrived and the cycle it was presented.

**The failure stamp is the determination instant** — the cycle where the wrongness appears,
not the cycle its trigger fired. For `P |=> Q` that is `T+1`; for `P |-> ##[a:b] Q` it is
`T+b`, the instant the last chance was missed, which is the only well-defined choice for a
window. The stamp is the first line of diagnosis: a person reads `violated @T` and looks at
column T of the counterexample table, so a report pointing one cycle before its own evidence
wastes exactly the person it exists for. (Found by the FIFO differential — the two contracts
agreed on every verdict while stamping the same violation one cycle apart, which no verdict
comparison could catch; only a person reading both reports side by side did. A differential
is blind to whatever it does not compare.)

### 3.4 `@assume` — an integrity constraint, not a stimulus

v2's certificate takes no stimulus file. An assumption is a constraint on the world, written
into the contract:

```prolog
:- filling(T), not fill_home(T).      % a fill is for a line whose fetch is in flight
```

Executions violating it are excluded rather than reported, which is exactly the difference
between an assumption and a property.

### 3.5 `@scenario` — a constrained abstract start and one cycle

v2 scenarios are not scripts. Each is a state description, an input, and an expectation,
evaluated over a compliant abstract start plus one cycle — cost independent of depth and
history. The compiler emits the triple plus its two definitions:

```prolog
scenario(allocate_when_empty, empty_offered, any_input, one_allocated).
holds(empty_offered, T) :- …            % the constrained start
did(one_allocated)      :- …            % the expectation, read at instant 1
```

### 3.6 Objects and `create` — the design's slots, seen through an indexed window

`create entry N` does not allocate. The miss queue's entries **are the design's slots**, and
the specification sees them through an indexed family of windows —
`slot_valid(I,T)`, `slot_address(I,A,T)`, `slot_filled(I,T)` — whose index ranges over
`0..depth-1`, with `depth` a `#const` from the signature's parameters.

So there is no pool of specification-side identifiers and no capacity to derive: the
capacity is a parameter, and "a request is allocated" is a property about some free slot
becoming valid with that address. This removes what the previous draft called the third hard
part entirely.

### 3.7 Delivered data — an obligation, not an enumeration

Where a property states the required *form* of a delivered value, the compiler emits
`model(Port, Want, T)` with an `obligation_span(N)`, and the certificate compares the
design's delivered term with the specification's: identical terms are discharged by
identity, a symbolic difference is **owed to Lean**, a concrete difference is a violation
with a witness table. Data is never enumerated on either side.

## 4. What the compiler must refuse, and what it must be clever about

### 4.1 The check this route learned it needs: contradictory constructions

On 2026-08-31 the miss queue's specification was read by a person, approved, and then found
— while a design was being written against it — to contain a flat contradiction. Three
behaviours disagreed about the same wire:

```
@behavior signalReady              roomForDemand  -> ready on request
@behavior refusePrefetchAtReserve  ...            -> refuse R
@behavior stallRepeatDemand        ...            -> refuse R
```

`accepted(R)` is `valid && ready`, from the interface's protocol. So with depth 4, a reserve
of 1 and three live entries, `roomForDemand` holds, ready goes high, and a non-matching
prefetch is *accepted* — while `refusePrefetchAtReserve` refuses it. The machine accepts and
refuses the same request in the same instant. One of the specification's own scenarios sat
exactly on that state and would have failed.

**This is the argument for mechanical translation, in one example.** The contradiction
survived being written carefully, read line by line against the grammar, and approved. What
found it was a person trying to build hardware from it. A compiler must find it first.

> **The check:** for any two behaviours whose constructions conflict — accept against refuse,
> two different values driven onto one signal, a state set and cleared — the compiler must
> establish that their antecedents cannot both hold. If they can, it is a **static error**,
> not something a priority order resolves.

The important part is that **this check is a solve, not a syntactic pass.** Whether two
antecedents can hold together is a satisfiability question over the window vocabulary and the
interface, and the tool that answers it is already in the stack: the compiler emits the
question and clingo answers it. That makes the check exact rather than approximate, and it
costs one small solve per conflicting pair.

The repair, for the record, was to decide acceptance in exactly **one** place: `ready` became
class-dependent (a queue can have room for a demand and none for a prefetch in the same
instant — that *is* the reserve), and the two `refuse` behaviours were deleted because they
restated what `ready` already decided. Saying a thing twice is how the two came to disagree.

### 4.1b The generated TEXT is checked before it leaves the emitter

Two malformations are refused at emission, and one incident sits behind both
(2026-08-31): a renaming let a fresh helper collide with a claim's reserved main name,
so two lowerings shared one head — and one rule ended up NEGATING ITS OWN HEAD in its
body, unstratified nonsense wearing a contract. Reading the output caught it once;
`wellformed_problems` catches it every time: a rule whose body negates its own head, and
a head defined in two separated places (one lowering emits a head's rules together, so
distance means two owners). The emitter refuses to emit rather than warns — a malformed
contract that ships is a false certificate waiting to happen. Gate:
`test_v2_generated_contract_wellformedness_check`, with both sabotages.

### 4.2 The same check, on the OUTPUT: is the generated contract self-consistent?

Section 4.1 checks the behaviours against each other. There is a second, cheaper check that
must run on the **generated `spec.lp` itself**, and the miss queue paid for its absence twice.

**And before any of that: does the output GROUND?** It is the cheapest question of all and it
was the last one asked. A compiler that reports its refusals and never reads what it wrote can
exit 0 on an artifact the solver will not accept — and in ASP that failure is not local.
Clingo does not skip an unsafe rule; it stops grounding and takes the whole program with it,
so one free variable in one auxiliary rule means no refinement, no certificate, and no
discrimination against a second configuration. The case that showed it was a boundary
declaration whose position variable was bound in the claim's rule and free in the separate
rule the declaration became.

Two properties make this affordable enough to run unconditionally, and both are worth stating
because a check that is expensive or noisy gets switched off:

- **Safety is syntactic**, so the contract grounds *on its own* — no design, no linkage.
  Almost every rule grounds to nothing, and the whole corpus compile including the check
  costs a fraction of a second.
- **Only `error:` counts.** The undefined atoms a standalone contract necessarily has produce
  info messages on every correct compile; a check that treated those as failures would fire
  constantly and be disabled within a week.

The general form is worth naming, because this is a class rather than a bug: **every other
check here asks whether the artifact says the right thing, and this one asks whether it can
be read at all.** A front end owes both.

An **assumption set that admits no execution makes every property vacuous.** Two of the miss
queue's assumptions — "a request is held until it is taken" and "the fetch pipe honours the
stall" — were each defensible alone and jointly impossible: a stalled repeat demand had to
stay presented *and* go away. Nothing said so. The certificate eventually reported two
scenarios as "no compliant state", which is a true statement about the wrong subject: it
names the scenario, not the assumption pair that killed it.

So the compiler must, on its own output:

> **Check that the assumptions admit an execution at all**, and that each scenario's start
> state survives them. Both are solves — one `#project` over the assumption set alone, one
> per scenario — and both are cheap because they need no design.

The second half matters more than it looks. A scenario is the route's anti-vacuity device, so
a scenario silently excluded by an assumption disarms the very check that exists to catch
silence. Reporting *"scenario X is excluded by assumption Y"* is the difference between a
five-minute fix and the afternoon this one cost.

The general form of the rule, which applies to both this section and the last: **a
specification can be false, and it can also be empty — and empty is the more dangerous of the
two, because everything it claims is true.**

**Refuse, by name:**

- Anything that would need specification-side state outside a `refmodel` gate (§3.1).
- A bare `s_eventually` with no reduction to a bound, a ranking, or work-conservation. That
  reduction is a proof step (the methodology's obligations chapter), not a translation step.
- A quantifier over a domain that is not bounded by a declared index or a parameter.
- Any cross-file inconsistency from §2.3.

Refusal is by name, never by silent omission — the route's central guarantee.

**Be clever about — and this is one of the strongest arguments for having a compiler at
all.** v2's performance budget is currently a *human discipline*: the author must know that
a count grounds over its whole domain, that pointers should be wrap-bit encoded so "full" is
one modular relation rather than arithmetic, that a history ghost should be replaced by a
one-step relation. The DSL lets the author write the intent — `atMost(depth, …)`, "the
pointer advances on the event and holds otherwise" — and leaves the *encoding* to the
compiler, which can emit the profitable spelling every time instead of the obvious one.

Where the compiler cannot find a cheap spelling, it must say so before the solve rather
than after a timeout. Grounding blowups are the route's most expensive failure mode, and
the compiler is the first place with enough information to predict one.

## 5. What "correct" must mean

Scope first: this is about **the front end only**. Whether the design meets the contract is
what the certificate answers, and whether the printed SystemVerilog matches the design is
what the round trip answers. Both exist. What is unproven is the new step: **does `spec.lp`
mean what the specification says?**

**The wrong bar, and this repository has already paid for it.** Version 3 of the RTL
translator achieved byte-identical output against version 2 and was retired for its
*acceptance criterion*: defining correctness as agreement with an artifact nobody had proven
meant it was obliged to reproduce version 2's defects, and it did. So "the compiler emits
the `spec.lp` I would have written by hand" is not correctness. Neither is "the generated
contract certifies" — a translation that drops a property also certifies, and faster.

**The right bar needs two independent definitions and a theorem between them.**

1. A **denotational semantics** for the language, written independently of the compiler:
   a specification plus its signature denotes a set of trace properties over the ports
   and the declared windows.
2. The **semantics of the generated ASP**, which already exists and is proven here: stable
   models, with Fages' theorem giving completion = stable models for tight programs.
3. The theorem: a trace derives some `bad` under `compile(S)` exactly when it violates the
   meaning of `S`.

**And the mechanism that keeps the theorem about the shipping compiler** rather than an
idealised one is the technique `proofs/` already uses: **derived tables** — generators that
run the real compiler, parse its output back, and check it against the model on every build.
A formal model that can drift from the code is a model of nothing.

**Two limits, stated plainly.** The theorem closes the step from DSL to ASP; it does not
close *intent to DSL*, which is the same irreducible edge the methodology already names
between English and contract, and it is guarded the same way — worked examples, scenarios
that must stay reachable, a reference interpreter a human can check by hand. And proving the
**parser** accepts exactly the grammar is a different problem, whose structural answer is to
stop having two grammars: one machine-readable grammar file generating both the parser and
the methodology's EBNF block, with a gate that fails if either drifts.

## 6. The staged plan

Each stage is useful on its own and has a gate. The ordering puts the cheapest bug-finding
first, because in this repository's history the differentials, not the proofs, found the
defects.

**Stage 0 — one grammar and one schema.** The EBNF moves to a machine-readable file
generating both the parser and the document's grammar block; the signature gets a schema and
every `.yaml` is validated against it. *Gate:* a drift test fails if document and parser
disagree; a malformed signature is refused by name rather than half-read.

*Done, with one half honestly outstanding.* The core grammar generates the parser, and the
surface's CONDITION patterns generate the controlled-English matchers — a production with no
handler, or a handler with no production, is refused at import, and both rendered blocks in
the methodology are drift-gated. The surface's EFFECT shapes are *documented* in the grammar
file and *dispatched* in code, so that half is a description which can drift and no gate
catches it. Extending the derivation to the effects is tracked in `AUTOMATION.md`.

**Stage 1 — the signature front end.** Names, roles, protocols, parameters; the six
cross-file checks of §2.3; the expansion of interface predicates to `val/3`. *Gate:* every
check has a witness and a sabotage that must fail.

**Stage 2 — properties and assumptions.** §3.2 and §3.4 over an existing hand-written
design. *Gate:* the compiled FIFO contract and the hand-written one **agree on verdicts**
across the certificate — base, step and scenarios — for the real `l1`, and for a sabotaged
`l1` that must fail the same way. Note this is agreement on *behaviour*, not on text.

**Stage 3 — behaviours.** The event monitor, the frame monitor, and the trigger-completeness
obligation of §3.3. *Gate:* the methodology's one-word buffer (Chapter 5) certifies end to end from
its two files.

**Stage 4 — windows, indices and the mount manifest.** §3.1 and §3.6. *Gate:* the miss queue
compiles from its controlled English (`rvMissq.cnl` — the plan named the symbolic
`rvMissq.spec`, since archived) + `rvMissq.yaml`, and its manifest matches what
`l1.inv.lp` actually mounts.

**Stage 5 — the reference interpreter and the differential.** A direct evaluator answering
"does this trace satisfy this spec?", run against the ASP solve on random traces × small
specs. *Gate:* thousands of cases agreeing, and a deliberate mistranslation caught.
*Executed (2026-08-31), for the property layer:* `dsl/interp.py` evaluates the core's
property claims and lowered assumptions over concrete traces, from the methodology's stated
meanings; the differential pins seeded random traces against the generated contract under
clingo and agrees on admissibility and every (monitor, instant) verdict, with all of the
miss queue's property monitors exercised and two sabotage families caught (a monitor
silently dropped; a bound off by one operator). Building it found and fixed six interpreter
defects — which is the differential doing its job on its own second half. Behaviour
event/frame monitors and scenarios are the owed remainder, recorded in the worklist.

**Stage 6 — the meaning-preservation theorem** in Lean, against the semantics of §5, with
drift-checked generators against the shipping compiler.
*Executed (2026-08-31), the schema half:* `lib/lean/RouteLean/Claims.lean` states what each
claim lowering MEANS (a denotation over traces) and proves each monitor schema — same-cycle,
next-cycle, the bounded window — faithful to it: fires somewhere iff the meaning is
violated; the window's determination-instant fact is a theorem, and the two natural
mis-lowerings (first-instant-only window; dropped far-end live guard) are exhibited wrong by
countermodels, per the house sabotage rule. Axioms: the standard three. The tie to the
running Python is Stage 5's differential; the full per-construct denotational semantics
(quantifiers, behaviours) remains the open larger half.

## 7. Decisions

Three are settled by your scoping and are recorded rather than re-asked: the compiler
targets v2's conventions; it emits `spec.lp` only, since linkage names a design's registers
(§1.1); and it emits no `l0`, which v2 keeps as a diagnostic rung rather than a required
one.

Still open:

1. **Does the compiler emit the mount manifest as a file, or as a report?** *Recommendation:
   a file* — it is the natural input to the window-with-no-glass check, which is owed
   anyway.
2. **How hard should the compiler work at the cheap spelling (§4)?** *Recommendation: start
   with refusal, not cleverness* — reject what it knows will ground badly, and add each
   profitable encoding only when a real specification needs it. Guessing an encoding is how
   a compiler becomes unpredictable.
3. **Where does the semantics live first — the reference interpreter, or Lean?**
   *Recommendation: the interpreter* (Stage 5), because it finds mistranslations immediately
   and makes the Lean development easier to write.
4. **Does the signature stay a separate file?** *Recommendation: yes* — it is the one file a
   non-specification reader needs, it is the natural home for the industry-shaped metadata,
   and §2.3's cross-file checks exist only because the two are written independently.
