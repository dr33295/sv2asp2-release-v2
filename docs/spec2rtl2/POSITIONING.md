# Why This Route, and Not a Prover-Only Route

This document answers a question every reader of this route eventually asks: hardware
verification with proof assistants is a serious, well-funded research direction — Amazon
is building semantics platforms in Lean, and academic groups are attaching LLM agents to
provers to verify circuits — so why does this route put an answer-set solver at the
center and use Lean only at the edges? The answer is structural, not a matter of taste,
and it is worth having on paper because the route's architecture looks contrarian until
the division of labor is understood. The comparison below is grounded in what the
referenced projects actually are, with sources at the end.

---

## 1. The comparison class: what the prover-centric efforts are

**Amazon's Strata** [1, 2] is a Lean 4 platform for formalizing the *syntax and semantics
of languages*: a family of composable intermediate representations ("dialects", inspired
by MLIR), with an intermediate verification language (Laurel) that generates verification
conditions by symbolic evaluation and discharges them to an **SMT solver**. It is the
foundation under Amazon's broader Lean investment — the Cedar authorization language's
verified core [3], differential-privacy proofs, AI-chip compilation checks, agent
guardrails [4] — and its shape matters for this comparison: *the semantics live in the
prover; the per-instance verification conditions are discharged by an automated solver.*
Amazon does not hand-prove each program either.

**CircuitProver** [5] (HKUST) is the closest academic hardware analogue: a deterministic
translator turns Chisel designs into Lean 4 semantic models; an **LLM agent** reads the
English specification, formulates the Lean theorems (validated by co-simulation at small
bit-widths), plans a proof, and iterates against Lean's feedback, accumulating a reusable
lemma library. On a suite of 63 parameterized unit-scale tasks it reaches 100% with a
strong model; without the accumulated library, 92%.

**The NUS line** [6, 7] — agentic verification with proof assistants — applies the same
shape to software: LLM agents writing formal proofs for program-verification tasks, with
the recurring finding that proof development remains the cost center even when agents
carry it.

All three are serious work, and one of them (Strata's shape) this route quietly agrees
with. The disagreement is about *where the per-design work should land*.

---

## 2. Why the control half belongs to a decision procedure

### 2.1 The logic matches the problem, so there is no proof to find

Synthesizable RTL control is a finite transition system, and the route's emitted logic
programs are tight and stratified, so their Clark completion *is* the design's semantics
(Fages' theorem — proven, not assumed, in this repository's own metatheory). There is no
encoding gap between the model and the mathematics. Consequently the normal-form
induction — state abstracted at the window start, properties assumed over the window,
violation sought at the next instant — is a **single solve**: the solver *decides* it.

In a proof assistant, the same statement — "these properties are inductive over the
transition relation, for all time" — is a theorem with no native decision procedure.
Someone must find the induction structure, the strengthening invariants, the lemma
decomposition; Lean's powerful `bv_decide` is bounded and combinational and does not
touch temporal induction. This is precisely why CircuitProver needs an agent loop and a
curated proof library *for unit-scale modules*: the prover has no push-button for the
thing this route's certificate does in one query. The route's certificate needs no agent
because there is nothing to search for.

### 2.2 Counterexamples are first-class

A failed induction step here returns a *model* — a waveform-like table of every net at
every instant — in seconds, and the route's invariant-request workflow converges by
reading it. A failed Lean proof returns an open goal, which names no state and no cycle.
The retry loops of the agentic-prover papers are, in effect, heuristic reconstructions of
the diagnostic object a model-theoretic solver emits natively.

### 2.3 The marginal cost per design is seconds, not proofs

Measured on this corpus: the FIFO's nine safety properties are inductive with zero
hand-written invariants in about two seconds (`examples/spec2rtl2/fifo/`); the Am2901 —
2^68 states of architectural memory — proved inductive in three seconds in its v1 form;
the multiplier family's pipeline conveyor certifies in 1.8 seconds
(`examples/spec2rtl2/booth_production32/`). Against that, every prover-route design is a
proof-engineering episode, agentic or human. The route's own Lean cost is paid **once per
algorithm, not once per design**: the compressor lemma, the Booth recoding lemma, and the
disjoint-bits lemma were each proven once and reused across three multiplier machines.

### 2.4 The same engine checks the specification itself

An inductive certificate can be vacuously green — a spec whose situations are
contradictory, a monitor over a window nothing mounts. The route's scenario runner makes
non-vacuity a *checked* property: every scenario has a satisfiability leg that must
succeed ("this situation is possible and the natural operation occurs") before the
unviolability leg means anything, and an unreachable value-obligation is a loud failure.
Proof assistants do not naturally ask whether your theorem is vacuous — a contentless
Lean theorem typechecks, a hazard this repository has met in its own proof ledger and now
guards against structurally. CircuitProver's specification step, meanwhile, trusts an LLM
formalization validated by small-width co-simulation — a weaker specification trust root
than resolved English with per-clause rule tags and a sabotage discipline that
demonstrates every checker catching a planted bug.

### 2.5 The criterion for when the prover is used at all

The division is not a mood; it is a printed verdict. Lean enters a design's certificate
exactly when a delivered-value obligation ends with two terms that differ as symbols —
the checker's honest admission that a value claim exceeded its decidable reach — and the
certificate records the debt (**OWED to Lean**) on its last line until the theorem
discharges it. When the datapath is enumerable, no obligation is ever owed and no Lean
proof exists to write: the Am2901 entry's adder and status equations are proven correct
by the *checker's own exhaustive decision* — every operand pair, every carry, every
function, from every one of 2^68 states — with no prover involvement at all. The
prover-route projects have no analogue of this line: the prover is engaged uniformly,
whether or not a decision procedure could have settled the claim. (`METHODOLOGY.md`
§5.4 states the rule and the two worked cases.)

### 2.6 The route is not anti-Lean — it places Lean where Amazon places it

The division of labor here is the same one Strata embodies, with a different per-instance
engine. In this repository, Lean holds what must be held by a prover: the **translator's
metatheory** (every emitted rule schema proven against a formal model, 225/225 ledger
obligations — the analogue of Strata's semantics-in-Lean layer, built independently and
earlier), and the **datapath arithmetic** (the owed-to-Lean protocol: delivered values
compared as symbolic terms, the arithmetic obligation discharged structurally, for every
input width, by induction over the circuit's shape). The per-design temporal control goes
to ASP rather than SMT because that is where the domain's semantics point: stable-model
semantics gives foundedness and state natively, the ground programs are legible enough to
read in a design review, and the whole certificate — induction, scenarios, obligations —
is one engine's vocabulary.

---

## 3. The honest limits

Stating the boundary keeps the claim clean.

- **Parameterization.** The ASP control certificate runs at parameter instances (depth 4,
  width 8); the for-all-widths statements live in the Lean half, where the structural
  proofs are width-generic. A prover-only route states parameterized theorems natively.
- **Unbounded liveness.** The route proves liveness as bounded-safety (a ghost counter,
  starvation within N); genuinely unbounded temporal properties are prover territory.
- **Grounding walls are real.** The solver's grounding phase enumerates blindly, and this
  route's methodology exists precisely to engineer around that (windows instead of
  notebooks, tokens instead of values, the opaque-datapath directive). That discipline is
  a cost the prover route does not pay in this form — it pays instead in proof
  engineering, which measurement shows to be the larger bill for this problem class.

---

## References

1. **Strata** — an extensible platform for formalizing language syntax and semantics,
   built in Lean 4; dialect-based IRs, VC generation, SMT discharge.
   https://github.com/strata-org/Strata
2. Computer Weekly, *AWS bets big on Lean programming language to bring mathematical
   guarantees to agentic AI*.
   https://www.computerweekly.com/blog/CW-Developer-Network/AWS-bets-big-on-Lean-programming-language-to-bring-mathematical-guarantees-to-agentic-AI
3. *Lean Powers Secure Software at AWS: Cedar's Journey with Verified Development.*
   https://lean-lang.org/use-cases/cedar/
4. Amazon Science, *Amazon is investing in the Lean Focused Research Organization*.
   https://www.amazon.science/news/amazon-is-investing-in-the-lean-focused-research-organization
5. **CircuitProver: Agentic Lean 4 Theorem Proving with Reusable Circuit Proof Library
   for Hardware Verification** (HKUST). arXiv:2607.27259.
   https://arxiv.org/html/2607.27259
6. Zhao Huan (National University of Singapore) — agentic verification of software
   systems; agentic concolic execution.
   https://zhaohuanqdcn.github.io/
7. *A Case Study on the Effectiveness of LLMs in Verification with Proof Assistants.*
   arXiv:2508.18587. https://arxiv.org/pdf/2508.18587

Internal evidence cited: `examples/spec2rtl2/fifo/` (nine properties, zero invariants,
~2 s), the multiplier family (`wallace32`, `booth_wallace32`, `booth_production32`; one
contract, three machines, shared structural Lean lemmas), the Am2901 v2 entry (eight
properties inductive at K=1 with zero invariants over 2^68 states, all arithmetic decided
by the checker, no Lean owed), and the translator metatheory (`proofs/`, 225/225
obligations). The methodology behind each claim
is `METHODOLOGY.md` in this directory; the walkthrough of a full certificate is
`WALKTHROUGH.md`.
