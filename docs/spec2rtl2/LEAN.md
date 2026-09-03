# The Lean side — what is proven in Lean, how ASP hands a question over, and where everything lives

This is the central reference for every piece of Lean in this repository: why a second
prover exists at all, the exact mechanism by which an ASP certificate hands an arithmetic
question to Lean, the function and primitive vocabulary both sides share, and an
inventory of every Lean development — what it defines, what its main theorems say, and
how to build it. It is the Lean counterpart of `TOOL.md` (which documents the Python).

Written 2026-08-27. Counts are as of that date; the build gates named in §9 are what
keep them honest.

---

## 1. Why a second prover exists

The route's division of labor is stated in `METHODOLOGY.md` §5.4 and defended against
the prover-only alternatives in `POSITIONING.md`; one paragraph of it is enough here.

clingo decides questions about **finite control** exhaustively: an induction step over a
handful of registers is a finite search, and "no violating window exists" is a decision,
not an argument. What clingo cannot do is quantify over **all values of a wide
datapath** — a 32-bit multiplier input is not a thing you enumerate inside a grounder.
Lean is the opposite: quantifying over every `BitVec 32` is its native habitat, but
every step of a proof must be argued. So the route sends each question to the engine
that decides it: control, scheduling, handshakes, state machines → clingo; *the value
delivered on a data output equals the value promised* → Lean, exactly when that question
survives the checker.

**The rule for when Lean is owed** (METHODOLOGY §5.4): a delivery obligation whose two
sides are both *numbers* is decided by the checker on the spot — equal is discharged,
different is a violation. Lean is owed precisely when an obligation's sides are still
**terms** — symbolic expressions over the data inputs — that differ *as symbols*. An
entry whose whole behavior is enumerable never produces such a residue: the Am2901's 512
microinstructions are checked outright and its certificate carries **no Lean at all**,
by rule rather than by omission.

---

## 2. The map — every Lean body in the repository

Entry rows are relative to `examples/spec2rtl2/`.

| where | question it answers | size | notes |
|:----------------------|:---------------------------|:-------------|:-------------------|
| `proofs/lean` (`GroundTruthProofs`) | is the **translator's emitted schema** correct? (M1–M4, Fages, 14 derived Stage-C tables) | ~680 top-level theorems, 60+ files | core-only Lean 4; zero `sorry`; axioms `{propext, Classical.choice, Quot.sound}`; never `native_decide`; the 225/225 obligation ledger. Read `proofs/README.md`. |
| `lib/lean` (`RouteLean`) | the route's **central Lean library** — the multiplier development shared by the entries (`RouteLean.Mul`: the compressor/reduction spine; `RouteLean.Booth`: the abstract radix-4 half through `booth_rows_sum`) | `Mul`: 4 theorems, 4 defs; `Booth`: 24 theorems, 10 defs | core-only; entry projects `require` it by relative path; the Lean twin of `lib/aspfirst` |
| `wallace32/` `lean/Wallace.lean` | the Wallace tree delivers `a * b` at 64 bits, for **any** number of reduction layers | 6 theorems, 3 defs (+ the library) | §8.1 |
| `booth_wallace32/` `lean/BoothWallace.lean` | the radix-4 Booth recoding's 17 rows sum to the same product | 4 theorems (+ the library) | §8.2 |
| `booth_production32/` `lean/BoothProduction.lean` | invert-plus-one-correction-row equals true negation — no carry chains interfere | 19 theorems, 7 defs (+ the library) | §8.3 |
| `booth/lean/` (`Booth4`) | the sequential Booth datapath's **exported obligation**, plus the refuted first attempt | 2 content files + lakefile | the worked export example, §4 |

Scope note: this document covers the **current v2 route** only. Lean that belongs to
other routes or eras — the rtl2asp goldschmidt case study
(`examples/rtl2asp/goldschmidt_divider/lean/`, documented by its own `README.md` and
`PENCIL_PROOF.md`) and the archived v1 developments (`archive/spec2rtl_v1/…`, consult
through the `v1` branch) — is deliberately not catalogued here. `proofs/lean` *is* in
scope: it is not legacy but the live trust root the v2 export states its theorems over.

Three different *kinds* of Lean live in that table, and keeping them apart is most of
the orientation:

1. **The metatheory** (`proofs/lean`): proofs *about the translator* — that the rule
   schemas it emits mean what the specification says, once and for all designs. You
   never touch this per entry.
2. **Entry developments** (the multiplier family): proofs *about one design's
   arithmetic* — hand-written; the entries share their common halves through the
   central library and keep only what is their own.
3. **Exported obligations** (`Booth4/Exported.lean`): machine-generated statements that
   carry an ASP certificate's *owed residue* into Lean. §§3–4 explain this mechanism,
   because it is the load-bearing joint between the two provers.

---

## 3. The handover, part one — how an obligation arises in a certificate

Start with the concrete example. The Booth entry's specification promises: *at the due
cycle, the product output equals the sign-extended product of the operands*. Under the
**symbolic reading**, the datapath's nets do not carry numbers — each carries a **term**,
a symbolic expression built from the input tokens (`in(a,T)`, `in(b,T)`) by the same
operators the design applies (`add`, `ashr`, `slc`, …). By the due cycle the product net
holds one closed term: the exact expression tree the hardware computed. The spec, on its
side, builds the term it promised. Now two expressions must be compared.

The contract does not compare them itself. It states an **obligation**:

```
obl(Tag, Have, Want, T)     % "at instant T, the value Have must equal Want"
```

and the runner (`refine.py`) supplies the comparison policy — three rules, quoted:

```
obl_viol(Tag, T) :- obl(Tag, H, W, T), H != W, @issym(H) = 0, @issym(W) = 0.
obl_owed(Tag, T) :- obl(Tag, H, W, T), H != W, @issym(H) = 1.
obl_owed(Tag, T) :- obl(Tag, H, W, T), H != W, @issym(W) = 1.
bad(Tag, T)      :- obl_viol(Tag, T).
```

Read them as a decision tree. Both sides concrete numbers and different → a
**violation**, a `bad`, the run fails. Both sides the *same* symbol or the same number →
discharged by identity, nothing to do. Either side still symbolic and the two differ
*as symbols* → **`obl_owed`**: the question is genuinely arithmetic, a grounder cannot
decide it, and the report says so — *owed to Lean*, reported, never silently passed and
never failed. This is the route's honesty mechanism for data: the certificate is green
only together with its owed list, and the owed list is what Lean must close.

Two further forms feed the same protocol:

- **The `model` form.** A previous level may have *modeled* an output abstractly
  (`p_model(N, V, T)`: "net N will carry V"). Once the current level actually builds
  the net, the model stops being a definition and becomes a claim about the built
  value — the runner turns it into an obligation automatically:
  `obl(model(N), V2, V, T) :- p_model(N, V, T), val(N, V2, T).` (and likewise
  `cmodel` for a concrete child's contract model).
- **Boundaries.** A control decision computed *from* data (`boundary(P, W)` — "is the
  divisor zero?") is evaluated outright when its arguments are concrete (`pval`), and
  freed to one value per distinct term when they are symbolic — so control proofs
  quantify over the boundary's outcomes without ever enumerating data.

---

## 4. The handover, part two — the export turns an owed obligation into a theorem

```
python -m sv2asp.aspfirst2 export SPEC SCENARIO LEVEL -o FILE.lean
```

**Why a scenario is required.** Under free control, an iterative datapath's term family
explodes: every possible schedule writes a different history into the registers, and the
set of terms a net can hold is the cross-product of those histories (the Booth lesson,
`LEARNINGS.md`). Under one **pinned scenario** — a single job from reset — every net
holds exactly one term per instant, and the obligation is one closed expression. The
exported theorem therefore states the obligation *for the schedule the scenario
exhibits*. That the datapath's answer does not depend on what came before (it is
reloaded on every accept) is a **control** fact, proven in ASP by the induction — the
file's generated header says exactly this, so the theorem cannot be over-read.

**What the exporter does**, step by step:

1. Solves the level under the scenario in the symbolic reading (`#show obl/4`) — the
   run must be SATISFIABLE (a scenario is one legal run, or there is nothing to export).
2. Drops every obligation whose two sides are already the identical term ("discharged
   by identity").
3. Collects each remaining pair's **input tokens** and turns them into universally
   quantified variables — one `Nat` variable per port (suffixed `name_T` if the term
   spans several instants of the same port), each bounded by its port width.
4. Renders both terms as Lean — **hash-consed**: every distinct compound subterm
   becomes one `let` binding, so the rendering is linear in the DAG where the raw tree
   can be exponential. (This is a paid-for lesson: an unrolled Booth term was 66 KB of
   nested expression and Lean timed out elaborating it; the same term as a DAG is 55
   shared subterms.)
5. Emits, per obligation, a `_have` definition (what the datapath computed), a `_want`
   definition (what the spec promised), and the theorem in **bounded-forall** shape:

   ```lean
   theorem product : ∀ a, a < 2 ^ 4 → ∀ b, b < 2 ^ 4 →
       product_have a b = product_want a b := by
     decide
   ```

   The tactic is chosen by size: **`decide`** when the quantified inputs total ≤ 16
   bits — that shape is exactly what `Nat.decidableBallLT` makes kernel-decidable, an
   exhaustive check *inside the proof kernel* (not `native_decide`; no trusted
   compiler). Wider than 16 bits, the exporter writes a loud `sorry` placeholder with
   the advice to prove by `bv_decide` over `BitVec` or by hand — **the file does not
   build until someone does**, so an unproven obligation can never look proven.

**The operator dictionary.** Terms are rendered over the function models of
`proofs/lean` (§5) via a fixed table: `add→fAdd, sub→fSub, mul→fMul, idiv→fIdiv,
imod→fImod, sidiv→fSidiv, simod→fSimod, band→fAnd, bor→fOr, bxor→fXor, shl→fShl,
shr→fShr, ashr→fAshr, ipow→fPow, bnot→fNot, neg→fNeg, sext→fSext, slc→fSlc,
parity→fParity, popcnt→fPopcnt, rand→fRand, ror→fRor, rxor→fRxor, rnand→fRnand,
rnor→fRnor, rxnor→fRxnor, wcmp→fWcmp`. The boolean-flavored ops (`ite`, `logand`,
`logor`, `lnot`, `eq`, `ne`, `lt`, `le`, `gt`, `ge`) are rendered as `if … then 1 else
0` expressions directly. An op with no Lean image is **refused by name** at export —
never dropped. (`clz` is the one named case; see §10 for a wrinkle in its message.)

**The worked artifact** is the Booth entry's `lean/Booth4/`:

- `Exported.lean` — generated (by the v1-era exporter; the v2 command emits the same
  shape): `product_have` as a 55-binding DAG, `product_want` as the promise
  `fMul (fSext a 4 8) (fSext b 4 8) 8`, and the theorem at 8 input bits, closed by
  `decide`.
- `Obligation.lean` — the hand-written mirror: `step` (one Booth step on the register
  triple), `pAtDue` (load, three steps, the fourth composed), `promise`, the theorem
  `product` again by `decide` — and, kept deliberately, **`product_no_guard_is_false`**:
  the entry's first, unguarded datapath attempt as a *disproved* theorem, whose
  counterexample is exactly the one clingo produced (−8 × −8 read back as 192). A
  refuted attempt preserved as a theorem is the strongest witness that the obligation
  is not vacuous.

---

## 5. Why a theorem over `Funcs` means anything — the bridge

A fair question: the exported theorem is about functions called `fAdd`, `fMul`, … —
what connects *those* to the certificate, and to hardware? The chain has four links,
each independently gated:

1. **The ASP evaluated the same functions.** Every concrete solve in the route computes
   terms with the `@func` builtins of `src/sv2asp/emit/lib.py` (`@add`, `@mul`, …) —
   the authoring library and the translator share them.
2. **`GroundTruthProofs/Funcs.lean` is a generated mirror of that Python.** It is
   emitted by `proofs/gen_funcs_lean.py`; each definition's doc comment quotes the
   Python line it mirrors, and the generator's `--check` fails the build if `lib.py`
   drifts from the frozen copy. Example of the shape:
   `def fAdd (a b w : Nat) : Nat := (a + b) % 2 ^ w`.
3. **M1 proves each mirror equals its `BitVec` operation** at every width, plus the
   `Wf` invariant that values stay masked (`0 ≤ v < 2^w`). So `fAdd` is not merely
   *like* hardware addition — it is proven to *be* `BitVec.add` under the encoding.
4. **The executed Python is pinned to the mirrors** by `Conformance.lean` (kernel
   tables of real outputs) and by the ~90k-vector `@func` differential in
   `tests/test_lean_funcs.py`, which exercises the clingo Number/String encoding layer
   underneath.

Put together: proving `product_have = product_want` over `Funcs` is proving the
datapath's arithmetic **under the very semantics the certificate used** — there is no
second, informal translation step between the two provers where meaning could shift.

The mirrors keep the Python's honest quirks rather than idealizing them, because the
bridge is to the code that runs: they are total where Python raises (so the
sign-decoding family's denotation theorems carry a `0 < w` hypothesis); `fSigned` and
`fWcmp` return `Int` (their clingo results can be negative); `fParity` ignores its
width argument exactly as the Python does; `fClz` has the Python's 64-bit window
hardwired. Each of those was a *finding* — the mirror made the quirk visible.

---

## 6. The shared vocabulary, part one — the function library

For authoring purposes the table in §4 *is* the inventory: those are the operators a
design's `def(net, expr)` terms may use with a Lean image on the other side. Three
practical groupings:

- **Word arithmetic and logic** (`fAdd fSub fMul fIdiv fImod fSidiv fSimod fAnd fOr
  fXor fShl fShr fAshr fPow fNot fNeg fSext fSlc`) — all masked to their width
  argument, all proven equal to the corresponding `BitVec` operation in M1.
- **Reductions and counts** (`fParity fPopcnt fRand fRor fRxor fRnand fRnor fRxnor`,
  plus `fClz`) — fold a word to a bit or a count; the fuel-structural helpers
  (`bitLen`, `popCountN`) are written so `decide` can evaluate them in the kernel.
- **Comparisons and selection** — rendered inline as `if`-expressions over `Nat`
  (`eq ne lt le gt ge ite logand logor lnot`), with `fWcmp` as the wide-value
  comparator returning `Int`.

If a design needs an operator outside this set, the exporter refuses by name, and the
right move is usually the one the LZC took: declare the unit **contract-only** and
prove its content separately, rather than growing the term language ad hoc.

---

## 7. The shared vocabulary, part two — the primitives

The authoring library (`lib/aspfirst/aspfirst.lp`) defines five state primitives, and
every design's state lives in instances of them:

| primitive | what it is | reset |
|---|---|---|
| `ff` | edge-triggered register with enable | none |
| `arff` | the same, with an asynchronous active-low reset forcing `reset_value` | level force + release-edge gating |
| `lata` | level-sensitive transparent-high latch | none |
| `farray` | an array of registers: one write port, any number of `mrd` readers | optional, forces every cell |
| `spram` | single-port RAM with a real port conflict to reason about | none |

Since the divided-counter entry, `ff`/`arff` also carry **derived-clock** rule
variants: a clock pin wired to a design-computed net makes the register rise-triggered
on the master axis (update exactly across the net's 0→1 transitions, positive-complement
holds elsewhere).

What Lean has to say about these is indirect but load-bearing: the primitives' rules
**mirror the translator's emitted schema literal for literal** (gated by
`test_aspfirst_lib_mirrors_emitter`), and that schema is M2's subject in `proofs/lean` —
single-valued combinational cells, exactly-one-value-per-cycle registers, the
asynchronous release edge (`Async.lean`), latch transparency (`Latch.lean`), gated
clocks (`ClockGate.lean`), memories (`Mem.lean`). So a certificate's claims about state
inherit a formally characterized semantics. The one currently **owed** piece: the
edge-derived clock's rise kind (F27) has no formal model yet — `TRANSLATION_SPEC.md`
§S1.2 records the debt in place.

---

## 8. The hand-written entry developments

The three 32-bit multipliers share one deliberately rule-identical ASP contract (the
suite enforces it three ways); their Lean developments correspondingly share a spine —
`csaS`/`csaC` (the 3:2 compressor exactly as the generator emits it), `reduce`/`reduceN`
(one layer of triples; n layers), and the two sum-preservation theorems `reduce_sum` /
`reduceN_sum` — then diverge exactly where the machines diverge: in what the *rows* are.
**The shared text lives once, in the central library `lib/lean`** (centralized
2026-08-27 at the user's direction; before that it was three byte-identical copies):
`RouteLean.Mul` holds the spine, `RouteLean.Booth` the abstract radix-4 half the two
Booth machines share, and each entry file `import`s and `open`s `RouteLean`, keeping
only what is its own.
Each file states its main theorem for **any number of reduction layers `n`**, which is
what makes the proof independent of the tree's particular shape: the certificate proves
the pipeline timing, Lean proves the tree's content, and neither mandates the other.

### 8.1 `wallace32` — `Wallace.lean` (6 theorems, 3 defs + the library spine)

The simple-partial-product machine: `pps a b` is the list of 32 rows, row *i* being
"`a` shifted by *i* if `b`'s bit *i*, else 0"; `product` is `setWidth 64 a * zeroExtend
64 b`. The development runs: `csa_sum` — one compressor preserves the sum modulo 2^64
(proven by `bv_decide` after `shl1_eq_add` converts the shifted carry into an
addition); `natSum_eq` — the numeric bridge summing rows in `Nat`; `sum_toNat` — no
overflow occurs (the whole sum fits 64 bits); `pps_sum` — the rows sum to the product;
and `wallace_correct` — after any `n` reduction layers, the surviving sum-and-carry
pair adds to the product. Axiom note: `csa_sum`'s `bv_decide` introduces
its theorem-scoped native axiom (`RouteLean.csa_sum._native.bv_decide.ax_1_5` in the
build's audit line) — the **only** native axiom in the family, inherited once through
the central library by everything that reuses the lemma, and recorded as an owed
cleanup (§10).

### 8.2 `booth_wallace32` — `BoothWallace.lean` (4 theorems + the library)

The radix-4 recoding machine: 17 encoded rows instead of 32. The heart is the
**offset-digit recoding lemma**: each Booth digit is `b[2i−1] + b[2i] − 2·b[2i+1]`
(values −2…+2), and the weighted digit sum telescopes to the multiplier's value. The
development defines the encoder **decision for decision as the generator emits it**
(`row`), proves each leaf case (`leaf_pos2`, `leaf_neg2` — the negative rows exact
modulo 2^64), lifts row equality through congruence (`row_congr`, `rowsum_congr`,
working all-`Nat` with an offset so no subtraction underflows), and lands
`booth_rows_sum` → `booth_correct`. The file also carries the **license lemma** the
production sibling relies on: `negsel_shl_eq` — negate-then-shift of a selected
multiple equals invert-then-shift plus a correction `1` at the row's weight (via
`neg_eq_not_add_one` and `shl_add_distrib`). That lemma is the formal permission slip
for the production machine's cheaper hardware.

### 8.3 `booth_production32` — `BoothProduction.lean` (19 theorems, 7 defs + the library)

The production form: negative rows are *inverted* (no 64-bit negators), and all 17
correction bits are gathered into **one extra compressor row**, `corrRow b = ((b >>> 1)
&&& 0x55555555).setWidth 64` — the mask picks exactly the even bit positions where a
correction may sit. The proof's crux is the **disjoint-bits development**: the 17
correction bits live at pairwise distinct even weights, so their sum has no carries —
formalized by `corrBit_toNat`, `corr_fold`, `div2_testBit`, `corrRow_eq` (the masked
word *equals* the sum of its bits), letting `hw_rows_sum` show the hardware's rows
(inverted rows + the correction row) sum to the ideal Booth rows, and
`booth_production_correct` close the same contract-level statement as the siblings.
The abstract half it shares with the sibling is imported from `RouteLean.Booth` rather
than restated, so the two machines provably argue from the same recoding. Its header carries the family's hardest-won mechanical lesson:
`simp` unfolding a 17-layer recursion over a *symbolic* coefficient sends the kernel
into deep recursion — the cure is one-step definitional unfolds (`have hstep : … :=
rfl`), recorded in `LEARNINGS.md` §Lean.

### 8.4 `booth` — `Booth4/` — covered in §4 (the export's worked example).


### Axiom discipline, across all of them

Every development ends with `#print axioms <main theorem>`; the expected profile is the
standard three (`propext`, `Classical.choice`, `Quot.sound`), plus the scoped
`bv_decide` axiom exactly where that tactic was used — today the single
`RouteLean.csa_sum._native.bv_decide` axiom the whole multiplier family inherits
through the central library.
`proofs/lean` itself admits no native axiom at all — its audit (`AxiomAudit.lean`, run
by the gate) is a build error on any deviation.

---

## 9. Building and checking

Entry directories are under `examples/spec2rtl2/`; every build is `lake build` run in
the project's `lean/` directory.

| what | where to build | gate |
|:-----------------|:---------------|:------------------------|
| the translator programme | `proofs/lean` | `tests/test_lean_funcs.py` (build + axiom audit + every generator drift check + the ~90k-vector differential) |
| the central library | `lib/lean` | core-only; ~2 s |
| a multiplier development | `<entry>/lean` | core-only; `require`s `lib/lean` by relative path; no mathlib |
| the Booth obligation pair | `booth/lean` | core-only; requires `proofs/lean` by relative path for `GroundTruthProofs.Funcs` |
| regenerate an export | the §4 command | the emitted file refuses to build until every theorem is closed |

The toolchain paths come from `sv2asp.toml` (`docs/guide/SV2ASP_USAGE.md`); the three
Lean-dependent tests in the route suite skip *by name* when no built Lean project is
present, and `SV2ASP_REQUIRE_LEAN=1` upgrades those skips to failures for a gating run.

---

## 10. Open items on the Lean side (as of 2026-08-27)

1. **The rise-kind formal model** (F27): the edge-derived clock's tick rule has no
   `ClockGate.gclkTick`-analogue in `proofs/lean` yet; `TRANSLATION_SPEC.md` §S1.2
   marks it owed in place.
2. **`csa_sum` without the native axiom**: the one `bv_decide` in the multiplier family
   pulls its scoped native axiom into all three developments' profiles (now through
   `RouteLean.Mul`, so it is one axiom in one place); a structural proof would clean
   the whole family to the standard three at a stroke.
3. **The exporter's `clz` message is stale**: it refuses `clz` saying `Funcs` has no
   `fClz` — `Funcs.lean` *does* define `fClz` (with the Python's 64-bit window). Either
   wire the mapping (and accept the windowed semantics) or correct the message; until
   then the refusal is right for possibly the wrong reason.
4. **The v2 exporter has no committed generated artifact and no dedicated test**: the
   Booth entry's `Exported.lean` was produced by the v1-era command (same mechanism,
   same shape); `tests/test_aspfirst2.py` does not yet exercise `export.py`. A witness
   entry plus a suite test would close this.

### `RouteLean/Claims.lean` — what the compiler's claim lowerings mean, proven faithful

The specification compiler lowers claims to `failType` monitors in three temporal schemas —
same-cycle (`|->`, and `always` as its true-antecedent case), next-cycle (`|=>`, `##1`),
and the bounded window (`##[1:N]`). This module gives each schema a denotation over
abstract traces and proves the monitor faithful to it: it fires somewhere **iff** the
denotation is violated (`now_faithful`, `next_faithful`, `window_faithful`). The window's
stamp convention rests on a proven fact (`window_silent_of_witness`: a consequent satisfied
anywhere in the window silences that window's monitor — so the stamp `t+N` is the first
instant that could know). Two countermodels carry the house sabotage rule:
`first_only_is_wrong` (a window judged at its first instant fires on a satisfied claim) and
`unguarded_next_is_wrong` (dropping the far-end live guard blames the design for an instant
the reset owns). Axioms: the standard three; the countermodels use fewer. The bridge to the
Python that runs is the Stage-5 differential (`dsl/interp.py`), which holds the generated
contract and an independent evaluator of these same meanings to identical verdicts on
random traces. Gate: `test_v2_stage6_claim_schemas_proven_in_lean`.

### `RouteLean/Rotation.lean` — why a rotating arbiter cannot starve, at every depth

The miss queue answers one waiting entry per cycle, choosing by a pointer that advances after
each answer, and its specification bounds the wait by `depth`. The certificate proves that at
the depth it runs; this file supplies the half a grounder cannot, because **clingo grounds** —
`depth` must be a number before anything reasons about it, so a fact about all depths is not a
hard problem for the solver but one it cannot be given.

| theorem | what it says |
|---|---|
| `after_succ` | one answer moves the pointer on by one — ties the model to the design's own update, so the lemma is about the arbiter that exists |
| `reaches` | for any position, the pointer arrives within `n` answers, for every `n` |

Axioms: `propext`, `Quot.sound`. No `sorry`. Tightness is deliberately not proven and the file
says so. Same split as `Cam.lean`: an arithmetic truth proven once for all parameters here,
borrowed by the control layer in ASP. The reasoning is methodology Chapter 34.
