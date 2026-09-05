# The v2 linkage lint — what it does, and why

## Part 1 — in plain words

### The problem it guards against

When we prove a property "for all time," the proof works by induction: assume the machine is in
*some* state where everything has been fine so far, and show one more clock cycle cannot break
anything. That argument is cheap and simple when the only state that exists is the design's own
flip-flops and memory cells — the tool lets those take any value, assumes the properties held,
and checks one step.

It stops being cheap the moment the *specification* carries state of its own. In version 1 our
specs did this constantly: to say "the value that comes out must be the value that went in," the
spec kept its own little notebook — a bookkeeping machine that watched the ports and wrote down
what happened. That notebook is extra state. The proof then has to ask: what could the notebook
say at the start of the induction window? Could it disagree with the design? Is every notebook
state the checker imagines actually possible? Answering those questions is what made version-1
proofs slow — on the out-of-order core, one such question ran fifteen minutes without finishing.

Version 2's answer: **the spec is not allowed to keep a notebook.** Anything the spec wants to
talk about must either be a port, or a *window* into the design — a symbol defined, at every
moment, as "whatever this register holds right now." A window has no memory of its own, so the
induction has nothing extra to manage. The lint is the guard at the door: it reads your spec
and tells you, before anything runs, whether you accidentally wrote a notebook.

### How to tell a window from a notebook

Read any rule and ask: **does tomorrow's value depend on today's?**

- *"The write pointer symbol IS whatever the write-pointer register holds right now."* — that's
  a **window**. If you deleted it and re-added it, nothing would be lost; it carries no memory.
- *"When a push happens, remember the pushed value."* — that's a **notebook**. It has memory:
  its value tomorrow depends on what it saw today. Delete it and history is gone.

That's the entire distinction the lint draws, mechanically, from your rules.

### The one place a notebook is still allowed

Sometimes you *want* an independent set of books — a referee that tracks what should happen
purely by watching the ports, never looking inside the design. That's genuinely valuable during
**testing**: run a script, and if the design and the referee ever disagree, one of them is
wrong. But the referee must never enter the induction (that's the expensive part), so v2 makes
the split explicit: every rule of the referee is labeled `refmodel` ("reference model"). Think
of it as equipment allowed on the test bench but not in the cleanroom. The lint checks the
label is on **every** rule of the referee — a notebook with even one unlabeled page is refused,
because the tool can no longer promise it stays out of the proof.

### What the tool then tells you, honestly

A property that compares the design against the referee can only be checked while the referee
exists — during testing. The tool will not quietly claim it proved such a property forever; it
lists it as **BOUNDED-ONLY**: "checked in every test run, not part of the for-all-time proof."
You get the strongest true statement, never a stronger-sounding false one.

### What to do when the lint refuses your spec

The message names the offending symbols and offers the only two honest options:

1. **Turn the notebook into a window.** Usually the design already remembers the thing you were
   tracking — a pointer register, a memory cell. Define your symbol as a view of that, "right
   now," and the state you were duplicating disappears. (This is almost always the right fix,
   and it usually *simplifies* the spec.)
2. **Make it part of the referee.** If the symbol really must be independent bookkeeping, label
   every one of its rules `refmodel` and accept that properties reading it are test-time
   checks, not proofs.

### Why the FIFO spec passes

Its pointer and cell symbols are windows ("the write pointer IS this register, now"). Its
correctness rules are one-step statements over those windows ("on an accepted push the pointer
advances by exactly one; a cell nobody wrote still holds its value"). Its referee — an
event-driven queue that watches pushes and pops — is fully labeled `refmodel`, so its one
comparison rule is reported bounded-only. Nothing else remembers anything, so the induction
frees exactly the design's registers and nothing more.

---

## Part 2 — the mechanics (for the implementer)

Implementation: `ghost_gating` and `props_reading` in `src/sv2asp/aspfirst2/induct.py`, called
from the spec-scale block of `src/sv2asp/aspfirst2/refine.py`.

**State detection.** The file is parsed with clingo's AST (no regex). A predicate is state iff
some rule defines it at a later instant than that rule's body: head `p(..., T+c)` with a body
literal at `T` (or head at `T`, body at `T-c`). Heads at the body's own instant are
definitions. The monitor vocabulary (`bad`, `goal`, `viol`, `assume`) is excluded — a `bad` at
`T+1` over a body at `T` is a one-step property, not state. This is v1's freeing detector,
repurposed as a refusal gate.

**Gating.** Every rule whose head is a state predicate must carry a positive literal exactly
`refmodel`. Per-rule and literal, deliberately — both of these are refused:

```prolog
g(V, T+1) :- refmodel, val(a, V, T).
g(V, T+1) :- g(V, T), val(b, 1, T).        % the hold rule forgot the label -> refused

h(T)      :- refmodel, val(a, 1, T).
g(V, T+1) :- h(T), val(a, V, T).           % inert in practice, but not verifiable by reading
                                           % this one rule alone -> refused
```

Conservative refusal beats silent acceptance: with the literal rule, any single rule can be
checked in isolation. Witness: `test_v2_gating_is_per_rule_and_literal`.

**The refusal message** names the predicates and the two fixes:

> `induct: <file> defines spec-side ghost STATE outside refmodel: <names>. v2 has no spec-side
> ghost machinery -- LINK each symbol to the design's flops/memories (a derived view, defined
> at every instant), or gate every rule of an independent reference model with a literal
> refmodel (bounded legs only). METHODOLOGY tenets 2 and 4.`

**BOUNDED-ONLY classification.** Gated predicates are inert in the step (`refmodel` is absent
there), so any `bad`/`viol` whose body reads one is excluded from the step's asks and reported
by name — else it would be listed as vacuously "inductive." Known limitation, stated: the
classification reads one level of direct body references; a monitor reaching the referee
through an ungated same-instant helper is not classified. Until the reachability closure lands
(owed, with a sabotage test), the discipline is: monitors read gated predicates directly. Since 2026-09-05 the bounded legs -- the base, the scenarios, the delivery
obligation -- ASSERT the fact `refmodel.`, so a gated rule is live exactly there; before that
no leg asserted it and a gated rule was inert everywhere, which is the reason a gated
`model` obligation was always reported UNREACHABLE (a field report's probe).

**Where it runs.** `refine`'s spec-scale path, per monitor file (the spec and each level's
`.inv`). It does not run for `contract <m>.lp` (`unit_scale=True`): a unit contract's
event-captured job ghost is the sanctioned exception — at unit scale the v1 machinery proves in
seconds, and composition never carries it into a step.

**Checking a file by hand:**

```bash
PYTHONPATH=src python3 - <<'PY'
from sv2asp.aspfirst2.induct import ghost_gating
g = ghost_gating(open("examples/spec2rtl2/fifo/spec.lp").read())
for name, (arity, gated) in sorted(g.items()):
    print(f"{name}/{arity}:", "gated" if gated else "UNGATED -> the lint refuses")
PY
```

An empty result means the file carries no state at all — the am2901 shape, the fastest kind.
