# The FIFO design, and the reasoning behind it (`l1.lp`)

This file explains not just what the design is but WHY each piece is the way it is — including
the alternatives that were rejected and what rejecting them bought. Read it before `l1.lp`; the
code is then a transcription of this reasoning.

## The picture

Four numbered slots arranged in a circle. Two markers walk the circle, always clockwise, one
slot at a time:

- the **write marker** stands on the slot the next pushed value will drop into;
- the **read marker** stands on the slot holding the oldest value — the one a pop takes.

A push drops its value into the write marker's slot and moves that marker one step. A pop takes
the read marker's slot and moves that marker one step. **Values never move.** First-in-first-out
is geometry: the read marker follows the exact path the write marker took, so values leave in
arrival order without anything ever being shifted.

## Decision 1 — a circular buffer, not a shift register

The obvious alternative: keep the oldest value always in slot 0 and shift everything forward on
each pop. Rejected for three reasons that reinforce each other. In hardware, shifting moves
every stored value every pop — four times the switching for no function. In the spec, our
retention property says "a slot nobody wrote keeps its value" — TRUE of a circular buffer,
FALSE of a shift register, so the property set and this structure agree sentence for sentence.
And for the prover, "values never move" means the storage claims are LOCAL — each slot's story
involves only that slot and one marker — which is what keeps every check small.

## Decision 2 — the lap bit, not a count

If both markers stand on the same slot, are we empty or full? Position alone cannot say — both
happen. The textbook fixes are (a) keep a count of stored values, or (b) give each marker one
extra bit: WHICH LAP of the circle it is on. We chose the lap bit, twice over:

- **The user's correction, which reshaped the whole spec:** a count is a number, and the
  checker has no symbolic arithmetic — every numeric claim is checked by trying values, so
  counts get expensive exactly when the FIFO gets deep. The lap bit replaces arithmetic with
  two comparisons: same slot + same lap = empty; same slot + different lap = full.
- **Hardware agrees:** maintaining a counter that stays coherent with two independent events
  (push and pop, possibly simultaneous) is a classic source of off-by-one bugs; comparing two
  registers is cheaper and cannot drift.

That is why the pointers are 3 bits for 4 slots: two bits say which slot, one says which lap.

## Decision 3 — markers move only on their event (enable-gated registers)

Each marker register has an enable: it loads `pointer + 1` exactly when its event (an accepted
push / a served pop) happens, and holds otherwise. This is not just tidy hardware — it makes
the design and the spec THE SAME SENTENCES. The spec's pointer property reads "on the event,
advance by exactly one; otherwise hold." The register's wiring reads identically. When the
proof later checks that property, it is checking a transcription, not a derivation — the fewer
inferential steps between spec and circuit, the less room for both to be wrong in compensating
ways.

## Decision 4 — acceptance is gated on reset

`push_accepted = reset_n AND push AND not full`. The obvious half: during reset the machine
must do nothing, and the spec's vocabulary (`accepted_push` requires the machine to be live)
should coincide with the design's — same words, same meaning.

The subtle half is the real reason: **the storage array has no reset pin** (decision 5), and a
write port does not know about reset unless something tells it. Without this gate, a `push=1`
during the reset cycle would write a cell on the reset edge. The pointer registers are safe
regardless — the register library refuses to load across a reset edge (a lesson version 1 paid
for in a family of silent bugs) — but the array's write enable is ours to guard, and this gate
is the guard.

## Decision 5 — the storage is not reset

Resetting the four cells would buy nothing: `empty` already says "nothing here is meaningful,"
cells only acquire meaning when a push writes them, and the spec explicitly leaves `data_pop`
unconstrained while `valid_pop = 0` (a cited don't-care). Real hardware agrees — memory arrays
are rarely resettable, and demanding reset here would rule out real implementations. In
checked runs the cells start at zero (a testing convention, supplied by a companion file, not a
claim about the design); in the proof they start free, which is stronger.

## Decision 6 — the oldest value is always on the output ("show-ahead")

`data_pop` continuously shows the read marker's slot; a pop does not FETCH the value — it was
already showing — the pop just moves the marker. The alternative (register the output, deliver
one cycle after the pop) adds a register, a cycle of latency, and a second timing convention to
specify. Show-ahead keeps the same-cycle handshake the spec already defines, and `valid_pop`
falls out as literally "not empty."

## How the design meets the spec — the linkage (`l1.inv.lp`)

Three lines: the spec's `pointer_push` window IS this design's `write_pointer` register;
`pointer_pop` IS `read_pointer`; `cell_value(A)` IS slot A. That is the entire adapter. A
different implementation of the same spec — different register names, a different internal
scheme — would rewrite these three lines and nothing else. The spec never learned this
design's names; this file is where the two vocabularies are bolted together.

## What we expect the proof to say, and why

The prediction, written down before the run so it can be wrong in public: **inductive at
window 1 with zero extra invariants.** The reasoning: every property is a local, one-step
relation — flags versus pointers, pointer advance, slot land-and-hold — and NONE of them
mentions how many values are stored. Proofs usually need extra invariants to fence off
impossible states ("the count can never be 5") because some property silently depends on the
fence. Here there is nothing to fence: even a marker configuration that normal operation could
never produce satisfies or violates each property on its own terms. If the prediction is
wrong, the failed check will name the state it needs fenced, and that request — not a guess —
is what an invariant would be written from.
