# fifo — the v2 pilot-scale example (DRAFT v2, awaiting the user's read)

A synchronous FIFO, depth = the `depth` parameter (4 in this instantiation), width 8, one clock, active-low reset. Written v2-first. Revision
after the user's review: NO derived `count` in the vocabulary — ASP has no symbolic `Nat`, so a
count grounds over its whole domain and scales badly with depth. The vocabulary is the
hardware's own: **wrap-bit pointers and the `full`/`empty` flags** — every relation is an
equality or a successor over a small domain, and the queue properties become ADDRESS-LOCAL cell
relations (no rank indexing, no shift discipline).

## 1. The interface

| port | dir | width | meaning |
|---|---|---|---|
| `clk` | in | 1 | the clock |
| `reset_n` | in | 1 | active-low reset |
| `push` | in | 1 | enqueue request |
| `data_push` | in | 8 | the value to enqueue |
| `full` | out | 1 | no room: a push this cycle is refused |
| `pop` | in | 1 | dequeue request |
| `data_pop` | out | 8 | the oldest value, meaningful while `valid_pop = 1` |
| `valid_pop` | out | 1 | `data_pop` is valid (show-ahead: the head is on the output now) |
| `empty` | out | 1 | nothing stored: a pop this cycle is refused |

Handshake (the C-conventions family): a push is ACCEPTED iff `push=1 ∧ full=0`; a pop is SERVED
iff `pop=1 ∧ empty=0`. A refused request does nothing. Both may happen in the same cycle.
Port-only helper definitions: `accepted_push(T)`, `served_pop(T)`.

## 2. The linked symbols (what the ports do not expose)

| symbol | domain | meaning | linkage (written with the level) |
|---|---|---|---|
| `pointer_push(P, T)` | 0..7 | where the next accepted push lands: address = P mod 4, wrap bit = P div 4 | the design's write pointer register |
| `pointer_pop(P, T)` | 0..7 | the next value out: same encoding | the design's read pointer register |
| `cell_value(A, V, T)` | A = 0..3 | what storage cell A holds | the memory cells, directly |

Derived views, defined at every instant — no state of their own. The wrap bit is what lets the
flags be pointer RELATIONS instead of arithmetic: empty ⟺ the pointers are equal; full ⟺ they
differ exactly in the wrap bit. No subtraction, no count, anywhere.

## 3. The properties — one named `bad` per kind of wrongness

**Flags** (pointer relations, not arithmetic):
- `bad(empty_wrong, T)` — `empty` ≠ (`pointer_push = pointer_pop`).
- `bad(full_wrong, T)` — `full` ≠ (pointers equal in address, opposite in wrap bit).
- `bad(valid_wrong, T)` — `valid_pop` ≠ (`empty = 0`): the consumer handshake and the
  producer-side view are the same fact, stated once each way.

**Pointer discipline** (one-step successor relations):
- `bad(pointer_push_wrong, T+1)` — on an accepted push the write pointer advances by exactly 1
  (mod 8); otherwise it holds.
- `bad(pointer_pop_wrong, T+1)` — same for the read pointer on a served pop.
- `bad(reset_wrong, T)` — under reset (and on the release edge) both pointers are 0.

**Storage** (address-local relations — together with the pointer discipline these ARE
first-in-first-out):
- `bad(push_landed_wrong, T+1)` — on an accepted push, the cell at the write pointer's address
  holds `data_push` at T+1.
- `bad(cell_disturbed, T+1)` — any cell NOT written this cycle holds its value (retention and
  no-invention in one frame property).
- `bad(pop_value_wrong, T)` — on a served pop, `data_pop` = the cell at the read pointer's
  address.

## 4. Where first-in-first-out lives (tenet 7)

No rule anywhere asserts "values leave in arrival order." It is a THEOREM of the mechanism
properties: the pointers advance one step per event in one direction, a pushed value lands at
the write pointer's slot and stays until overwritten, and a served pop delivers the read
pointer's slot — so the read pointer traverses exactly the path the write pointer took, slot by
slot, and order follows. The induction proves those mechanism properties for all time; order is
their consequence. One honest boundary, recorded: this property set fits pointer-discipline
storage (a circular buffer); a shift-register implementation would need a different property
set. (An earlier draft also kept an event-driven referee under a scripted run as a behavioural
cross-check; the user retired scripted walks entirely — 2026-08-25 — and the referee went with
them. It is in git history if ever wanted.)

## 5. The scenarios (anti-vacuity, one cycle each)

Each scenario places the machine in a compliant interesting state (the properties assumed — the
same confinement the induction uses), applies one input, and checks the NATURAL OPERATION:

| scenario | state | input | expected |
|---|---|---|---|
| `push_when_full` | full | push | refused |
| `pop_when_full` | full | pop | served; room at T+1 |
| `push_when_empty` | empty | push | accepted; non-empty at T+1 |
| `pop_when_empty` | empty | pop | refused |
| `one_entry_pop` | one entry | pop | served; empty at T+1 |
| `push_and_pop_mid` | mid | both | both happen |
| `push_at_wrap_edge` | pointer at depth−1 | push | accepted; wrap bit set at T+1 |

Two solves each: SAT with the expectation (possible, and the natural operation happens — witness
printed); UNSAT with the expectation negated (the natural operation cannot be violated from any
compliant such state). Cost independent of depth and history — no script walks anywhere.

## 6. Deliberately not specified

`data_pop` while `valid_pop = 0` (a don't-care, cited when coverage is checked); timing beyond the
same-cycle handshake convention; the storage cell type (the linkage reads whatever cells the
level declares).

## 7. The expected induction shape (to be confirmed when the level is built)

The freed state is: two 3-bit pointers, the four 8-bit cells (as tokens — data), and the flag
outputs if registered. The confinement invariant the step is expected to request: the pointers'
wrap-distance never exceeds 4 — expressible as a small pointer relation (domain 8x8), the ring
invariant's FIFO-sized sibling. Everything grounds over domains of size 8 or 4; nothing scales
with the data width.
