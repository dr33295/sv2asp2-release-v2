# rvMissq — instruction-fetch miss queue specification

This block sits between an instruction cache's miss path and memory. When a fetch misses,
the cache records the miss here and carries on; this block asks memory for the line, and
when the line comes back it hands it to whoever was waiting. Without it, a fetch miss
would stall the front end until memory answered.

Two kinds of miss arrive here, and nearly every rule below depends on which:

- A **demand** miss is a line the fetch pipe needs *now* — the front end is waiting on it.
- A **prefetch** miss is speculative: some predictor believes the line will be wanted
  soon. Nobody is waiting, and if it never arrives, nothing breaks.

Demand misses therefore win the memory port, get their data handed back, and are
protected against being crowded out. Prefetch misses take what is left over.

This document is plain English and stands on its own. It says nothing about how the block
is built — no storage structures, comparators, or arbiters appear, because none of that
is needed to say what the block must do.

---

## 1. Vocabulary

A **request** is one miss offered to the block, carrying a line address, a destination
tag, and a class (demand or prefetch).

An **entry** is what the queue holds — and an entry is **a line being fetched, not a
request**. This is the decision everything else follows from. An entry has an address, a
class of its own, and, while its class is demand, the destination tag of the one request
waiting on it. `depth` counts entries, so it counts *distinct lines in flight*.

A **fetch** is one enquiry to memory for one line. A **fill** is memory's answer. A
**forward** is this block handing a line's data back to the fetch pipe, which happens for
demand requests only.

A request **merges** when the line it wants already has an entry: no new entry is taken
and no second enquiry is made. What merging *does* depends on the two classes:

- a **demand** merging into a **prefetch** entry **lifts** it — the entry becomes demand
  and takes the demand's destination tag;
- a **prefetch** merging into a **demand** entry changes nothing: the entry stays demand,
  and the prefetch is simply satisfied by the fetch already under way;
- a **prefetch** merging into a **prefetch** entry changes nothing;
- a **demand** meeting a **demand** entry is the one case that does not merge. The entry
  already holds a demand tag and has nowhere to put a second, so the fetch pipe is
  stalled instead (D7).

An entry's class can also change on its own: a **redirect** downgrades every demand entry
to prefetch.

---

## 2. What the block does

**Accept.** A request is taken in while the queue has room for its class (§4, P6).

**Fetch each line once.** The first request for a line starts a fetch. A later request
for the same line, arriving while that fetch is still in flight, joins it.

**Choose what to ask memory for.** At most `maxOutstandingFetches` fetches may be in
flight at once. When more entries want fetching than that allows, **demand goes first**.

**Catch the fill.** When memory returns a line, every request joined to that fetch has
its data.

**Forward, for demand only.** A demand request whose data has arrived is handed back to
the fetch pipe with its own destination tag. A prefetch request's data goes to the cache;
nobody is waiting for it, so nothing is handed back and the entry simply ends.

**Reclassify.** A redirect turns every demand entry into a prefetch — the fetch pipe has
changed direction and is no longer waiting. A demand request for a line already held as a
prefetch lifts that entry to demand instead of taking a new one.

**Stall the fetch pipe** when a demand miss arrives for a line that is already the
subject of an outstanding *demand* miss.

---

## 3. Interface

One clock; every signal is sampled on its rising edge. One reset, `resetN`, active low.

Two handshake conventions are used:

- **ready/valid** — the sender asserts `valid`, the receiver asserts `ready`, the
  transfer happens on a cycle where both are asserted, and the sender must hold the
  request until it does.
- **valid only** — the sender asserts `valid` and the receiver always takes it; there is
  no way to refuse.

| signal | direction | width | meaning |
|---|---|---|---|
| `clk` | in | 1 | the clock |
| `resetN` | in | 1 | reset, active low |
| `requestValid` | in | 1 | a miss is presented |
| `requestReady` | out | 1 | the block can take it this cycle |
| `requestAddress` | in | `addressWidth` | the line address of the miss |
| `requestTag` | in | `tagWidth` | destination tag, opaque to this block |
| `requestIsDemand` | in | 1 | 1 = demand miss, 0 = prefetch |
| `redirectValid` | in | 1 | the fetch pipe has changed direction |
| `fetchStall` | out | 1 | the fetch pipe must not present a new demand miss |
| `memoryRequestValid` | out | 1 | the block is asking memory for a line |
| `memoryRequestReady` | in | 1 | memory takes the enquiry this cycle |
| `memoryRequestAddress` | out | `addressWidth` | the line being asked for |
| `fillValid` | in | 1 | memory is returning a line |
| `fillAddress` | in | `addressWidth` | which line |
| `fillData` | in | `dataWidth` | the line's contents |
| `forwardValid` | out | 1 | a demand request is being answered |
| `forwardTag` | out | `tagWidth` | the destination tag of the request being answered |
| `forwardData` | out | `dataWidth` | that request's line data |

Address, tag, and line data are **opaque**: the block compares addresses to each other
for equality and copies tags and data through unchanged, and does nothing else with any
of them.

**Parameters.**

| parameter | default | meaning |
|---|---|---|
| `depth` | 8 | entries the queue holds |
| `maxOutstandingFetches` | 4 | fetches that may be in flight at memory at once |
| `demandReserve` | 1 | entries kept free for demand misses |
| `addressWidth` | 26 | line address (32-bit physical address, 64-byte lines) |
| `dataWidth` | 128 | a cache line as delivered |
| `tagWidth` | 4 | destination tag |

---

## 4. What the block promises

**P1 — No demand miss is lost.** Every accepted demand request is eventually forwarded,
unless it is downgraded first (P11).

**P2 — Nothing is forwarded twice.** No request is forwarded more than once.

**P3 — Every forward is real.** Each forward answers exactly one request that was
accepted earlier, was demand at the moment its data arrived, and has not been answered.

**P4 — Every forward is correct.** A forward carries the destination tag of the request
it answers and the data of the line that request asked for — exactly what memory
returned, unchanged.

**P5 — One fetch per line.** While a line's fetch is in flight, the block does not ask
memory for that line again. Requests arriving for that line join the fetch under way.

**P6 — The block does not overfill, and demand always has room.** No request is accepted
when the queue is full. A **prefetch** is accepted only while more than `demandReserve`
entries are free; a **demand** may take any free entry. Prefetches therefore cannot crowd
demand out of the queue.

**P7 — Demand goes first.** Whenever the block asks memory for a line, and some entry
wanting a fetch is demand, the line it asks for belongs to a demand entry. Prefetch lines
are fetched only when no demand entry is waiting to be fetched.

**P8 — The fetch limit is respected.** At no time are more than `maxOutstandingFetches`
fetches in flight — taken by memory and not yet filled. Joining an existing fetch does
not count against this, because it causes no enquiry.

**P9 — The block keeps asking, and keeps forwarding.** While an entry wants a fetch and
the fetch limit allows one, the block is asking memory. While any demand entry's data has
arrived and has not been forwarded, the block is forwarding.

**P10 — A second demand for the same line stalls the fetch pipe.** While a demand request
is presented for a line that already has an outstanding demand entry, `fetchStall` is
asserted and the request is not accepted. The stall lasts until the earlier entry has
been forwarded.

**P11 — A redirect downgrades every demand entry.** When a redirect arrives, every
outstanding demand entry becomes a prefetch. It keeps its place and its fetch, but it is
no longer forwarded when its data arrives, and it no longer has priority.

**P12 — A demand for a prefetched line lifts that entry.** When a demand request arrives
for a line already being prefetched, **no new entry is taken and no second enquiry is
made**: the existing entry becomes demand and takes the request's destination tag. It
thereby gains priority for the memory port, and it is forwarded when the data arrives.
A prefetch arriving for a line already demanded is the mirror image and changes nothing:
the entry stays demand, and the prefetch is satisfied by the fetch already under way.

**P13 — Prefetch entries end quietly.** When a prefetch entry's data arrives, nothing is
forwarded and the entry ends. (Writing the line into the cache is the cache's business,
not this block's.)

**P14 — The block is quiet under reset.** While `resetN` is low, the block asks memory
for nothing, forwards nothing, and does not stall the fetch pipe.

**P14b — A newcomer may join a line whose fill is arriving this very cycle.** An entry is
still joinable during the cycle its fill lands, so a demand arriving at that instant lifts the
entry and is answered from the fill that is already on its way. This is deliberate, and it is
a consequence of an entry being a *line* rather than a request: a newcomer meeting a landing
line is simply an early hit, and making it start a fresh episode would fetch the same line
twice for no reason. (An earlier, request-shaped version of this block excluded the landing
cycle for exactly the opposite reason — there, an entry belonged to one request, so a
newcomer could not be folded into it.)

**P14c — An enquiry to memory is an offer, and the offer may be re-prioritised.** While
`memoryRequestValid` is high and memory has not taken the enquiry, the address presented may
change — specifically, a demand miss arriving during a stall displaces a prefetch enquiry.
This is a deliberate departure from the usual ready/valid convention, in which a payload is
held stable once valid is asserted, and it is recorded in the signature as well. The reason
is that demand-before-prefetch is the whole point of the two classes: without this, a demand
would wait for however long memory happened to stall a prefetch it had not yet accepted. The
obligation it places on the integrator is to sample the address **on the handshake, not on
valid**.

**P14d — A demand waiting on a returned line is answered in rotation.** When several filled
demanding entries exist, exactly one is answered per cycle, and the choice rotates rather than
favouring any fixed entry. Rotation is *required*, not merely permitted, and the requirement
exists to make P-forward's bound true at any depth: with a fixed order, a repeatedly recycled
low-priority entry can overtake a waiting high-priority one indefinitely — a freed entry can
be re-allocated, fetched and refilled in about three cycles, while answering drains one per
cycle. The specification does not say *which* rotation; a pointer that advances after each
answer is the obvious one.

**P15 — Reset empties the queue.** While `resetN` is low the queue holds no entries at
all, and none is in flight. From the first cycle after reset releases the block starts
from empty: nothing carried over, no line half-fetched, no tag owed an answer.

This was missing from the first version of this specification and was found by writing the
contract, which could not be written without knowing it. It is stated rather than left to
the implementer because the alternative reading — that entries survive reset — makes the
block unusable after a redirect-and-reset, and because a fill arriving for a line the queue
no longer remembers would violate the environment's own assumption (A1).

---

## 5. What is assumed of the world

These are obligations on whoever integrates the block. A system that breaks one gets no
guarantee from anything above.

**P16 — One entry per line.** Two joinable entries never hold the same line address. This
is the fact that makes merging meaningful — a request can *join the line* only if the line
has one home — and the traceability gate found it stated nowhere in this document while the
checkable specification relied on it throughout. A promise the machine checks deserves a
sentence a person can point to.

**P17 — An entry is in exactly one phase.** A live entry is waiting to fetch, or waiting
for its fill, or holding its line — never two of these at once. The phases are the
vocabulary's own meanings made mutually exclusive; stating it here closes the loop the
compiled certificate's history demanded (the clause once entered the checkable spec under a
false justification, and its true one is this sentence).

**A1 — Fills answer fetches.** A fill arrives only for a line whose fetch this block made
and memory accepted, and which has not yet been answered. Memory does not fill twice for
one fetch, and does not fill lines nobody asked for.

**A2 — Memory eventually answers.** Memory eventually takes an enquiry the block is
making, and eventually returns a line for an enquiry it took. No bound is assumed on
either.

**A3 — Outstanding demand tags are distinct.** Two demand requests outstanding at the
same time carry different destination tags. Without this, neither the fetch pipe nor any
proof could tell which request a forward answers.

**A4 — A request is held until taken.** Once `requestValid` is asserted, the requester
holds the request unchanged until the block accepts it.

**A5 — WITHDRAWN (2026-08-31).** This assumption — the fetch pipe honours the stall — was
found to have no correct reading when the contract was built. Read same-cycle, it excludes
the very situation the stall exists for, since `fetchStall` is this block's combinational
answer to a repeat demand; read next-cycle, it contradicts A4, because a repeat demand is
not accepted and so must stay presented while the stall says it must go away. The queue
never needed it: `requestReady` is low for a repeat demand, so the queue is protected
whatever the pipe does, and `fetchStall` is advice to the pipe upstream, not a promise this
block leans on. The original text follows for the record. While `fetchStall` is asserted, the fetch pipe
does not present a new demand miss. (It may continue to present prefetches.)

---

## 6. Decisions taken

Each of these resolves a point the plain description left open. The alternative is given
where one is genuinely defensible, so overturning any of them is cheap.

**D1 — Queue depth and fetch limit are two different numbers.** `depth` bounds entries
held; `maxOutstandingFetches` bounds enquiries in flight at memory. They are independent
because merging means several entries can share one enquiry. *Alternative:* a single
number, which would waste queue capacity whenever merging occurs.

**D2 — Priority is by class only.** Demand beats prefetch for the memory port; among two
demand entries, or two prefetch entries, the choice is unspecified. *Alternative:*
oldest-first within a class, which would be a stronger promise than anything outside the
block can observe.

**D3 — A redirect downgrades every outstanding demand entry.** The block serves a single
fetch stream, so a change of direction invalidates all of them. *Alternative:* if the
redirect carried an age or a tag, only entries younger than it would be downgraded — a
sharper rule that needs a wider redirect interface.

**D4 — A downgraded entry keeps its place and its fetch.** An enquiry already made cannot
be recalled, and the line is likely still useful, so the entry stays as a prefetch: it
loses priority and its forward, not its slot. *Alternative:* drop it outright, freeing the
entry sooner but wasting the fetch already in flight.

**D5 — The reservation is headroom for allocation, not a dedicated place.** A prefetch
*allocates* only while more than `demandReserve` entries are free; a demand may take the
last one. Nothing reserves a particular entry, and nothing needs to: when a demand **lifts**
a prefetch entry (P12) it consumes no free entry at all, so a lifted entry neither needs
nor occupies "the reserved one". *Alternative:* physically dedicating an entry to demand,
which is the same guarantee with less flexibility and a harder invariant.

**D6 — An entry is a LINE, not a request, and lifting is what merging does.** This is the
decision the whole specification turns on, and it took two wrong drafts to reach. The first
said a demand arriving for a prefetched line converts that entry and takes no new entry;
the second "corrected" it to say the demand takes its own entry and the *line* becomes
urgent. Both mis-modelled the queue. An entry is a line, it carries at most one demand
tag, and a demand merging into a prefetch entry **lifts** it — acquiring the tag, the
priority, and the forward — while taking no entry and making no second enquiry. The
mirror cases follow immediately: prefetch-into-demand changes nothing, and demand-into-
demand has nowhere to put a second tag, which is exactly why D7 stalls rather than merges.
*Alternative:* let an entry hold a list of demand tags, which removes the stall at the
cost of a per-entry list and multiple forwards per line.

**D7 — A second demand for a line already demanded stalls the fetch pipe until the first
is forwarded.** The fetch pipe is in order; a repeat demand for a line already being
demanded means the front end is re-asking, and it must wait for the answer rather than
occupy a second entry. *Alternative:* merge the two, which would need two forwards for one
line and a second tag to track.

**D8 — Whole lines only.** The block neither reads nor modifies any part of a line;
selecting the wanted instruction bytes is the fetch pipe's business.

**D9 — Reset happens once, and its style is free.** Reset is asserted before the first
working cycle and never again; every promise above is made about the run that follows.
The specification is neutral between synchronous and asynchronous reset — it requires
only what both provide.

---

## 7. What an implementer is free to choose

The specification is written so that none of these can fail a check: how entries are
stored; which of several demand entries is fetched or forwarded first (D2); how addresses
are compared; how the block records that entries share a fetch; how class is represented;
whether reset is synchronous or asynchronous (D9); and the exact `requestReady` waveform,
subject only to P6.

---

### 7a. What this specification does NOT promise

One clause is worth stating as an absence, because its earlier name suggested more than it
delivered. The block promises that **once a line has come back, a demand waiting on it is
answered within `depth` cycles** (P-forward). It does *not* promise that every demand is
eventually answered.

The difference is where the unbounded waiting lives. Memory's promise to answer a fetch it has
accepted is an assumption about the world (A-fill). But nothing here assumes memory ever
*accepts* a fetch: if `memoryRequestReady` stays low for ever, an entry waits for ever in the
wanting state, and no clause is violated. **Acceptance fairness and response fairness are two
separate obligations on the environment, and this specification takes only the second.**

Claiming end-to-end delivery would need the first as well — "an enquiry that is presented is
eventually taken" — and would turn a bounded safety claim into a liveness one. That is a
deliberate choice to revisit, not an oversight, and it is recorded here so that nobody reads
the forwarding clause as more than it says.

## 8. What is deliberately not specified

Writing filled lines into the cache (P13); the cache arrays and the hit path; the
predictor that produces prefetches; how the fetch pipe chooses to redirect; virtual
memory and translation; memory's latency and ordering beyond A1 and A2; and what the
fetch pipe does with a forwarded line (D8).

---

## 9. Honesty about the model

**One timebase.** A single clock, with handshakes treated as settled values on it.
Metastability and clock-domain crossing are out of scope: every promise here is a
protocol promise, not a timing promise.

## How the English is checked — the traceability table

Every promise and assumption above maps to the declaration in `rvMissq.cnl` that checks it
— or says plainly why nothing does. This table is machine-read by
`test_v2_cnl_traceability`: a clause mapping to a declaration that does not exist fails the
gate, and so does a `.cnl` claim that no clause owns.

| clause | checked by (in `rvMissq.cnl`) |
|---|---|
| P1 | `demandForwardedAfterFill` — the bounded half; the unbounded half is the environment's A2 |
| P2 | `forwardedEntryIsFreed`, `forwardIsReal` — the entry is gone next cycle, which is *why* twice is impossible |
| P3 | `forwardIsReal` |
| P4 | `forwardIsCorrect` |
| P5 | `fetchIsReal`, `fetchDoesNotRestart` — one fetch per episode, by construction |
| P6 | `neverOverfilled`, `demandAlwaysHasRoom`, `requestReady`, `prefetchRefusedAtReserve` |
| P7 | `demandFirst`, `demandBeatsPrefetch` |
| P8 | `fetchLimitHeld` |
| P9 | `askMemory`, `forwardDemand`, `demandForwardedAfterFill` |
| P10 | `stallRepeatDemand`, `repeatDemandStalls` |
| P11 | `redirect` |
| P12 | `liftPrefetchToDemand`, `demandLiftsAPrefetch` |
| P13 | `finishPrefetch`, `prefetchIsNeverForwarded` |
| P14 | `quietUnderReset` |
| P14b | `joinable` — the definition includes the landing cycle, `prefetchMergesIntoDemand` exercises it |
| P14c | SIGNATURE — `payload: reprioritisable` on `memoryRequest`, with the integrator's obligation |
| P14d | `forwardDemand` — the `choose fairly` obligation; its checking is Phase 3, its parametric half is `RouteLean.Rotation.reaches` |
| P15 | `emptyUnderReset` |
| P16 | `oneEntryPerLine` |
| P17 | `entryPhasesDoNotOverlap` |
| A1 | `fillsAnswerFetches` |
| A2 | `memoryEventuallyAnswers` |
| A3 | NOT TRANSCRIBED — distinct outstanding demand tags is an environment promise no declaration yet states; recorded as owed, not silently absent |
| A4 | `requestHeldUntilTaken` |
| A5 | WITHDRAWN — see the assumption's own entry for the reason |

**Assumptions are obligations.** A1 to A5 are assumed, never proven. Each is something
the integrator must ensure, and the promises in §4 hold only where they do.

**Liveness has a shape.** P1 says a demand miss is *eventually* forwarded, and that rests
on A2 — memory answering. It is not a bound: this specification does not say how long a
demand miss may wait, only that it is not lost or passed over forever.
