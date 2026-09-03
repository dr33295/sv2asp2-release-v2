# The FIFO, Step by Step

This document walks one design — a four-entry FIFO queue — through the entire spec2rtl v2
route, from a paragraph of English to SystemVerilog carrying a proof. At every step it
shows three things: **what you write**, **what the tool does with it**, and **what comes
back**. Every file excerpt is taken from the real artifact in `examples/spec2rtl2/fifo/`,
and every piece of tool output shown was produced by running the command shown above it —
including the failing run, which was produced by deliberately planting a classic bug.

Read this beside two companions: `METHODOLOGY.md` explains *why* each step is shaped the
way it is; `TOOL.md` explains the Python that runs underneath, file by file. This document
is the *how it feels to use it*.

---

## Step 0 — The English

Everything starts from a paragraph a person could say aloud:

> A FIFO queue, four entries deep, eight bits wide. Push writes a value in; pop reads the
> oldest value out. A `full` flag refuses pushes; an `empty` flag refuses pops. Data comes
> out in the order it went in.

This paragraph is the only input. Everything else in this document is derived from it, and
the route's whole purpose is that the derivation ends in a proof rather than a shrug.

---

## Step 1 — Resolving the English

English is ambiguous, and the first step is to decide every ambiguity *on paper, before
any code*. For the FIFO the resolutions that mattered (recorded in the entry's
`SPECIFICATION.md`, with the reasoning in `DESIGN.md`):

- **What happens on push-when-full?** The push is *refused* — nothing changes. (The
  alternative, overwrite-oldest, is a different device.)
- **Is the output registered or show-ahead?** Show-ahead: `data_pop` always displays the
  oldest value; `pop` consumes it. A `valid_pop` output says when `data_pop` means
  anything — a decision the original paragraph never mentions, added during resolution
  because without it "the output is correct" is not even stateable.
- **How will the spec talk about occupancy?** Not with a count. A count is a number that
  the checker would have to enumerate (0..depth per instant), and — the deeper reason — a
  count is *redundant* state: the two pointers already determine it. The specification's
  vocabulary is **wrap-bit pointers**: each pointer runs over `0..2·depth−1`, its low bits
  are the address, its top bit flips each time it wraps. Then *empty* is "the pointers are
  equal" and *full* is "same address, opposite wrap bit" — pure equalities over an
  eight-value domain, which a checker handles without breaking stride.

Each checkable sentence of the resolved specification is tagged with the name of the rule
that will check it, so the prose and the contract can be audited against each other.

---

## Step 2 — Writing the contract: `spec.lp`

The contract is a text file of logic rules. It contains exactly three kinds of thing, and
it is worth seeing each in the real file.

**First, the window declarations.** The specification needs to see the design's pointers
and storage, but no design exists yet — so it *declares* the vocabulary and leaves the
connection for later:

```
pointer_push(P, T)   -- what the design uses as its push-side pointer, at instant T
pointer_pop(P, T)    -- likewise for the pop side
cell_value(A, V, T)  -- what the storage holds at address A
```

**Second, the properties** — one named `bad` rule per kind of wrongness. Here is the
empty-flag property, and it is worth reading aloud once, because every rule in the route
reads the same way:

```prolog
bad(empty_wrong, T) :- live(T), pointer_push(P, T), pointer_pop(P, T), val(empty, 0, T).
bad(empty_wrong, T) :- live(T), pointer_push(P, T), pointer_pop(Q, T), P != Q, val(empty, 1, T).
```

Read: "it is a wrongness called `empty_wrong` at time T if the design is out of reset, the
two pointers are equal, and the `empty` output is 0" — and symmetrically, empty asserted
when the pointers differ. Two rules because the flag can be wrong in two directions;
together they pin `empty` exactly. The full flag gets the same two-sided treatment against
"same address, opposite wrap", written as pointer arithmetic:

```prolog
bad(full_wrong, T) :- live(T), pointer_push(P, T), pointer_pop(Q, T),
                      Q = (P + depth) \ (2*depth), val(full, 0, T).
```

The pointer-discipline properties say each pointer *advances by exactly one on its event
and holds otherwise* — again two-sided (moved when it shouldn't, or didn't when it
should). The storage properties are address-local: a pushed value must land in the cell
the push pointer addressed (`push_landed_wrong`); every other cell must be undisturbed
(`cell_disturbed`); a served pop must output the cell the pop pointer addresses
(`pop_value_wrong`).

Notice what is *absent*: no rule anywhere says "first in, first out." That behaviour is a
**theorem** of the mechanism properties — if pointers advance in order, values land where
addressed and hold, and pops read the addressed cell, then order-preservation follows.
This is deliberate (METHODOLOGY, Chapter 4): a wrong design cannot satisfy the behaviour
vacuously, because it would have to defeat several independent local claims at once.

**Third, the scenarios** — the liveness half. Each is one fact naming a situation, an
input, and the natural operation:

```prolog
scenario(push_when_full,   is_full,  do_push, push_refused).
scenario(push_and_pop_mid, is_mid,   do_both, both_happen).
scenario(one_entry_pop,    is_one,   do_pop,  pop_served_and_empty).
```

with each name defined over the same vocabulary — `is_full` is a pointer relation,
`do_push` is a port pattern, `push_refused` is what must then happen. There are seven,
covering both boundaries, the middle, and the wrap edge.

---

## Step 3 — Writing the design: `l1.lp`

The design is written in the route's authoring language: facts that declare nets, define
combinational logic, and instantiate registers from a small library whose meaning is
fixed. The FIFO's core, from the real file:

```prolog
param(depth, 4).                             % overridable at instantiation
param(width, 8).
param(pointer_width, add(address_width, 1)). % address bits + the wrap bit

def(push_accepted, logand(reset_n, logand(push, lnot(full)))).

inst(u_write_pointer, arff).                 % an async-reset flop, from the library
  pin(u_write_pointer, clk, clk).  pin(u_write_pointer, rstL, reset_n).
  pin(u_write_pointer, en, push_accepted).   % advances ONLY on an accepted push
  pin(u_write_pointer, d, wp_plus_one).  pin(u_write_pointer, q, write_pointer).

def(empty, eq(read_pointer, write_pointer)).
def(full,  eq(read_pointer, write_pointer_opposed)).   % opposed = write_pointer + depth

inst(storage, farray).                       % depth x width array of flops, one write port
  pin(storage, we, push_accepted).
  pin(storage, wa, write_address).  pin(storage, wd, data_push).
def(data_pop, mrd(storage, read_address)).   % read combinationally: show-ahead
```

Reading it as hardware: two wrap-bit pointer registers that advance on their own event;
flags computed as pure pointer equalities (there is no count anywhere in this design
either); a flop-array storage written at the push address; the output wired to the cell at
the pop address. The `param` facts make the design generic — the tool verifies at the
defaults and the printer will emit `#(parameter DEPTH = 4, WIDTH = 8)`.

What does the tool do with this file on its own? The **lint** (`python -m sv2asp.aspfirst2
lint l1.lp`) checks it is inside the authoring subset — every fact well-formed, every pin
a declared net, widths consistent, no combinational loops — and refuses anything else with
the line number. A design that lints is a design whose meaning is fully determined by the
rule library.

---

## Step 4 — Connecting them: the linkage `l1.inv.lp`

The specification declared three windows; this design mounts them. The entire file:

```prolog
pointer_push(P, T)  :- val(write_pointer, P, T).
pointer_pop(P, T)   :- val(read_pointer, P, T).
cell_value(A, V, T) :- val(cell(storage, A), V, T).
```

One line per window: "what the spec calls the push pointer *is* this design's
`write_pointer` register." Each is a derived view — defined at every instant, from the
design's own flops, holding no state of its own. A different implementation of the same
specification would rewrite only this file.

This is the route's central move (METHODOLOGY, Chapter 2). The specification never keeps
its own copy of the queue; it looks at the design's queue through declared glass.

---

## Step 5 — The certificate

One command runs the entire proof:

```
$ python -m sv2asp.aspfirst2 refine spec.lp l1.lp --induct 1
```

and the real output, in full:

```
refine: l1.lp  spec spec.lp  NO STIMULUS (v2 certificate path: base from reset with free inputs + the step, window K=1)
  lint: OK; abstract: 0 net(s)
  live: OK -- some instant is judged within the base window (the monitors can fire)
  base: OK -- from reset, no property can fire on ANY input sequence within 1 live step(s)
  induct K=1: state freed at T=0: write_pointer(3), read_pointer(3); cells storage[4x8]; inputs free every instant: push data_push pop; reset held released: reset_n
  induct: no ghost state (no history predicate in the monitors)
  induct: property set -- bad ['empty_wrong', 'full_wrong', 'valid_wrong', 'pointer_push_wrong', 'pointer_pop_wrong', 'reset_wrong', 'push_landed_wrong', 'cell_disturbed', 'pop_value_wrong']; environment (assumed at every instant): []
  induct: INDUCTIVE at K=1 -- [...all nine...]: with the base, they hold for ALL time (inputs free every instant; reset released after T=0)
  scenario push_when_full: OK -- is_full+do_push is possible, and the natural operation (push_refused) cannot be violated
  scenario pop_when_full: OK -- is_full+do_pop is possible, and the natural operation (pop_served_and_room) cannot be violated
  scenario push_when_empty: OK -- is_empty+do_push is possible, and the natural operation (push_accepted_and_nonempty) cannot be violated
  scenario pop_when_empty: OK -- is_empty+do_pop is possible, and the natural operation (pop_refused) cannot be violated
  scenario one_entry_pop: OK -- is_one+do_pop is possible, and the natural operation (pop_served_and_empty) cannot be violated
  scenario push_and_pop_mid: OK -- is_mid+do_both is possible, and the natural operation (both_happen) cannot be violated
  scenario push_at_wrap_edge: OK -- is_wrapedge+do_push is possible, and the natural operation (push_accepted_and_wrapped) cannot be violated
REFINE: OK
```

This takes about two seconds. Now read it line by line, because each line is one distinct
piece of work the tool performed.

**`lint: OK`** — the subset gate again, plus the *linkage lint*: if the specification had
tried to smuggle in stateful bookkeeping (a predicate defined at a later instant than the
facts it reads), the run would stop here and name it.

**`live: OK`** — asked first: can any instant be judged at all? Every monitor is guarded by
`live(T)`, and a contract in which nothing derives it would pass every check for the wrong
reason. This line is the tool refusing to be fooled that way before it asks anything else.

**`base: OK`** — the tool built a small logic program: the design's rules, from reset
(reset asserted at instant 0, released after), with *every input a free choice at every
instant*, over a two-instant horizon — and asked clingo: *can any `bad` fire?* Clingo
explored every input combination symbolically and answered UNSAT — no. That is the
induction's base case: the first live step after reset is clean no matter what the
environment does.

**`induct K=1: state freed at T=0: ...`** — this line is the route's central move, so
stop on it. The step does **not** start at reset and walk forward. It **abstracts the
initial state**: both 3-bit pointers are freed to any of their 8 values, all four storage
cells to any 8-bit value, and the window begins *there* — in an arbitrary state, with the
inputs free at every instant. A full FIFO is not reached by four pushes; it is one of the
freed assignments, conjured directly. So are all the other full FIFOs, and every empty,
one-entry, mid, and wrapped state, and — this is the point — **every state any real run
could ever be in**, at any depth. That over-approximation is why one 2-instant window
proves a for-all-time claim: if no freed state can step into a violation, no reachable
state can either, ever. And it is why the cost is two seconds regardless of how deep an
interesting state lives: the thousand-cycle walk that simulation would need is replaced by
"let the registers be anything."

The freedom is deliberately too generous — the freed registers can also take assignments
no real run produces — and the *next* ingredient is what tames it: the step **assumes the
nine properties across the window**, carving the arbitrary states down to the compliant
ones. A FIFO whose pointers disagree with its flags is not compliant (the flag properties
exclude it), so it never enters the argument; every *reachable* state of a correct design
is compliant, so the coverage argument still closes. When you hear "the certificate is an
induction," this pair — free the state, assume the properties — is the entire content of
the phrase. Note also, the following line, **no ghost state**: the specification brought
no bookkeeping of its own, so the freed state is precisely the design's real state and
nothing more.

**`induct: INDUCTIVE at K=1`** — the heart. The tool built the step program: state
arbitrary at the window start, all nine properties *assumed* to hold across the window,
and clingo asked to find a next instant where any property fires. UNSAT — no such window
exists. Any compliant state, under any input, leads only to compliant states; with the
base, the nine properties hold at every cycle of every run, forever. Note what did *not*
happen: no invariant had to be added by hand. The nine properties confine each other
tightly enough to be their own inductive strengthening — the reward for the two-sided,
mechanism-level style of Step 2. (When a step *does* fail, the route's doctrine is that
the counterexample is usually an unreachable-but-compliant state, and the fix is a new
named property that excludes it — an *invariant request*, not a bug report.)

**The seven scenario lines** — for each, the tool ran *two* solves over a one-step window
whose start is an arbitrary *compliant* state constrained to the named situation. First:
can the situation occur at all, with the natural operation happening? (It must be
satisfiable — this is what kills vacuity; a specification whose "full" is contradictory
dies here, loudly.) Second: can the natural operation *fail* to happen from any such
state? (It must be unsatisfiable.) So `push_when_full: OK` means: real full states exist,
and *no* full state anywhere in the reachable-or-not universe of compliant states accepts
a push. Depth never enters: "full" was described, not reached by walking — the same
abstract-the-start move the step uses, pointed at liveness instead of safety.

**`REFINE: OK`** — the certificate exists: nine safety properties inductive for all time,
seven liveness checks non-vacuous and unviolable.

---

## Step 6 — What failure looks like (two experiments)

A certificate you have never seen fail is a certificate you should not yet trust, so we
break the design on purpose. The FIFO's classic bug is the wrap bit: a designer computes
`full` by comparing the *addresses* and forgets the wrap, so full and empty become
indistinguishable.

**Experiment one — the accident.** Our first attempt at planting the bug replaced the full
flag with "addresses equal AND not empty":

```prolog
def(full, logand(eq(read_address, write_address), lnot(empty))).
```

The certificate **passed, completely**. And it was right to: work the arithmetic and
"addresses equal but pointers different" is *exactly* "same address, opposite wrap" — we
had accidentally written a correct alternative implementation of full. The certificate
judges behaviour, not spelling; an equivalent design is supposed to pass. (This
non-sabotage is preserved here deliberately: it is the clearest demonstration of what a
behavioural contract means.)

**Experiment two — the real bug.** Drop the qualifier:

```prolog
def(full, eq(read_address, write_address)).
```

Now the empty FIFO — addresses both 0 — claims to be full. The certificate, immediately:

```
  lint: OK; abstract: 0 net(s)
  FAIL base: a property fires from reset -- bad(full_wrong,1), bad(full_wrong,2)
--- counterexample: base (from reset, inputs free) ---
T  reset_n  push  data_push  full  pop  data_pop  valid_pop  empty  ...  write_pointer  read_pointer
0        0     0          2     1    0         0          0      1  ...              0             0
1        1     0        128     1    1         0          0      1  ...              0             0
2        1     1        243     1    1         0          0      1  ...              0             0
REFINE: FAILED
```

Read the table like a waveform: rows are instants, columns are nets. At T=1 reset has
released, both pointers are 0 — a genuinely empty FIFO — and the `full` column reads 1
while `empty` also reads 1. The rule `bad(full_wrong)` fired because full is asserted
while the pointers are *not* in the full relation. The base caught it: this bug is visible
one step from reset, before induction was even needed. The named bad told us *which* flag
is lying, and the table shows the state that convicts it.

Restore the correct line and the certificate is green again. This pair of experiments is
the route's **sabotage discipline** in miniature: every checker earns trust by catching a
planted break — and an accidental *equivalent* passing is the flip side that proves the
contract constrains only what it should.

---

## Step 7 — Printing the SystemVerilog

```
$ python -m sv2asp.aspfirst2 print l1.lp -o fifo.sv
```

The printer maps the authored facts to RTL one-to-one — no optimization, no inference; the
structure you verified is the structure you get:

```systemverilog
module fifo #(
  parameter DEPTH = 4,
  parameter WIDTH = 8
) (
  input  logic clk,  input logic reset_n,
  input  logic push, input logic [WIDTH-1:0] data_push, output logic full,
  input  logic pop,  output logic [WIDTH-1:0] data_pop,
  output logic valid_pop, output logic empty
);
  localparam ADDRESS_WIDTH = $clog2(DEPTH);
  localparam POINTER_WIDTH = (ADDRESS_WIDTH+1);
  ...
  assign empty = read_pointer == write_pointer;
  assign full  = read_pointer == write_pointer_opposed;

  always_ff @(posedge clk or negedge reset_n)
    if (!reset_n) write_pointer <= '0;
    else if (push_accepted) write_pointer <= wp_plus_one;

  always_ff @(posedge clk) if (push_accepted) storage[write_address] <= data_push;
```

The `param` facts became real parameters; the derived widths became `localparam`s; the
`arff` instances became the async-reset always_ff idiom; the `farray` became an array
write. The header comment in the real file says the important thing: *the ASP is the
source; do not edit this file.*

---

## Step 8 — The round trip

The print is a translation, and translations can be wrong — so the route closes the loop
with an independent reader and an independent simulator. A short concrete story is written
for this stage only (`roundtrip_scenario.lp`: reset, fill to full with a refused push, a
same-cycle push+pop, drain to empty, the wrap exercised; every pushed value distinct so a
swapped order would be visible):

```
$ python -m sv2asp.aspfirst2 roundtrip l1.lp roundtrip_scenario.lp --icarus     # or --sim auto: Verilator if installed
print: fifo.sv (behav)
sv2asp: modular translates with --strict-coverage, exit 0
authored: SATISFIABLE, 242 (net, T) samples
modular: SATISFIABLE, 242 (net, T) samples
ASP sides agree on all 242 samples (every net and memory cell, every T)
icarus agrees on all 182 definite samples
ROUNDTRIP: OK
```

What happened, line by line: the design was printed; the print was translated *back* into
logic by **sv2asp** — the repository's independent SystemVerilog translator, which shares
no code with the printer — under `--strict-coverage`, meaning any construct it could not
faithfully translate would be a loud failure rather than a silent drop; the authored model
and the translated print were each solved under the same story, and **every net and every
memory cell at every instant** compared — 242 samples, all equal; and Icarus Verilog
simulated the printed file directly, agreeing on all 182 samples where a 4-state simulator
has a definite value. (The difference, 242 versus 182, is power-on: before a register is
first written, Icarus says X where the model's test convention says 0 — a convention
mismatch, counted and excluded honestly rather than compared falsely.)

Three independent readings of the design — the authored logic, an independent translator's
reading of the printed RTL, and a simulator's execution of it — agree sample for sample.
No proof claim rests on this story; it is the check that the *printing* lost nothing.

---

## Step 9 — What you now hold

It is worth ending by stating exactly what each artifact establishes, because the route's
honesty lives in these distinctions:

- **Proven for all time** (the certificate): the nine safety properties — flags exact,
  pointers disciplined, storage landing/holding/serving correctly — hold at every cycle
  of every run, for any input sequence, from the base and step by induction. And
  first-in-first-out order follows from them as a theorem of the mechanism.
- **Checked, non-vacuously** (the scenarios): the interesting situations are all
  possible, and in each the natural operation cannot be violated from any compliant
  state.
- **Checked, bounded** (the round trip): the printed RTL means what the verified model
  means, on a story that exercises fill, refusal, simultaneity, drain, and wrap — with an
  independent translator and a real simulator as referees.
- **Demonstrated** (the sabotage): the checkers catch the classic bug, and accept a
  behaviourally equivalent variant — the contract binds behaviour, not spelling.

For a design with a wide datapath, one more layer appears — delivered values are compared
as symbolic terms and the arithmetic obligation is *owed to Lean*, then discharged there
structurally; the multiplier family (`wallace32` and its siblings) is the worked example
of that layer, and METHODOLOGY Chapter 5 explains it.

That is the whole route: resolve, contract, design, link, certify, break-and-restore,
print, round-trip — and at the end, RTL whose specification conformance is a checked
mathematical fact.
