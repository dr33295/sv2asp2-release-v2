# fifo.spec -- the FIFO's checkable specification. The English in force is SPECIFICATION.md;
# the wires are fifo.yaml. Notation: docs/spec2rtl2/ROUTE_METHODOLOGY.md, Part II.
#
# THE VOCABULARY THIS BLOCK NEEDS, and why it is a pointer domain rather than arithmetic:
# a FIFO's whole state is two pointers, and every claim about it is one of three relations --
# they are equal (empty), they are a lap apart (full), or one has advanced (a push or a pop).
# Written with `+` and `%` those would be arithmetic in the step vocabulary, which this route
# forbids because it enumerates. Written as `next`, `opposite` and `address` they are three
# named relations on a small domain, and the specification says what it means instead of
# computing it.

disable iff (!reset_n)

# ---- what the world is granted -----------------------------------------------------------
# Nothing. The FIFO promises its behaviour for every input sequence, which is why this file
# has no @assume at all -- worth noticing rather than mistaking for an omission.

# ---- the state the specification names ----------------------------------------------------

@index address : depth
  meaning: a storage cell. An INDEX, not an object: addresses do not come and go, so nothing
           here ever asks whether one still exists.

@state pointerPush : pointer(depth)
  meaning: what the design uses as its push-side pointer. A wrap-bit pointer: it counts to
           twice the depth so that "same cell, different lap" is a relation rather than a
           count that has to be kept somewhere.

@state pointerPop : pointer(depth)
  meaning: likewise for the pop side

@state cellValue[address] : value(width)
  meaning: what the storage holds at each address

# ---- vocabulary ----------------------------------------------------------------------------

@define acceptedPush
  kind: event
  meaning: a word was offered and the FIFO had room, so it was taken this cycle
  holds when push.valid && push.ready

@define servedPop
  kind: event
  meaning: a word was requested and the FIFO had one, so it was handed over this cycle
  holds when pop.valid && pop.ready

@define isEmpty
  kind: condition
  meaning: the two pointers are at the same place, on the same lap
  holds when pointerPush == pointerPop

@define isFull
  kind: condition
  meaning: the two pointers name the same cell on opposite laps
  holds when opposite(pointerPush, pointerPop)

# ---- the flags say what the pointers say ----------------------------------------------------

# The flags are spoken of by ROLE, not by wire name. `full` and `empty` are this block's ready
# wires read the other way up (the signature says `active: low`), so a property that named them
# directly would be about polarity rather than about the FIFO. `push.ready` is true exactly when
# a word can be taken, whichever way the wire runs.

@property emptyIsRight
  isEmpty |-> !pop.ready

@property emptyIsNotRight
  !isEmpty |-> pop.ready

@property fullIsRight
  isFull |-> !push.ready

@property fullIsNotRight
  !isFull |-> push.ready

@property validPopIsTheComplementOfEmpty
  !isEmpty |-> valid_pop.high

@property nothingValidWhenEmpty
  isEmpty |-> valid_pop.low

# ---- pointer discipline: advance on the event, hold otherwise --------------------------------

@property pushPointerAdvances
  acceptedPush |=> pointerPush == next($past(pointerPush))

@property pushPointerHolds
  !acceptedPush |=> $stable(pointerPush)

@property popPointerAdvances
  servedPop |=> pointerPop == next($past(pointerPop))

@property popPointerHolds
  !servedPop |=> $stable(pointerPop)

@property resetStartsAtZero
  enable iff (!reset_n)
  !reset_n |-> pointerPush == 0 && pointerPop == 0

# ---- storage: address-local relations ---------------------------------------------------------

@property pushLands
  acceptedPush |=> cellValue[address($past(pointerPush))] == $past(data_push)
  # `$past` on the POINTER as well as on the word, and the lowering is what showed it: by the
  # next instant the push pointer has advanced, so `address(pointerPush)` names the cell that
  # will be written NEXT, not the one just written. Read as English the original sentence
  # sounds right, which is how it survived being written and read.

@property cellIsUndisturbed
  each address A (
    !(acceptedPush && address(pointerPush) == A) |=> $stable(cellValue[A])
  )

@property popServesTheCell
  servedPop |-> data_pop == cellValue[address(pointerPop)]

# ---- what must stay possible -------------------------------------------------------------------

@scenario pushWhenFull
  isFull && push.valid |-> !acceptedPush

@scenario popWhenEmpty
  isEmpty && pop.valid |-> !servedPop

@scenario pushWhenEmpty
  isEmpty && push.valid |=> !isEmpty

@scenario popWhenFull
  isFull && pop.valid |=> !isFull

@scenario pushAndPopTogether
  !isEmpty && !isFull && push.valid && pop.valid
  |-> acceptedPush && servedPop
