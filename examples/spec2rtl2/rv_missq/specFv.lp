% spec2rtl2/rv_missq/spec.lp -- the instruction-fetch miss queue's contract, WRITTEN BY HAND
% from rvMissq.spec and rvMissq.yaml (2026-08-31). It is deliberately hand-written: when the
% DSL compiler exists, this file is the DIFFERENTIAL -- the two contracts must agree on every
% VERDICT of the certificate, on the real design and on sabotaged ones. Never on their text:
% "byte-identical to something nobody proved" is the acceptance bar version 3 was retired for.
%
% THE ONE MODELLING DECISION, from the specification: an ENTRY IS A LINE being fetched, not a
% request. So a demand arriving on a line already being prefetched LIFTS that entry -- taking
% its tag and its priority -- rather than allocating a second one. Everything below follows.
%
% What this file contains, and nothing else:
%   * the WINDOWS it declares and never defines (a level's .inv mounts them on its own flops)
%   * the derived events, which are ports only
%   * the boundary declarations: every address comparison, and only those
%   * the PROMISES, one named failType per kind of wrongness
%   * the SCENARIOS: a constrained abstract start plus one cycle
%
% Vocabulary note: addresses, tags and line data are OPAQUE (the signature says so). They are
% compared through the equality theory -- boundary(eq(A,B),1) declares the question, pval reads
% the answer -- and never enumerated. A 26-bit address enumerated would be 67 million values.

#const depth = 4.
#const maxOutstandingFetches = 2.
#const demandReserve = 1.

slot(0..depth-1).
live(T) :- val(resetN, 1, T).

% ---- THE WINDOWS this contract declares -----------------------------------------------------
% Each is a derived view of the design's own state, defined at every instant by the level's
% linkage. The spec declares them and never defines them (tenet 2b).
%
%   entryValid(I, T)        slot I holds a live entry
%   entryAddress(I, A, T)   its line address                        (opaque token)
%   entryTag(I, X, T)       the demand tag it will answer           (opaque token)
%   demanding(I, T)         the fetch pipe is waiting on it -- its CURRENT class
%   wantsFetch(I, T)        its enquiry has not been taken by memory yet
%   inFlight(I, T)          memory took the enquiry, the fill has not arrived
%   filled(I, T)            the line came back, the entry has not ended
%   lineData(I, V, T)       the data memory returned                (opaque token)
%   forwardOf(I, T)         WHICH entry this instant's forward answers -- the structural
%                           representative: the spec wants to name the answered entry, so the
%                           hardware carries the name rather than the spec inferring it
%   liveEntries(N, T)       how many entries exist          } two counters the design must
%   inFlightCount(N, T)     how many enquiries are in flight} carry; it needs both anyway
#defined entryValid/2.  #defined entryAddress/3.  #defined entryTag/3.
#defined demanding/2.   #defined wantsFetch/2.    #defined inFlight/2.
#defined filled/2.      #defined lineData/3.      #defined forwardOf/2.
#defined liveEntries/2. #defined inFlightCount/2.

% ---- derived events: ports only -------------------------------------------------------------
accepted(T)    :- live(T), val(requestValid, 1, T), val(requestReady, 1, T).
fetchTaken(T)  :- live(T), val(memoryRequestValid, 1, T), val(memoryRequestReady, 1, T).
filling(T)     :- live(T), val(fillValid, 1, T).
forwarding(T)  :- live(T), val(forwardValid, 1, T).
redirecting(T) :- live(T), val(redirectValid, 1, T).
demandOffered(T)   :- live(T), val(requestValid, 1, T), val(requestIsDemand, 1, T).
prefetchOffered(T) :- live(T), val(requestValid, 1, T), val(requestIsDemand, 0, T).

% joinable: the entry exists and its fill has not arrived -- this cycle included
joinable(I, T) :- wantsFetch(I, T).
joinable(I, T) :- inFlight(I, T).

% ---- the CAM: every address comparison in the block, and only these -------------------------
boundary(eq(A, B), 1) :- val(requestAddress, A, T), entryAddress(I, B, T), joinable(I, T).
boundary(eq(A, B), 1) :- filling(T), val(fillAddress, A, T), entryAddress(I, B, T), inFlight(I, T).
% declared whenever an enquiry is PRESENTED, not only when it is taken: demand_first asks
% which entry is being enquired for while memoryRequestValid is high, and memoryRequestReady
% may still be low. Declaring the comparison only on the taken cycle left that question with
% no answer, which reads exactly like a violation. (Found by the first certificate run.)
boundary(eq(A, B), 1) :- live(T), val(memoryRequestValid, 1, T), val(memoryRequestAddress, A, T),
                         entryAddress(I, B, T), wantsFetch(I, T).
boundary(eq(A, B), 1) :- entryAddress(I, A, T), entryAddress(J, B, T),
                         joinable(I, T), joinable(J, T), I != J.

requestMatches(I, T) :- live(T), val(requestValid, 1, T), val(requestAddress, A, T),
                        entryAddress(I, B, T), joinable(I, T), pval(eq(A, B), 1).
someRequestMatch(T)  :- requestMatches(_, T).
fillLands(I, T)      :- filling(T), val(fillAddress, A, T), entryAddress(I, B, T),
                        inFlight(I, T), pval(eq(A, B), 1).
enquiryFor(I, T)     :- fetchTaken(T), val(memoryRequestAddress, A, T), entryAddress(I, B, T),
                        wantsFetch(I, T), pval(eq(A, B), 1).

% ---- ASSUMPTIONS: what the world promises ---------------------------------------------------
% R1 a fill answers a line whose enquiry is in flight  (@assume fillsAnswerFetches)
:- filling(T), not fillLands(_, T).
% R2 IS NOT A CONSTRAINT ON THIS INTERFACE, and the certificate is what showed it. Two
% readings were tried and both are wrong. Same-cycle ("no demand while stalled") excludes the
% very situation the stall exists for -- fetchStall is the block's combinational answer TO a
% repeat demand. Next-cycle contradicts R3: a repeat demand is not accepted, so R3 requires it
% to stay presented, while R2 requires it to go away. A stalled request would have to both
% stay and leave.
%
% The resolution is that the queue does not need the assumption at all. `requestReady` is low
% for a repeat demand, so the queue is protected whatever the pipe does; fetchStall is advice
% to the fetch pipe upstream (stop generating new misses), not a promise the queue leans on.
% An assumption that only restates what an output already guarantees is worth deleting: here
% it made two of the specification's own scenarios unsatisfiable.
% R3 a request is held, unchanged, until it is taken   (@assume requestHeldUntilTaken)
:- live(T), live(T+1), val(requestValid, 1, T), not accepted(T), val(requestValid, 0, T+1).
% The ADDRESS half of R3 cannot be written as token identity, and getting this wrong cost two
% scenarios. Under the symbolic reading every data input gets a FRESH TOKEN each instant, so
% `val(requestAddress, A, T), not val(requestAddress, A, T+1)` is true by construction -- it
% says "the token differs", which it always does. As an assumption it therefore excluded every
% state in which a request is offered and not taken, which is precisely the situation
% prefetch_refused_at_reserve and repeat_demand_stalls exist to exhibit.
%
% Stability of an opaque payload is a statement about EQUALITY, not identity, so it goes
% through the equality theory like every other address comparison: declare the question, then
% require the answer.
boundary(eq(A, B), 1) :- live(T), live(T+1), val(requestValid, 1, T), not accepted(T),
                         val(requestAddress, A, T), val(requestAddress, B, T+1).
:- live(T), live(T+1), val(requestValid, 1, T), not accepted(T),
   val(requestAddress, A, T), val(requestAddress, B, T+1), pval(eq(A, B), 0).
% (memoryEventuallyAnswers is an unbounded fairness promise: it constrains no finite window,
%  so it appears here as a comment rather than a constraint. The machine's own obligation is
%  bounded -- see demand_forwarded_after_fill.)

% ---- PROMISES: one named failType per kind of wrongness -------------------------------------

% [reset_quiet] under reset the block asks nothing, answers nothing, stalls nobody   (P14)
failType(reset_quiet, T) :- val(resetN, 0, T), val(memoryRequestValid, 1, T).
failType(reset_quiet, T) :- val(resetN, 0, T), val(forwardValid, 1, T).
failType(reset_quiet, T) :- val(resetN, 0, T), val(fetchStall, 1, T).

% [reset_empty] and it starts from EMPTY -- no entries, nothing in flight               (P15)
% This was the gap the contract found: the first version of the English never said it, and a
% queue whose entries survive reset would take a fill for a line it no longer remembers, which
% breaks the environment's own assumption.
failType(reset_empty, T) :- val(resetN, 0, T), entryValid(_, T).
failType(reset_empty, T) :- val(resetN, 0, T), liveEntries(N, T), N != 0.
failType(reset_empty, T) :- val(resetN, 0, T), inFlightCount(N, T), N != 0.

% [never_overfilled] the queue never holds more than depth entries
failType(never_overfilled, T) :- live(T), liveEntries(N, T), N > depth.

% [fetch_limit_held] never more enquiries in flight than the limit allows
failType(fetch_limit_held, T) :- live(T), inFlightCount(N, T), N > maxOutstandingFetches.

% [demand_always_has_room] a demand offered below the reserve, on a line not already being
% demanded, must be takeable. Stated about an offered DEMAND because `ready` depends on the
% class of the request -- the queue can have room for a demand and none for a prefetch in the
% same instant, which is what the reserve is for.
failType(demand_always_has_room, T) :- demandOffered(T), not repeatDemand(T),
                                       liveEntries(N, T), N <= depth - demandReserve,
                                       val(requestReady, 0, T).

% [ready_is_right] `ready` is exactly the class-dependent room test -- the single place
% acceptance is decided. A demand may take the reserve; a prefetch may not; a repeat demand
% is never taken.
failType(ready_is_right, T) :- prefetchOffered(T), not someRequestMatch(T),
                               liveEntries(N, T), N >= depth - demandReserve,
                               val(requestReady, 1, T).
failType(ready_is_right, T) :- live(T), val(requestValid, 1, T), liveEntries(N, T), N >= depth,
                               not someRequestMatch(T), val(requestReady, 1, T).

% [slot_phase] THE INVARIANT THE INDUCTION ASKED FOR. An entry is in exactly one phase: it
% is waiting for its enquiry to go out, or waiting for the fill, or holding the line. The
% step frees every register, so without this it may begin in a state that is both waiting to
% fetch AND already filled -- and from there the design does two contradictory things at once.
% Not reachable, which is exactly why it is an invariant rather than a bug.
failType(slot_phase, T) :- live(T), wantsFetch(I, T), inFlight(I, T).
failType(slot_phase, T) :- live(T), wantsFetch(I, T), filled(I, T).
failType(slot_phase, T) :- live(T), inFlight(I, T), filled(I, T).

% [one_entry_per_line] two joinable entries never hold the same line -- what makes merging work
failType(one_entry_per_line, T) :- live(T), joinable(I, T), joinable(J, T), I != J,
                                   entryAddress(I, A, T), entryAddress(J, B, T),
                                   pval(eq(A, B), 1).

% [fetch_is_real] an enquiry is only ever taken for an entry that still WANTS one. The old
% name for this was one_fetch_per_line, which is not what it checks -- the review was right.
failType(fetch_is_real, T) :- fetchTaken(T), not enquiryFor(_, T).

% [want_never_returns] and here is the claim the old name made, as a ONE-STEP relation: a live
% entry never goes back to wanting a fetch. With enquiry_clears_want, a line is therefore
% fetched once per episode -- no interval operator needed, and the language deliberately has
% none. Setting `want` is allowed only where the entry did not exist, which is allocation.
failType(want_never_returns, T+1) :- live(T), live(T+1), entryValid(I, T),
                                     not wantsFetch(I, T), entryValid(I, T+1),
                                     wantsFetch(I, T+1).

% [demand_first] while a demanding entry is waiting, the enquiry made is a demanding one
demandWaiting(T)   :- wantsFetch(I, T), demanding(I, T).
askedDemanding(T)  :- live(T), val(memoryRequestValid, 1, T), val(memoryRequestAddress, A, T),
                      entryAddress(I, B, T), wantsFetch(I, T), demanding(I, T), pval(eq(A, B), 1).
failType(demand_first, T) :- live(T), val(memoryRequestValid, 1, T), demandWaiting(T),
                             not askedDemanding(T).

% [forward_is_real] a forward answers exactly one entry, and that entry is filled and demanding
failType(forward_is_real, T) :- forwarding(T), not forwardOf(_, T).
failType(forward_is_real, T) :- forwarding(T), forwardOf(I, T), forwardOf(J, T), I != J.
failType(forward_is_real, T) :- forwarding(T), forwardOf(I, T), not filled(I, T).
failType(forward_is_real, T) :- forwarding(T), forwardOf(I, T), not demanding(I, T).
failType(forward_is_real, T) :- forwardOf(_, T), not forwarding(T).

% [forward_is_correct] it carries that entry's tag and that entry's line
failType(forward_is_correct, T) :- forwarding(T), forwardOf(I, T), entryTag(I, X, T),
                                   not val(forwardTag, X, T).
failType(forward_is_correct, T) :- forwarding(T), forwardOf(I, T), lineData(I, V, T),
                                   not val(forwardData, V, T).

% [forwarded_entry_is_freed] the entry is gone the cycle after it is answered. This is WHY a
% demand cannot be answered twice, which is worth more than asserting that it is not.
failType(forwarded_entry_is_freed, T+1) :- forwarding(T), live(T+1), forwardOf(I, T),
                                           entryValid(I, T+1).

% [demand_forwarded_after_fill] a filled demanding entry is answered within depth cycles, or
% stops being demanding (a redirect can do that). The unbounded part -- memory answering at
% all -- is the environment's promise, not the machine's.
servedWithin(I, T) :- live(T), filled(I, T), demanding(I, T), K = 1..depth,
                      forwarding(T+K), forwardOf(I, T+K).
servedWithin(I, T) :- live(T), filled(I, T), demanding(I, T), K = 1..depth,
                      live(T+K), not demanding(I, T+K).
failType(demand_forwarded_after_fill, T) :- live(T), filled(I, T), demanding(I, T),
                                            live(T+depth), not servedWithin(I, T).

% ---- THE MACHINE, as one-step relations: an event rule and a frame rule per window ----------
% The frame rules are the frame condition made explicit: if nothing caused a change, a change
% is wrong. Every trigger that writes a window must appear in that window's frame disjunction,
% or the contract forbids a change the specification allows.

% allocation: an accepted request that matched nothing takes a free slot, on the line offered
allocating(T) :- accepted(T), not someRequestMatch(T).
failType(allocation_wrong, T+1) :- allocating(T), live(T+1), not allocatedSomewhere(T).
allocatedSomewhere(T) :- allocating(T), slot(I), not entryValid(I, T), entryValid(I, T+1),
                         val(requestAddress, A, T), entryAddress(I, A, T+1), wantsFetch(I, T+1).
% a demand allocation arrives demanding and carrying its tag; a prefetch does not
failType(allocation_wrong, T+1) :- allocating(T), demandOffered(T), live(T+1), slot(I),
                                   not entryValid(I, T), entryValid(I, T+1),
                                   not demanding(I, T+1).
failType(allocation_wrong, T+1) :- allocating(T), prefetchOffered(T), live(T+1), slot(I),
                                   not entryValid(I, T), entryValid(I, T+1), demanding(I, T+1).

% lifting: a demand meeting a joinable prefetch entry makes THAT entry demanding, on its tag,
% and takes no slot. This is the entry-is-a-line decision, checkable.
lifting(I, T) :- accepted(T), demandOffered(T), requestMatches(I, T), not demanding(I, T).
failType(lift_wrong, T+1) :- lifting(I, T), live(T+1), not demanding(I, T+1).
failType(lift_wrong, T+1) :- lifting(I, T), live(T+1), val(requestTag, X, T),
                             not entryTag(I, X, T+1).

% merging: a prefetch meeting a joinable entry changes nothing at all. Stated as "it
% allocates nothing" rather than "the population is unchanged" -- an unrelated prefetch entry
% may end in the same cycle, and the count would move for a reason that has nothing to do with
% the merge. (Found by the first step run.)
merging(T) :- accepted(T), prefetchOffered(T), someRequestMatch(T).
failType(merge_wrong, T+1) :- merging(T), live(T+1), slot(I), not entryValid(I, T),
                              entryValid(I, T+1).

% a second demand for a line already demanding stalls the fetch pipe, and is not taken.
% Note it is NOT taken because `ready` is low -- acceptance is decided in one place only,
% which is the repair for the contradiction the design step found (two behaviours deciding
% acceptance, and disagreeing at the reserve).
repeatDemand(T) :- demandOffered(T), requestMatches(I, T), demanding(I, T).
failType(repeat_demand_wrong, T) :- repeatDemand(T), val(fetchStall, 0, T).
failType(repeat_demand_wrong, T) :- repeatDemand(T), val(requestReady, 1, T).

% the enquiry, taken: every entry wanting that line goes in flight
failType(enquiry_clears_want, T+1) :- enquiryFor(I, T), live(T+1), wantsFetch(I, T+1).
failType(enquiry_clears_want, T+1) :- enquiryFor(I, T), live(T+1), not inFlight(I, T+1).

% the fill, landing: every in-flight entry on that line becomes filled, holding the data
failType(fill_lands, T+1) :- fillLands(I, T), live(T+1), inFlight(I, T+1).
failType(fill_lands, T+1) :- fillLands(I, T), live(T+1), not filled(I, T+1).
failType(fill_lands, T+1) :- fillLands(I, T), live(T+1), val(fillData, V, T),
                             not lineData(I, V, T+1).

% a redirect downgrades every demanding entry
failType(redirect_downgrades, T+1) :- redirecting(T), live(T+1), demanding(I, T+1),
                                      demanding(I, T).

% a filled entry that is not demanding ends
failType(prefetch_ends, T+1) :- live(T), live(T+1), filled(I, T), not demanding(I, T),
                                entryValid(I, T+1).

% ---- THE FRAME: nothing changes unless something above caused it ----------------------------
% demanding: set by an allocation of a demand, or a lift; cleared by a redirect or by ending
demandingMayChange(I, T) :- lifting(I, T).
demandingMayChange(I, T) :- redirecting(T), slot(I).
demandingMayChange(I, T) :- allocating(T), slot(I), not entryValid(I, T).
demandingMayChange(I, T) :- forwarding(T), forwardOf(I, T).
failType(demanding_disturbed, T+1) :- live(T), live(T+1), entryValid(I, T), entryValid(I, T+1),
                                      demanding(I, T), not demandingMayChange(I, T),
                                      not demanding(I, T+1).
failType(demanding_disturbed, T+1) :- live(T), live(T+1), entryValid(I, T), entryValid(I, T+1),
                                      not demanding(I, T), not demandingMayChange(I, T),
                                      demanding(I, T+1).

% the line address never changes while the entry lives -- an entry IS a line
failType(address_disturbed, T+1) :- live(T), live(T+1), entryValid(I, T), entryValid(I, T+1),
                                    entryAddress(I, A, T), not entryAddress(I, A, T+1).

% wantsFetch is cleared only by the enquiry being taken, and set only by allocation
wantChanges(I, T) :- enquiryFor(I, T).
wantChanges(I, T) :- allocating(T), slot(I), not entryValid(I, T).
failType(want_disturbed, T+1) :- live(T), live(T+1), entryValid(I, T), entryValid(I, T+1),
                                 wantsFetch(I, T), not wantChanges(I, T), not wantsFetch(I, T+1).

% inFlight changes only on the enquiry or the fill
inflightChanges(I, T) :- enquiryFor(I, T).
inflightChanges(I, T) :- fillLands(I, T).
failType(inflight_disturbed, T+1) :- live(T), live(T+1), entryValid(I, T), entryValid(I, T+1),
                                     inFlight(I, T), not inflightChanges(I, T),
                                     not inFlight(I, T+1).

% a landed line is retained until the entry ends
failType(data_disturbed, T+1) :- live(T), live(T+1), entryValid(I, T+1), filled(I, T),
                                 lineData(I, V, T), not lineData(I, V, T+1).

% an entry appears only by allocation and disappears only by being answered or ending
entryMayAppear(I, T)    :- allocating(T), slot(I).
entryMayDisappear(I, T) :- forwarding(T), forwardOf(I, T).
entryMayDisappear(I, T) :- filled(I, T), not demanding(I, T).
failType(entry_appeared, T+1) :- live(T), live(T+1), not entryValid(I, T), slot(I),
                                 not entryMayAppear(I, T), entryValid(I, T+1).
failType(entry_vanished, T+1) :- live(T), live(T+1), entryValid(I, T),
                                 not entryMayDisappear(I, T), not entryValid(I, T+1).

% the two counters agree with what they count -- this is what makes them windows rather than
% a second opinion. Stated per slot, so it costs depth rules and not a count.
failType(occupancy_wrong, T) :- live(T), liveEntries(N, T), N = 0, entryValid(_, T).
failType(inflight_count_wrong, T) :- live(T), inFlightCount(N, T), N = 0, inFlight(_, T).

% ---- SCENARIOS: a constrained abstract start plus one cycle ---------------------------------
scenario(demand_lifts_a_prefetch,   prefetch_entry_and_demand_offered, any_input, lifted).
scenario(prefetch_merges,           demand_entry_and_prefetch_offered, any_input, merged).
scenario(demand_beats_prefetch,     both_waiting,                      any_input, asked_demanding).
scenario(prefetch_refused_at_reserve, at_the_reserve_prefetch_offered, any_input, refused).
scenario(repeat_demand_stalls,      demanding_entry_and_demand_again,  any_input, stalled).
scenario(fill_then_forward,         filled_and_demanding,              any_input, forwarded).

% every scenario's INPUT slot: no constraint beyond the machine being out of reset. Omitting
% this made all six scenarios report "no compliant state" -- the runner asserts
% `:- not holds(Input, 0).`, so an undefined input name is an unsatisfiable demand, not a
% permissive one. (Found by the first scenario run.)
holds(any_input, T) :- live(T).

holds(prefetch_entry_and_demand_offered, T) :- demandOffered(T), requestMatches(I, T),
                                               not demanding(I, T).
holds(demand_entry_and_prefetch_offered, T) :- prefetchOffered(T), requestMatches(I, T),
                                               demanding(I, T).
holds(both_waiting, T) :- wantsFetch(I, T), demanding(I, T), wantsFetch(J, T),
                          not demanding(J, T), I != J, inFlightCount(N, T),
                          N < maxOutstandingFetches.
holds(at_the_reserve_prefetch_offered, T) :- prefetchOffered(T), not someRequestMatch(T),
                                             liveEntries(N, T), N = depth - demandReserve.
holds(demanding_entry_and_demand_again, T) :- demandOffered(T), requestMatches(I, T),
                                              demanding(I, T).
holds(filled_and_demanding, T) :- filled(I, T), demanding(I, T).

did(lifted)           :- lifting(I, 0), demanding(I, 1).
% a merge takes no slot: no slot goes from free to occupied. NOT "the count is unchanged" --
% an unrelated prefetch entry may end in the same cycle, which moves the count for a reason
% that has nothing to do with the merge. (The same mistake as merge_wrong, one line over.)
did(merged)           :- merging(0), not slotFilledIn(1).
slotFilledIn(1) :- slot(I), not entryValid(I, 0), entryValid(I, 1).
did(asked_demanding)  :- askedDemanding(0).
did(refused)          :- val(requestReady, 0, 0).
did(stalled)          :- val(fetchStall, 1, 0).
did(forwarded)        :- forwarding(0).
