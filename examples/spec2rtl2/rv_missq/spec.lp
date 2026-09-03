% GENERATED from rvMissq.cnl.core and its signature -- do not edit. The
% comparison against a hand-written contract is on VERDICTS, never on text.
#const depth = 4.
#const maxOutstandingFetches = 2.
#const demandReserve = 1.
#const addressWidth = 26.
#const dataWidth = 128.
#const tagWidth = 4.
live(T) :- val(resetN, 1, T).

% deepest temporal reference in the claim set: 1 / depth cycle(s). If the
% induction step fails, RAISE K TOWARD THIS before writing an invariant -- the
% route's rule, with an incident behind it: an invariant was once added here
% while the real cause was elsewhere, and it survived as cargo until a
% measurement showed the set inductive at K=1 without it.

% every scenario's INPUT slot: no constraint beyond the machine being out of
% reset. The runner asserts `:- not holds(Input, 0).`, so an undefined input
% name is an unsatisfiable demand, not a permissive one -- the lesson the
% hand-written contract paid for when all six scenarios reported
% 'no compliant state' over one missing line.
holds(any_input, T) :- live(T).

% The equality theory's CONCRETE half, carried by the contract itself so it is
% independent of the design's reading. The runner loads the symbolic companion
% only when the design declares data() -- a concrete design never does, and
% without this rule every declared boundary would be an atom nothing derives,
% making each opaque comparison silently unsatisfiable. Concrete operands
% compute; token operands leave this rule silent and take the theory's free
% bits instead. (Found on the FIFO, whose design is concrete while its
% signature rightly calls the payload opaque.)
pval(P, V) :- boundary(P, _), P = eq(A, B), @issym(A) = 0, @issym(B) = 0, V = @eq(A, B).

roomForDemand(T) :- liveEntries(LiveEntries, T), LiveEntries < depth.
entryId(V) :- entryExists(V, T).
roomForPrefetch(T) :- liveEntries(LiveEntries, T), LiveEntries < (depth - demandReserve).
fetchLimitAllows(T) :- inFlightCount(InFlightCount, T), InFlightCount < maxOutstandingFetches.
boundary(eq(X1Address, FAddress), 1) :- entryAddress(X1, X1Address, T), val(fillAddress, FAddress, T).
fillsAnswerFetchesFound(T) :- gtime(T), entryExists(X1, T), inFlight(X1, T), entryAddress(X1, X1Address, T), val(fillAddress, FAddress, T), pval(eq(X1Address, FAddress), 1).
fillsAnswerFetchesHolds(T) :- gtime(T), fillsAnswerFetchesFound(T).
:- live(T), val(fillValid, 1, T), not fillsAnswerFetchesHolds(T).
requestHeldUntilTakenHolds2(T) :- gtime(T), val(requestValid, 1, T), val(requestReady, 1, T).
boundary(eq(RequestAddress, RequestAddressNext), 1) :- val(requestAddress, RequestAddress, T), val(requestAddress, RequestAddressNext, T+1).
boundary(eq(RequestTag, RequestTagNext), 1) :- val(requestTag, RequestTag, T), val(requestTag, RequestTagNext, T+1).
requestHeldUntilTakenHolds(T) :- gtime(T), gtime(T+1), val(requestValid, 1, T+1), val(requestAddress, RequestAddress, T), val(requestAddress, RequestAddressNext, T+1), pval(eq(RequestAddress, RequestAddressNext), 1), val(requestTag, RequestTag, T), val(requestTag, RequestTagNext, T+1), pval(eq(RequestTag, RequestTagNext), 1), val(requestIsDemand, RequestIsDemand, T), val(requestIsDemand, RequestIsDemand, T+1).
:- live(T), live(T+1), val(requestValid, 1, T), not requestHeldUntilTakenHolds2(T), not requestHeldUntilTakenHolds(T).
allocateDemandAny2(X1, T) :- gtime(T), entryId(X1), wantsFetch(X1, T).
allocateDemandAny2(X1, T) :- gtime(T), entryId(X1), inFlight(X1, T).
boundary(eq(X1Address2, RAddress2), 1) :- entryAddress(X1, X1Address2, T), val(requestAddress, RAddress2, T).
allocateDemandFound2(T) :- gtime(T), entryExists(X1, T), allocateDemandAny2(X1, T), entryAddress(X1, X1Address2, T), val(requestAddress, RAddress2, T), pval(eq(X1Address2, RAddress2), 1).
allocateDemandHolds(T) :- gtime(T), allocateDemandFound2(T).
failType(allocateDemandWrong, T) :- live(T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 1, roomForDemand(T), not allocateDemandHolds(T), not val(requestReady, 1, T).
allocateDemandCreated(T) :- gtime(T), entryId(E), not entryExists(E, T), entryExists(E, T+1), entryAddress(E, EAddress, T+1), val(requestAddress, RAddress3, T), EAddress = RAddress3, entryTag(E, ETag, T+1), val(requestTag, RTag, T), ETag = RTag, demanding(E, T+1), wantsFetch(E, T+1).
failType(allocateDemandWrong, T+1) :- live(T), live(T+1), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 1, roomForDemand(T), not allocateDemandHolds(T), not allocateDemandCreated(T).
allocatePrefetchAny2(X1, T) :- gtime(T), entryId(X1), wantsFetch(X1, T).
allocatePrefetchAny2(X1, T) :- gtime(T), entryId(X1), inFlight(X1, T).
boundary(eq(X1Address2, RAddress2), 1) :- entryAddress(X1, X1Address2, T), val(requestAddress, RAddress2, T).
allocatePrefetchFound2(T) :- gtime(T), entryExists(X1, T), allocatePrefetchAny2(X1, T), entryAddress(X1, X1Address2, T), val(requestAddress, RAddress2, T), pval(eq(X1Address2, RAddress2), 1).
allocatePrefetchHolds(T) :- gtime(T), allocatePrefetchFound2(T).
failType(allocatePrefetchWrong, T) :- live(T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 0, roomForPrefetch(T), not allocatePrefetchHolds(T), not val(requestReady, 1, T).
allocatePrefetchCreated(T) :- gtime(T), entryId(E), not entryExists(E, T), entryExists(E, T+1), entryAddress(E, EAddress, T+1), val(requestAddress, RAddress3, T), EAddress = RAddress3, wantsFetch(E, T+1).
failType(allocatePrefetchWrong, T+1) :- live(T), live(T+1), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 0, roomForPrefetch(T), not allocatePrefetchHolds(T), not allocatePrefetchCreated(T).
liftPrefetchToDemandAny(E, T) :- gtime(T), entryId(E), wantsFetch(E, T).
liftPrefetchToDemandAny(E, T) :- gtime(T), entryId(E), inFlight(E, T).
liftPrefetchToDemandHolds(E, T) :- gtime(T), entryId(E), demanding(E, T).
boundary(eq(EAddress, RAddress), 1) :- entryAddress(E, EAddress, T), val(requestAddress, RAddress, T).
failType(liftPrefetchToDemandWrong, T) :- live(T), entryExists(E, T), liftPrefetchToDemandAny(E, T), not liftPrefetchToDemandHolds(E, T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 1, entryAddress(E, EAddress, T), val(requestAddress, RAddress, T), pval(eq(EAddress, RAddress), 1), not val(requestReady, 1, T).
liftPrefetchToDemandDid(E, T) :- gtime(T), entryId(E), demanding(E, T+1).
failType(liftPrefetchToDemandWrong, T+1) :- live(T), live(T+1), entryExists(E, T), liftPrefetchToDemandAny(E, T), not liftPrefetchToDemandHolds(E, T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 1, entryAddress(E, EAddress, T), val(requestAddress, RAddress, T), pval(eq(EAddress, RAddress), 1), not liftPrefetchToDemandDid(E, T).
liftPrefetchToDemandDid2(E, T) :- gtime(T), entryId(E), entryTag(E, ETag, T+1), val(requestTag, RTag, T), ETag = RTag.
failType(liftPrefetchToDemandWrong, T+1) :- live(T), live(T+1), entryExists(E, T), liftPrefetchToDemandAny(E, T), not liftPrefetchToDemandHolds(E, T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 1, entryAddress(E, EAddress, T), val(requestAddress, RAddress, T), pval(eq(EAddress, RAddress), 1), not liftPrefetchToDemandDid2(E, T).
mergePrefetchAny(X1, T) :- gtime(T), entryId(X1), wantsFetch(X1, T).
mergePrefetchAny(X1, T) :- gtime(T), entryId(X1), inFlight(X1, T).
boundary(eq(X1Address, RAddress), 1) :- entryAddress(X1, X1Address, T), val(requestAddress, RAddress, T).
mergePrefetchFound(T) :- gtime(T), entryExists(X1, T), mergePrefetchAny(X1, T), entryAddress(X1, X1Address, T), val(requestAddress, RAddress, T), pval(eq(X1Address, RAddress), 1).
failType(mergePrefetchWrong, T) :- live(T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 0, mergePrefetchFound(T), not val(requestReady, 1, T).
stallRepeatDemandAny(X1, T) :- gtime(T), entryId(X1), wantsFetch(X1, T).
stallRepeatDemandAny(X1, T) :- gtime(T), entryId(X1), inFlight(X1, T).
boundary(eq(X1Address, RAddress), 1) :- entryAddress(X1, X1Address, T), val(requestAddress, RAddress, T).
stallRepeatDemandFound(T) :- gtime(T), entryExists(X1, T), stallRepeatDemandAny(X1, T), demanding(X1, T), entryAddress(X1, X1Address, T), val(requestAddress, RAddress, T), pval(eq(X1Address, RAddress), 1).
failType(stallRepeatDemandWrong, T) :- live(T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 1, stallRepeatDemandFound(T), not val(fetchStall, 1, T).
failType(stallRepeatDemandWrong, T) :- live(T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 1, stallRepeatDemandFound(T), not val(requestReady, 0, T).
requestReadyDemandAny2(X1, T) :- gtime(T), entryId(X1), wantsFetch(X1, T).
requestReadyDemandAny2(X1, T) :- gtime(T), entryId(X1), inFlight(X1, T).
boundary(eq(X1Address2, RAddress2), 1) :- entryAddress(X1, X1Address2, T), val(requestAddress, RAddress2, T).
requestReadyDemandFound2(T) :- gtime(T), entryExists(X1, T), requestReadyDemandAny2(X1, T), demanding(X1, T), entryAddress(X1, X1Address2, T), val(requestAddress, RAddress2, T), pval(eq(X1Address2, RAddress2), 1).
requestReadyDemandHolds(T) :- gtime(T), val(requestIsDemand, RIsDemand3, T), RIsDemand3 = 1, requestReadyDemandFound2(T).
requestReadyDemandAny4(X1, T) :- gtime(T), entryId(X1), wantsFetch(X1, T).
requestReadyDemandAny4(X1, T) :- gtime(T), entryId(X1), inFlight(X1, T).
boundary(eq(X1Address3, RAddress3), 1) :- entryAddress(X1, X1Address3, T), val(requestAddress, RAddress3, T).
requestReadyDemandFound3(T) :- gtime(T), entryExists(X1, T), requestReadyDemandAny4(X1, T), entryAddress(X1, X1Address3, T), val(requestAddress, RAddress3, T), pval(eq(X1Address3, RAddress3), 1).
requestReadyDemandAny3(T) :- gtime(T), requestReadyDemandFound3(T).
requestReadyDemandAny3(T) :- gtime(T), roomForDemand(T).
failType(requestReadyDemandWrong, T) :- live(T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 1, not requestReadyDemandHolds(T), requestReadyDemandAny3(T), not val(requestReady, 1, T).
requestReadyDemandOnlyAny2(X1, T) :- gtime(T), entryId(X1), wantsFetch(X1, T).
requestReadyDemandOnlyAny2(X1, T) :- gtime(T), entryId(X1), inFlight(X1, T).
boundary(eq(X1Address2, RAddress2), 1) :- entryAddress(X1, X1Address2, T), val(requestAddress, RAddress2, T).
requestReadyDemandOnlyFound2(T) :- gtime(T), entryExists(X1, T), requestReadyDemandOnlyAny2(X1, T), demanding(X1, T), entryAddress(X1, X1Address2, T), val(requestAddress, RAddress2, T), pval(eq(X1Address2, RAddress2), 1).
requestReadyDemandOnlyHolds2(T) :- gtime(T), val(requestIsDemand, RIsDemand3, T), RIsDemand3 = 1, requestReadyDemandOnlyFound2(T).
requestReadyDemandOnlyAny4(X1, T) :- gtime(T), entryId(X1), wantsFetch(X1, T).
requestReadyDemandOnlyAny4(X1, T) :- gtime(T), entryId(X1), inFlight(X1, T).
boundary(eq(X1Address3, RAddress3), 1) :- entryAddress(X1, X1Address3, T), val(requestAddress, RAddress3, T).
requestReadyDemandOnlyFound3(T) :- gtime(T), entryExists(X1, T), requestReadyDemandOnlyAny4(X1, T), entryAddress(X1, X1Address3, T), val(requestAddress, RAddress3, T), pval(eq(X1Address3, RAddress3), 1).
requestReadyDemandOnlyAny3(T) :- gtime(T), requestReadyDemandOnlyFound3(T).
requestReadyDemandOnlyAny3(T) :- gtime(T), roomForDemand(T).
requestReadyDemandOnlyHolds(T) :- gtime(T), not requestReadyDemandOnlyHolds2(T), requestReadyDemandOnlyAny3(T).
failType(requestReadyDemandOnly, T) :- live(T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 1, val(requestReady, 1, T), not requestReadyDemandOnlyHolds(T).
requestReadyPrefetchAny2(X2, T) :- gtime(T), entryId(X2), wantsFetch(X2, T).
requestReadyPrefetchAny2(X2, T) :- gtime(T), entryId(X2), inFlight(X2, T).
boundary(eq(X2Address, RAddress), 1) :- entryAddress(X2, X2Address, T), val(requestAddress, RAddress, T).
requestReadyPrefetchFound(T) :- gtime(T), entryExists(X2, T), requestReadyPrefetchAny2(X2, T), entryAddress(X2, X2Address, T), val(requestAddress, RAddress, T), pval(eq(X2Address, RAddress), 1).
requestReadyPrefetchAny(T) :- gtime(T), requestReadyPrefetchFound(T).
requestReadyPrefetchAny(T) :- gtime(T), roomForPrefetch(T).
failType(requestReadyPrefetchWrong, T) :- live(T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 0, requestReadyPrefetchAny(T), not val(requestReady, 1, T).
requestReadyPrefetchOnlyAny2(X2, T) :- gtime(T), entryId(X2), wantsFetch(X2, T).
requestReadyPrefetchOnlyAny2(X2, T) :- gtime(T), entryId(X2), inFlight(X2, T).
boundary(eq(X2Address, RAddress), 1) :- entryAddress(X2, X2Address, T), val(requestAddress, RAddress, T).
requestReadyPrefetchOnlyFound(T) :- gtime(T), entryExists(X2, T), requestReadyPrefetchOnlyAny2(X2, T), entryAddress(X2, X2Address, T), val(requestAddress, RAddress, T), pval(eq(X2Address, RAddress), 1).
requestReadyPrefetchOnlyAny(T) :- gtime(T), requestReadyPrefetchOnlyFound(T).
requestReadyPrefetchOnlyAny(T) :- gtime(T), roomForPrefetch(T).
requestReadyPrefetchOnlyHolds(T) :- gtime(T), requestReadyPrefetchOnlyAny(T).
failType(requestReadyPrefetchOnly, T) :- live(T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 0, val(requestReady, 1, T), not requestReadyPrefetchOnlyHolds(T).
askMemoryFound2(T) :- gtime(T), entryExists(X1, T), demanding(X1, T), wantsFetch(X1, T).
askMemoryHolds(T) :- gtime(T), askMemoryFound2(T).
askMemoryAny(E, T) :- gtime(T), entryId(E), demanding(E, T).
askMemoryAny(E, T) :- gtime(T), entryId(E), not askMemoryHolds(T).
askMemoryWanted(T) :- gtime(T), entryExists(E, T), wantsFetch(E, T), askMemoryAny(E, T), fetchLimitAllows(T).
askMemoryDid(E, T) :- gtime(T), entryAddress(E, EAddress, T), val(memoryRequestValid, 1, T), val(memoryRequestAddress, EAddress, T).
askMemoryServed(T) :- gtime(T), entryExists(E, T), wantsFetch(E, T), askMemoryAny(E, T), fetchLimitAllows(T), askMemoryDid(E, T).
failType(askMemoryWrong, T) :- live(T), askMemoryWanted(T), not askMemoryServed(T).
boundary(eq(EAddress, A), 1) :- entryAddress(E, EAddress, T), val(memoryRequestAddress, A, T).
enquiryTakenHolds(E, T) :- gtime(T), entryId(E), wantsFetch(E, T).
enquiryTakenDid(E, T) :- gtime(T), entryId(E), not enquiryTakenHolds(E, T+1), inFlight(E, T+1).
failType(enquiryTakenWrong, T+1) :- live(T), live(T+1), val(memoryRequestValid, 1, T), val(memoryRequestReady, 1, T), entryExists(E, T), wantsFetch(E, T), entryAddress(E, EAddress, T), val(memoryRequestAddress, A, T), pval(eq(EAddress, A), 1), not enquiryTakenDid(E, T).
boundary(eq(EAddress, FAddress), 1) :- entryAddress(E, EAddress, T), val(fillAddress, FAddress, T).
receiveFillHolds(E, T) :- gtime(T), entryId(E), inFlight(E, T).
receiveFillDid(E, T) :- gtime(T), entryId(E), filled(E, T+1), not receiveFillHolds(E, T+1), lineData(E, LineData, T+1), val(fillData, FData, T), LineData = FData.
failType(receiveFillWrong, T+1) :- live(T), live(T+1), val(fillValid, 1, T), entryExists(E, T), inFlight(E, T), entryAddress(E, EAddress, T), val(fillAddress, FAddress, T), pval(eq(EAddress, FAddress), 1), not receiveFillDid(E, T).
forwardDemandFound(T) :- gtime(T), entryExists(X1, T), filled(X1, T), demanding(X1, T).
forwardDemandCandidates(T) :- gtime(T), entryExists(E, T), filled(E, T), demanding(E, T).
forwardDemandDid(E, T) :- gtime(T), val(forwardValid, 1, T), forwarded(E, T), entryTag(E, ETag, T), val(forwardTag, ETag, T), lineData(E, LineData, T), val(forwardData, LineData, T).
failType(forwardDemandWrong, T) :- live(T), forwardDemandFound(T), entryId(E), forwarded(E, T), not forwardDemandDid(E, T).
forwardDemandHolds(E, T) :- gtime(T), entryId(E), entryExists(E, T).
forwardDemandDid2(E, T) :- gtime(T), entryId(E), not forwardDemandHolds(E, T+1).
failType(forwardDemandWrong, T+1) :- live(T), live(T+1), forwardDemandFound(T), entryId(E), forwarded(E, T), not forwardDemandDid2(E, T).
forwardDemandFulfilled(T) :- gtime(T), entryExists(E, T), filled(E, T), demanding(E, T), forwarded(E, T), forwardDemandDid(E, T), forwardDemandDid2(E, T).
failType(forwardDemandWrong, T) :- live(T), forwardDemandFound(T), forwardDemandCandidates(T), not forwardDemandFulfilled(T).
failType(forwardDemandWrong, T) :- live(T), entryId(E), entryId(E2), forwarded(E, T), forwarded(E2, T), E != E2.
finishPrefetchHolds(E, T) :- gtime(T), entryId(E), demanding(E, T).
finishPrefetchHolds2(E, T) :- gtime(T), entryId(E), entryExists(E, T).
finishPrefetchDid(E, T) :- gtime(T), entryId(E), not finishPrefetchHolds2(E, T+1).
failType(finishPrefetchWrong, T+1) :- live(T), live(T+1), entryExists(E, T), filled(E, T), not finishPrefetchHolds(E, T), entryExists(E, T), not finishPrefetchDid(E, T).
redirectHolds(X1, T) :- gtime(T), entryId(X1), demanding(X1, T).
redirectDid(X1, T) :- gtime(T), entryId(X1), not redirectHolds(X1, T+1).
failType(redirectWrong, T+1) :- live(T), live(T+1), val(redirectValid, 1, T), entryExists(X1, T), demanding(X1, T), not redirectDid(X1, T).
demandForwardedAfterFillHolds2(E, T) :- gtime(T), K = 1..depth, entryId(E), demanding(E, T).
demandForwardedAfterFillAny2(E, T) :- gtime(T), K = 1..depth, entryId(E), entryExists(E, T), forwarded(E, T).
demandForwardedAfterFillAny2(E, T) :- gtime(T), K = 1..depth, entryId(E), not demandForwardedAfterFillHolds2(E, T).
demandForwardedAfterFillHolds3(E, T) :- gtime(T), K = 1..depth, entryId(E), entryExists(E, T).
demandForwardedAfterFillAny(E, T) :- gtime(T), K = 1..depth, entryId(E), demandForwardedAfterFillAny2(E, T).
demandForwardedAfterFillAny(E, T) :- gtime(T), K = 1..depth, entryId(E), not demandForwardedAfterFillHolds3(E, T).
demandForwardedAfterFillHolds(E, T) :- gtime(T), K = 1..depth, gtime(T+K), entryExists(E, T), demandForwardedAfterFillAny(E, T+K).
failType(demandForwardedAfterFill, T+depth) :- live(T), live(T+depth), entryExists(E, T), entryExists(E, T), filled(E, T), demanding(E, T), not demandForwardedAfterFillHolds(E, T).
entryPhasesDoNotOverlapHolds2(E, T) :- gtime(T), entryId(E), wantsFetch(E, T), inFlight(E, T).
entryPhasesDoNotOverlapHolds3(E, T) :- gtime(T), entryId(E), wantsFetch(E, T), filled(E, T).
entryPhasesDoNotOverlapHolds4(E, T) :- gtime(T), entryId(E), inFlight(E, T), filled(E, T).
entryPhasesDoNotOverlapHolds(E, T) :- gtime(T), entryExists(E, T), not entryPhasesDoNotOverlapHolds2(E, T), not entryPhasesDoNotOverlapHolds3(E, T), not entryPhasesDoNotOverlapHolds4(E, T).
failType(entryPhasesDoNotOverlap, T) :- live(T), entryExists(E, T), entryExists(E, T), not entryPhasesDoNotOverlapHolds(E, T).
fetchDoesNotRestartHolds2(E, T) :- gtime(T), entryId(E), wantsFetch(E, T).
fetchDoesNotRestartHolds3(E, T) :- gtime(T), entryId(E), entryExists(E, T).
fetchDoesNotRestartHolds4(E, T) :- gtime(T), entryId(E), wantsFetch(E, T).
fetchDoesNotRestartAny(E, T) :- gtime(T), entryId(E), not fetchDoesNotRestartHolds3(E, T).
fetchDoesNotRestartAny(E, T) :- gtime(T), entryId(E), not fetchDoesNotRestartHolds4(E, T).
fetchDoesNotRestartHolds(E, T) :- gtime(T), gtime(T+1), entryExists(E, T), fetchDoesNotRestartAny(E, T+1).
failType(fetchDoesNotRestart, T+1) :- live(T), live(T+1), entryExists(E, T), entryExists(E, T), not fetchDoesNotRestartHolds2(E, T), not fetchDoesNotRestartHolds(E, T).
forwardedEntryIsFreedHolds2(E, T) :- gtime(T), entryId(E), entryExists(E, T).
forwardedEntryIsFreedFound(T) :- gtime(T), entryExists(E, T), corresponds(D, E, T), not forwardedEntryIsFreedHolds2(E, T+1).
forwardedEntryIsFreedHolds3(E, T) :- gtime(T), entryId(E), entryExists(E, T).
forwardedEntryIsFreedBody(E, T) :- gtime(T), entryId(E), not forwardedEntryIsFreedHolds3(E, T+1).
forwardedEntryIsFreedCounterex(T) :- gtime(T), entryExists(E, T), corresponds(D, E, T), not forwardedEntryIsFreedBody(E, T).
forwardedEntryIsFreedHolds(T) :- gtime(T), not forwardedEntryIsFreedCounterex(T).
failType(forwardedEntryIsFreed, T) :- live(T), val(forwardValid, 1, T), not forwardedEntryIsFreedHolds(T).
forwardIsRealOne(T) :- gtime(T), entryExists(E, T), corresponds(D, E, T), filled(E, T), demanding(E, T).
forwardIsRealTwo(T) :- gtime(T), entryExists(E, T), corresponds(D, E, T), filled(E, T), demanding(E, T), entryExists(E2, T), corresponds(D, E2, T), filled(E2, T), demanding(E2, T), E != E2.
forwardIsRealHolds(T) :- gtime(T), forwardIsRealOne(T), not forwardIsRealTwo(T).
failType(forwardIsReal, T) :- live(T), val(forwardValid, 1, T), not forwardIsRealHolds(T).
boundary(eq(DTag, ETag), 1) :- val(forwardTag, DTag, T), entryTag(E, ETag, T).
boundary(eq(DData, LineData), 1) :- val(forwardData, DData, T), lineData(E, LineData, T).
forwardIsCorrectFound(T) :- gtime(T), entryExists(E, T), corresponds(D, E, T), val(forwardTag, DTag, T), entryTag(E, ETag, T), pval(eq(DTag, ETag), 1), val(forwardData, DData, T), lineData(E, LineData, T), pval(eq(DData, LineData), 1).
boundary(eq(DTag2, ETag2), 1) :- val(forwardTag, DTag2, T), entryTag(E, ETag2, T).
boundary(eq(DData2, LineData2), 1) :- val(forwardData, DData2, T), lineData(E, LineData2, T).
forwardIsCorrectBody(E, T) :- gtime(T), entryId(E), val(forwardTag, DTag2, T), entryTag(E, ETag2, T), pval(eq(DTag2, ETag2), 1), val(forwardData, DData2, T), lineData(E, LineData2, T), pval(eq(DData2, LineData2), 1).
forwardIsCorrectCounterex(T) :- gtime(T), entryExists(E, T), corresponds(D, E, T), not forwardIsCorrectBody(E, T).
forwardIsCorrectHolds(T) :- gtime(T), not forwardIsCorrectCounterex(T).
failType(forwardIsCorrect, T) :- live(T), val(forwardValid, 1, T), not forwardIsCorrectHolds(T).
oneEntryPerLineAny(E, T) :- gtime(T), entryId(E), wantsFetch(E, T).
oneEntryPerLineAny(E, T) :- gtime(T), entryId(E), inFlight(E, T).
oneEntryPerLineAny2(P, T) :- gtime(T), entryId(P), wantsFetch(P, T).
oneEntryPerLineAny2(P, T) :- gtime(T), entryId(P), inFlight(P, T).
boundary(eq(EAddress, PAddress), 1) :- entryAddress(E, EAddress, T), entryAddress(P, PAddress, T).
oneEntryPerLineHolds(E, P, T) :- gtime(T), entryExists(E, T), entryExists(P, T), entryAddress(E, EAddress, T), entryAddress(P, PAddress, T), pval(eq(EAddress, PAddress), 0).
failType(oneEntryPerLine, T) :- live(T), entryExists(E, T), entryExists(P, T), E != P, oneEntryPerLineAny(E, T), oneEntryPerLineAny2(P, T), not oneEntryPerLineHolds(E, P, T).
boundary(eq(X1Address, A), 1) :- entryAddress(X1, X1Address, T), val(memoryRequestAddress, A, T).
fetchIsRealFound(T) :- gtime(T), entryExists(X1, T), wantsFetch(X1, T), entryAddress(X1, X1Address, T), val(memoryRequestAddress, A, T), pval(eq(X1Address, A), 1).
fetchIsRealHolds(T) :- gtime(T), fetchIsRealFound(T).
failType(fetchIsReal, T) :- live(T), val(memoryRequestValid, 1, T), val(memoryRequestReady, 1, T), not fetchIsRealHolds(T).
demandFirstFound(T) :- gtime(T), entryExists(U, T), demanding(U, T), wantsFetch(U, T).
boundary(eq(EAddress, A), 1) :- entryAddress(E, EAddress, T), val(memoryRequestAddress, A, T).
demandFirstFound2(T) :- gtime(T), entryExists(E, T), entryAddress(E, EAddress, T), val(memoryRequestAddress, A, T), pval(eq(EAddress, A), 1), demanding(E, T).
demandFirstHolds(T) :- gtime(T), demandFirstFound2(T).
failType(demandFirst, T) :- live(T), val(memoryRequestValid, 1, T), demandFirstFound(T), not demandFirstHolds(T).
fetchLimitHeldHolds(T) :- gtime(T), inFlightCount(InFlightCount, T), InFlightCount <= maxOutstandingFetches.
failType(fetchLimitHeld, T) :- live(T), not fetchLimitHeldHolds(T).
neverOverfilledHolds(T) :- gtime(T), liveEntries(LiveEntries, T), LiveEntries <= depth.
failType(neverOverfilled, T) :- live(T), not neverOverfilledHolds(T).
demandAlwaysHasRoomAny2(X1, T) :- gtime(T), entryId(X1), wantsFetch(X1, T).
demandAlwaysHasRoomAny2(X1, T) :- gtime(T), entryId(X1), inFlight(X1, T).
boundary(eq(X1Address2, RAddress2), 1) :- entryAddress(X1, X1Address2, T), val(requestAddress, RAddress2, T).
demandAlwaysHasRoomFound2(T) :- gtime(T), entryExists(X1, T), demandAlwaysHasRoomAny2(X1, T), demanding(X1, T), entryAddress(X1, X1Address2, T), val(requestAddress, RAddress2, T), pval(eq(X1Address2, RAddress2), 1).
demandAlwaysHasRoomHolds2(T) :- gtime(T), val(requestIsDemand, RIsDemand3, T), RIsDemand3 = 1, demandAlwaysHasRoomFound2(T).
demandAlwaysHasRoomHolds(T) :- gtime(T), val(requestReady, 1, T).
failType(demandAlwaysHasRoom, T) :- live(T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 1, not demandAlwaysHasRoomHolds2(T), liveEntries(LiveEntries, T), LiveEntries <= (depth - demandReserve), not demandAlwaysHasRoomHolds(T).
prefetchIsNeverForwardedFound(T) :- gtime(T), entryExists(E, T), corresponds(D, E, T), demanding(E, T).
prefetchIsNeverForwardedBody(E, T) :- gtime(T), entryId(E), demanding(E, T).
prefetchIsNeverForwardedCounterex(T) :- gtime(T), entryExists(E, T), corresponds(D, E, T), not prefetchIsNeverForwardedBody(E, T).
prefetchIsNeverForwardedHolds(T) :- gtime(T), not prefetchIsNeverForwardedCounterex(T).
failType(prefetchIsNeverForwarded, T) :- live(T), val(forwardValid, 1, T), not prefetchIsNeverForwardedHolds(T).
quietUnderResetHolds(T) :- gtime(T), not val(memoryRequestValid, 1, T), not val(forwardValid, 1, T), not val(fetchStall, 1, T).
failType(quietUnderReset, T) :- gtime(T), not val(resetN, 1, T), not quietUnderResetHolds(T).
emptyUnderResetHolds(T) :- gtime(T), liveEntries(LiveEntries, T), LiveEntries = 0, inFlightCount(InFlightCount, T), InFlightCount = 0.
failType(emptyUnderReset, T) :- gtime(T), not val(resetN, 1, T), not emptyUnderResetHolds(T).
demandLiftsAPrefetchAny(E, T) :- gtime(T), entryId(E), wantsFetch(E, T).
demandLiftsAPrefetchAny(E, T) :- gtime(T), entryId(E), inFlight(E, T).
demandLiftsAPrefetchHolds(E, T) :- gtime(T), entryId(E), demanding(E, T).
boundary(eq(RAddress, EAddress), 1) :- val(requestAddress, RAddress, T), entryAddress(E, EAddress, T).
holds(demandLiftsAPrefetchS, T) :- gtime(T), entryExists(E, T), demandLiftsAPrefetchAny(E, T), not demandLiftsAPrefetchHolds(E, T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 1, val(requestAddress, RAddress, T), entryAddress(E, EAddress, T), pval(eq(RAddress, EAddress), 1).
boundary(eq(ETag, RTag), 1) :- entryTag(E, ETag, 1), val(requestTag, RTag, T).
did(demandLiftsAPrefetchD) :- entryExists(E, 0), demandLiftsAPrefetchAny(E, 0), not demandLiftsAPrefetchHolds(E, 0), val(requestValid, 1, 0), val(requestIsDemand, RIsDemand, 0), RIsDemand = 1, val(requestAddress, RAddress, 0), entryAddress(E, EAddress, 0), pval(eq(RAddress, EAddress), 1), entryExists(E, 1), demanding(E, 1), entryTag(E, ETag, 1), val(requestTag, RTag, T), pval(eq(ETag, RTag), 1).
scenario(demandLiftsAPrefetch, demandLiftsAPrefetchS, any_input, demandLiftsAPrefetchD).
prefetchMergesIntoDemandAny(E, T) :- gtime(T), entryId(E), wantsFetch(E, T).
prefetchMergesIntoDemandAny(E, T) :- gtime(T), entryId(E), inFlight(E, T).
boundary(eq(RAddress, EAddress), 1) :- val(requestAddress, RAddress, T), entryAddress(E, EAddress, T).
holds(prefetchMergesIntoDemandS, T) :- gtime(T), entryExists(E, T), prefetchMergesIntoDemandAny(E, T), demanding(E, T), not val(redirectValid, 1, T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 0, val(requestAddress, RAddress, T), entryAddress(E, EAddress, T), pval(eq(RAddress, EAddress), 1).
did(prefetchMergesIntoDemandD) :- entryExists(E, 0), prefetchMergesIntoDemandAny(E, 0), demanding(E, 0), not val(redirectValid, 1, 0), val(requestValid, 1, 0), val(requestIsDemand, RIsDemand, 0), RIsDemand = 0, val(requestAddress, RAddress, 0), entryAddress(E, EAddress, 0), pval(eq(RAddress, EAddress), 1), entryExists(E, 1), demanding(E, 1).
scenario(prefetchMergesIntoDemand, prefetchMergesIntoDemandS, any_input, prefetchMergesIntoDemandD).
demandBeatsPrefetchHolds(P, T) :- gtime(T), entryId(P), demanding(P, T).
holds(demandBeatsPrefetchS, T) :- gtime(T), entryExists(P, T), entryExists(D, T), not demandBeatsPrefetchHolds(P, T), wantsFetch(P, T), demanding(D, T), wantsFetch(D, T), fetchLimitAllows(T).
did(demandBeatsPrefetchD) :- entryExists(P, 0), entryExists(D, 0), not demandBeatsPrefetchHolds(P, 0), wantsFetch(P, 0), demanding(D, 0), wantsFetch(D, 0), fetchLimitAllows(0), val(memoryRequestValid, 1, 0), entryAddress(D, DAddress, 0), val(memoryRequestAddress, DAddress, 0).
scenario(demandBeatsPrefetch, demandBeatsPrefetchS, any_input, demandBeatsPrefetchD).
prefetchRefusedAtReserveAny2(X1, T) :- gtime(T), entryId(X1), wantsFetch(X1, T).
prefetchRefusedAtReserveAny2(X1, T) :- gtime(T), entryId(X1), inFlight(X1, T).
boundary(eq(X1Address2, RAddress2), 1) :- entryAddress(X1, X1Address2, T), val(requestAddress, RAddress2, T).
prefetchRefusedAtReserveFound2(T) :- gtime(T), entryExists(X1, T), prefetchRefusedAtReserveAny2(X1, T), entryAddress(X1, X1Address2, T), val(requestAddress, RAddress2, T), pval(eq(X1Address2, RAddress2), 1).
prefetchRefusedAtReserveHolds(T) :- gtime(T), prefetchRefusedAtReserveFound2(T).
holds(prefetchRefusedAtReserveS, T) :- gtime(T), liveEntries(LiveEntries, T), LiveEntries = (depth - demandReserve), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 0, not prefetchRefusedAtReserveHolds(T).
prefetchRefusedAtReserveHolds2(T) :- gtime(T), val(requestValid, 1, T), val(requestReady, 1, T).
did(prefetchRefusedAtReserveD) :- liveEntries(LiveEntries, 0), LiveEntries = (depth - demandReserve), val(requestValid, 1, 0), val(requestIsDemand, RIsDemand, 0), RIsDemand = 0, not prefetchRefusedAtReserveHolds(0), not prefetchRefusedAtReserveHolds2(0).
scenario(prefetchRefusedAtReserve, prefetchRefusedAtReserveS, any_input, prefetchRefusedAtReserveD).
repeatDemandStallsAny(X1, T) :- gtime(T), entryId(X1), wantsFetch(X1, T).
repeatDemandStallsAny(X1, T) :- gtime(T), entryId(X1), inFlight(X1, T).
boundary(eq(X1Address, RAddress), 1) :- entryAddress(X1, X1Address, T), val(requestAddress, RAddress, T).
repeatDemandStallsFound(T) :- gtime(T), entryExists(X1, T), repeatDemandStallsAny(X1, T), demanding(X1, T), entryAddress(X1, X1Address, T), val(requestAddress, RAddress, T), pval(eq(X1Address, RAddress), 1).
holds(repeatDemandStallsS, T) :- gtime(T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 1, repeatDemandStallsFound(T).
did(repeatDemandStallsD) :- val(requestValid, 1, 0), val(requestIsDemand, RIsDemand, 0), RIsDemand = 1, repeatDemandStallsFound(0), val(fetchStall, 1, 0).
scenario(repeatDemandStalls, repeatDemandStallsS, any_input, repeatDemandStallsD).
mayDemandingClear(E, T) :- gtime(T), entryId(E), val(redirectValid, 1, T), entryExists(X1, T), demanding(X1, T).
failType(demandingDisturbed, T+1) :- live(T), live(T+1), entryExists(E, T), entryExists(E, T+1), demanding(E, T), not mayDemandingClear(E, T), not demanding(E, T+1).
mayDemandingSet(E, T) :- gtime(T), entryId(E), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 1, roomForDemand(T), not allocateDemandHolds(T).
mayDemandingSet(E, T) :- gtime(T), entryId(E), entryExists(E, T), liftPrefetchToDemandAny(E, T), not liftPrefetchToDemandHolds(E, T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 1, entryAddress(E, EAddress, T), val(requestAddress, RAddress, T), pval(eq(EAddress, RAddress), 1).
failType(demandingDisturbed, T+1) :- live(T), live(T+1), entryExists(E, T), entryExists(E, T+1), not demanding(E, T), not mayDemandingSet(E, T), demanding(E, T+1).
failType(filledDisturbed, T+1) :- live(T), live(T+1), entryExists(E, T), entryExists(E, T+1), filled(E, T), not mayFilledClear(E, T), not filled(E, T+1).
mayFilledSet(E, T) :- gtime(T), entryId(E), val(fillValid, 1, T), entryExists(E, T), inFlight(E, T), entryAddress(E, EAddress, T), val(fillAddress, FAddress, T), pval(eq(EAddress, FAddress), 1).
failType(filledDisturbed, T+1) :- live(T), live(T+1), entryExists(E, T), entryExists(E, T+1), not filled(E, T), not mayFilledSet(E, T), filled(E, T+1).
mayInFlightClear(E, T) :- gtime(T), entryId(E), val(fillValid, 1, T), entryExists(E, T), inFlight(E, T), entryAddress(E, EAddress, T), val(fillAddress, FAddress, T), pval(eq(EAddress, FAddress), 1).
failType(inFlightDisturbed, T+1) :- live(T), live(T+1), entryExists(E, T), entryExists(E, T+1), inFlight(E, T), not mayInFlightClear(E, T), not inFlight(E, T+1).
mayInFlightSet(E, T) :- gtime(T), entryId(E), val(memoryRequestValid, 1, T), val(memoryRequestReady, 1, T), entryExists(E, T), wantsFetch(E, T), entryAddress(E, EAddress, T), val(memoryRequestAddress, A, T), pval(eq(EAddress, A), 1).
failType(inFlightDisturbed, T+1) :- live(T), live(T+1), entryExists(E, T), entryExists(E, T+1), not inFlight(E, T), not mayInFlightSet(E, T), inFlight(E, T+1).
mayWantsFetchClear(E, T) :- gtime(T), entryId(E), val(memoryRequestValid, 1, T), val(memoryRequestReady, 1, T), entryExists(E, T), wantsFetch(E, T), entryAddress(E, EAddress, T), val(memoryRequestAddress, A, T), pval(eq(EAddress, A), 1).
failType(wantsFetchDisturbed, T+1) :- live(T), live(T+1), entryExists(E, T), entryExists(E, T+1), wantsFetch(E, T), not mayWantsFetchClear(E, T), not wantsFetch(E, T+1).
mayWantsFetchSet(E, T) :- gtime(T), entryId(E), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 1, roomForDemand(T), not allocateDemandHolds(T).
mayWantsFetchSet(E, T) :- gtime(T), entryId(E), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 0, roomForPrefetch(T), not allocatePrefetchHolds(T).
failType(wantsFetchDisturbed, T+1) :- live(T), live(T+1), entryExists(E, T), entryExists(E, T+1), not wantsFetch(E, T), not mayWantsFetchSet(E, T), wantsFetch(E, T+1).
mayEntryAddressWrite(E, T) :- gtime(T), entryId(E), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 1, roomForDemand(T), not allocateDemandHolds(T).
mayEntryAddressWrite(E, T) :- gtime(T), entryId(E), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 0, roomForPrefetch(T), not allocatePrefetchHolds(T).
failType(entryAddressDisturbed, T+1) :- live(T), live(T+1), entryExists(E, T), entryExists(E, T+1), entryAddress(E, V, T), not mayEntryAddressWrite(E, T), not entryAddress(E, V, T+1).
mayEntryTagWrite(E, T) :- gtime(T), entryId(E), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 1, roomForDemand(T), not allocateDemandHolds(T).
mayEntryTagWrite(E, T) :- gtime(T), entryId(E), entryExists(E, T), liftPrefetchToDemandAny(E, T), not liftPrefetchToDemandHolds(E, T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 1, entryAddress(E, EAddress, T), val(requestAddress, RAddress, T), pval(eq(EAddress, RAddress), 1).
failType(entryTagDisturbed, T+1) :- live(T), live(T+1), entryExists(E, T), entryExists(E, T+1), entryTag(E, V, T), not mayEntryTagWrite(E, T), not entryTag(E, V, T+1).
mayLineDataWrite(E, T) :- gtime(T), entryId(E), val(fillValid, 1, T), entryExists(E, T), inFlight(E, T), entryAddress(E, EAddress, T), val(fillAddress, FAddress, T), pval(eq(EAddress, FAddress), 1).
failType(lineDataDisturbed, T+1) :- live(T), live(T+1), entryExists(E, T), entryExists(E, T+1), lineData(E, V, T), not mayLineDataWrite(E, T), not lineData(E, V, T+1).
mayAllocate(T) :- gtime(T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 1, roomForDemand(T), not allocateDemandHolds(T).
mayAllocate(T) :- gtime(T), val(requestValid, 1, T), val(requestIsDemand, RIsDemand, T), RIsDemand = 0, roomForPrefetch(T), not allocatePrefetchHolds(T).
failType(entryAppeared, T+1) :- live(T), live(T+1), entryId(E), not entryExists(E, T), not mayAllocate(T), entryExists(E, T+1).
mayVanish(E, T) :- gtime(T), entryId(E), forwardDemandFound(T), entryId(E), forwarded(E, T).
mayVanish(E, T) :- gtime(T), entryId(E), entryExists(E, T), filled(E, T), not finishPrefetchHolds(E, T), entryExists(E, T).
failType(entryVanished, T+1) :- live(T), live(T+1), entryExists(E, T), not mayVanish(E, T), not entryExists(E, T+1).
failType(inFlightCountNotSingleValued, T) :- live(T), inFlightCount(A, T), inFlightCount(B, T), A != B.
failType(liveEntriesNotSingleValued, T) :- live(T), liveEntries(A, T), liveEntries(B, T), A != B.
failType(entryAddressNotSingleValued, T) :- live(T), entryAddress(K0, A, T), entryAddress(K0, B, T), A != B.
failType(entryTagNotSingleValued, T) :- live(T), entryTag(K0, A, T), entryTag(K0, B, T), A != B.
failType(lineDataNotSingleValued, T) :- live(T), lineData(K0, A, T), lineData(K0, B, T), A != B.
