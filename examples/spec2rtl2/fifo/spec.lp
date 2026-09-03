% spec2rtl2/fifo/spec.lp -- the FIFO contract, v2. THREE things and nothing else: the linked
% windows the level must mount (pointer_push/2, pointer_pop/2, cell_value/3 -- declared here,
% defined by each level's .inv), the PROPERTIES (one named bad per kind of wrongness, every one
% a port fact or a one-step relation over the windows), and the SCENARIOS (a constrained
% abstract start + one cycle + an expectation -- the anti-vacuity checks). No script exists and
% no event-driven referee: scripted walks were retired (the user, 2026-08-25 -- "if we have to
% run for 10 cycles on a large design, the whole point of the induction is lost"), and the
% referee only ever ran under a script. First-in-first-out is not asserted behaviourally
% anywhere: it is a THEOREM of the mechanism properties below (pointers advance in order +
% slots land and hold + the served value is the read pointer's slot), proven for all time by
% the induction. Vocabulary: wrap-bit pointers (P in 0..2*depth-1, address = P \ depth, wrap =
% P / depth); empty is pointer equality, full is "same address, opposite wrap".

% the SIZE parameter: the depth, overridable per instantiation (clingo -c depth=N). Every
% domain below derives from it: pointers live in 0..2*depth-1 (address = P \ depth, wrap bit =
% P / depth), full is Q = (P + depth) \ (2*depth). The name must not collide with any net of a
% level (the v1 lesson: a #const rewrites same-named symbols) -- `depth` is reserved.
#const depth = 4.

live(T) :- val(reset_n, 1, T).

% ---- port-only helper definitions (no state) ----------------------------------------------------
accepted_push(T) :- live(T), val(push, 1, T), val(full, 0, T).
served_pop(T)    :- live(T), val(pop, 1, T), val(empty, 0, T).

% ---- flags: pointer relations, not arithmetic  [empty_wrong, full_wrong, valid_wrong] -----------
bad(empty_wrong, T) :- live(T), pointer_push(P, T), pointer_pop(P, T), val(empty, 0, T).
bad(empty_wrong, T) :- live(T), pointer_push(P, T), pointer_pop(Q, T), P != Q, val(empty, 1, T).
bad(full_wrong, T)  :- live(T), pointer_push(P, T), pointer_pop(Q, T), Q = (P + depth) \ (2*depth),
                       val(full, 0, T).
bad(full_wrong, T)  :- live(T), pointer_push(P, T), pointer_pop(Q, T), Q != (P + depth) \ (2*depth),
                       val(full, 1, T).
bad(valid_wrong, T) :- live(T), val(valid_pop, V, T), val(empty, E, T), V + E != 1.

% ---- pointer discipline: successor on the event, hold otherwise  [pointer_*_wrong, reset_wrong] --
bad(pointer_push_wrong, T+1) :- accepted_push(T), live(T+1), pointer_push(P, T),
                                Q = (P + 1) \ (2*depth), not pointer_push(Q, T+1).
bad(pointer_push_wrong, T+1) :- live(T), live(T+1), not accepted_push(T), pointer_push(P, T),
                                not pointer_push(P, T+1).
bad(pointer_pop_wrong, T+1)  :- served_pop(T), live(T+1), pointer_pop(P, T),
                                Q = (P + 1) \ (2*depth), not pointer_pop(Q, T+1).
bad(pointer_pop_wrong, T+1)  :- live(T), live(T+1), not served_pop(T), pointer_pop(P, T),
                                not pointer_pop(P, T+1).
% under reset both pointers are 0, and still 0 on the release edge (nothing can have been
% accepted during reset -- accepted_push requires live)
bad(reset_wrong, T)   :- val(reset_n, 0, T), pointer_push(P, T), P != 0.
bad(reset_wrong, T)   :- val(reset_n, 0, T), pointer_pop(P, T), P != 0.
bad(reset_wrong, T+1) :- val(reset_n, 0, T), live(T+1), pointer_push(P, T+1), P != 0.
bad(reset_wrong, T+1) :- val(reset_n, 0, T), live(T+1), pointer_pop(P, T+1), P != 0.

% ---- storage: address-local relations  [push_landed_wrong, cell_disturbed, pop_value_wrong] -----
written(A, T) :- accepted_push(T), pointer_push(P, T), A = P \ depth.
bad(push_landed_wrong, T+1) :- accepted_push(T), live(T+1), pointer_push(P, T), A = P \ depth,
                               val(data_push, V, T), not cell_value(A, V, T+1).
bad(cell_disturbed, T+1)    :- live(T), live(T+1), cell_value(A, V, T), not written(A, T),
                               not cell_value(A, V, T+1).
bad(pop_value_wrong, T)     :- served_pop(T), pointer_pop(P, T), A = P \ depth, cell_value(A, V, T),
                               not val(data_pop, V, T).

% ---- scenarios (anti-vacuity, the v2 way -- the user's correction, 2026-08-25) ------------------
% NOT goals reached by walking a script there (on a deep design that walk costs what induction
% exists to avoid). A scenario is a CONSTRAINED ABSTRACT START plus one cycle: the machine is
% PLACED in the interesting state (compliant -- the properties are assumed, the same confinement
% as the step), the input applied, the step observed. Each is one solve over a 1..2-instant
% window; SAT = the situation is possible and the witness table shows the transition; UNSAT =
% the spec and design contradict there, loudly. Cost independent of depth and history.
% scenario(Name, State, Input, Expectation): the runner asserts State and Input at T=0 over a
% compliant abstract start (properties assumed), and CHECKS the Expectation -- the user's
% refinement: a scenario is a DIRECTED test of the natural operation, not a bare witness. At
% the boundaries the natural operation is the refusal; everywhere else it is acceptance/service,
% with the next-state effect where that is the point.
scenario(push_when_full,    is_full,     do_push, push_refused).
scenario(pop_when_full,     is_full,     do_pop,  pop_served_and_room).
scenario(push_when_empty,   is_empty,    do_push, push_accepted_and_nonempty).
scenario(pop_when_empty,    is_empty,    do_pop,  pop_refused).
scenario(one_entry_pop,     is_one,      do_pop,  pop_served_and_empty).
scenario(push_and_pop_mid,  is_mid,      do_both, both_happen).
scenario(push_at_wrap_edge, is_wrapedge, do_push, push_accepted_and_wrapped).
% the state constraints, over the LINKED vocabulary (compliant states only -- the properties
% are assumed at T=0 by the runner, so a full state here is a real full state)
holds(is_full, T)     :- pointer_push(P, T), pointer_pop(Q, T), Q = (P + depth) \ (2*depth).
holds(is_empty, T)    :- pointer_push(P, T), pointer_pop(P, T).
holds(is_one, T)      :- pointer_push(P, T), pointer_pop(Q, T), P = (Q + 1) \ (2*depth).
holds(is_mid, T)      :- pointer_push(P, T), pointer_pop(Q, T), P != Q, Q != (P + depth) \ (2*depth).
holds(is_wrapedge, T) :- pointer_push(depth - 1, T), pointer_pop(Q, T), Q != 2*depth - 1.   % next push sets the wrap
                                                                          % bit and may NOT fill
% the input constraints, over the ports
holds(do_push, T) :- val(push, 1, T), val(pop, 0, T).
holds(do_pop, T)  :- val(push, 0, T), val(pop, 1, T).
holds(do_both, T) :- val(push, 1, T), val(pop, 1, T).
% the expectations -- what the NATURAL OPERATION is, per scenario; `did(E)` must hold in the
% witness or the scenario FAILS (a machine refusing service in a mid state is caught here)
did(push_refused)              :- live(0), not accepted_push(0).
did(pop_refused)               :- live(0), not served_pop(0).
did(pop_served_and_room)       :- served_pop(0), val(full, 0, 1).
did(push_accepted_and_nonempty):- accepted_push(0), val(empty, 0, 1).
did(pop_served_and_empty)      :- served_pop(0), val(empty, 1, 1).
did(both_happen)               :- accepted_push(0), served_pop(0).
did(push_accepted_and_wrapped) :- accepted_push(0), pointer_push(depth, 1).
