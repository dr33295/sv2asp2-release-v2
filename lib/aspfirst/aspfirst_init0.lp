% lib/aspfirst/aspfirst_init0.lp -- CONCRETE power-on state for an ASP-first design: every UNRESET
% state element pinned to zero at T=0 (the twin of the translator's --init-zero / <top>__init0.lp).
%
% The design layer is the TRANSITION RELATION and carries no initial state (F4). A test wants one
% model, so this file names one -- zero, which is arbitrary and not what hardware does (an unreset
% register or uninitialised array reads x). It is therefore OPT-IN: compose it when you want a
% single concrete trace; leave it out to see exactly which values the reset defines. An `arff`
% is NOT pinned: its power-on value comes from asserting its reset at T=0, as the hardware's does.
% An ENUM-typed register's zero is the TAG whose value is 0 (val(state, idle, 0)), not the number:
% the design's rules read tags. (Found by the dataset's first entry: an enum `ff` with no reset had NO
% value at T=0 under this file -- loud as a totality failure, but wrong.)
enumq(Q) :- wire(Q, enum(_)).
val(Q, 0, 0)          :- inst(I, ff), pin(I, q, Q), not enumq(Q).
val(Q, L, 0)          :- inst(I, ff), pin(I, q, Q), wire(Q, enum(E)), enum_member(E, L, 0).
val(Q, 0, 0)          :- inst(I, lata), pin(I, en, EN), pin(I, q, Q), val(EN, 0, 0), not enumq(Q).   % only while opaque
val(Q, L, 0)          :- inst(I, lata), pin(I, en, EN), pin(I, q, Q), val(EN, 0, 0), wire(Q, enum(E)), enum_member(E, L, 0).
val(cell(M, A), 0, 0) :- inst(M, spram), addr(M, A).
% A `farray` too -- omitted when the cell was added, and invisible until a design used one WITHOUT a
% reset. `gshare`'s pht has one, so its cells come from the reset force and this rule was never
% missed; `am2901`'s register file has none, because the part has none, and every `mrd` read of it
% was dark from T=0 (loud as a totality failure, but the construct was unusable). The `rstL` guard
% keeps this file's own distinction rather than inventing one: an `ff` is pinned because it has no
% reset, an `arff` is not because its reset defines it, and a `farray` is whichever of those it is.
val(cell(M, A), 0, 0) :- inst(M, farray), addr(M, A), not pin(M, rstL, _).
