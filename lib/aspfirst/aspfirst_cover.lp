% lib/aspfirst/aspfirst_cover.lp -- TOTALITY: does every wire have a value at every instant?
%
% A guarded combinational net whose arms miss a case is UNBOUND there (TRANSLATION_SPEC S3.3): a
% property over it can pass vacuously, and a printed `always_comb` would infer a latch where the
% ASP has no value. This companion REQUIRES a gap (the require-the-violation polarity, S5.1):
%   SATISFIABLE  = a counterexample -- `gap(Net, T)` names the wire and the instant;
%   UNSATISFIABLE = every wire is defined at every instant of the searched space.
% Run it with the inputs the arms are guarded on left FREE (a choice rule per input in the
% scenario), a reset asserted at T=0 and aspfirst_init0.lp composed, so the only possible gap is
% one the AUTHOR left. Property layer: the `not` here never enters the design.
gap(N, T) :- wire(N, _), not clock(N), gtime(T), not val(N, _, T).
:- not gap(_, _).
#show gap/2.
