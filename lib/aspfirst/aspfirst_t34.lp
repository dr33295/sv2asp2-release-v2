% lib/aspfirst/aspfirst_t34.lp -- the SINGLE-VALUEDNESS guard for an ASP-first design (the twin of
% the translator's <top>__t34.lp). Property layer: a design whose rules give one signal two values
% in one instant is a defect (overlapping comb arms that disagree, two drivers of one net), and
% clingo would otherwise report the extra answer sets as if they were legitimate.
:- val(Sig, V1, T), val(Sig, V2, T), V1 != V2.
