% lib/aspfirst/aspfirst_symbolic.lp -- the SYMBOLIC reading: control in ASP, data as TERMS.
%
% Compose this (refine does, whenever the design declares a data/1 net) and every data net carries a
% symbolic term over the input tokens instead of an enumerated value: `in(a, 3)` for input `a` at
% instant 3, `add(in(a,3), in(b,3), 32)` for what was computed from it. Nothing about a data value
% is ever enumerated, so a 32-bit datapath grounds like a 1-bit one. The design file is unchanged
% (data(N) is a declaration); the library's @funcs return a term whenever a value argument is a
% term (the symbolic wrappers in the generated script), so registers, memories, muxes and
% arithmetic simply carry terms.
%
% Where data meets CONTROL -- a compare, a reduction, a bit, a narrow slice, a popcount -- is the
% BOUNDARY. If its value flows only into DATA (a mux arm, a data register), it stays a TERM (the lint's
% dat(E)): exact and linear. If it reaches control (an enable, a guard, a control output: the lint's
% bnd(E, W)), it is a FREE VALUE, one
% choice per DISTINCT argument term (not per instant: a predicate of a held value stays consistent
% while it is held), so every control proof under this reading holds for EVERY valuation of the
% boundary -- i.e. for all data. Syntactic identity is exact (eq(t, t) = 1) and the standard pairs
% are kept consistent; everything else about the data is left to the obligation exported to Lean
% (the CDS split, notes/design/ASP_FIRST_CDS_PLAN.md).
%
% A boundary-capable op in a DATA context (a slice of a word feeding more arithmetic; the lint's
% dat(E)) keeps its term. Concrete results (control operands) pass through in the library itself.
#defined data/1.  #defined bnd/2.  #defined dat/1.  #defined bres/3.

% ---- tokens: one fresh symbol per data input per instant --------------------------------------
val(N, in(N, T), T) :- data(N), port(N, input, _), gtime(T).

% ---- data-role results keep the term ---------------------------------------------------------
ev(E, P, T) :- bres(E, P, T), dat(E), @issym(P) = 1.

% ---- TERM MODE: a boundary that flows only into DATA keeps its term (the lint marks it dat), and the
% truth ops build the logical TERM when handed one -- so every net has ONE term per instant (linear),
% and a select bit that feeds back into a datapath (Booth's q0) does not fork the term family.
% through the base library's tv/4 truth table -- no @truth inside a candidate join (the same
% quadratic the base rules had; see the tv/4 comment there).
ev(logand(A, B), logand(VA, VB), T) :- term(logand(A, B)), tv(A, VA, TA, T), tv(B, VB, TB, T),
                                       TA != 0, TB != 0, TA + TB >= 3.
ev(logor(A, B), logor(VA, VB), T)   :- term(logor(A, B)),  tv(A, VA, TA, T), tv(B, VB, TB, T),
                                       TA != 1, TB != 1, TA + TB >= 2.
ev(lnot(A), lnot(VA), T)            :- term(lnot(A)), tv(A, VA, 2, T).
ev(ite(S, A, B), ite(VS, VA, VB), T) :- term(ite(S, A, B)), tv(S, VS, 2, T), ev(A, VA, T), ev(B, VB, T).

% ---- boundaries the SPEC depends on: `boundary(P, W)` -- a predicate of a data value the monitors read
% through pval(P, V). Freed per term here when its argument is a token (the concrete case, a number,
% is evaluated by the runner); the design's own computation of the same term shares the value.
#defined boundary/2.
bp(P, W) :- boundary(P, W), P = slc(A, _, _), @issym(A) = 1.
bp(P, W) :- boundary(P, W), P = bit(A, _), @issym(A) = 1.
bp(P, W) :- boundary(P, W), P = clz(A, _), @issym(A) = 1.
bp(P, W) :- boundary(P, W), P = eq(A, _), @issym(A) = 1.      bp(P, W) :- boundary(P, W), P = eq(_, B), @issym(B) = 1.
bp(P, W) :- boundary(P, W), P = ne(A, _), @issym(A) = 1.      bp(P, W) :- boundary(P, W), P = ne(_, B), @issym(B) = 1.
bp(P, W) :- boundary(P, W), P = lt(A, _, _), @issym(A) = 1.   bp(P, W) :- boundary(P, W), P = lt(_, B, _), @issym(B) = 1.
bp(P, W) :- boundary(P, W), P = ge(A, _, _), @issym(A) = 1.   bp(P, W) :- boundary(P, W), P = ge(_, B, _), @issym(B) = 1.

% ---- the boundary that reaches CONTROL: one free value per distinct term, over the result width ------
bp(P, W) :- bres(E, P, T), bnd(E, W), @issym(P) = 1.
{ pval(P, V) : V = 0..2**W-1 } = 1 :- bp(P, W).
ev(E, V, T) :- bres(E, P, T), bnd(E, _), @issym(P) = 1, pval(P, V).

% ---- what IS known about the boundary: identity, and the standard pairs -------------------------
% GENERATIVE symmetry (2026-08-28, the user's suggestion): whenever one orientation of a
% pair is a boundary, its mirror exists too -- the symmetry tie always binds, transitivity
% needs one spelling, and the gate-spelling link is orientation-closed for free.
bp(eq(B, A), W) :- bp(eq(A, B), W).
pval(eq(X, X), 1) :- bp(eq(X, X), _).
pval(ne(X, X), 0) :- bp(ne(X, X), _).
:- pval(eq(A, B), V), pval(ne(A, B), V).                       % eq / ne complement
:- pval(eq(A, B), V), pval(eq(B, A), 1 - V).                   % eq symmetric
:- pval(lt(A, B, W), V), pval(ge(A, B, W), V).                 % lt / ge complement
:- pval(gt(A, B, W), V), pval(le(A, B, W), V).                 % gt / le complement
:- pval(lt(A, B, W), V), pval(gt(B, A, W), 1 - V).             % lt(a,b) = gt(b,a)
:- pval(le(A, B, W), V), pval(ge(B, A, W), 1 - V).             % le(a,b) = ge(b,a)
:- pval(eq(A, B), 1), pval(lt(A, B, W), 1).                    % equal -> not less
:- pval(eq(A, B), 1), pval(gt(A, B, W), 1).
:- pval(lt(A, B, W), 1), pval(gt(A, B, W), 1).                 % not both
:- pval(slt(A, B, W), V), pval(sge(A, B, W), V).               % the signed family
:- pval(sgt(A, B, W), V), pval(sle(A, B, W), V).
:- pval(slt(A, B, W), V), pval(sgt(B, A, W), 1 - V).
:- pval(sle(A, B, W), V), pval(sge(B, A, W), 1 - V).
:- pval(eq(A, B), 1), pval(slt(A, B, W), 1).
:- pval(eq(A, B), 1), pval(sgt(A, B, W), 1).
:- pval(slt(A, B, W), 1), pval(sgt(A, B, W), 1).

% ---- equality is TRANSITIVE (the CAM theory, 2026-08-28) ----------------------------------------
% A match vector over many slots (a CAM) needs more than the pairwise facts above: without
% transitivity a request token may "equal" two slot tokens that a monitor holds distinct, and the
% uniqueness proofs report spurious counterexamples (the miss-queue entry's risk, probed in
% notes/design/ASP_FIRST_MISSQ_PLAN.md). These constraints close eq over every chain the program
% actually COMPARES: pval(eq(..)) atoms exist only for compared pairs (bp), so the closure is
% restricted to those pairs -- the cheap form the plan note named -- and, being CONSTRAINTS over
% already-existing choices, they add no choice space: every pruned model was impossible for real
% values (equality is transitive), so soundness of the over-approximation is preserved. With
% GENERATIVE symmetry (below), every compared pair exists in both orientations, so the
% textbook single spelling suffices -- the closure still reaches only compared pairs.
:- pval(eq(A, B), 1), pval(eq(B, C), 1), pval(eq(A, C), 0).

% ---- the GATE spelling of equality (the CAM datapath link, 2026-08-28) --------------------------
% A real comparator cell is XOR-then-NOR: rnor(bxor(A, B, W), W). Its boundary bit and eq(A, B)'s
% answer the same question, and leaving the two spellings independent is the boundary-spelling
% hazard (two free values for one question -- the gsdiv lesson). The link is a DATAPATH FACT,
% proven once for every width in Lean (lib/lean, RouteLean.Cam.comparator_is_equality: the
% XOR-NOR tree over masked operands computes exactly equality, stated over the Funcs models the
% ASP evaluates), and assumed here as a consistency constraint -- the same license as the eq/ne
% complement facts above, each an arithmetic truth the control layer borrows.
:- pval(rnor(bxor(A, B, W), W), V), pval(eq(A, B), 1 - V).
#show pval/2.
