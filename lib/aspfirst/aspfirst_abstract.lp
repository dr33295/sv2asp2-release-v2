% lib/aspfirst/aspfirst_abstract.lp -- the ABSTRACTION companion for the refinement loop.
%
% A design under refinement (spec -> ASP_0 -> ASP_1 -> ... -> ASP_n -> RTL) marks the parts it has
% not implemented yet as `abstract(Net)`. This file gives such a net a FREE VALUE at every instant
% -- one choice per instant over the net's whole domain -- so the level is a program whose traces
% are every behaviour the unrefined part could have, restricted only by the invariants the level
% states (its `bad/2` monitors, asserted as `:- bad(_, _).` by the refine runner). Refining a level
% replaces an `abstract(N)` by a def / instance / rules; the runner checks the concrete level never
% violates the abstract level's invariants and still meets the spec.
%
% This is a companion, not the design layer: the design file stays positive-definite; the choice
% lives here, exactly as the power-on choices live in __xinit.lp.
{ val(N, V, T) : V = 0..2**W-1 }         = 1 :- abstract(N), wire(N, W), W = 1..30, gtime(T), not data(N).
{ val(N, L, T) : enum_member(E, L, _) }  = 1 :- abstract(N), wire(N, enum(E)), gtime(T).
%
% An abstract DATA net (the symbolic reading) is not a free value: it takes what its MODEL says where a
% model speaks -- `model(N, V, T)` in the level's .inv.lp, or in an abstract child's contract -- and a
% fresh token elsewhere. A model is the definitional form of an assumption about a data output; the
% level (or child) that builds the output inherits it as an OBLIGATION (concrete mismatch = bad, term
% mismatch = owed to Lean) through the runner's obligation protocol.
#defined data/1.  #defined model/3.
modeled(N, T) :- model(N, _, T).
val(N, V, T)         :- abstract(N), data(N), model(N, V, T).
val(N, tok(N, T), T) :- abstract(N), data(N), gtime(T), not modeled(N, T).
%
% An abstract ARCHITECTURAL MEMORY (`arch_mem(M, D, W)` + `abstract(M)`): every cell a free value each
% instant -- or what a model says (`model(cell(M, A), V, T)`), or a fresh token per cell per instant
% when the memory holds data (`data(M)`). The spec reads its cells as `val(cell(M, A), V, T)`, exactly
% as it would read a built spram's, so a level that has not built the memory yet is still checked
% against everything the spec says about it.
#defined arch_mem/3.
addr(M, A) :- arch_mem(M, D, _), abstract(M), A = 0..D-1.        % (a BUILT one has the spram's addr)
{ val(cell(M, A), V, T) : V = 0..2**W-1 } = 1 :- abstract(M), arch_mem(M, _, W), addr(M, A), gtime(T),
                                                 not data(M), not modeled(cell(M, A), T).
val(cell(M, A), V, T)             :- abstract(M), arch_mem(M, _, _), addr(M, A), model(cell(M, A), V, T).
val(cell(M, A), tok(cell(M, A), T), T) :- abstract(M), arch_mem(M, _, _), data(M), addr(M, A), gtime(T),
                                          not modeled(cell(M, A), T).
