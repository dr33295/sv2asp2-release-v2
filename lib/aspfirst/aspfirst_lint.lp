% lib/aspfirst/aspfirst_lint.lp -- STATIC checks over an ASP-first design's facts. Every finding is a
% `lint(...)` atom; `python -m sv2asp.aspfirst lint` composes this with the design (and the
% `comb_head/1`, `dep/2` facts it derives from any guarded comb rules) and reports them. This is
% the lint layer, not the design layer: negation over static facts is fine here.
%
% Findings (all errors unless marked WARN):
%   lint(undeclared_net(N))          a leaf mentioned in an expression/pin/def that is not a port or net
%   lint(multi_driver(N, K))         a net with K != 1 drivers (defs + comb-rule heads + cell outputs)
%   lint(input_driven(N))            a def / cell output / rule head on an INPUT port
%   lint(width_mismatch(N, WN, WE))  def(N, E) where E's result width is not N's declared width
%   lint(operand_wider_than_op(E))   an operand wider than the op's result width (silent truncation)
%   lint(ite_arm_width(E))           the two arms of an ite differ in width
%   lint(sel_not_1bit(E))            WARN: an ite/logical selector wider than 1 bit (SV `!= 0` truth applies)
%   lint(enum_in_arith(E))           an enum-typed operand under an arithmetic/bitwise op
%   lint(unknown_cell(I, C))         inst(I, C) with C not a library cell
%   lint(unpinned(I, P))             a required pin of the cell not connected
%   lint(unknown_pin(I, P))          a pin the cell does not have
%   lint(missing_iparam(I, P))       a required iparam not given
%   lint(pin_width(I, P, WP, WE))    a pin whose net width WP is not the expected WE
%   lint(addr_width(M, D, W))        spram: 2^(address width) != depth
%   lint(comb_loop(N))               N combinationally depends on itself
%   lint(wide_bare(E))               a k(V, W) with V >= 2^31 written as a bare number (hard rule 4)
%   lint(abstract_input(N))          abstract(N) on an INPUT port (inputs are already free)
%   lint(abstract_too_wide(N, W))    an abstract net wider than 30 bits (2^W choices per instant)

#defined comb_head/1.  #defined dep/2.  #defined enum_member/3.  #defined iparam/3.  #defined pin/3.
#defined inst/2.  #defined def/2.  #defined port/3.  #defined net/2.  #defined abstract/1.  #defined mparam/3.
#defined arch_mem/3.
% ARCHITECTURAL memories: declared => built as an spram of that shape, or abstract -- never neither
% (the spec would read cells nobody derives: silently vacuous), never both
lint(arch_mem_unbuilt(M))      :- arch_mem(M, _, _), not abstract(M), not inst(M, spram), not inst(M, farray).
lint(arch_mem_shape(M, D, W))  :- arch_mem(M, D, W), mem_inst(M), iparam(M, depth, D2), D2 != D.
lint(arch_mem_shape(M, D, W))  :- arch_mem(M, D, W), mem_inst(M), iparam(M, width, W2), W2 != W.
mem_inst(M) :- inst(M, spram).   mem_inst(M) :- inst(M, farray).
% a `mrd(M, A)` read of a memory nothing declares -- found through the lint's own subterm walk
% (`occ/2`), so a read nested anywhere in an expression is caught
lint(mrd_undeclared(M)) :- occ(_, mrd(M, _)), not mem_inst(M), not arch_mem(M, _, _).
lint(arch_mem_abstract_and_built(M)) :- arch_mem(M, _, _), abstract(M), inst(M, _).

% ---- architectural single REGISTERS ------------------------------------------------------------
% `arch_reg(N, W)` is the memory's twin: state the specification NAMES that is one register rather
% than an array. The level must either leave it ABSTRACT or BUILD it as a register whose `q` pin is
% this net. The check is POSITIVE -- "driven by a state instance" -- rather than "defined somewhere":
% a named register that is neither abstract nor built would be free forever, and the contract reading
% it would prove nothing while looking green. That is the vacuity failure this whole mechanism exists
% to avoid, so the gate for it must not be the weaker one.
#defined arch_reg/2.
reg_driven(N) :- pin(I, q, N), inst(I, C), cell(C).
lint(arch_reg_unbuilt(N))  :- arch_reg(N, _), not abstract(N), not reg_driven(N).
lint(arch_reg_defined(N))  :- arch_reg(N, _), def(N, _).          % state, not combinational
lint(arch_reg_abstract_and_built(N)) :- arch_reg(N, _), abstract(N), reg_driven(N).
% an enum MEMBER named like a net/port: in ASP `tag(red)` and the net `red` are different namespaces;
% in SystemVerilog they are ONE, so the print's `col_n = red;` would assign the 1-bit port to the enum
% (found by the dataset's traffic light: members red/green/yellow beside the outputs red/green/yellow)
lint(tag_collides_with_net(L)) :- enum_member(_, L, _), wire(L, _).
lint(tag_collides_with_inst(L)) :- enum_member(_, L, _), inst(L, _).

% ---- what the library knows about cells ------------------------------------------------------
cell(ff).    cell_pin(ff, clk).   cell_pin(ff, en).   cell_pin(ff, d).   cell_pin(ff, q).
             cell_iparam(ff, width).
cell(arff).  cell_pin(arff, clk). cell_pin(arff, en). cell_pin(arff, rstL). cell_pin(arff, d). cell_pin(arff, q).
             cell_iparam(arff, width). cell_iparam(arff, reset_value).
cell(lata).  cell_pin(lata, en).  cell_pin(lata, d).  cell_pin(lata, q).
             cell_iparam(lata, width).
cell(spram). cell_pin(spram, clk). cell_pin(spram, we). cell_pin(spram, wa). cell_pin(spram, wd).
             cell_pin(spram, ra). cell_pin(spram, rd).
             cell_iparam(spram, depth). cell_iparam(spram, width).
% farray -- an array of REGISTERS. No read PIN: its readers are `mrd(M, A)` expressions, any number of
% them, which is the whole reason it is not a spram. `rstL`/`reset_value` are optional (a farray may
% have no reset), so they are not required pins.
cell(farray). cell_pin(farray, clk). cell_pin(farray, we). cell_pin(farray, wa). cell_pin(farray, wd).
              cell_pin(farray, rstL).
              cell_iparam(farray, depth). cell_iparam(farray, width). cell_iparam(farray, reset_value).
% ...and the reset really is optional, which the two facts below finally make true of the GATE and
% not merely of the comment. `reset_value` is optional only in the sense of "absent when there is no
% reset": pin `rstL` and it becomes required again, because the reset rules read it and a reset with
% no value would be a hole.
opt_pin(farray, rstL).
opt_iparam(farray, reset_value).
lint(missing_iparam(I, reset_value)) :- inst(I, farray), pin(I, rstL, _), not iparam(I, reset_value, _).
cell_out(ff, q).  cell_out(arff, q).  cell_out(lata, q).  cell_out(spram, rd).
% pins that are always 1 bit
onebit(clk). onebit(en). onebit(rstL). onebit(we).

% ---- widths of terms -------------------------------------------------------------------------
w(N, W) :- wire(N, W).
numw(E, W)    :- w(E, W), W = 0..65536.          % a NUMERIC width (an enum's is `enum(E)`)
numwire(N, W) :- wire(N, W), W = 0..65536.
w(k(V, W), W)        :- term(k(V, W)).
w(tag(L), enum(E))   :- term(tag(L)), enum_member(E, L, _).
arith(add; sub; mul; and; or; xor; shl; shr; ashr; idiv; imod; sidiv; simod).
w(E, W) :- term(E), E = add(_, _, W).    w(E, W) :- term(E), E = sub(_, _, W).
w(E, W) :- term(E), E = mul(_, _, W).    w(E, W) :- term(E), E = and(_, _, W).
w(E, W) :- term(E), E = or(_, _, W).     w(E, W) :- term(E), E = xor(_, _, W).
w(E, W) :- term(E), E = shl(_, _, W).    w(E, W) :- term(E), E = shr(_, _, W).
w(E, W) :- term(E), E = ashr(_, _, W).   w(E, W) :- term(E), E = idiv(_, _, W).
w(E, W) :- term(E), E = imod(_, _, W).   w(E, W) :- term(E), E = sidiv(_, _, W).
w(E, W) :- term(E), E = simod(_, _, W).
w(E, W) :- term(E), E = bnot(_, W).      w(E, W) :- term(E), E = neg(_, W).
w(E, W) :- term(E), E = sext(_, _, W).   w(E, W) :- term(E), E = slc(_, _, W).
w(E, 1) :- term(E), E = bit(_, _).
w(E, WA + WB) :- term(E), E = cat(_, WA, _, WB).
w(E, 1) :- term(E), E = eq(_, _).        w(E, 1) :- term(E), E = ne(_, _).
w(E, 1) :- term(E), E = lt(_, _, _).     w(E, 1) :- term(E), E = le(_, _, _).
w(E, 1) :- term(E), E = gt(_, _, _).     w(E, 1) :- term(E), E = ge(_, _, _).
w(E, 1) :- term(E), E = slt(_, _, _).    w(E, 1) :- term(E), E = sle(_, _, _).
w(E, 1) :- term(E), E = sgt(_, _, _).    w(E, 1) :- term(E), E = sge(_, _, _).
w(E, 1) :- term(E), E = logand(_, _).    w(E, 1) :- term(E), E = logor(_, _).
w(E, 1) :- term(E), E = lnot(_).
w(E, 1) :- term(E), E = ror(_, _).       w(E, 1) :- term(E), E = rand(_, _).
w(E, 1) :- term(E), E = rxor(_, _).      w(E, 1) :- term(E), E = rnand(_, _).
w(E, 1) :- term(E), E = rnor(_, _).      w(E, 1) :- term(E), E = rxnor(_, _).
w(E, 1) :- term(E), E = parity(_, _).
w(E, W) :- term(E), E = popcnt(_, WO), W = WO.      % the count fits the operand's width
w(E, 7) :- term(E), E = clz(_, _).                  % 0..64 over a 64-bit field, so 7 bits
w(E, W) :- term(E), E = ite(_, A, _), w(A, W).

% an operator term (as opposed to a leaf)
opform(E) :- term(E), E = add(_, _, _).    opform(E) :- term(E), E = sub(_, _, _).
opform(E) :- term(E), E = mul(_, _, _).    opform(E) :- term(E), E = and(_, _, _).
opform(E) :- term(E), E = or(_, _, _).     opform(E) :- term(E), E = xor(_, _, _).
opform(E) :- term(E), E = shl(_, _, _).    opform(E) :- term(E), E = shr(_, _, _).
opform(E) :- term(E), E = ashr(_, _, _).   opform(E) :- term(E), E = idiv(_, _, _).
opform(E) :- term(E), E = imod(_, _, _).   opform(E) :- term(E), E = sidiv(_, _, _).
opform(E) :- term(E), E = simod(_, _, _).  opform(E) :- term(E), E = bnot(_, _).
opform(E) :- term(E), E = mrd(_, _).       % a flop-array read is an expression form
opform(E) :- term(E), E = neg(_, _).       opform(E) :- term(E), E = sext(_, _, _).
opform(E) :- term(E), E = slc(_, _, _).    opform(E) :- term(E), E = bit(_, _).
opform(E) :- term(E), E = cat(_, _, _, _). opform(E) :- term(E), E = eq(_, _).
opform(E) :- term(E), E = ne(_, _).        opform(E) :- term(E), E = lt(_, _, _).
opform(E) :- term(E), E = le(_, _, _).     opform(E) :- term(E), E = gt(_, _, _).
opform(E) :- term(E), E = ge(_, _, _).     opform(E) :- term(E), E = slt(_, _, _).
opform(E) :- term(E), E = sle(_, _, _).    opform(E) :- term(E), E = sgt(_, _, _).
opform(E) :- term(E), E = sge(_, _, _).    opform(E) :- term(E), E = logand(_, _).
opform(E) :- term(E), E = logor(_, _).     opform(E) :- term(E), E = lnot(_).
opform(E) :- term(E), E = ror(_, _).       opform(E) :- term(E), E = rand(_, _).
opform(E) :- term(E), E = rxor(_, _).      opform(E) :- term(E), E = rnand(_, _).
opform(E) :- term(E), E = rnor(_, _).      opform(E) :- term(E), E = rxnor(_, _).
opform(E) :- term(E), E = parity(_, _).    opform(E) :- term(E), E = popcnt(_, _).
opform(E) :- term(E), E = clz(_, _).
opform(E) :- term(E), E = ite(_, _, _).    opform(E) :- term(E), E = k(_, _).
opform(E) :- term(E), E = tag(_).

% ---- declarations ----------------------------------------------------------------------------
lint(undeclared_net(N)) :- term(N), not opform(N), not wire(N, _).
lint(undeclared_net(N)) :- pin(_, _, N), not wire(N, _).
lint(undeclared_net(N)) :- def(N, _), not wire(N, _).
lint(undeclared_net(N)) :- comb_head(N), not wire(N, _).
lint(unknown_enum(E))   :- wire(_, enum(E)), not enum_member(E, _, _).
lint(unknown_tag(L))    :- term(tag(L)), not enum_member(_, L, _).

% ---- drivers ---------------------------------------------------------------------------------
driver(N, def) :- def(N, _).
driver(N, rule) :- comb_head(N).
driver(N, out(I)) :- inst(I, C), cell_out(C, P), pin(I, P, N).
driver(N, abstract) :- abstract(N).                 % an abstract net IS driven -- by a free choice
lint(undeclared_net(N)) :- abstract(N), not wire(N, _), not arch_mem(N, _, _).
lint(abstract_input(N)) :- abstract(N), port(N, input, _).      % inputs are already free (the stimulus)
lint(abstract_too_wide(N, W)) :- abstract(N), numwire(N, W), W > 30, not data(N).   % 2^W choices (a DATA abstract is a token)
lint(multi_driver(N, K)) :- wire(N, _), not port(N, input, _), K = #count { D : driver(N, D) }, K != 1.
lint(input_driven(N))    :- port(N, input, _), driver(N, _).

% ---- widths ----------------------------------------------------------------------------------
lint(width_mismatch(N, WN, WE)) :- def(N, E), wire(N, WN), w(E, WE), WN != WE.
lint(enum_in_arith(E)) :- opform(E), E = add(A, _, _), w(A, enum(_)).
lint(enum_in_arith(E)) :- opform(E), E = add(_, B, _), w(B, enum(_)).
lint(enum_in_arith(E)) :- opform(E), E = sub(A, _, _), w(A, enum(_)).
lint(enum_in_arith(E)) :- opform(E), E = sub(_, B, _), w(B, enum(_)).
lint(enum_in_arith(E)) :- opform(E), E = and(A, _, _), w(A, enum(_)).
lint(enum_in_arith(E)) :- opform(E), E = or(A, _, _),  w(A, enum(_)).
lint(enum_in_arith(E)) :- opform(E), E = xor(A, _, _), w(A, enum(_)).
lint(enum_in_arith(E)) :- opform(E), E = mul(A, _, _), w(A, enum(_)).
% operand wider than the op's result -> silent truncation of A or B (write a slc to say so)
lint(operand_wider_than_op(E)) :- opform(E), E = add(A, _, W),  numw(A, WA), WA > W.
lint(operand_wider_than_op(E)) :- opform(E), E = add(_, B, W),  numw(B, WB), WB > W.
lint(operand_wider_than_op(E)) :- opform(E), E = sub(A, _, W),  numw(A, WA), WA > W.
lint(operand_wider_than_op(E)) :- opform(E), E = sub(_, B, W),  numw(B, WB), WB > W.
lint(operand_wider_than_op(E)) :- opform(E), E = mul(A, _, W),  numw(A, WA), WA > W.
lint(operand_wider_than_op(E)) :- opform(E), E = mul(_, B, W),  numw(B, WB), WB > W.
lint(operand_wider_than_op(E)) :- opform(E), E = and(A, _, W),  numw(A, WA), WA > W.
lint(operand_wider_than_op(E)) :- opform(E), E = and(_, B, W),  numw(B, WB), WB > W.
lint(operand_wider_than_op(E)) :- opform(E), E = or(A, _, W),   numw(A, WA), WA > W.
lint(operand_wider_than_op(E)) :- opform(E), E = or(_, B, W),   numw(B, WB), WB > W.
lint(operand_wider_than_op(E)) :- opform(E), E = xor(A, _, W),  numw(A, WA), WA > W.
lint(operand_wider_than_op(E)) :- opform(E), E = xor(_, B, W),  numw(B, WB), WB > W.
lint(operand_wider_than_op(E)) :- opform(E), E = shl(A, _, W),  numw(A, WA), WA > W.
lint(operand_wider_than_op(E)) :- opform(E), E = shr(A, _, W),  numw(A, WA), WA > W.
lint(operand_wider_than_op(E)) :- opform(E), E = ashr(A, _, W), numw(A, WA), WA > W.
lint(operand_wider_than_op(E)) :- opform(E), E = bnot(A, W),    numw(A, WA), WA > W.
lint(operand_wider_than_op(E)) :- opform(E), E = neg(A, W),     numw(A, WA), WA > W.
lint(operand_wider_than_op(E)) :- opform(E), E = sext(A, F, _), numw(A, WA), WA > F.
lint(operand_wider_than_op(E)) :- opform(E), E = slc(A, L, W),  numw(A, WA), L + W > WA.
lint(operand_wider_than_op(E)) :- opform(E), E = bit(A, I),     numw(A, WA), I >= WA.
lint(operand_wider_than_op(E)) :- opform(E), E = cat(A, WA, _, _), numw(A, W), W != WA.
lint(operand_wider_than_op(E)) :- opform(E), E = cat(_, _, B, WB), numw(B, W), W != WB.
lint(operand_wider_than_op(E)) :- opform(E), E = lt(A, _, W),   numw(A, WA), WA > W.
lint(operand_wider_than_op(E)) :- opform(E), E = lt(_, B, W),   numw(B, WB), WB > W.
lint(operand_wider_than_op(E)) :- opform(E), E = le(A, _, W),   numw(A, WA), WA > W.
lint(operand_wider_than_op(E)) :- opform(E), E = le(_, B, W),   numw(B, WB), WB > W.
lint(operand_wider_than_op(E)) :- opform(E), E = gt(A, _, W),   numw(A, WA), WA > W.
lint(operand_wider_than_op(E)) :- opform(E), E = gt(_, B, W),   numw(B, WB), WB > W.
lint(operand_wider_than_op(E)) :- opform(E), E = ge(A, _, W),   numw(A, WA), WA > W.
lint(operand_wider_than_op(E)) :- opform(E), E = ge(_, B, W),   numw(B, WB), WB > W.
lint(operand_wider_than_op(E)) :- opform(E), E = ror(A, W),     numw(A, WA), WA != W.
lint(operand_wider_than_op(E)) :- opform(E), E = rand(A, W),    numw(A, WA), WA != W.
lint(operand_wider_than_op(E)) :- opform(E), E = rxor(A, W),    numw(A, WA), WA != W.
lint(operand_wider_than_op(E)) :- opform(E), E = popcnt(A, W),  numw(A, WA), WA != W.
lint(operand_wider_than_op(E)) :- opform(E), E = clz(A, _),     numw(A, WA), WA > 64.
% ite ARM WIDTHS are checked in `lint.py::ite_arm_widths`. As a rule here it read
%     lint(ite_arm_width(E)) :- opform(E), E = ite(_, A, B), w(A, WA), w(B, WB), WA != WB.
% and that single line was 100% of the lint's cost on a large design: `w(A,WA), w(B,WB)` is a
% width-by-width join the grounder does not restrict by E first, so it forms a cross product
% against every `ite`. Everything above grounded in 66,663 rules; adding this one did not finish
% in forty seconds. Looking up two widths and comparing them is not a search problem.
lint(sel_not_1bit(E))  :- opform(E), E = ite(S, _, _), w(S, WS), WS != 1.
lint(sel_not_1bit(E))  :- opform(E), E = logand(A, _), w(A, WS), WS != 1.
lint(sel_not_1bit(E))  :- opform(E), E = logand(_, B), w(B, WS), WS != 1.
lint(sel_not_1bit(E))  :- opform(E), E = logor(A, _), w(A, WS), WS != 1.
lint(sel_not_1bit(E))  :- opform(E), E = logor(_, B), w(B, WS), WS != 1.
lint(sel_not_1bit(E))  :- opform(E), E = lnot(A), w(A, WS), WS != 1.
lint(wide_bare(E)) :- term(E), E = k(V, _), V >= 2147483647.       % clingo wraps at 2^31: it must be a "string"
lint(const_too_wide(E)) :- term(E), E = k(V, W), W < 31, V >= 2 ** W.

% ---- cells -----------------------------------------------------------------------------------
lint(unknown_cell(I, C))   :- inst(I, C), not cell(C).
% OPTIONAL pins and iparams. `cell_pin`/`cell_iparam` declare what a cell HAS; `opt_pin`/`opt_iparam`
% carve out the ones it may go without. Without this the two rules below required every declared pin,
% so a `farray` with no reset -- a register file, which commonly has none -- could not be authored at
% all, even though the library defines that case explicitly (`fa_run(M,T) :- ..., not fa_has_rst(M)`,
% "a farray may have no reset at all") and the comment above claimed it was optional. The semantics
% permitted it and the gate forbade it. Found on `examples/spec2rtl/am2901`, whose register file has
% no reset because the part has none.
#defined opt_pin/2.  #defined opt_iparam/2.
lint(unpinned(I, P))       :- inst(I, C), cell_pin(C, P), not pin(I, P, _), not opt_pin(C, P).
lint(unknown_pin(I, P))    :- inst(I, C), cell(C), pin(I, P, _), not cell_pin(C, P).
lint(missing_iparam(I, P)) :- inst(I, C), cell_iparam(C, P), not iparam(I, P, _), not opt_iparam(C, P).
lint(pin_width(I, P, WP, 1)) :- inst(I, C), cell(C), pin(I, P, N), onebit(P), wire(N, WP), WP != 1.
lint(pin_width(I, d, WP, WE)) :- inst(I, C), cell(C), pin(I, d, N), numwire(N, WP), iparam(I, width, WE), WP != WE.
lint(pin_width(I, q, WP, WE)) :- inst(I, C), cell(C), pin(I, q, N), numwire(N, WP), iparam(I, width, WE), WP != WE.
lint(pin_width(I, wd, WP, WE)) :- inst(I, spram), pin(I, wd, N), wire(N, WP), iparam(I, width, WE), WP != WE.
lint(pin_width(I, wd, WP, WE)) :- inst(I, farray), pin(I, wd, N), wire(N, WP), iparam(I, width, WE), WP != WE.
lint(pin_width(I, rd, WP, WE)) :- inst(I, spram), pin(I, rd, N), wire(N, WP), iparam(I, width, WE), WP != WE.
lint(pin_width(I, wa, WP, WA)) :- inst(I, spram), pin(I, wa, N), wire(N, WP), pin(I, ra, N2), wire(N2, WA), WP != WA.
lint(addr_width(M, D, W)) :- inst(M, spram), iparam(M, depth, D), pin(M, wa, N), numwire(N, W), D != 2 ** W.
lint(enum_reg_reset_not_tag(I)) :- inst(I, arff), pin(I, q, Q), wire(Q, enum(E)), iparam(I, reset_value, RV), not enum_member(E, RV, _).

% ---- combinational loops -----------------------------------------------------------------------
% Detected in `lint.py::comb_loops`, in PYTHON, and the reason is measured rather than stylistic.
%
% This section used to build `inside/2` (an expression's immediate subterms, one rule per operator),
% close it into `leaf_of/2` (the NETS an expression reads), join that into `dep/2` (N's value depends
% on M's at the same instant) and close THAT into `reach/2` -- two transitive closures computed by
% GROUNDING. On tens of nets it is invisible. On a 16x16 toroid, where every cell reads eight
% neighbours, `reach/2` grounds toward 4,353^2 pairs: the lint stopped finishing in ten minutes while
% the DESIGN it was checking grounded in 51k rules and under a hundred seconds. The check cost orders
% of magnitude more than the thing checked.
%
% Nothing here was being SOLVED, only inspected. A depth-first walk over the same edges is linear in
% them, and it can name the cycle rather than only the fact of one. `lint(undeclared_net(N))` via
% `dep` went with it: a leaf that is not an op form and not a wire is already caught above.
%
% What stays in ASP is what genuinely reasons over the library's own `term`/`ev` structure -- the
% data/boundary section below -- so those checks cannot drift from the semantics they check.

#show lint/1.

% ---- data nets: the CDS split at authoring time (docs/guide/ASP_FIRST_DESIGN.md 1d) ------------
% data(N) declares a net whose VALUES are never enumerated in verification: under the symbolic
% companion it carries a term over the input tokens. This section (a) closes the declaration
% (a net fed by a data term must be declared data), (b) finds the BOUNDARY -- every op with a data
% operand whose result is control (a compare, a reduction, a bit, a narrow slice, a popcount) --
% and emits bnd(E, W) / dat(E) role facts the companion consumes, (c) refuses data where a value
% would be read as TRUTH or as an address, and where the machinery does not reach yet.
%   lint(undeclared_data(N))         N is fed a data term (a def, a register d->q, a memory wd->rd): declare data(N)
%   lint(compare_in_data_net(N, E))  a compare/reduction is control; do not declare its net data
%   lint(data_in_truth(E))           a raw data term as an ite selector or a logical operand: name the boundary (eq/ne/lt ...)
%   lint(data_in_pin(I, P, N))       a data net on a control pin (en, we, rstL, clk, wa, ra)
%   lint(data_in_rule(H, N))         a guarded comb rule reads or guards on a data net (not supported yet)
%   lint(rule_on_data(H))            a guarded comb rule defines a data net (not supported yet)
%   lint(boundary_too_wide(E, W))    a boundary result wider than 8 bits (2^W choices per distinct term): declare data or narrow
% A boundary that flows only into DATA (a mux arm, a data register) is TERM MODE (dat(E): kept as a term,
% exact, linear); one that reaches control (an enable, a guard, a control output) is FREE per term (bnd(E, W)).
#defined data/1.
% dterm(E): E mentions data (some leaf is a data net)
dterm(N) :- data(N), wire(N, _).
dterm(E) :- opform(E), E = add(A, _, _), dterm(A).      dterm(E) :- opform(E), E = add(_, B, _), dterm(B).
dterm(E) :- opform(E), E = sub(A, _, _), dterm(A).      dterm(E) :- opform(E), E = sub(_, B, _), dterm(B).
dterm(E) :- opform(E), E = mul(A, _, _), dterm(A).      dterm(E) :- opform(E), E = mul(_, B, _), dterm(B).
dterm(E) :- opform(E), E = and(A, _, _), dterm(A).      dterm(E) :- opform(E), E = and(_, B, _), dterm(B).
dterm(E) :- opform(E), E = or(A, _, _), dterm(A).       dterm(E) :- opform(E), E = or(_, B, _), dterm(B).
dterm(E) :- opform(E), E = xor(A, _, _), dterm(A).      dterm(E) :- opform(E), E = xor(_, B, _), dterm(B).
dterm(E) :- opform(E), E = shl(A, _, _), dterm(A).      dterm(E) :- opform(E), E = shl(_, B, _), dterm(B).
dterm(E) :- opform(E), E = shr(A, _, _), dterm(A).      dterm(E) :- opform(E), E = shr(_, B, _), dterm(B).
dterm(E) :- opform(E), E = ashr(A, _, _), dterm(A).     dterm(E) :- opform(E), E = ashr(_, B, _), dterm(B).
dterm(E) :- opform(E), E = idiv(A, _, _), dterm(A).     dterm(E) :- opform(E), E = idiv(_, B, _), dterm(B).
dterm(E) :- opform(E), E = imod(A, _, _), dterm(A).     dterm(E) :- opform(E), E = imod(_, B, _), dterm(B).
dterm(E) :- opform(E), E = sidiv(A, _, _), dterm(A).    dterm(E) :- opform(E), E = sidiv(_, B, _), dterm(B).
dterm(E) :- opform(E), E = simod(A, _, _), dterm(A).    dterm(E) :- opform(E), E = simod(_, B, _), dterm(B).
dterm(E) :- opform(E), E = bnot(A, _), dterm(A).        dterm(E) :- opform(E), E = neg(A, _), dterm(A).
dterm(E) :- opform(E), E = sext(A, _, _), dterm(A).
dterm(E) :- opform(E), E = cat(A, _, _, _), dterm(A).   dterm(E) :- opform(E), E = cat(_, _, B, _), dterm(B).
dterm(E) :- opform(E), E = ite(_, A, _), dterm(A).      dterm(E) :- opform(E), E = ite(_, _, B), dterm(B).
dterm(E) :- opform(E), E = slc(A, _, _), dterm(A).      dterm(E) :- opform(E), E = bit(A, _), dterm(A).
dterm(E) :- opform(E), E = popcnt(A, _), dterm(A).
dterm(E) :- opform(E), E = clz(A, _), dterm(A).
% boundary-capable ops (a control result may be computed from data)
bcap(E) :- opform(E), E = eq(_, _).      bcap(E) :- opform(E), E = ne(_, _).
bcap(E) :- opform(E), E = lt(_, _, _).   bcap(E) :- opform(E), E = le(_, _, _).
bcap(E) :- opform(E), E = gt(_, _, _).   bcap(E) :- opform(E), E = ge(_, _, _).
bcap(E) :- opform(E), E = slt(_, _, _).  bcap(E) :- opform(E), E = sle(_, _, _).
bcap(E) :- opform(E), E = sgt(_, _, _).  bcap(E) :- opform(E), E = sge(_, _, _).
bcap(E) :- opform(E), E = ror(_, _).     bcap(E) :- opform(E), E = rand(_, _).
bcap(E) :- opform(E), E = rxor(_, _).    bcap(E) :- opform(E), E = rnand(_, _).
bcap(E) :- opform(E), E = rnor(_, _).    bcap(E) :- opform(E), E = rxnor(_, _).
bcap(E) :- opform(E), E = parity(_, _).
bcap(E) :- opform(E), E = slc(_, _, _).  bcap(E) :- opform(E), E = bit(_, _).  bcap(E) :- opform(E), E = popcnt(_, _).
bcap(E) :- opform(E), E = clz(_, _).
% a boundary-capable op HAS a data operand (its operand mentions data)
bdata(E) :- bcap(E), E = eq(A, _), dterm(A).      bdata(E) :- bcap(E), E = eq(_, B), dterm(B).
bdata(E) :- bcap(E), E = ne(A, _), dterm(A).      bdata(E) :- bcap(E), E = ne(_, B), dterm(B).
bdata(E) :- bcap(E), E = lt(A, _, _), dterm(A).   bdata(E) :- bcap(E), E = lt(_, B, _), dterm(B).
bdata(E) :- bcap(E), E = le(A, _, _), dterm(A).   bdata(E) :- bcap(E), E = le(_, B, _), dterm(B).
bdata(E) :- bcap(E), E = gt(A, _, _), dterm(A).   bdata(E) :- bcap(E), E = gt(_, B, _), dterm(B).
bdata(E) :- bcap(E), E = ge(A, _, _), dterm(A).   bdata(E) :- bcap(E), E = ge(_, B, _), dterm(B).
bdata(E) :- bcap(E), E = slt(A, _, _), dterm(A).  bdata(E) :- bcap(E), E = slt(_, B, _), dterm(B).
bdata(E) :- bcap(E), E = sle(A, _, _), dterm(A).  bdata(E) :- bcap(E), E = sle(_, B, _), dterm(B).
bdata(E) :- bcap(E), E = sgt(A, _, _), dterm(A).  bdata(E) :- bcap(E), E = sgt(_, B, _), dterm(B).
bdata(E) :- bcap(E), E = sge(A, _, _), dterm(A).  bdata(E) :- bcap(E), E = sge(_, B, _), dterm(B).
bdata(E) :- bcap(E), E = ror(A, _), dterm(A).     bdata(E) :- bcap(E), E = rand(A, _), dterm(A).
bdata(E) :- bcap(E), E = rxor(A, _), dterm(A).    bdata(E) :- bcap(E), E = rnand(A, _), dterm(A).
bdata(E) :- bcap(E), E = rnor(A, _), dterm(A).    bdata(E) :- bcap(E), E = rxnor(A, _), dterm(A).
bdata(E) :- bcap(E), E = parity(A, _), dterm(A).
bdata(E) :- bcap(E), E = slc(A, _, _), dterm(A).  bdata(E) :- bcap(E), E = bit(A, _), dterm(A).
bdata(E) :- bcap(E), E = popcnt(A, _), dterm(A).
bdata(E) :- bcap(E), E = clz(A, _), dterm(A).
% RAW data: a term whose value is a data term (a data leaf, or a data-preserving op over one) --
% as opposed to a boundary-capable op, whose value is control
rawd(E) :- dterm(E), not bcap(E).
% ---- (a) the declaration must close
lint(undeclared_data(N)) :- def(N, E), rawd(E), not data(N).
lint(undeclared_data(Q)) :- inst(I, C), cell_out(C, q), pin(I, d, D), data(D), pin(I, q, Q), not data(Q).
lint(undeclared_data(RD)) :- inst(M, spram), pin(M, wd, WD), data(WD), pin(M, rd, RD), not data(RD).
% ---- (b) roles: data context flows down from a data net's def through data-preserving ops
dctx(E) :- def(N, E), data(N).
dctx(A) :- dctx(E), E = add(A, _, _).    dctx(B) :- dctx(E), E = add(_, B, _).
dctx(A) :- dctx(E), E = sub(A, _, _).    dctx(B) :- dctx(E), E = sub(_, B, _).
dctx(A) :- dctx(E), E = mul(A, _, _).    dctx(B) :- dctx(E), E = mul(_, B, _).
dctx(A) :- dctx(E), E = and(A, _, _).    dctx(B) :- dctx(E), E = and(_, B, _).
dctx(A) :- dctx(E), E = or(A, _, _).     dctx(B) :- dctx(E), E = or(_, B, _).
dctx(A) :- dctx(E), E = xor(A, _, _).    dctx(B) :- dctx(E), E = xor(_, B, _).
dctx(A) :- dctx(E), E = shl(A, _, _).    dctx(B) :- dctx(E), E = shl(_, B, _).
dctx(A) :- dctx(E), E = shr(A, _, _).    dctx(B) :- dctx(E), E = shr(_, B, _).
dctx(A) :- dctx(E), E = ashr(A, _, _).   dctx(B) :- dctx(E), E = ashr(_, B, _).
dctx(A) :- dctx(E), E = idiv(A, _, _).   dctx(B) :- dctx(E), E = idiv(_, B, _).
dctx(A) :- dctx(E), E = imod(A, _, _).   dctx(B) :- dctx(E), E = imod(_, B, _).
dctx(A) :- dctx(E), E = sidiv(A, _, _).  dctx(B) :- dctx(E), E = sidiv(_, B, _).
dctx(A) :- dctx(E), E = simod(A, _, _).  dctx(B) :- dctx(E), E = simod(_, B, _).
dctx(A) :- dctx(E), E = bnot(A, _).      dctx(A) :- dctx(E), E = neg(A, _).
dctx(A) :- dctx(E), E = sext(A, _, _).
dctx(A) :- dctx(E), E = cat(A, _, _, _). dctx(B) :- dctx(E), E = cat(_, _, B, _).
dctx(A) :- dctx(E), E = ite(_, A, _).    dctx(B) :- dctx(E), E = ite(_, _, B).
dctx(A) :- dctx(E), E = slc(A, _, _).    dctx(A) :- dctx(E), E = bit(A, _).   dctx(A) :- dctx(E), E = popcnt(A, _).
dctx(A) :- dctx(E), E = clz(A, _).
% ---- where does a boundary's value FLOW? (term mode vs free) ------------------------------------
% sub(E, A): A is a direct subterm of E; occ(M, E): E occurs in the def of net M
sub(E, A) :- opform(E), E = add(A, _, _).    sub(E, B) :- opform(E), E = add(_, B, _).
sub(E, A) :- opform(E), E = sub(A, _, _).    sub(E, B) :- opform(E), E = sub(_, B, _).
sub(E, A) :- opform(E), E = mul(A, _, _).    sub(E, B) :- opform(E), E = mul(_, B, _).
sub(E, A) :- opform(E), E = and(A, _, _).    sub(E, B) :- opform(E), E = and(_, B, _).
sub(E, A) :- opform(E), E = or(A, _, _).     sub(E, B) :- opform(E), E = or(_, B, _).
sub(E, A) :- opform(E), E = xor(A, _, _).    sub(E, B) :- opform(E), E = xor(_, B, _).
sub(E, A) :- opform(E), E = shl(A, _, _).    sub(E, B) :- opform(E), E = shl(_, B, _).
sub(E, A) :- opform(E), E = shr(A, _, _).    sub(E, B) :- opform(E), E = shr(_, B, _).
sub(E, A) :- opform(E), E = ashr(A, _, _).   sub(E, B) :- opform(E), E = ashr(_, B, _).
sub(E, A) :- opform(E), E = idiv(A, _, _).   sub(E, B) :- opform(E), E = idiv(_, B, _).
sub(E, A) :- opform(E), E = imod(A, _, _).   sub(E, B) :- opform(E), E = imod(_, B, _).
sub(E, A) :- opform(E), E = sidiv(A, _, _).  sub(E, B) :- opform(E), E = sidiv(_, B, _).
sub(E, A) :- opform(E), E = simod(A, _, _).  sub(E, B) :- opform(E), E = simod(_, B, _).
sub(E, A) :- opform(E), E = bnot(A, _).      sub(E, A) :- opform(E), E = neg(A, _).
sub(E, A) :- opform(E), E = mrd(_, A).       % a flop-array read: its INDEX is the subterm
sub(E, A) :- opform(E), E = sext(A, _, _).   sub(E, A) :- opform(E), E = slc(A, _, _).   sub(E, A) :- opform(E), E = bit(A, _).
sub(E, A) :- opform(E), E = cat(A, _, _, _). sub(E, B) :- opform(E), E = cat(_, _, B, _).
sub(E, A) :- opform(E), E = eq(A, _).        sub(E, B) :- opform(E), E = eq(_, B).
sub(E, A) :- opform(E), E = ne(A, _).        sub(E, B) :- opform(E), E = ne(_, B).
sub(E, A) :- opform(E), E = lt(A, _, _).     sub(E, B) :- opform(E), E = lt(_, B, _).
sub(E, A) :- opform(E), E = le(A, _, _).     sub(E, B) :- opform(E), E = le(_, B, _).
sub(E, A) :- opform(E), E = gt(A, _, _).     sub(E, B) :- opform(E), E = gt(_, B, _).
sub(E, A) :- opform(E), E = ge(A, _, _).     sub(E, B) :- opform(E), E = ge(_, B, _).
sub(E, A) :- opform(E), E = slt(A, _, _).    sub(E, B) :- opform(E), E = slt(_, B, _).
sub(E, A) :- opform(E), E = sle(A, _, _).    sub(E, B) :- opform(E), E = sle(_, B, _).
sub(E, A) :- opform(E), E = sgt(A, _, _).    sub(E, B) :- opform(E), E = sgt(_, B, _).
sub(E, A) :- opform(E), E = sge(A, _, _).    sub(E, B) :- opform(E), E = sge(_, B, _).
sub(E, A) :- opform(E), E = logand(A, _).    sub(E, B) :- opform(E), E = logand(_, B).
sub(E, A) :- opform(E), E = logor(A, _).     sub(E, B) :- opform(E), E = logor(_, B).
sub(E, A) :- opform(E), E = lnot(A).
sub(E, A) :- opform(E), E = ror(A, _).       sub(E, A) :- opform(E), E = rand(A, _).     sub(E, A) :- opform(E), E = rxor(A, _).
sub(E, A) :- opform(E), E = rnand(A, _).     sub(E, A) :- opform(E), E = rnor(A, _).     sub(E, A) :- opform(E), E = rxnor(A, _).
sub(E, A) :- opform(E), E = parity(A, _).    sub(E, A) :- opform(E), E = popcnt(A, _).
sub(E, A) :- opform(E), E = clz(A, _).
sub(E, S) :- opform(E), E = ite(S, _, _).    sub(E, A) :- opform(E), E = ite(_, A, _).   sub(E, B) :- opform(E), E = ite(_, _, B).
occ(M, E) :- def(M, E).
occ(M, A) :- occ(M, E), sub(E, A).
% csink(N): the value of net N REACHES CONTROL -- a control pin, a guarded rule, a control output, or
% (through defs and registers) any of those
csink(N) :- pin(_, P, N), P = (en; we; wa; ra; rstL; clk).
csink(N) :- comb_head(H), dep(H, N).
csink(N) :- port(N, output, _), not data(N).
csink(N) :- def(M, E), csink(M), occ(M, N), wire(N, _).
csink(D) :- inst(I, C), cell_out(C, q), pin(I, d, D), pin(I, q, Q), csink(Q).
csink(D) :- inst(I, spram), pin(I, wd, D), pin(I, rd, RD), csink(RD).
% a boundary is FREE per term when it reaches control through the net it is defined in; otherwise it
% only feeds data and KEEPS its term (term mode -- exact and linear)
bfree(E)  :- bdata(E), occ(M, E), csink(M).
dat(E)    :- bdata(E), not bfree(E).
bnd(E, W) :- bdata(E), bfree(E), w(E, W).
lint(compare_in_data_net(N, E)) :- def(N, E), data(N), bcap(E), E = eq(_, _).
lint(compare_in_data_net(N, E)) :- def(N, E), data(N), bcap(E), E = ne(_, _).
lint(compare_in_data_net(N, E)) :- def(N, E), data(N), bcap(E), E = lt(_, _, _).
lint(compare_in_data_net(N, E)) :- def(N, E), data(N), bcap(E), E = le(_, _, _).
lint(compare_in_data_net(N, E)) :- def(N, E), data(N), bcap(E), E = gt(_, _, _).
lint(compare_in_data_net(N, E)) :- def(N, E), data(N), bcap(E), E = ge(_, _, _).
lint(boundary_too_wide(E, W)) :- bnd(E, W), W > 8.
% ---- (c) refusals
lint(data_in_truth(E)) :- opform(E), E = ite(S, _, _), rawd(S).
lint(data_in_truth(E)) :- opform(E), E = logand(A, _), rawd(A).   lint(data_in_truth(E)) :- opform(E), E = logand(_, B), rawd(B).
lint(data_in_truth(E)) :- opform(E), E = logor(A, _), rawd(A).    lint(data_in_truth(E)) :- opform(E), E = logor(_, B), rawd(B).
lint(data_in_truth(E)) :- opform(E), E = lnot(A), rawd(A).
lint(data_in_pin(I, P, N)) :- pin(I, P, N), data(N), P = (en; we; rstL; clk; wa; ra).
lint(data_in_rule(H, N)) :- comb_head(H), dep(H, N), data(N).
lint(rule_on_data(H))    :- comb_head(H), data(H).
lint(undeclared_net(N))  :- data(N), not wire(N, _), not arch_mem(N, _, _).
#show bnd/2.  #show dat/1.
