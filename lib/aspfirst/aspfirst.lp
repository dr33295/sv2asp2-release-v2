% lib/aspfirst/aspfirst.lp -- the ASP-first DESIGN LIBRARY.
%
% An RTL block is authored as FACTS over this vocabulary (plus, optionally, guarded combinational
% rules in the restricted form of docs/guide/ASP_FIRST_DESIGN.md); the rules below give the facts
% their meaning. Every state-holding shape here MIRRORS the translator's emitted schema
% (docs/TRANSLATION_SPEC.md; proofs/): the FF capture/hold pair, ARFF's four async-reset rules
% with the reset read at BOTH ends of the edge, the memory write + `mem_hold` partition. Hold and
% set semantics therefore come from the PRIMITIVES, never from the author.
%
%   solve:  clingo design.lp lib/aspfirst/aspfirst.lp scenario.lp
%           [lib/aspfirst/aspfirst_init0.lp]   -- concrete zero power-on for unreset state (opt-in)
%           [lib/aspfirst/aspfirst_t34.lp]     -- single-valuedness guard (property layer)
%           [lib/aspfirst/aspfirst_cover.lp]   -- totality: SAT = some wire has no value somewhere
%           [lib/aspfirst/aspfirst_abstract.lp] -- gives every abstract(Net) a free value per instant (refinement)
%           [lib/aspfirst/aspfirst_symbolic.lp] -- the SYMBOLIC reading: data(Net)s carry terms, boundaries are free per term
%   The scenario supplies `#const k = ..` and `time(<clk>, 0..k)` -- exactly as for a translated design.
%
% VOCABULARY (authored facts, one per line):
%   module(Name).
%   port(Sig, input | output, W).      net(Sig, W).      net(Sig, enum(E)).   port(Sig, Dir, enum(E)).
%   enum_member(E, Label, Value).      param(P, V).      (documentary; widths are concrete)
%   def(Sig, Expr).                    -- combinational: Sig = Expr at every instant
%   inst(I, Cell).  pin(I, Pin, Sig).  iparam(I, P, V).  -- a primitive instance, its pins, its params
%   abstract(Sig).                     -- NOT YET REFINED: a free value each instant (see aspfirst_abstract.lp);
%                                         constrained only by the level's invariants; the lint counts them
%
% EXPR terms (widths explicit; every W is the RESULT width; wide constants as "decimal" strings):
%   k(V, W)  tag(Label)  <net>
%   add/sub/mul/and/or/xor/shl/shr/ashr(A, B, W)   idiv/imod/sidiv/simod(A, B, W)
%   bnot/neg(A, W)   sext(A, FromW, ToW)   slc(A, Lo, W)  (LOW bit + WIDTH, the @slc convention)   bit(A, I)
%   cat(A, WA, B, WB)   (A is the HIGH part)
%   eq/ne(A, B)   lt/le/gt/ge(A, B, W)  (unsigned at W)   slt/sle/sgt/sge(A, B, W)  (signed at W)
%   logand/logor(A, B)   lnot(A)   (SV truth: != 0)      ror/rand/rxor/rnand/rnor/rxnor/parity/popcnt(A, W)
%   clz(A, SGN)   leading ZEROS of A in a 64-bit field; SGN=1 counts leading SIGN bits -> 0..64
%   ite(S, A, B)   (S != 0 selects A)
%
% CELLS (pins; iparams):
%   ff     clk en d q                    ; width
%   arff   clk en rstL d q               ; width reset_value      -- async, active-LOW reset
%   lata   en d q                        ; width                  -- level-sensitive latch (transparent while en=1)
%   spram  clk we wa wd ra rd            ; depth width            -- single write port, combinational read
%   farray clk we wa wd [rstL]           ; depth width [reset_value] -- an array of REGISTERS: any
%                                                                  number of `mrd(M, A)` readers; an
%                                                                  async reset forces EVERY cell
%
%   data(Sig).                         -- a DATA net: its values are never enumerated in verification; with
%                                         aspfirst_symbolic.lp composed it carries symbolic TERMS over the
%                                         input tokens (the CDS split at authoring time; guide 1d)
%
% NOT here: any T=0 fact (F4 -- power-on is a separate artifact), any `not` in a design rule (the
% design layer stays positive-definite; the companions below carry the only negation).

% ---- BEGIN GENERATED (sv2asp.emit.lib -- the @func script; do not edit) ----
% @func LEGEND (wide-safe; values >= 2^31 are canonical decimal strings, see _wv/_we):
%   @add(A, B, W)       A + B, wrapped to W bits (mod 2^W)
%   @sub(A, B, W)       A - B, wrapped to W bits (SV subtraction wraps)
%   @mul(A, B, W)       A * B, wrapped to W bits
%   @idiv(A, B, W)      A / B unsigned, truncated (B=0 -> 0)
%   @imod(A, B, W)      A mod B unsigned (B=0 -> 0)
%   @sidiv(A, B, W)     A / B SIGNED at width W, truncate toward zero (B=0 -> 0)
%   @simod(A, B, W)     A mod B SIGNED at width W, sign of dividend (B=0 -> 0)
%   @band(A, B, W)      bitwise A & B
%   @bor(A, B, W)       bitwise A | B
%   @bxor(A, B, W)      bitwise A ^ B
%   @shl(A, N, W)       A << N, truncated to W bits
%   @shr(A, N, W)       A >> N logical (zero-fill)
%   @ashr(A, N, W)      A >> N arithmetic (sign-fill), sign taken at width W
%   @ipow(A, B, W)      A ** B, wrapped to W bits
%   @bnot(V, W)         bitwise complement ~V, W bits
%   @neg(V, W)          two's-complement negate -V (mod 2^W)
%   @sext(V, FromW, ToW) sign-extend V from FromW to ToW bits
%   @signed(V, W)       V read as a SIGNED int (two's-complement, W bits) -- narrow compares only
%   @wcmp(A, B, W, S)   3-way compare -> -1 / 0 / +1; S=1 signed at width W, S=0 unsigned
%   @slc(V, Lo, W)      bit slice V[Lo+W-1 : Lo] -- args (value, LOW bit, WIDTH), NOT SV [hi:lo]
%   @parity(V, W)       XOR-reduction of V's bits -> 0/1
%   @popcnt(V, W)       count of 1-bits in V[W-1:0] ($countones)
%   @rand(V, W)        AND-reduction &V over W bits -> 0/1 (V == all-ones)
%   @ror(V, W)         OR-reduction  |V over W bits -> 0/1 (V != 0)
%   @rxor(V, W)        XOR-reduction ^V over W bits -> 0/1 (parity)
%   @rnand(V, W)       NAND-reduction ~&V over W bits -> 0/1
%   @rnor(V, W)        NOR-reduction  ~|V over W bits -> 0/1
%   @rxnor(V, W)       XNOR-reduction ~^V over W bits -> 0/1
%   @clz(V, SGN)       count-leading-zeros (SGN=0) or leading-sign-bits (SGN=1) of V[63:0] -> 0..64
#script (python)
from clingo import Number, String, SymbolType
def _wv(x):  return x.number if x.type == SymbolType.Number else int(x.string)   # Number|String -> int
def _we(r):  return Number(r) if r < 2 ** 31 else String(str(r))   # int -> canonical Number|String
def add(a, b, w):     return _we((_wv(a) + _wv(b)) % (2 ** w.number))   # wrap mod 2^w
def sub(a, b, w):     return _we((_wv(a) - _wv(b)) % (2 ** w.number))   # SV subtraction wraps
def mul(a, b, w):     return _we((_wv(a) * _wv(b)) % (2 ** w.number))   # wrap mod 2^w
def idiv(a, b, w): return _we((_wv(a)//_wv(b))%(2**w.number)) if _wv(b) else _we(0)  # /0->0
def imod(a, b, w): return _we((_wv(a)%_wv(b))%(2**w.number)) if _wv(b) else _we(0)  # %0->0
def sidiv(a, b, w):
    bb = _wv(b)
    if not bb: return _we(0)
    m = 2 ** w.number; h = 1 << (w.number - 1)
    A = _wv(a) - m if _wv(a) & h else _wv(a)
    B = bb - m if bb & h else bb
    q = abs(A) // abs(B)
    return _we((-q if (A < 0) != (B < 0) else q) % m)   # signed /, trunc toward zero
def simod(a, b, w):
    bb = _wv(b)
    if not bb: return _we(0)
    m = 2 ** w.number; h = 1 << (w.number - 1)
    A = _wv(a) - m if _wv(a) & h else _wv(a)
    B = bb - m if bb & h else bb
    q = abs(A) // abs(B)
    if (A < 0) != (B < 0): q = -q
    return _we((A - B * q) % m)   # signed %, sign of dividend
def band(a, b, w):    return _we(_wv(a) & _wv(b))   # bitwise (no overflow)
def bor(a, b, w):     return _we(_wv(a) | _wv(b))   # bitwise (no overflow)
def bxor(a, b, w):    return _we(_wv(a) ^ _wv(b))   # bitwise (no overflow)
def shl(a, b, w):     return _we((_wv(a) << _wv(b)) % (2 ** w.number))   # left shift, trunc
def shr(a, b, w):     return _we(_wv(a) >> _wv(b))   # logical right shift (zero-fill)
def ashr(a, n, w):
    x = _wv(a)
    s = x - (2 ** w.number) if (x >> (w.number - 1)) & 1 else x
    return _we((s >> _wv(n)) % (2 ** w.number))
def ipow(a, b, w):    return _we((_wv(a) ** _wv(b)) % (2 ** w.number))   # wrap mod 2^w
def bnot(v, w):     return _we((~_wv(v)) & (2 ** w.number - 1))   # bitwise complement ~v
def neg(v, w):      return _we((-_wv(v)) % (2 ** w.number))   # two's-complement negate -v
def sext(v, fw, tw):
    x = _wv(v)
    s = x - (2 ** fw.number) if (x >> (fw.number - 1)) & 1 else x
    return _we(s % (2 ** tw.number))
def signed(v, w): x=_wv(v); return Number(x-(2**w.number) if x>>(w.number-1)&1 else x)
def wcmp(a, b, w, s):
    x = _wv(a); y = _wv(b)
    if s.number:
        m = 2 ** w.number; h = 1 << (w.number - 1)
        x = x - m if x & h else x
        y = y - m if y & h else y
    return Number((x > y) - (x < y))
def slc(v, lo, w):    return _we((_wv(v) >> lo.number) % (2 ** w.number))   # v[lo+w-1:lo] -- args=(V,LOW,WIDTH), not [hi:lo]
def parity(v, w):     return Number(bin(_wv(v)).count('1') % 2)   # reduction xor
def popcnt(v, w):    return Number(bin(_wv(v) & (2 ** w.number - 1)).count('1'))   # $countones
def rand(v, w):   return Number(1 if (_wv(v) & (2**w.number-1)) == 2**w.number-1 else 0)  # &v
def ror(v, w):    return Number(1 if (_wv(v) & (2**w.number-1)) != 0 else 0)   # |v
def rxor(v, w):   return Number(bin(_wv(v) & (2**w.number-1)).count('1') % 2)   # ^v
def rnand(v, w):  return Number(0 if (_wv(v) & (2**w.number-1)) == 2**w.number-1 else 1)  # ~&v
def rnor(v, w):   return Number(0 if (_wv(v) & (2**w.number-1)) != 0 else 1)   # ~|v
def rxnor(v, w):  return Number(1 - bin(_wv(v) & (2**w.number-1)).count('1') % 2)  # ~^v
def clz(v, sgn, w):
    x = _wv(v) & 0xFFFFFFFFFFFFFFFF
    if sgn.number:
        x = ((x ^ ((x << 1) & 0xFFFFFFFFFFFFFFFF)) | 1) & 0xFFFFFFFFFFFFFFFF
    return Number(64 - x.bit_length() if x else 64)

# ---- aspfirst additions: compare helpers, issym, and the symbolic wrappers (see aspfirst_symbolic.lp) ----
from clingo import Function
def _issym(x):  return x.type == SymbolType.Function and len(x.arguments) > 0   # a compound term = a data token
def issym(x):   return Number(1 if _issym(x) else 0)
def truth(x):   # SV truth of a value: 0 = a concrete zero, 1 = a concrete non-zero (a wide String is never 0, an enum tag is true), 2 = a TERM
    if _issym(x): return Number(2)
    if x.type == SymbolType.Number: return Number(0 if x.number == 0 else 1)
    return Number(1)
def eq(a, b):   return Number(1 if a == b else 0)     # symbol equality: values are canonical, tags are constants
def ne(a, b):   return Number(0 if a == b else 1)
def lt(a, b, w):  return Number(1 if wcmp(a, b, w, Number(0)).number == -1 else 0)
def le(a, b, w):  return Number(1 if wcmp(a, b, w, Number(0)).number != 1 else 0)
def gt(a, b, w):  return Number(1 if wcmp(a, b, w, Number(0)).number == 1 else 0)
def ge(a, b, w):  return Number(1 if wcmp(a, b, w, Number(0)).number != -1 else 0)
def slt(a, b, w): return Number(1 if wcmp(a, b, w, Number(1)).number == -1 else 0)
def sle(a, b, w): return Number(1 if wcmp(a, b, w, Number(1)).number != 1 else 0)
def sgt(a, b, w): return Number(1 if wcmp(a, b, w, Number(1)).number == 1 else 0)
def sge(a, b, w): return Number(1 if wcmp(a, b, w, Number(1)).number != -1 else 0)
def _symwrap(name, f, nvals):
    def g(*args):
        if any(_issym(x) for x in args[:nvals]): return Function(name, list(args))
        return f(*args)
    return g

add = _symwrap('add', add, 2)
sub = _symwrap('sub', sub, 2)
mul = _symwrap('mul', mul, 2)
idiv = _symwrap('idiv', idiv, 2)
imod = _symwrap('imod', imod, 2)
sidiv = _symwrap('sidiv', sidiv, 2)
simod = _symwrap('simod', simod, 2)
band = _symwrap('band', band, 2)
bor = _symwrap('bor', bor, 2)
bxor = _symwrap('bxor', bxor, 2)
shl = _symwrap('shl', shl, 2)
shr = _symwrap('shr', shr, 2)
ashr = _symwrap('ashr', ashr, 2)
ipow = _symwrap('ipow', ipow, 2)
bnot = _symwrap('bnot', bnot, 1)
neg = _symwrap('neg', neg, 1)
sext = _symwrap('sext', sext, 1)
signed = _symwrap('signed', signed, 1)
wcmp = _symwrap('wcmp', wcmp, 2)
slc = _symwrap('slc', slc, 1)
parity = _symwrap('parity', parity, 1)
popcnt = _symwrap('popcnt', popcnt, 1)
rand = _symwrap('rand', rand, 1)
ror = _symwrap('ror', ror, 1)
rxor = _symwrap('rxor', rxor, 1)
rnand = _symwrap('rnand', rnand, 1)
rnor = _symwrap('rnor', rnor, 1)
rxnor = _symwrap('rxnor', rxnor, 1)
clz = _symwrap('clz', clz, 1)
eq = _symwrap('eq', eq, 2)
ne = _symwrap('ne', ne, 2)
lt = _symwrap('lt', lt, 2)
le = _symwrap('le', le, 2)
gt = _symwrap('gt', gt, 2)
ge = _symwrap('ge', ge, 2)
slt = _symwrap('slt', slt, 2)
sle = _symwrap('sle', sle, 2)
sgt = _symwrap('sgt', sgt, 2)
sge = _symwrap('sge', sge, 2)
#end.
% ---- END GENERATED ----

% the authored vocabulary + the scenario's clock: declared so an unused predicate is not an `info`
#defined def/2.  #defined inst/2.  #defined pin/3.  #defined iparam/3.  #defined port/3.  #defined net/2.
#defined enum_member/3.  #defined param/2.  #defined time/2.  #defined abstract/1.  #defined data/1.  #defined mparam/3.

% ---- time -----------------------------------------------------------------------------------
gtime(T) :- time(_, T).

% ---- wires ----------------------------------------------------------------------------------
wire(N, W) :- port(N, _, W).
wire(N, W) :- net(N, W).
wire(N, W) :- arch_reg(N, W).      % an architectural single register IS a net; see arch_reg below
#defined arch_reg/2.
clock(C)   :- pin(_, clk, C).          % a clock is a TIME domain (time(C, T)), it carries no val
clock(C)   :- time(C, _).              % (also whatever the scenario ticks -- a level with no cells yet)

% ---- expression evaluation ------------------------------------------------------------------
% `term/1` is the closure of every subterm the design mentions, so each `ev` rule is safe and
% grounds only over the design's own terms (linear in subterms x instants).
term(E) :- def(_, E).
term(A) :- term(mrd(_, A)).
term(A) :- term(add(A, _, _)).      term(B) :- term(add(_, B, _)).
term(A) :- term(sub(A, _, _)).      term(B) :- term(sub(_, B, _)).
term(A) :- term(mul(A, _, _)).      term(B) :- term(mul(_, B, _)).
term(A) :- term(and(A, _, _)).      term(B) :- term(and(_, B, _)).
term(A) :- term(or(A, _, _)).       term(B) :- term(or(_, B, _)).
term(A) :- term(xor(A, _, _)).      term(B) :- term(xor(_, B, _)).
term(A) :- term(shl(A, _, _)).      term(B) :- term(shl(_, B, _)).
term(A) :- term(shr(A, _, _)).      term(B) :- term(shr(_, B, _)).
term(A) :- term(ashr(A, _, _)).     term(B) :- term(ashr(_, B, _)).
term(A) :- term(idiv(A, _, _)).     term(B) :- term(idiv(_, B, _)).
term(A) :- term(imod(A, _, _)).     term(B) :- term(imod(_, B, _)).
term(A) :- term(sidiv(A, _, _)).    term(B) :- term(sidiv(_, B, _)).
term(A) :- term(simod(A, _, _)).    term(B) :- term(simod(_, B, _)).
term(A) :- term(bnot(A, _)).         term(A) :- term(neg(A, _)).
term(A) :- term(sext(A, _, _)).     term(A) :- term(slc(A, _, _)).      term(A) :- term(bit(A, _)).
term(A) :- term(cat(A, _, _, _)).   term(B) :- term(cat(_, _, B, _)).
term(A) :- term(eq(A, _)).          term(B) :- term(eq(_, B)).
term(A) :- term(ne(A, _)).          term(B) :- term(ne(_, B)).
term(A) :- term(lt(A, _, _)).       term(B) :- term(lt(_, B, _)).
term(A) :- term(le(A, _, _)).       term(B) :- term(le(_, B, _)).
term(A) :- term(gt(A, _, _)).       term(B) :- term(gt(_, B, _)).
term(A) :- term(ge(A, _, _)).       term(B) :- term(ge(_, B, _)).
term(A) :- term(slt(A, _, _)).      term(B) :- term(slt(_, B, _)).
term(A) :- term(sle(A, _, _)).      term(B) :- term(sle(_, B, _)).
term(A) :- term(sgt(A, _, _)).      term(B) :- term(sgt(_, B, _)).
term(A) :- term(sge(A, _, _)).      term(B) :- term(sge(_, B, _)).
term(A) :- term(logand(A, _)).      term(B) :- term(logand(_, B)).
term(A) :- term(logor(A, _)).       term(B) :- term(logor(_, B)).
term(A) :- term(lnot(A)).
term(A) :- term(ror(A, _)).         term(A) :- term(rand(A, _)).        term(A) :- term(rxor(A, _)).
term(A) :- term(rnand(A, _)).       term(A) :- term(rnor(A, _)).        term(A) :- term(rxnor(A, _)).
term(A) :- term(parity(A, _)).      term(A) :- term(popcnt(A, _)).      term(A) :- term(clz(A, _)).
term(S) :- term(ite(S, _, _)).      term(A) :- term(ite(_, A, _)).      term(B) :- term(ite(_, _, B)).

% a defined signal takes its expression's value at every instant
val(N, V, T) :- def(N, E), ev(E, V, T).

% leaves
ev(N, V, T)        :- term(N), wire(N, _), val(N, V, T).
ev(k(V, W), V, T)  :- term(k(V, W)), gtime(T).
ev(tag(L), L, T)   :- term(tag(L)), gtime(T).
% a flop-array read: `mrd(M, A)` is the cell at the value of A, this instant -- an expression, so any
% number of readers at any number of indices compose (the reason `farray` exists, see above)
ev(mrd(M, A), V, T) :- term(mrd(M, A)), ev(A, VA, T), val(cell(M, VA), V, T).

% arithmetic / bitwise -- each op is the SAME @func the translator emits, at the same width
evl(add(A, B, W), VA, T) :- term(add(A, B, W)), ev(A, VA, T).
ev(add(A, B, W), V, T) :- evl(add(A, B, W), VA, T), ev(B, VB, T), V = @add(VA, VB, W).
evl(sub(A, B, W), VA, T) :- term(sub(A, B, W)), ev(A, VA, T).
ev(sub(A, B, W), V, T) :- evl(sub(A, B, W), VA, T), ev(B, VB, T), V = @sub(VA, VB, W).
evl(mul(A, B, W), VA, T) :- term(mul(A, B, W)), ev(A, VA, T).
ev(mul(A, B, W), V, T) :- evl(mul(A, B, W), VA, T), ev(B, VB, T), V = @mul(VA, VB, W).
evl(and(A, B, W), VA, T) :- term(and(A, B, W)), ev(A, VA, T).
ev(and(A, B, W), V, T) :- evl(and(A, B, W), VA, T), ev(B, VB, T), V = @band(VA, VB, W).
evl(or(A, B, W), VA, T) :- term(or(A, B, W)), ev(A, VA, T).
ev(or(A, B, W), V, T) :- evl(or(A, B, W), VA, T), ev(B, VB, T), V = @bor(VA, VB, W).
evl(xor(A, B, W), VA, T) :- term(xor(A, B, W)), ev(A, VA, T).
ev(xor(A, B, W), V, T) :- evl(xor(A, B, W), VA, T), ev(B, VB, T), V = @bxor(VA, VB, W).
evl(shl(A, B, W), VA, T) :- term(shl(A, B, W)), ev(A, VA, T).
ev(shl(A, B, W), V, T) :- evl(shl(A, B, W), VA, T), ev(B, VB, T), V = @shl(VA, VB, W).
evl(shr(A, B, W), VA, T) :- term(shr(A, B, W)), ev(A, VA, T).
ev(shr(A, B, W), V, T) :- evl(shr(A, B, W), VA, T), ev(B, VB, T), V = @shr(VA, VB, W).
evl(ashr(A, B, W), VA, T) :- term(ashr(A, B, W)), ev(A, VA, T).
ev(ashr(A, B, W), V, T) :- evl(ashr(A, B, W), VA, T), ev(B, VB, T), V = @ashr(VA, VB, W).
evl(idiv(A, B, W), VA, T) :- term(idiv(A, B, W)), ev(A, VA, T).
ev(idiv(A, B, W), V, T) :- evl(idiv(A, B, W), VA, T), ev(B, VB, T), V = @idiv(VA, VB, W).
evl(imod(A, B, W), VA, T) :- term(imod(A, B, W)), ev(A, VA, T).
ev(imod(A, B, W), V, T) :- evl(imod(A, B, W), VA, T), ev(B, VB, T), V = @imod(VA, VB, W).
evl(sidiv(A, B, W), VA, T) :- term(sidiv(A, B, W)), ev(A, VA, T).
ev(sidiv(A, B, W), V, T) :- evl(sidiv(A, B, W), VA, T), ev(B, VB, T), V = @sidiv(VA, VB, W).
evl(simod(A, B, W), VA, T) :- term(simod(A, B, W)), ev(A, VA, T).
ev(simod(A, B, W), V, T) :- evl(simod(A, B, W), VA, T), ev(B, VB, T), V = @simod(VA, VB, W).
ev(bnot(A, W), V, T)     :- term(bnot(A, W)),      ev(A, VA, T), V = @bnot(VA, W).
ev(neg(A, W), V, T)      :- term(neg(A, W)),      ev(A, VA, T), V = @neg(VA, W).
ev(sext(A, F, W), V, T)  :- term(sext(A, F, W)),  ev(A, VA, T), V = @sext(VA, F, W).
% slc / bit / reductions / compares are BOUNDARY-CAPABLE: their result may be a control value
% computed from data. They go through bres/3 (the op's raw @func result); a concrete result passes
% straight through below; a symbolic one (a term -- data reached the op) is resolved by the
% symbolic companion: kept as a data term where the role is data, freed as a boundary choice per
% distinct term otherwise (aspfirst_symbolic.lp).
bres(slc(A, L, W), R, T)   :- term(slc(A, L, W)),   ev(A, VA, T), R = @slc(VA, L, W).
bres(bit(A, I), R, T)      :- term(bit(A, I)),      ev(A, VA, T), R = @slc(VA, I, 1).
evl(cat(A, WA, B, WB), VA, T) :- term(cat(A, WA, B, WB)), ev(A, VA, T).
ev(cat(A, WA, B, WB), V, T) :- evl(cat(A, WA, B, WB), VA, T), ev(B, VB, T),
                               H = @shl(VA, WB, WA + WB), V = @bor(H, VB, WA + WB).
% reductions
bres(ror(A, W), R, T)    :- term(ror(A, W)),    ev(A, VA, T), R = @ror(VA, W).
bres(rand(A, W), R, T)   :- term(rand(A, W)),   ev(A, VA, T), R = @rand(VA, W).
bres(rxor(A, W), R, T)   :- term(rxor(A, W)),   ev(A, VA, T), R = @rxor(VA, W).
bres(rnand(A, W), R, T)  :- term(rnand(A, W)),  ev(A, VA, T), R = @rnand(VA, W).
bres(rnor(A, W), R, T)   :- term(rnor(A, W)),   ev(A, VA, T), R = @rnor(VA, W).
bres(rxnor(A, W), R, T)  :- term(rxnor(A, W)),  ev(A, VA, T), R = @rxnor(VA, W).
bres(parity(A, W), R, T) :- term(parity(A, W)), ev(A, VA, T), R = @parity(VA, W).
bres(popcnt(A, W), R, T) :- term(popcnt(A, W)), ev(A, VA, T), R = @popcnt(VA, W).
bres(clz(A, S), R, T)    :- term(clz(A, S)),    ev(A, VA, T), R = @clz(VA, S, 64).
% comparisons -- through the aspfirst compare helpers: equality is symbol equality (canonical wide
% values, enum tags), ORDER goes through @wcmp inside them (native `<` on a wide String is
% lexicographic -- hard rule 4). Boundary-capable like the ops above.
% STAGED like the arithmetic above: bind the left operand through the term first. gringo's
% join-order heuristic put these two on the raw ev x ev cross-product at 2^10 (16.4M @eq +
% 16.4M @ne calls on ve146's step -- 135 of its 138 seconds); staging caps the candidates at
% the semantic minimum, per-term |A| x |B|.
evl(eq(A, B), VA, T) :- term(eq(A, B)), ev(A, VA, T).
evl(ne(A, B), VA, T) :- term(ne(A, B)), ev(A, VA, T).
bres(eq(A, B), R, T)     :- evl(eq(A, B), VA, T), ev(B, VB, T), R = @eq(VA, VB).
bres(ne(A, B), R, T)     :- evl(ne(A, B), VA, T), ev(B, VB, T), R = @ne(VA, VB).
evl(lt(A, B, W), VA, T) :- term(lt(A, B, W)), ev(A, VA, T).
bres(lt(A, B, W), R, T) :- evl(lt(A, B, W), VA, T), ev(B, VB, T), R = @lt(VA, VB, W).
evl(le(A, B, W), VA, T) :- term(le(A, B, W)), ev(A, VA, T).
bres(le(A, B, W), R, T) :- evl(le(A, B, W), VA, T), ev(B, VB, T), R = @le(VA, VB, W).
evl(gt(A, B, W), VA, T) :- term(gt(A, B, W)), ev(A, VA, T).
bres(gt(A, B, W), R, T) :- evl(gt(A, B, W), VA, T), ev(B, VB, T), R = @gt(VA, VB, W).
evl(ge(A, B, W), VA, T) :- term(ge(A, B, W)), ev(A, VA, T).
bres(ge(A, B, W), R, T) :- evl(ge(A, B, W), VA, T), ev(B, VB, T), R = @ge(VA, VB, W).
evl(slt(A, B, W), VA, T) :- term(slt(A, B, W)), ev(A, VA, T).
bres(slt(A, B, W), R, T) :- evl(slt(A, B, W), VA, T), ev(B, VB, T), R = @slt(VA, VB, W).
evl(sle(A, B, W), VA, T) :- term(sle(A, B, W)), ev(A, VA, T).
bres(sle(A, B, W), R, T) :- evl(sle(A, B, W), VA, T), ev(B, VB, T), R = @sle(VA, VB, W).
evl(sgt(A, B, W), VA, T) :- term(sgt(A, B, W)), ev(A, VA, T).
bres(sgt(A, B, W), R, T) :- evl(sgt(A, B, W), VA, T), ev(B, VB, T), R = @sgt(VA, VB, W).
evl(sge(A, B, W), VA, T) :- term(sge(A, B, W)), ev(A, VA, T).
bres(sge(A, B, W), R, T) :- evl(sge(A, B, W), VA, T), ev(B, VB, T), R = @sge(VA, VB, W).
% a CONCRETE boundary-capable result is the op's value; a symbolic one waits for the companion
ev(E, R, T) :- bres(E, R, T), @issym(R) = 0.
% logical -- SV truth: a value is true iff it is not 0. Through @truth: 0 = a concrete zero, 1 = a
% concrete non-zero (a wide String is never 0; an enum tag counts as true), 2 = a TERM -- the symbolic
% reading's companion then builds the logical TERM instead (aspfirst_symbolic.lp), so a term is never
% silently read as "true".
% `tv/4` tables SV truth ONCE per ev tuple of a logical operand (linear by construction), so
% no @truth call ever sits inside a candidate join. Measured on ve146_serialdata's induction
% step: the un-tabled rules put @truth in an ev x ev cross-product -- 1.28M Python calls at a
% free 8-bit register, quadratic in the ev table -- and the step never grounded at 10 bits.
tvarg(A) :- term(logand(A, _)).   tvarg(B) :- term(logand(_, B)).
tvarg(A) :- term(logor(A, _)).    tvarg(B) :- term(logor(_, B)).
tvarg(A) :- term(lnot(A)).        tvarg(S) :- term(ite(S, _, _)).
tv(A, VA, R, T) :- tvarg(A), ev(A, VA, T), R = @truth(VA).
ev(logand(A, B), 0, T) :- term(logand(A, B)), tv(A, _, 0, T), ev(B, _, T).
ev(logand(A, B), 0, T) :- term(logand(A, B)), ev(A, _, T), tv(B, _, 0, T).
ev(logand(A, B), 1, T) :- term(logand(A, B)), tv(A, _, 1, T), tv(B, _, 1, T).
ev(logor(A, B), 1, T)  :- term(logor(A, B)),  tv(A, _, 1, T), ev(B, _, T).
ev(logor(A, B), 1, T)  :- term(logor(A, B)),  ev(A, _, T), tv(B, _, 1, T).
ev(logor(A, B), 0, T)  :- term(logor(A, B)),  tv(A, _, 0, T), tv(B, _, 0, T).
ev(lnot(A), 1, T)      :- term(lnot(A)), tv(A, _, 0, T).
ev(lnot(A), 0, T)      :- term(lnot(A)), tv(A, _, 1, T).
% selection -- a concrete selector picks ONE arm (only that arm is joined); a term selector is the companion's
ev(ite(S, A, B), V, T) :- term(ite(S, A, B)), tv(S, _, 1, T), ev(A, V, T).
ev(ite(S, A, B), V, T) :- term(ite(S, A, B)), tv(S, _, 0, T), ev(B, V, T).

% ---- primitives -- the emitted schema shapes with the instance's pins joined in --------------
% ff: capture on en=1, hold on en=0 (TRANSLATION_SPEC S4.1; the FF cell of primitives_demo)
val(Q, V, T+1) :- inst(I, ff), pin(I, clk, CK), pin(I, en, EN), pin(I, d, D), pin(I, q, Q),
                  time(CK, T), T < k, val(EN, 1, T), val(D, V, T).
val(Q, V, T+1) :- inst(I, ff), pin(I, clk, CK), pin(I, en, EN), pin(I, q, Q),
                  time(CK, T), T < k, val(EN, 0, T), val(Q, V, T).

% arff: async active-low reset, read at BOTH ends of the edge (S4.2; Async.lean arff_exactly_one)
%   (A) level force -- no clock;  (R) the edge under reset;  (B) capture;  (C) hold
val(Q, RV, T)   :- inst(I, arff), pin(I, rstL, R), pin(I, q, Q), iparam(I, reset_value, RV),
                   val(R, 0, T).
val(Q, RV, T+1) :- inst(I, arff), pin(I, clk, CK), pin(I, rstL, R), pin(I, q, Q),
                   iparam(I, reset_value, RV), time(CK, T), T < k, val(R, 0, T), val(R, 1, T+1).
val(Q, V, T+1)  :- inst(I, arff), pin(I, clk, CK), pin(I, rstL, R), pin(I, en, EN), pin(I, d, D),
                   pin(I, q, Q), time(CK, T), T < k, val(R, 1, T), val(R, 1, T+1),
                   val(EN, 1, T), val(D, V, T).
val(Q, V, T+1)  :- inst(I, arff), pin(I, clk, CK), pin(I, rstL, R), pin(I, en, EN), pin(I, q, Q),
                   time(CK, T), T < k, val(R, 1, T), val(R, 1, T+1),
                   val(EN, 0, T), val(Q, V, T).

% ---- DERIVED CLOCKS (2026-08-27, the divided_counter entry) ---------------------------------
% A clock pin wired to a net the DESIGN COMPUTES (never an input port) is a DERIVED clock: it
% has no free time axis -- its edges are value transitions on the master axis. A register it
% clocks updates exactly across the net's RISING transitions (value 0 at T, 1 at T+1), reading
% its inputs at T -- the async-reset both-ends reading -- and HOLDS across every other pair of
% instants. The hold's complement-of-a-rise is spelled with two POSITIVE cases (CK=1 at T, or
% CK=0 at T+1), so the design layer stays positive-definite; the one negation below is the
% STATIC port/net classification, stratified by construction (facts only, no temporal cycle).
clock_port(CK) :- port(CK, input, _).
derived_clock(CK) :- inst(I, _), pin(I, clk, CK), not clock_port(CK).

% ff on a derived clock: capture on the rise (en=1), hold otherwise
val(Q, V, T+1) :- inst(I, ff), pin(I, clk, CK), derived_clock(CK), pin(I, en, EN), pin(I, d, D),
                  pin(I, q, Q), gtime(T), T < k, val(CK, 0, T), val(CK, 1, T+1),
                  val(EN, 1, T), val(D, V, T).
val(Q, V, T+1) :- inst(I, ff), pin(I, clk, CK), derived_clock(CK), pin(I, en, EN), pin(I, q, Q),
                  gtime(T), T < k, val(CK, 0, T), val(CK, 1, T+1), val(EN, 0, T), val(Q, V, T).
val(Q, V, T+1) :- inst(I, ff), pin(I, clk, CK), derived_clock(CK), pin(I, q, Q),
                  gtime(T), T < k, val(CK, 1, T), val(Q, V, T).
val(Q, V, T+1) :- inst(I, ff), pin(I, clk, CK), derived_clock(CK), pin(I, q, Q),
                  gtime(T), T < k, val(CK, 0, T+1), val(Q, V, T).

% arff on a derived clock: the level force (A) is clock-free and already applies; (R) the
% release edge keeps the reset value; (B) capture on the rise with reset high at both ends;
% (C) hold -- the two positive non-rise cases, plus en=0 on a rise
val(Q, RV, T+1) :- inst(I, arff), pin(I, clk, CK), derived_clock(CK), pin(I, rstL, R),
                   pin(I, q, Q), iparam(I, reset_value, RV),
                   gtime(T), T < k, val(R, 0, T), val(R, 1, T+1).
val(Q, V, T+1)  :- inst(I, arff), pin(I, clk, CK), derived_clock(CK), pin(I, rstL, R),
                   pin(I, en, EN), pin(I, d, D), pin(I, q, Q),
                   gtime(T), T < k, val(R, 1, T), val(R, 1, T+1),
                   val(CK, 0, T), val(CK, 1, T+1), val(EN, 1, T), val(D, V, T).
val(Q, V, T+1)  :- inst(I, arff), pin(I, clk, CK), derived_clock(CK), pin(I, rstL, R),
                   pin(I, en, EN), pin(I, q, Q),
                   gtime(T), T < k, val(R, 1, T), val(R, 1, T+1),
                   val(CK, 0, T), val(CK, 1, T+1), val(EN, 0, T), val(Q, V, T).
val(Q, V, T+1)  :- inst(I, arff), pin(I, clk, CK), derived_clock(CK), pin(I, rstL, R),
                   pin(I, q, Q), gtime(T), T < k, val(R, 1, T), val(R, 1, T+1),
                   val(CK, 1, T), val(Q, V, T).
val(Q, V, T+1)  :- inst(I, arff), pin(I, clk, CK), derived_clock(CK), pin(I, rstL, R),
                   pin(I, q, Q), gtime(T), T < k, val(R, 1, T), val(R, 1, T+1),
                   val(CK, 0, T+1), val(Q, V, T).

% lata: level-sensitive latch -- transparent while en=1 (same instant), holds when en=0 (S4.3)
val(Q, V, T)   :- inst(I, lata), pin(I, en, EN), pin(I, d, D), pin(I, q, Q), val(EN, 1, T), val(D, V, T).
val(Q, V, T+1) :- inst(I, lata), pin(I, en, EN), pin(I, q, Q), val(EN, 0, T+1), val(Q, V, T).

% spram: one write port, combinational read. Cells are val(cell(M, A), V, T); the write and the
% `mem_hold` partition are the memory shape of S5.3 (every cell is written or held, each cycle).
addr(M, A) :- inst(M, spram), iparam(M, depth, D), A = 0..D-1.
% (an ARCHITECTURAL memory -- `arch_mem(M, D, W)`, state the spec may name -- that the level leaves
%  ABSTRACT gets its `addr` and its free cells from the abstraction companion, aspfirst_abstract.lp)
#defined arch_mem/3.
val(cell(M, A), V, T+1) :- inst(M, spram), pin(M, clk, CK), pin(M, we, WE), pin(M, wa, WA), pin(M, wd, WD),
                           time(CK, T), T < k, val(WE, 1, T), val(WA, A, T), addr(M, A), val(WD, V, T).
val(cell(M, A), V, T+1) :- inst(M, spram), pin(M, clk, CK), time(CK, T), T < k,
                           val(cell(M, A), V, T), mem_hold(M, A, T).
mem_hold(M, A, T) :- addr(M, A), pin(M, we, WE), val(WE, 0, T).
mem_hold(M, A, T) :- addr(M, A), pin(M, we, WE), pin(M, wa, WA), val(WE, 1, T), val(WA, B, T), A != B.
val(RD, V, T) :- inst(M, spram), pin(M, ra, RA), pin(M, rd, RD), val(RA, A, T), val(cell(M, A), V, T).

% farray: an array of REGISTERS -- addressable cells, ONE write port, and ANY number of combinational
% readers, which are `mrd(M, A)` EXPRESSIONS rather than ports (a read of a flop array is logic, not a
% port). This is not a RAM and must not be modelled as one: the distinguishing evidence is that an
% async reset forces EVERY cell at the same instant, which no SRAM can do. VerilogEval's `gshare`
% reference is exactly this shape -- `logic [1:0] pht [127:0]` read at two indices in one cycle
% (seven reads in all) and reset by `for (i...) pht[i] = LNT;` inside its reset branch. Use `spram`
% when the design really has ports and a port conflict to reason about; use `farray` for a register
% file, a small table, a predictor's counters.
%   (A) level force -- no clock;  (R) the edge under reset;  (B) the write;  (C) the hold
%   Mirrors the translator's unpacked-array-register shape, including the per-CELL reset force (F16).
addr(M, A) :- inst(M, farray), iparam(M, depth, D), A = 0..D-1.
fa_rst(M, T) :- inst(M, farray), pin(M, rstL, R), val(R, 0, T).
fa_run(M, T) :- inst(M, farray), pin(M, rstL, R), val(R, 1, T).
fa_run(M, T) :- inst(M, farray), gtime(T), not fa_has_rst(M).      % a farray may have no reset at all
fa_has_rst(M) :- inst(M, farray), pin(M, rstL, _).
val(cell(M, A), RV, T)   :- fa_rst(M, T), addr(M, A), iparam(M, reset_value, RV).
val(cell(M, A), RV, T+1) :- inst(M, farray), pin(M, clk, CK), time(CK, T), T < k, addr(M, A),
                            iparam(M, reset_value, RV), fa_rst(M, T), fa_run(M, T+1).
val(cell(M, A), V, T+1)  :- inst(M, farray), pin(M, clk, CK), pin(M, we, WE), pin(M, wa, WA),
                            pin(M, wd, WD), time(CK, T), T < k, fa_run(M, T), fa_run(M, T+1),
                            val(WE, 1, T), val(WA, A, T), addr(M, A), val(WD, V, T).
val(cell(M, A), V, T+1)  :- inst(M, farray), pin(M, clk, CK), time(CK, T), T < k,
                            fa_run(M, T), fa_run(M, T+1), val(cell(M, A), V, T), fa_hold(M, A, T).
fa_hold(M, A, T) :- inst(M, farray), addr(M, A), pin(M, we, WE), val(WE, 0, T).
fa_hold(M, A, T) :- inst(M, farray), addr(M, A), pin(M, we, WE), pin(M, wa, WA),
                    val(WE, 1, T), val(WA, B, T), A != B.
