"""Width-generic Python @func library for the #script(python) block.

Each function takes the width as an argument (catalog Section 3.10), so the same
emitted program re-grounds at any size. Only functions actually referenced by the
emitted rules are included, in a fixed canonical order (determinism).

VALUE ENCODING (wide arithmetic). clingo's integer is 32-bit signed, so a value
that does not fit (>= 2^31) cannot be a clingo Number. Values are therefore
**magnitude-canonical**: a Number when 0 <= v < 2^31, else a clingo String of its
decimal form (masked, non-negative, no leading zeros). `_wv` decodes either form
to a Python int; `_we` re-encodes by magnitude. Because the form is canonical,
equal values have identical symbols -- so `==`/`!=` and the |x/&x reductions stay
native; only ORDERING compares need the `wcmp` helper. Narrow signals (<2^31)
are pure Numbers, exactly as before.
"""

from __future__ import annotations

# decode/encode helpers, prepended to every emitted #script block.
_HELPERS = (
    "def _wv(x):  return x.number if x.type == SymbolType.Number else int(x.string)   # Number|String -> int\n"
    "def _we(r):  return Number(r) if r < 2 ** 31 else String(str(r))   # int -> canonical Number|String"
)

# name -> source lines of the def
_LIB: dict[str, str] = {
    "add": "def add(a, b, w):     return _we((_wv(a) + _wv(b)) % (2 ** w.number))   # wrap mod 2^w",
    "sub": "def sub(a, b, w):     return _we((_wv(a) - _wv(b)) % (2 ** w.number))   # SV subtraction wraps",
    "mul": "def mul(a, b, w):     return _we((_wv(a) * _wv(b)) % (2 ** w.number))   # wrap mod 2^w",
    "and": "def band(a, b, w):    return _we(_wv(a) & _wv(b))   # bitwise (no overflow)",
    "or":  "def bor(a, b, w):     return _we(_wv(a) | _wv(b))   # bitwise (no overflow)",
    "xor": "def bxor(a, b, w):    return _we(_wv(a) ^ _wv(b))   # bitwise (no overflow)",
    "shl": "def shl(a, b, w):     return _we((_wv(a) << _wv(b)) % (2 ** w.number))   # left shift, trunc",
    "shr": "def shr(a, b, w):     return _we(_wv(a) >> _wv(b))   # logical right shift (zero-fill)",
    "pow": "def ipow(a, b, w):    return _we((_wv(a) ** _wv(b)) % (2 ** w.number))   # wrap mod 2^w",
    "div": "def idiv(a, b, w): return _we((_wv(a)//_wv(b))%(2**w.number)) if _wv(b) else _we(0)  # /0->0",
    "mod": "def imod(a, b, w): return _we((_wv(a)%_wv(b))%(2**w.number)) if _wv(b) else _we(0)  # %0->0",
    "not": "def bnot(v, w):     return _we((~_wv(v)) & (2 ** w.number - 1))   # bitwise complement ~v",
    "neg": "def neg(v, w):      return _we((-_wv(v)) % (2 ** w.number))   # two's-complement negate -v",
    # args are (value, LOW bit, WIDTH), not SV's [hi:lo]: x[71:40] (32b, low=40) -> @slc(V,40,32).
    "slc": "def slc(v, lo, w):    return _we((_wv(v) >> lo.number) % (2 ** w.number))"
           "   # v[lo+w-1:lo] -- args=(V,LOW,WIDTH), not [hi:lo]",
    "parity": "def parity(v, w):     return Number(bin(_wv(v)).count('1') % 2)   # reduction xor",
    "popcnt": "def popcnt(v, w):    return Number(bin(_wv(v) & (2 ** w.number - 1)).count('1'))   # $countones",
    # bit-reductions to 0/1 over V[w-1:0], for a reduction used INSIDE a word expression (|x,&x,^x
    # and negated). |x = (v!=0); &x = (v==all-ones); ^x = parity.
    "rand":  "def rand(v, w):   return Number(1 if (_wv(v) & (2**w.number-1)) == 2**w.number-1 else 0)  # &v",
    "ror":   "def ror(v, w):    return Number(1 if (_wv(v) & (2**w.number-1)) != 0 else 0)   # |v",
    "rxor":  "def rxor(v, w):   return Number(bin(_wv(v) & (2**w.number-1)).count('1') % 2)   # ^v",
    "rnand": "def rnand(v, w):  return Number(0 if (_wv(v) & (2**w.number-1)) == 2**w.number-1 else 1)  # ~&v",
    "rnor":  "def rnor(v, w):   return Number(0 if (_wv(v) & (2**w.number-1)) != 0 else 1)   # ~|v",
    "rxnor": "def rxnor(v, w):  return Number(1 - bin(_wv(v) & (2**w.number-1)).count('1') % 2)  # ~^v",
    # count-leading-zeros / count-leading-sign-bits (the "clz"-kind primitive interface).
    # @clz(V, SGN): SGN=0 -> CLZ of V[63:0] (number of leading 0-bits, 0..64, fits in 7 bits);
    #               SGN=1 -> CLS: count leading SIGN bits of V (= CLZ of ((V ^ (V<<1)) | 1), i.e.
    #               how many consecutive bits equal the MSB, minus 1), matching the usual
    #               cls-via-clz reduction: clsIn = (in ^ {in[62:0], 1'b0}) | 64'h1.
    "clz": (
        "def clz(v, sgn, w):\n"
        "    x = _wv(v) & 0xFFFFFFFFFFFFFFFF\n"
        "    if sgn.number:\n"
        "        x = ((x ^ ((x << 1) & 0xFFFFFFFFFFFFFFFF)) | 1) & 0xFFFFFFFFFFFFFFFF\n"
        "    return Number(64 - x.bit_length() if x else 64)\n"
    ),
    # signed-aware helpers: the stored value is the two's-complement bit pattern (0..2^w-1).
    # @signed maps it to a (possibly negative) python int and is used ONLY inside a NARROW (<=31-bit)
    # native clingo comparison -- a wide signed compare routes through @wcmp instead. @sext/@ashr/
    # @sidiv/@simod re-mask to width.
    "signed": "def signed(v, w): x=_wv(v); return Number(x-(2**w.number) if x>>(w.number-1)&1 else x)",
    # wide-safe 3-way compare (-1/0/1): the ordering path for width>=32 (native < / @signed would
    # overflow). s=1 -> sign-interpret both operands at width w; s=0 -> unsigned magnitudes.
    "wcmp": (
        "def wcmp(a, b, w, s):\n"
        "    x = _wv(a); y = _wv(b)\n"
        "    if s.number:\n"
        "        m = 2 ** w.number; h = 1 << (w.number - 1)\n"
        "        x = x - m if x & h else x\n"
        "        y = y - m if y & h else y\n"
        "    return Number((x > y) - (x < y))"
    ),
    "sext": (
        "def sext(v, fw, tw):\n"
        "    x = _wv(v)\n"
        "    s = x - (2 ** fw.number) if (x >> (fw.number - 1)) & 1 else x\n"
        "    return _we(s % (2 ** tw.number))"
    ),
    "ashr": (
        "def ashr(a, n, w):\n"
        "    x = _wv(a)\n"
        "    s = x - (2 ** w.number) if (x >> (w.number - 1)) & 1 else x\n"
        "    return _we((s >> _wv(n)) % (2 ** w.number))"
    ),
    "sidiv": (
        "def sidiv(a, b, w):\n"
        "    bb = _wv(b)\n"
        "    if not bb: return _we(0)\n"
        "    m = 2 ** w.number; h = 1 << (w.number - 1)\n"
        "    A = _wv(a) - m if _wv(a) & h else _wv(a)\n"
        "    B = bb - m if bb & h else bb\n"
        "    q = abs(A) // abs(B)\n"
        "    return _we((-q if (A < 0) != (B < 0) else q) % m)   # signed /, trunc toward zero"
    ),
    "simod": (
        "def simod(a, b, w):\n"
        "    bb = _wv(b)\n"
        "    if not bb: return _we(0)\n"
        "    m = 2 ** w.number; h = 1 << (w.number - 1)\n"
        "    A = _wv(a) - m if _wv(a) & h else _wv(a)\n"
        "    B = bb - m if bb & h else bb\n"
        "    q = abs(A) // abs(B)\n"
        "    if (A < 0) != (B < 0): q = -q\n"
        "    return _we((A - B * q) % m)   # signed %, sign of dividend"
    ),
}
# clingo @-name per op: `and`/`or`/`not` are Python keywords (-> b-prefix); `pow` shadows a builtin.
FUNC_NAME = {"and": "band", "or": "bor", "xor": "bxor", "not": "bnot",
             "pow": "ipow", "div": "idiv", "mod": "imod"}

# human-readable legend per op (keyed like _LIB; the emitted @-name + args + meaning). Rendered as
# `%` comments alongside the #script block so the completion is readable without decoding the Python.
_LEGEND: dict[str, str] = {
    "add": "@add(A, B, W)       A + B, wrapped to W bits (mod 2^W)",
    "sub": "@sub(A, B, W)       A - B, wrapped to W bits (SV subtraction wraps)",
    "mul": "@mul(A, B, W)       A * B, wrapped to W bits",
    "div": "@idiv(A, B, W)      A / B unsigned, truncated (B=0 -> 0)",
    "mod": "@imod(A, B, W)      A mod B unsigned (B=0 -> 0)",
    "sidiv": "@sidiv(A, B, W)     A / B SIGNED at width W, truncate toward zero (B=0 -> 0)",
    "simod": "@simod(A, B, W)     A mod B SIGNED at width W, sign of dividend (B=0 -> 0)",
    "and": "@band(A, B, W)      bitwise A & B",
    "or":  "@bor(A, B, W)       bitwise A | B",
    "xor": "@bxor(A, B, W)      bitwise A ^ B",
    "shl": "@shl(A, N, W)       A << N, truncated to W bits",
    "shr": "@shr(A, N, W)       A >> N logical (zero-fill)",
    "ashr": "@ashr(A, N, W)      A >> N arithmetic (sign-fill), sign taken at width W",
    "pow": "@ipow(A, B, W)      A ** B, wrapped to W bits",
    "not": "@bnot(V, W)         bitwise complement ~V, W bits",
    "neg": "@neg(V, W)          two's-complement negate -V (mod 2^W)",
    "sext": "@sext(V, FromW, ToW) sign-extend V from FromW to ToW bits",
    "signed": "@signed(V, W)       V read as a SIGNED int (two's-complement, W bits) -- narrow compares only",
    "wcmp": "@wcmp(A, B, W, S)   3-way compare -> -1 / 0 / +1; S=1 signed at width W, S=0 unsigned",
    "slc": "@slc(V, Lo, W)      bit slice V[Lo+W-1 : Lo] -- args (value, LOW bit, WIDTH), NOT SV [hi:lo]",
    "parity": "@parity(V, W)       XOR-reduction of V's bits -> 0/1",
    "popcnt": "@popcnt(V, W)       count of 1-bits in V[W-1:0] ($countones)",
    "rand":  "@rand(V, W)        AND-reduction &V over W bits -> 0/1 (V == all-ones)",
    "ror":   "@ror(V, W)         OR-reduction  |V over W bits -> 0/1 (V != 0)",
    "rxor":  "@rxor(V, W)        XOR-reduction ^V over W bits -> 0/1 (parity)",
    "rnand": "@rnand(V, W)       NAND-reduction ~&V over W bits -> 0/1",
    "rnor":  "@rnor(V, W)        NOR-reduction  ~|V over W bits -> 0/1",
    "rxnor": "@rxnor(V, W)       XNOR-reduction ~^V over W bits -> 0/1",
    "clz":    "@clz(V, SGN)       count-leading-zeros (SGN=0) or leading-sign-bits (SGN=1) of V[63:0] -> 0..64",
}


def func_legend(used: set[str]) -> list[str]:
    """`%`-comment legend lines for the @func ops actually used, in canonical order. Empty if none."""
    lines = [_LEGEND[n] for n in _ORDER if n in used and n in _LEGEND]
    if not lines:
        return []
    return ["% @func LEGEND (wide-safe; values >= 2^31 are canonical decimal strings, see _wv/_we):",
            *(f"%   {ln}" for ln in lines)]

# canonical emission order (every key in _LIB must appear -> determinism + no silent omission)
_ORDER = ["add", "sub", "mul", "div", "mod", "sidiv", "simod", "and", "or", "xor",
          "shl", "shr", "ashr", "pow", "not", "neg", "sext", "signed", "wcmp", "slc", "parity", "popcnt",
          "rand", "ror", "rxor", "rnand", "rnor", "rxnor", "clz"]

#: @funcs registered by a site plugin rather than defined in `_LIB` above. Plugin funcs are
#: design-specific and outside the Lean proofs (`proofs/gen_funcs_lean.py`), which must still
#: refuse a BUILTIN that has no proven mirror; keeping the sets distinct is what lets that
#: drift check stay fail-loud regardless of what a plugin has registered.
PLUGIN_FUNCS: set[str] = set()


def register_funcs(funcs: dict[str, str], legend: dict[str, str] | None = None,
                   origin: str = "<plugin>") -> None:
    """Register site-plugin @funcs (see config.py). New names append to the canonical
    order; redefining a builtin is refused loudly -- a plugin must extend, not mutate."""
    for name, src in funcs.items():
        if name in _LIB:
            raise ValueError(f"@{name} already defined; plugin {origin} may not override builtins")
        _LIB[name] = src
        _ORDER.append(name)
        PLUGIN_FUNCS.add(name)
    for name, line in (legend or {}).items():
        _LEGEND.setdefault(name, line)



# Scenario-layer helper: parse an SV-style literal STRING to its integer bit pattern, so a
# hand-written scenario/property can say `val(x, @sv("8'hA5"), 0)` instead of decimal-only. NOT part
# of the design @func library (the translator folds RTL literals at elaboration); shipped as the
# standalone `lib/svlit.lp` that a scenario composes in: `clingo design.lp scenario.lp lib/svlit.lp`.
# Returns a Number when it fits in clingo's 32-bit int, else a canonical decimal String (wide value).
_SVLIT_LINES = [
    "#script (python)",
    "import re",
    "from clingo import Number, String",
    "",
    "def sv(s):",
    "    # SV-style literal string -> integer bit pattern (wide -> String):",
    "    #   @sv(\"8'hA5\")  @sv(\"8'b1010_0101\")  @sv(\"8'd165\")  -- sized h/b/d/o, masked to size",
    "    #   @sv(\"64'hFFFF_FFFF_FFFF_FFFF\")  -- a wide sized literal -> a canonical decimal String",
    "    #   @sv(\"165\")  @sv(\"0xA5\")  @sv(\"0b1010\")  @sv(\"-5\")  -- plain decimal / 0x / 0b / 0o",
    "    t = s.string.replace(\"_\", \"\").strip()",
    "    m = re.fullmatch(r\"(\\d+)?'[sS]?([hHbBdDoO])([0-9a-fA-F]+)\", t)",
    "    if m:",
    "        size, base, digits = m.group(1), m.group(2).lower(), m.group(3)",
    "        v = int(digits, {\"h\": 16, \"b\": 2, \"d\": 10, \"o\": 8}[base])",
    "        if size:",
    "            v &= (1 << int(size)) - 1",
    "    else:",
    "        v = int(t, 0)",
    "    return Number(v) if -(2 ** 31) <= v < 2 ** 31 else String(str(v))",
    "#end.",
]


_SVLIT_HEADER = (
    "% Auto-generated by sv2asp -- SV-literal helper for the hand-authored scenario/property layer.\n"
    "% Compose it in:  clingo design.lp scenario.lp lib/svlit.lp\n"
    "% Then write constants as @sv(\"8'hA5\"), @sv(\"8'b1010_0101\"), @sv(\"8'd165\"), @sv(\"0xA5\"), ...\n"
)


def svlit_script() -> str:
    """The `#script` block defining @sv for SV-style literals in the hand-authored scenario layer."""
    return "\n".join(_SVLIT_LINES) + "\n"


def svlit_lp_file() -> str:
    """The full committed `lib/svlit.lp` (header + script) -- single source of truth for the helper."""
    return _SVLIT_HEADER + svlit_script()


def render_script(used: set[str]) -> str:
    unknown = used - _LIB.keys()
    if unknown:  # a rule referenced an @func with no definition -> fail loud, never emit a broken script
        raise KeyError(f"emitted rules reference undefined @func(s): {sorted(unknown)}")
    funcs = [_LIB[name] for name in _ORDER if name in used]
    if not funcs:
        return ""
    body = "\n".join([_HELPERS, *funcs])   # _wv/_we first -- every op decodes/encodes through them
    return f"#script (python)\nfrom clingo import Number, String, SymbolType\n{body}\n#end.\n"

#: The EMITTED `@name` of a builtin, derived from the legend rather than restated.
#:
#: A stub is written against the emitted name (`@idiv`), while the library is keyed by its short
#: name (`div`), so anything reading `@func` references out of stub text has to map back. This
#: used to be a hand-written dict in stage3_emit: complete, but nothing enforced that, so adding
#: a builtin whose emitted name differs from its key would silently fail to register and a stub
#: legitimately using it would reference an undefined `@func` at GROUNDING time.
#:
#: Computed on each call, NOT cached at import: `_LIB`/`_LEGEND` are mutated by
#: `register_funcs` when a site plugin loads, so a snapshot taken at import goes stale the
#: moment a plugin registers anything. (The test suite caught exactly that.)


def emitted_names() -> dict[str, str]:
    """library key -> emitted `@name`, for every currently-registered func."""
    return {key: line.lstrip().lstrip("@").split("(")[0].strip()
            for key, line in _LEGEND.items()}


def key_of_emitted(name: str) -> str | None:
    """Library key for an emitted `@name`, or None if it is not a registered func.

    None means "not one of ours" -- a name the caller should leave alone. The tool's obligation
    is to register every builtin a CORRECT stub references; validating the stub's own content is
    the author's job, not the translator's."""
    for key, emitted in emitted_names().items():
        if emitted == name:
            return key
    return None
