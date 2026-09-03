"""The GENERATED region of `lib/aspfirst/aspfirst.lp`: the `@func` script block and its legend,
rendered from `sv2asp.emit.lib` so the library can never carry a different `@add` than the
translator emits. Everything outside the two markers is hand-written ASP; `regen_examples.py
--check` (and `test_aspfirst_lib_in_sync`) fail when the region differs from this render."""
from __future__ import annotations

import pathlib

from ..emit import lib as funclib

ROOT = pathlib.Path(__file__).resolve().parents[3]
LIB_DIR = ROOT / "lib" / "aspfirst"
LIB_LP = LIB_DIR / "aspfirst.lp"

BEGIN = "% ---- BEGIN GENERATED (sv2asp.emit.lib -- the @func script; do not edit) ----"
END = "% ---- END GENERATED ----"


#: value-argument count of every builtin, by EMITTED name (the rest of the arguments are widths /
#: positions / flags). The symbolic wrapper looks only at the value arguments.
_NVALS = {**{n: 2 for n in ("add", "sub", "mul", "idiv", "imod", "sidiv", "simod", "band", "bor", "bxor",
                            "shl", "shr", "ashr", "ipow", "wcmp")},
          **{n: 1 for n in ("bnot", "neg", "sext", "signed", "slc", "parity", "popcnt",
                            "rand", "ror", "rxor", "rnand", "rnor", "rxnor", "clz")}}

# aspfirst-only additions to the shared script: the compare helpers the library's `bres` rules
# call (concrete: 0/1 from symbol equality / @wcmp), `issym`, and the SYMBOLIC WRAPPERS -- every
# builtin returns the TERM `name(args)` when a value argument is a compound term (a data token),
# and behaves exactly as before otherwise. One implementation, total over both kinds of argument;
# the MODE is which companion is composed (aspfirst_symbolic.lp), not the functions.
_ASPFIRST_EXTRA = """\
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
"""


def _extra_script() -> str:
    lines = [_ASPFIRST_EXTRA]
    for name, n in {**{funclib.emitted_names()[k]: _NVALS[funclib.emitted_names()[k]]
                       for k in funclib._ORDER if k not in funclib.PLUGIN_FUNCS},
                    "eq": 2, "ne": 2, "lt": 2, "le": 2, "gt": 2, "ge": 2, "slt": 2, "sle": 2, "sgt": 2, "sge": 2}.items():
        lines.append(f"{name} = _symwrap('{name}', {name}, {n})")
    return "\n".join(lines) + "\n"


def generated_region() -> str:
    """Legend + `#script` for EVERY builtin @func (plugins excluded: they are site-specific), plus
    the aspfirst additions (compare helpers, issym, the symbolic wrappers) inside the same block."""
    used = {k for k in funclib._ORDER if k not in funclib.PLUGIN_FUNCS}
    legend = "\n".join(funclib.func_legend(used))
    script = funclib.render_script(used)
    assert script.endswith("#end.\n")
    script = script[:-len("#end.\n")] + _extra_script() + "#end.\n"
    return f"{BEGIN}\n{legend}\n{script}{END}\n"


def with_region(text: str) -> str:
    """`text` with its generated region replaced by a fresh render (inserted after the header
    comment block if absent)."""
    region = generated_region()
    if BEGIN in text and END in text:
        head, rest = text.split(BEGIN, 1)
        _, tail = rest.split(END + "\n", 1) if END + "\n" in rest else rest.split(END, 1)
        return head + region + tail
    return region + text


def lib_text() -> str:
    """The committed library with a fresh generated region (what `--check` compares against)."""
    return with_region(LIB_LP.read_text())
