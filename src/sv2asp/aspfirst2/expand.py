"""EXPAND an authored (or partly refined) design into the translator's EMITTED SCHEMA -- the form
you READ.

The compact form is what an author WRITES: `inst(u_wr_ptr, arff)` + pins, `def(fill, sub(..))`.
Its hold/set semantics live in `lib/aspfirst/aspfirst.lp` as generic rules over pins, which
means the design file itself shows none of them and looks nothing like sv2asp's output. This
module produces the other view: the SAME design as a self-contained `.lp` in the schema the
translator emits for RTL --

    * the schema facts (`type/3`, `decl_type/4`, `port/3`, `reg/1`, `clock/2`, `reset/3`,
      `element_type` / `array` / `dims` / `addr`, `cell/3`, `enum_value/3`);
    * every primitive INSTANTIATED: the library's rules with the pins substituted, so an `arff`
      register shows its four rules (level force, edge under reset, capture, hold) verbatim, per
      register -- the rules are read off `lib/aspfirst/aspfirst.lp` itself, not restated here;
    * every `def` as an `@func` cascade over hoisted temps (`<lhs>__eK`, the printer's SSA
      policy, so the temps in the expansion are the wires in the print), with `% file:line`
      provenance to the authored fact;
    * guarded comb rules verbatim; a memory as `val(u_mem(A), V, T)` (the translator's cell
      naming -- the `cell(M, A)` functor of the library exists only because a VARIABLE functor
      is not legal clingo; once the instance is known the functor is `u_mem(A)`);
    * abstract nets as `abstract/1` + `wire/2` facts (compose `aspfirst_abstract.lp` to run a
      level), and `gtime/1`, so the file runs WITHOUT the library, exactly like a translation.

`expand` is a VIEW and a runnable artifact; authoring, lint, refine and print stay on the compact
form. `test_aspfirst_expand_is_trace_equivalent` solves both forms under the pilots' scenarios."""
from __future__ import annotations

import pathlib
import re

from ..emit import lib as funclib
from .libgen import LIB_LP
from .compose import _expand_pack
from .load import Design, _split_top, statements
from .printer import enum_width, width_of

HEADER = ("% Expanded by sv2asp.aspfirst from {src} -- the design in the translator's EMITTED SCHEMA "
          "(the form you read; the authored facts are the form you write).\n"
          "% Runs like a translation: clingo {name}.lp scenario.lp  [{name}__init0.lp]"
          "  [lib/aspfirst/aspfirst_abstract.lp for a level with abstract nets]\n")


class ExpandError(Exception):
    pass


# ---------------------------------------------------------------------------------------------
# primitive rules, read off the library and instantiated
# ---------------------------------------------------------------------------------------------

_LIB_VARS = {"ff": {"I": None, "CK": "clk", "EN": "en", "D": "d", "Q": "q"},
             "arff": {"I": None, "CK": "clk", "EN": "en", "D": "d", "Q": "q", "R": "rstL"},
             "lata": {"I": None, "EN": "en", "D": "d", "Q": "q"},
             "spram": {"M": None, "CK": "clk", "WE": "we", "WA": "wa", "WD": "wd", "RA": "ra", "RD": "rd"},
             "farray": {"M": None, "CK": "clk", "WE": "we", "WA": "wa", "WD": "wd", "R": "rstL"}}
#: cells whose rules are quantified over an ADDRESS domain rather than over a single register
_MEM_CELLS = ("spram", "farray")


def _library_rules() -> str:
    text = LIB_LP.read_text()
    from .libgen import BEGIN, END
    text = text.split(BEGIN)[0] + text.split(END, 1)[1]
    return "\n".join(l for l in text.splitlines() if not l.startswith("#defined"))


def _subst(lit: str, mapping: dict) -> str:
    for var, net in mapping.items():
        lit = re.sub(r"(?<![\w])" + re.escape(var) + r"(?![\w])", net, lit)
    return lit


def instantiate(inst, d: Design) -> list:
    """The library's rules for `inst.cell`, with the instance's pins/iparams substituted and the
    `inst/pin/iparam` join literals removed -- the schema rules for THIS instance."""
    cell = inst.cell
    key = {"ff": "inst(I, ff)", "arff": "inst(I, arff)", "lata": "inst(I, lata)",
           "spram": "inst(M, spram)", "farray": "inst(M, farray)"}[cell]
    # Map only the pins the instance ACTUALLY has. `rstL` is optional on a farray (a register file
    # commonly has no reset), and this used to index it unconditionally -- a KeyError on the first
    # reset-less array anyone wrote. Third omission of this shape on this one cell, after the lint and
    # init0, all three because gshare's pht is the only farray in the corpus and it HAS a reset.
    mapping = {}
    for var, pin in _LIB_VARS[cell].items():
        if pin is None:
            mapping[var] = inst.name
        elif pin in inst.pins:
            mapping[var] = inst.pins[pin]
    no_reset = cell == "farray" and "rstL" not in inst.pins
    if cell == "arff" or (cell == "farray" and "reset_value" in inst.iparams):
        mapping["RV"] = str(inst.iparams["reset_value"])
    out = []
    for _, st in statements(_library_rules()):
        if ":-" not in st:
            continue
        head, body = st.split(":-", 1)
        head = head.strip()
        # the memory's auxiliary rules (`addr`, `mem_hold`) carry no `key` literal, so they are matched
        # by their HEAD -- but only when they belong to THIS cell: a rule naming another cell's `inst`
        # is that cell's. Without the second test, adding `farray` (whose head is also `addr(M, A)`)
        # emitted a duplicate `addr` into every spram design's expanded view.
        # `farray`'s per-cell LEVEL FORCE is keyed off `fa_rst`, not off `inst(M, farray)`, so it is
        # matched by its head like spram's aux rules are -- and only when it belongs to THIS cell.
        is_mem_aux = (cell in _MEM_CELLS
                      and (head.startswith("addr(M, A)") or head.startswith("mem_hold(M, A, T)")
                           or (cell == "farray" and head.startswith("val(cell(M, A), RV, T)")))
                      and ("inst(M, " not in st or f"inst(M, {cell})" in st))
        if key not in st and not is_mem_aux:
            continue
        if cell not in _MEM_CELLS and (head.startswith("addr(") or head.startswith("mem_hold(")):
            continue
        # A RESET-LESS farray: drop every reset rule rather than let the body filter collapse it into a
        # falsehood. `fa_has_rst(M) :- inst(M,farray), pin(M,rstL,_).` loses both literals and becomes
        # the FACT `fa_has_rst(m).` -- asserting a reset the array does not have, after which
        # `fa_run(M,T) :- ..., not fa_has_rst(M)` never fires and every cell freezes. The library's
        # own no-reset branch is "always running", and that is emitted as a fact below instead.
        if no_reset and ("R" in body or head.startswith(("fa_rst(", "fa_has_rst("))
                         or "reset_value" in head or "reset_value" in body):
            continue
        lits = [l for l in _split_top(body) if not l.startswith(("inst(", "pin(", "iparam("))]
        if cell in _MEM_CELLS:
            depth = inst.iparams["depth"]
            lits = [l.replace("A = 0..D-1", f"A = 0..{depth - 1}") for l in lits]
            # the write rule's `addr(M, A)` guard: the address read binds A (the translator's shape)
            if head.startswith("val(cell(M, A), V, T+1)") and any(l.startswith("val(WD,") for l in lits):
                lits = [l for l in lits if l != "addr(M, A)"]
        # every literal may be a join literal that is stripped (`fa_has_rst(M) :- inst(M, farray),
        # pin(M, rstL, _)` leaves nothing), and `head :- .` is not something to put in a view whose
        # whole point is being read -- it is a FACT.
        body_txt = ", ".join(_subst(l, mapping) for l in lits)
        rule = _subst(head, mapping) + (" :- " + body_txt if body_txt else "") + "."
        rule = rule.replace(f"cell({inst.name}, A)", f"{inst.name}(A)")
        rule = re.sub(r"\s+", " ", rule)
        out.append(rule)
    if no_reset:
        # the library's reset-less branch, specialised: this array is always running
        out.append(f"fa_run({inst.name}, T) :- gtime(T).")
    return out


# ---------------------------------------------------------------------------------------------
# combinational defs -> cascades over hoisted temps
# ---------------------------------------------------------------------------------------------

class _Cx:
    """Per-def expansion: temps + their rules + the ops used."""

    def __init__(self, d: Design, lhs: str, out: list, decls: list, used: set):
        self.d, self.lhs, self.n = d, lhs, 0
        self.out, self.decls, self.used = out, decls, used
        self._memo: dict = {}

    def temp(self, w, key: str) -> "tuple[str, bool]":
        """(name, is_new) -- the same subterm at the same width is one temp, defined once."""
        if key in self._memo:
            return self._memo[key], False
        # a lane MEMBER's temps (`gm(1)`) get a hoisting-safe stem (`gm_1__e0`): a name with parens is not an atom
        name = f"{re.sub(r'[()+-]', '_', self.lhs).rstrip('_')}__e{self.n}"
        self.n += 1
        self.decls.append((name, w))
        self._memo[key] = name
        return name, True

    def leaf(self, t):
        """(kind, text): ("net", name) | ("const", text) | ("tag", label). Non-leaves are hoisted."""
        if isinstance(t, str):
            return ("net", t)
        if t[0] == "k":
            v = t[1]
            return ("const", f'"{v[1]}"' if isinstance(v, tuple) else str(v))
        if t[0] == "tag":
            return ("tag", t[1])
        w = width_of(self.d, t)
        name, new = self.temp(w, repr(t))
        if new:
            self.rules(name, t)
        return ("net", name)

    def _bind(self, t, var: str, body: list) -> str:
        """Bind t's value to a term usable in a @func call: a net binds `var`, a const is inline."""
        kind, text = self.leaf(t)
        if kind == "net":
            body.append(f"val({text}, {var}, T)")
            return var
        return text

    def rules(self, lhs: str, t) -> None:
        """Emit the rule(s) defining `lhs` as ONE operator over leaves (the translator's shapes)."""
        op = t[0]
        arith = {"add": "add", "sub": "sub", "mul": "mul", "and": "band", "or": "bor", "xor": "bxor",
                 "shl": "shl", "shr": "shr", "ashr": "ashr", "idiv": "idiv", "imod": "imod",
                 "sidiv": "sidiv", "simod": "simod"}
        if op in arith:
            body: list = []
            a = self._bind(t[1], "V0", body)
            b = self._bind(t[2], "V1", body)
            self.used.add({"idiv": "div", "imod": "mod"}.get(op, op))     # library keys, not @names
            self.out.append(f"val({lhs}, V2, T) :- {', '.join(body)}, V2 = @{arith[op]}({a}, {b}, {t[3]}).")
            return
        if op == "clz":
            raise ExpandError(
                "clz has no expanded form yet. It is wired for AUTHORING and LINTING only, because there is no SystemVerilog construct for a leading-zero count -- lowering one means synthesising a priority encoder, a design decision nothing has needed yet. Until then a design that needs an LZC declares it as a CONTRACT-ONLY submodule and is proven from its contract; the print gives it as an interface stub. See notes/WORKLIST_SPEC2RTL.md.")
        una = {"bnot": "bnot", "neg": "neg", "ror": "ror", "rand": "rand", "rxor": "rxor",
               "rnand": "rnand", "rnor": "rnor", "rxnor": "rxnor", "parity": "parity", "popcnt": "popcnt"}
        if op in una:
            body = []
            a = self._bind(t[1], "V0", body)
            self.used.add({"bnot": "not", "neg": "neg"}.get(op, op))
            self.out.append(f"val({lhs}, V1, T) :- {', '.join(body)}, V1 = @{una[op]}({a}, {t[2]}).")
            return
        if op == "mrd":
            # `mrd(M, A)` -- a read of a flop array's cell at the value of A. In the EMITTED schema a
            # memory cell is `val(m(A), V, T)` (the address in the functor), which is exactly what the
            # translator writes for an unpacked-array read, so the expansion is a single literal. The
            # address is bound first: it may itself be an expression (`mrd(pht, xor(pc, bhr, 7))`).
            body = []
            a = self._bind(t[2], "V0", body)
            self.out.append(f"val({lhs}, V1, T) :- {', '.join(body)}, val({t[1]}(V0), V1, T)."
                            if body else f"val({lhs}, V1, T) :- val({t[1]}({a}), V1, T).")
            return
        if op == "sext":
            body = []
            a = self._bind(t[1], "V0", body)
            self.used.add("sext")
            self.out.append(f"val({lhs}, V1, T) :- {', '.join(body)}, V1 = @sext({a}, {t[2]}, {t[3]}).")
            return
        if op == "slc":
            body = []
            a = self._bind(t[1], "V0", body)
            self.used.add("slc")
            self.out.append(f"val({lhs}, V1, T) :- {', '.join(body)}, V1 = @slc({a}, {t[2]}, {t[3]}).")
            return
        if op == "bit":
            body = []
            a = self._bind(t[1], "V0", body)
            self.used.add("slc")
            self.out.append(f"val({lhs}, V1, T) :- {', '.join(body)}, V1 = @slc({a}, {t[2]}, 1).")
            return
        if op == "cat":
            body = []
            a = self._bind(t[1], "V0", body)
            b = self._bind(t[3], "V1", body)
            w = t[2] + t[4]
            self.used |= {"shl", "or"}
            self.out.append(f"val({lhs}, V3, T) :- {', '.join(body)}, V2 = @shl({a}, {t[4]}, {w}), V3 = @bor(V2, {b}, {w}).")
            return
        if op in ("eq", "ne"):
            body = []
            a = self._bind(t[1], "V0", body)
            b = self._bind(t[2], "V1", body)
            yes, no = ("=", "!=") if op == "eq" else ("!=", "=")
            self.out.append(f"val({lhs}, 1, T) :- {', '.join(body)}, {a} {yes} {b}.")
            self.out.append(f"val({lhs}, 0, T) :- {', '.join(body)}, {a} {no} {b}.")
            return
        if op in ("lt", "le", "gt", "ge", "slt", "sle", "sgt", "sge"):
            body = []
            a = self._bind(t[1], "V0", body)
            b = self._bind(t[2], "V1", body)
            s = 1 if op.startswith("s") else 0
            base = op[1:] if s else op
            yes, no = {"lt": ("= -1", "!= -1"), "le": ("!= 1", "= 1"), "gt": ("= 1", "!= 1"),
                       "ge": ("!= -1", "= -1")}[base]
            self.used.add("wcmp")
            self.out.append(f"val({lhs}, 1, T) :- {', '.join(body)}, @wcmp({a}, {b}, {t[3]}, {s}) {yes}.")
            self.out.append(f"val({lhs}, 0, T) :- {', '.join(body)}, @wcmp({a}, {b}, {t[3]}, {s}) {no}.")
            return
        if op in ("logand", "logor", "lnot", "ite"):
            self._logic(lhs, t)
            return
        if op == "pack":
            # `pack(L)`, the lane as one word: the SAME expansion the solver path uses
            # (compose._expand_pack), so the expanded form cannot drift from what was
            # verified -- one decision function, not a second copy (G24, 2026-09-02). The
            # expansion spells a member as the term `(L, j)` for the text path; the loaded
            # design names that member net `L(j)`, which is what a leaf here must be.
            lanes = self.d.lanes

            def member_nets(x):
                if isinstance(x, tuple) and len(x) == 2 and x[0] in lanes and isinstance(x[1], int):
                    return f"{x[0]}({x[1]})"
                return tuple(member_nets(y) for y in x) if isinstance(x, tuple) else x
            self.rules(lhs, member_nets(_expand_pack(t, self.d)))
            return
        raise ExpandError(f"cannot expand operator {op}")

    def _truth(self, t, pol: int) -> str:
        """A literal asserting leaf t is true (pol=1) / false (pol=0), 1-bit nets in the translator's
        `val(x, 1, T)` form, wider ones with the SV `!= 0` reading."""
        kind, text = self.leaf(t)
        if kind == "const":
            v = int(text.strip('"'))
            return "" if (v != 0) == bool(pol) else "false_literal"
        w = width_of(self.d, t)
        if w == 1:
            return f"val({text}, {pol}, T)"
        return f"val({text}, V_{text}, T), V_{text} != 0" if pol else f"val({text}, 0, T)"

    def _logic(self, lhs: str, t) -> None:
        op = t[0]
        if op == "lnot":
            self.out.append(f"val({lhs}, 1, T) :- {self._truth(t[1], 0)}.")
            self.out.append(f"val({lhs}, 0, T) :- {self._truth(t[1], 1)}.")
        elif op == "logand":
            self.out.append(f"val({lhs}, 1, T) :- {self._truth(t[1], 1)}, {self._truth(t[2], 1)}.")
            self.out.append(f"val({lhs}, 0, T) :- {self._truth(t[1], 0)}.")
            self.out.append(f"val({lhs}, 0, T) :- {self._truth(t[2], 0)}.")
        elif op == "logor":
            self.out.append(f"val({lhs}, 1, T) :- {self._truth(t[1], 1)}.")
            self.out.append(f"val({lhs}, 1, T) :- {self._truth(t[2], 1)}.")
            self.out.append(f"val({lhs}, 0, T) :- {self._truth(t[1], 0)}, {self._truth(t[2], 0)}.")
        elif op == "ite":
            body_a, body_b = [], []
            va = self._bind(t[2], "V", body_a)
            vb = self._bind(t[3], "V", body_b)
            va = va if va == "V" else va
            self.out.append(f"val({lhs}, {va}, T) :- {self._truth(t[1], 1)}" + (", " + ", ".join(body_a) if body_a else "") + ".")
            self.out.append(f"val({lhs}, {vb}, T) :- {self._truth(t[1], 0)}" + (", " + ", ".join(body_b) if body_b else "") + ".")
        # a constant that made a literal vacuous ("") leaves ", ." artefacts: tidy
        self.out[:] = [re.sub(r":-\s*,\s*", ":- ", re.sub(r",\s*,", ",", r)).replace(" :- .", " :- gtime(T).")
                       for r in self.out]
        if any("false_literal" in r for r in self.out):
            self.out[:] = [r for r in self.out if "false_literal" not in r]


# ---------------------------------------------------------------------------------------------
# the file
# ---------------------------------------------------------------------------------------------

def _tdecl(name: str, w) -> list:
    if isinstance(w, tuple):
        return [f"type({name}, enum, {w[1]}).", f"decl_type({name}, {w[1]}, {w[1]}, two_state)."]
    return [f"type({name}, bit, {w}).", f"decl_type({name}, logic, {w}, four_state)."]


def expand(d: Design, src: str = "<design>.lp") -> tuple:
    """(expanded_text, init0_text). `init0_text` is the twin of the translator's `__init0.lp` --
    every unreset state element (ff, spram cells) pinned to zero at T=0 -- or "" if none."""
    name = d.name
    body: list = []
    used: set = set()
    temps: list = []
    # -- combinational
    comb: list = []
    for n in d.def_order:
        line, stmt = d.src.get(("def", n), (0, ""))
        comb.append(f"% {pathlib.Path(src).name}:{line}  {stmt}.")
        cx = _Cx(d, n, comb, temps, used)
        t = d.defs[n]
        if isinstance(t, str):
            comb.append(f"val({n}, V, T) :- val({t}, V, T).")
        elif t[0] == "k":
            comb.append(f"val({n}, {cx.leaf(t)[1]}, T) :- gtime(T).")
        elif t[0] == "tag":
            comb.append(f"val({n}, {t[1]}, T) :- gtime(T).")
        else:
            cx.rules(n, t)
    for r in d.rules:
        comb.append(f"% {pathlib.Path(src).name}:{r.line}  (guarded comb rule)")
        comb.append(re.sub(r"\s+", " ", r.text) + ".")
        for st in r.steps:
            used.add({"band": "and", "bor": "or", "bxor": "xor", "bnot": "not", "idiv": "div",
                      "imod": "mod", "ipow": "pow"}.get(st.func, st.func))
    # -- schema
    sch: list = [f"module({name})."]
    for e, ms in d.enums.items():
        for l, v in ms:
            sch.append(f"enum_value({e}, {l}, {v}).")
    for p in d.ports:
        sch += _tdecl(p.name, p.width)
        sch.append(f"port({p.name}, {p.direction}, {name}).")
    for n in d.nets:
        sch += _tdecl(n.name, n.width)
    for tn, w in temps:
        sch += _tdecl(tn, w)
    regs, clocks, resets, mems, cells = [], [], [], [], []
    for i in d.insts:
        cells.append(f"cell({i.name}, {i.cell}, {name}).")
        if i.cell in ("ff", "arff", "lata"):
            regs.append(f"reg({i.pins['q']}).")
            if "clk" in i.pins:
                clocks.append(f"clock({i.pins['q']}, {i.pins['clk']}).")
            if i.cell == "arff":
                resets.append(f"reset({i.pins['q']}, {i.pins['rstL']}, active_low).")
        elif i.cell == "spram":
            depth, w = i.iparams["depth"], i.iparams["width"]
            aw = max(1, (depth - 1).bit_length())
            clocks.append(f"clock({i.name}, {i.pins['clk']}).")
            mems += [f"reg({i.name}).", f"element_type({i.name}_elem, bit, {w}).",
                     f"array({i.name}, {i.name}_elem, unpacked, addr_w({aw})).",
                     f"dims({i.name}, unpacked({depth}), packed({w}))."]
    sch += regs + clocks + resets + mems + cells
    # -- sequential / memory
    seq: list = []
    mem: list = []
    for i in d.insts:
        line, stmt = d.src.get(("inst", i.name), (0, ""))
        target = mem if i.cell == "spram" else seq
        target.append(f"% {pathlib.Path(src).name}:{line}  [{i.cell} {i.name}]  {stmt}.")
        target += instantiate(i, d)
    # -- abstract
    abst: list = []
    for n in d.abstracts:
        line, stmt = d.src.get(("abstract", n), (0, ""))
        abst.append(f"% {pathlib.Path(src).name}:{line}  {stmt}.   -- NOT YET REFINED")
        abst.append(f"abstract({n}).")
        abst.append(f"wire({n}, {_wtxt(d.width_of(n))}).")
    # -- assemble
    lines = [HEADER.format(src=pathlib.Path(src).name, name=name)]
    lines += funclib.func_legend(used)
    lines.append(funclib.render_script(used).rstrip("\n"))
    lines += ["", "% ---- SCHEMA ----"] + sch
    lines += ["", "% ---- CLOCK / HORIZON  (supplied by the run: #const k. + time(clk,0..k).) ----",
              "gtime(T) :- time(_, T)."]
    lines += ["", "% ---- COMBINATIONAL (Group 1) ----"] + comb
    if seq:
        lines += ["", "% ---- SEQUENTIAL (Group 2) ----"] + seq
    if mem:
        lines += ["", "% ---- MEMORY (Section 2.9) ----"] + mem
    if abst:
        lines += ["", "% ---- ABSTRACT (a free value per instant: compose lib/aspfirst/aspfirst_abstract.lp) ----"] + abst
    text = "\n".join(lines) + "\n"
    # -- init0 twin
    # THE TWIN OF lib/aspfirst/aspfirst_init0.lp, and it must actually mirror it. It did not: three
    # state shapes were missing or wrong, and the regen gate cannot see any of them because it checks
    # that the committed file matches what THIS function produces, never that what it produces is
    # right -- a gate comparing an artifact against itself.
    #   * an ENUM register was pinned to the NUMBER 0 rather than to the tag whose value is 0. The
    #     design's rules read TAGS, so `val(ph, 0, 0)` is an atom nothing reads and the register was
    #     dark at instant 0 in the expanded view. LATENT and already committed (ve146's artifact).
    #     The library file fixes exactly this and records finding it once before.
    #   * `lata` was missing entirely.
    #   * `farray` was missing entirely -- the one that blocked examples/spec2rtl/am2901.
    # An `arff` is NOT pinned, here as there: its power-on comes from asserting its reset.
    zero_tag = {e: next((l for l, v in ms if v == 0), None) for e, ms in d.enums.items()}

    def _pin_zero(net: str) -> str:
        w = d.width_of(net)
        if isinstance(w, tuple) and w[0] == "enum":
            tag = zero_tag.get(w[1])
            if tag is not None:
                return f"val({net}, {tag}, 0)."     # the TAG whose value is 0, not the number
        return f"val({net}, 0, 0)."

    init: list = []
    for i in d.insts:
        if i.cell == "ff":
            init.append(_pin_zero(i.pins["q"]))
        elif i.cell == "lata":
            init.append(_pin_zero(i.pins["q"]))
        elif i.cell == "spram":
            init.append(f"val({i.name}(A), 0, 0) :- addr({i.name}, A).")
        elif i.cell == "farray" and "rstL" not in i.pins:      # a reset-carrying one is defined by its reset
            init.append(f"val({i.name}(A), 0, 0) :- addr({i.name}, A).")
    init0 = ""
    if init:
        init0 = (f"% __init0.lp for `{name}` -- CONCRETE power-on state (all zeros), the twin of the translator's; "
                 f"opt-in, arbitrary, for testing.\n" + "\n".join(init) + "\n")
    return text, init0


def _wtxt(w) -> str:
    return f"enum({w[1]})" if isinstance(w, tuple) else str(w)
