"""`python -m sv2asp.aspfirst2 export SPEC SCENARIO LEVEL -o FILE.lean` -- the OBLIGATION EXPORT (CDS slice 2).

What is exported: every `obl(Tag, Have, Want, T)` the level produces under the SCENARIO in the symbolic
reading -- "at T the value Have must equal Want" -- whose two sides are not the same symbol. Have is
the closed term the DATAPATH computed (over the input tokens `in(port, T)`), Want the spec's promise.
Each distinct pair, with its tokens turned into universally quantified variables, becomes a Lean
theorem over the `@func` MODELS of proofs/lean (`GroundTruthProofs.Funcs`: fAdd fSub fMul fSlc fSext
fOr fShl ...) -- the very functions the ASP evaluates, each proven equal to its BitVec operation there.

Why a SCENARIO and not the free stimulus: under free control the term family of an iterative datapath
is a cross-product of histories (LESSONS E5, Booth); under a PINNED control schedule (one job from
reset) every net has one term per instant and the obligation is one closed expression. The theorem
therefore states the obligation FOR THE SCHEDULE THE SCENARIO EXHIBITS; that the datapath's result
does not depend on what came before (it is reloaded at every accept) is the control's business,
proven separately. The header of the file says so.

The proof tactic: `decide` when the quantified inputs total <= 16 bits (an exhaustive kernel check),
otherwise `bv_decide` is suggested and the theorem is left for the user to close (never `sorry`
silently: the file does not build until it is proven)."""
from __future__ import annotations

import pathlib
import re
from dataclasses import dataclass, field

from .libgen import LIB_DIR
from .lint import lint_composed
from .refine import _solve

# clingo term -> Lean over GroundTruthProofs.Funcs. Value arguments first, then widths / positions.
_LEAN_OPS = {
    "add": ("fAdd", 3), "sub": ("fSub", 3), "mul": ("fMul", 3), "idiv": ("fIdiv", 3), "imod": ("fImod", 3),
    "sidiv": ("fSidiv", 3), "simod": ("fSimod", 3), "band": ("fAnd", 3), "bor": ("fOr", 3), "bxor": ("fXor", 3),
    "shl": ("fShl", 3), "shr": ("fShr", 3), "ashr": ("fAshr", 3), "ipow": ("fPow", 3),
    "bnot": ("fNot", 2), "neg": ("fNeg", 2), "sext": ("fSext", 3), "slc": ("fSlc", 3),
    "parity": ("fParity", 2), "popcnt": ("fPopcnt", 2), "rand": ("fRand", 2), "ror": ("fRor", 2),
    "rxor": ("fRxor", 2), "rnand": ("fRnand", 2), "rnor": ("fRnor", 2), "rxnor": ("fRxnor", 2),
}

#: ops that are authorable but have no Lean image yet -- named so the exporter says WHY rather
#: than falling through to a generic failure. `clz` has no `fClz` in GroundTruthProofs.Funcs, and
#: adding one means proving its BitVec characterisation there first.
_LEAN_UNSUPPORTED = {
    "clz": "clz has no Lean image: GroundTruthProofs.Funcs has no fClz, and adding one means "
           "proving its BitVec characterisation there first. A design needing an LZC declares it "
           "as a CONTRACT-ONLY submodule instead. See notes/WORKLIST_SPEC2RTL.md.",
}


@dataclass
class Obligation:
    tag: str
    have: object          # clingo Symbol
    want: object
    instants: list = field(default_factory=list)


class ExportError(Exception):
    pass


def _tokens(sym, acc: dict) -> None:
    """Collect the input tokens `in(name, T)` (and `init(x)` / `tok(x, T)`) of a term: name -> set of instants."""
    if sym.type.name == "Function" and sym.arguments:
        if sym.name == "in" and len(sym.arguments) == 2:
            acc.setdefault(sym.arguments[0].name, set()).add(sym.arguments[1].number)
            return
        if sym.name in ("init", "tok"):
            acc.setdefault(str(sym.arguments[0]), set()).add(-1)
            return
        for a in sym.arguments:
            _tokens(a, acc)


class _Dag:
    """Hash-consed rendering: distinct compound subterms become `let` bindings (linear in the DAG,
    where the tree can be exponential -- Lean timed out elaborating a 66 KB unrolled Booth term)."""
    def __init__(self, var_of):
        self.var_of = var_of
        self.memo: dict = {}
        self.lets: list = []
    def name(self, sym) -> str:
        from clingo import SymbolType
        if sym.type == SymbolType.Function and sym.arguments and sym.name not in ("in", "init", "tok"):
            if sym in self.memo:
                return self.memo[sym]
            expr = _lean(sym, self.var_of, self)
            n = f"x{len(self.lets)}"
            self.lets.append((n, expr))
            self.memo[sym] = n
            return n
        return _lean(sym, self.var_of, self)
    def body(self, root) -> str:
        top = self.name(root)
        return "\n".join(f"  let {n} : Nat := {e}" for n, e in self.lets) + f"\n  {top}"


def _lean(sym, var_of, dag: "_Dag | None" = None) -> str:
    """Render ONE level of a clingo term as Lean over the Funcs models; children go through the DAG."""
    sub = (lambda a: dag.name(a)) if dag is not None else (lambda a: _lean(a, var_of))
    from clingo import SymbolType
    if sym.type == SymbolType.Number:
        return str(sym.number)
    if sym.type == SymbolType.String:
        return sym.string                                    # a wide value: its decimal digits
    if sym.type == SymbolType.Function:
        args = sym.arguments
        if not args:
            return sym.name                                  # an enum tag / a constant
        if sym.name == "in" or sym.name in ("init", "tok"):
            return var_of(sym)
        if sym.name in _LEAN_UNSUPPORTED:
            raise ValueError(_LEAN_UNSUPPORTED[sym.name])
        if sym.name in _LEAN_OPS:
            fn, n = _LEAN_OPS[sym.name]
            return "(" + fn + " " + " ".join(sub(a) for a in args) + ")"
        if sym.name == "ite" and len(args) == 3:
            return f"(if {sub(args[0])} ≠ 0 then {sub(args[1])} else {sub(args[2])})"
        if sym.name == "logand":
            return f"(if {sub(args[0])} ≠ 0 ∧ {sub(args[1])} ≠ 0 then 1 else 0)"
        if sym.name == "logor":
            return f"(if {sub(args[0])} ≠ 0 ∨ {sub(args[1])} ≠ 0 then 1 else 0)"
        if sym.name == "lnot":
            return f"(if {sub(args[0])} = 0 then 1 else 0)"
        if sym.name == "eq":
            return f"(if {sub(args[0])} = {sub(args[1])} then 1 else 0)"
        if sym.name == "ne":
            return f"(if {sub(args[0])} = {sub(args[1])} then 0 else 1)"
        if sym.name in ("lt", "le", "gt", "ge"):
            op = {"lt": "<", "le": "≤", "gt": ">", "ge": "≥"}[sym.name]
            return f"(if {sub(args[0])} {op} {sub(args[1])} then 1 else 0)"
        if sym.name == "wcmp":
            return f"(fWcmp {sub(args[0])} {sub(args[1])} {args[2]} {args[3]})"
        raise ExportError(f"cannot render `{sym}` in Lean (op {sym.name}/{len(args)})")
    raise ExportError(f"cannot render `{sym}`")


def export_lean(spec, scenario, level, out, k: "int | None" = None, namespace: "str | None" = None) -> str:
    spec, scenario, level, out = map(pathlib.Path, (spec, scenario, level, out))
    comp, errs, _ = lint_composed(level)
    if comp is None or errs:
        raise ExportError("the level does not lint: " + "; ".join(errs[:3]))
    d = comp.design
    if not d.data:
        raise ExportError("no data(...) net: the export needs the symbolic reading (declare the datapath nets data)")
    lib = LIB_DIR
    files = [comp.lp_path, lib / "aspfirst.lp", lib / "aspfirst_abstract.lp", lib / "aspfirst_t34.lp",
             lib / "aspfirst_init0.lp", lib / "aspfirst_symbolic.lp", scenario, spec]
    extra = comp.symfacts + comp.inv + "\n#show obl/4.\n#defined obl/4.\n"
    consts = {"k": k} if k is not None else {}
    st, atoms = _solve(files, extra, consts, timeout=600)
    if st != "SATISFIABLE":
        raise ExportError(f"the level under the scenario is {st}: nothing to export (a scenario must be one legal run)")
    from clingo import parse_term
    obls: dict = {}
    widths = {p.name: p.width for p in d.ports}
    for a in atoms:
        if not a.startswith("obl("):
            continue
        s = parse_term(a)
        tag, have, want, t = s.arguments
        if have == want:
            continue                                         # discharged by identity
        toks: dict = {}
        _tokens(have, toks); _tokens(want, toks)
        # tokens -> variables: one variable per port when a single instant is involved, else name_T
        multi = {n for n, ts in toks.items() if len(ts) > 1}
        def var_of(sym, multi=multi):
            n = sym.arguments[0].name if sym.name == "in" else str(sym.arguments[0])
            if sym.name == "in" and n in multi:
                return f"{n}_{sym.arguments[1].number}"
            return re.sub(r"\W", "_", n)
        dh, dw = _Dag(var_of), _Dag(var_of)
        have_body, want_body = dh.body(have), dw.body(want)
        key = (str(tag), have_body, want_body)
        ob = obls.setdefault(key, Obligation(str(tag), have, want))
        ob.have_body, ob.want_body = have_body, want_body
        ob.dag_size = len(dh.lets)
        ob.instants.append(t.number)
        ob.vars = sorted({(var_of(parse_term(f"in({n},{ts_})")) if n in widths else re.sub(r"\W", "_", n),
                          (widths.get(n) if isinstance(widths.get(n), int) else None))
                         for n, ts in toks.items() for ts_ in (ts if n in multi else [next(iter(ts))])})
    ns = namespace or re.sub(r"\W", "_", d.name).capitalize()
    L = [f"/-  {out.name} -- GENERATED by `python -m sv2asp.aspfirst2 export {spec.name} {scenario.name} {level.name}`.",
         "    The DATA obligations of the level under the scenario, as Lean theorems over the @func models of",
         "    proofs/lean (GroundTruthProofs.Funcs) -- the very functions the ASP evaluated. Each `Have = Want`:",
         "    Have is the closed term the datapath computed (input tokens as variables), Want the spec's promise.",
         "    The theorem states the obligation FOR THE SCHEDULE THE SCENARIO EXHIBITS; that the datapath's result",
         "    does not depend on earlier history is the control's business, proven in ASP. -/",
         "import GroundTruthProofs.Funcs", "", f"namespace {ns}", "open GroundTruthProofs", ""]
    if not obls:
        L.append("-- every obligation was discharged by identity: nothing is owed.")
    for i, ((tag, have_l, want_l), ob) in enumerate(obls.items()):
        vars_ = [(v, w) for v, w in ob.vars if w is not None]
        binders = " ".join(f"({v} : Nat)" for v, _ in vars_)
        hyps = " → ".join(f"{v} < 2 ^ {w}" for v, w in vars_)
        bits = sum(w for _, w in vars_)
        tactic = "decide" if bits <= 16 else "sorry   -- too wide for `decide`; prove with bv_decide over BitVec, or by hand"
        name = re.sub(r"\W", "_", tag) + ("" if len([o for o in obls if o[0] == tag]) == 1 else f"_{i}")
        args = " ".join(v for v, _ in vars_)
        # the bounded-forall shape `∀ a, a < 2^W → ∀ b, b < 2^W → P a b` is what `decide` decides (Nat.decidableBallLT)
        quant = " ".join(f"∀ {v}, {v} < 2 ^ {w} →" for v, w in vars_)
        L += [f"/-- what the datapath computed for `{tag}` (a DAG of {ob.dag_size} shared subterms, from the ASP term) -/",
              f"def {name}_have {binders} : Nat :=", ob.have_body, "",
              f"/-- what the spec promised for `{tag}` -/",
              f"def {name}_want {binders} : Nat :=", ob.want_body, "",
              f"/-- obligation `{tag}` at instant(s) {sorted(set(ob.instants))} of the scenario ({bits} input bits) -/",
              f"theorem {name} : {quant} {name}_have {args} = {name}_want {args} := by",
              f"  {tactic}", ""]
    L += [f"end {ns}", ""]
    out.write_text("\n".join(L))
    return f"exported {len(obls)} obligation(s) to {out}" + (" (all discharged by identity)" if not obls else "")
