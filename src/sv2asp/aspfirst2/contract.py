"""Verify an authored module STANDALONE against its own `<module>.contract.lp`.

The contract's `guarantee(Tag, T)` monitors become the spec's `bad`; its `require(Tag, T)`
monitors become an ASSUMPTION on the stimulus (`:- require(_, _)` -- the environment is assumed to
drive the module legally); the stimulus is generated from the module's ports (every input a free
choice over its width; a port named `rst_n`/`rst`/`reset*` asserted at T=0 only; the clock from the
cells' clk pins). Then the ordinary `refine` checks run on the module as a fully concrete level:
no `bad` (= no broken guarantee) reachable, totality, single-valuedness, and every `goal` the
contract states. A module that passes here can be instantiated ABSTRACT in a parent -- its
guarantee assumed there -- and the parent's `refine` will require the parent to honour the
module's `require`s."""
from __future__ import annotations

import atexit
import pathlib
import shutil
import re
import tempfile

from .compose import contract_of
from .load import load
from .refine import RefineResult, refine


def generated_stim(d, k: int) -> str:
    clocks = {i.pins.get("clk") for i in d.insts if "clk" in i.pins}
    clk = next(iter(clocks)) if clocks else "clk"
    out = [f"% generated stimulus for {d.name}: reset at T=0 (if any), every other input free",
           f"#const k = {k}.", f"time({clk}, 0..k)."]
    for p in d.inputs():
        if p.name in clocks or p.name in d.data:      # a DATA input is a token per instant (the symbolic reading)
            continue
        n = p.name
        if re.fullmatch(r"(rst_n|rstn|reset_n|resetn|nrst|rstN|resetN)", n):   # camelCase variants: the DSL route's naming convention
            out.append(f"val({n}, 0, 0).  val({n}, 1, T) :- time({clk}, T), T >= 1.")
        elif re.fullmatch(r"(rst|reset)", n):
            out.append(f"val({n}, 1, 0).  val({n}, 0, T) :- time({clk}, T), T >= 1.")
        elif isinstance(p.width, tuple):
            e = p.width[1]
            out.append(f"{{ val({n}, L, T) : enum_member({e}, L, _) }} = 1 :- time({clk}, T).")
        else:
            out.append(f"{{ val({n}, V, T) : V = 0..{2 ** p.width - 1} }} = 1 :- time({clk}, T).")
    return "\n".join(out) + "\n"


def contract_as_spec(text: str) -> str:
    """guarantee -> bad; require -> an assumption on the environment."""
    body = re.sub(r"(?<![\w])guarantee\(", "bad(", text)
    body = re.sub(r"(?<![\w])model\(", "cmodel(", body)          # a data-output MODEL is checked as an obligation
    return ("% the module's contract as a spec: guarantee = bad, require = assumed of the environment, model = obligation\n"
            + body + "\n:- require(_, _).\n#defined require/2.\n")


_VAL_REF = re.compile(r"\bval\(\s*([a-z_][\w]*(?:\([^()]*\))?)\s*,")


def dark_signals(text: str, d) -> list:
    """Signal names a contract READS with `val(N, ...)` that the design does not declare.

    A contract is written against the module's PORTS, and nothing checked that those ports exist.
    A clause over a name the design has no atom for can never fire, so the guarantee is VACUOUSLY
    satisfied and the run is green -- `spec: OK -- no bad reachable` on a design that is wrong.
    Found on examples/spec2rtl/intdiv/units/lzc: the operand was changed from a plain port to a
    `port_lane`, whose atoms are `a(0)..a(w-1)`, and the contract still said `val(a, A, T)`. It
    passed while the design was wrong for 170 of its 256 inputs.

    This is `compose.dark_terms`' rule one layer up: a read of something nothing derives is a hard
    problem, not a silence. A LANE BASE is reported too -- `val(a, ...)` where `a` is a lane is the
    exact mistake above, and the fix is to read a member, `val(a(0), ...)`.
    """
    known = set(d.wires())
    lanes = set(d.lanes)
    dark = []
    # Comments first: a contract that DOCUMENTS this trap writes `val(a, ...)` in its prose, and
    # scanning the raw text reports the documentation as the defect. (It did.)
    text = "\n".join(ln.split("%", 1)[0] for ln in text.splitlines())
    for m in _VAL_REF.finditer(text):
        n = m.group(1)
        base = n.split("(")[0]
        if "(" in n:
            if base not in lanes and n not in known:
                dark.append(n)
        elif n in lanes:
            dark.append(f"{n} (a LANE: read a member, {n}(0), not the base)")
        elif n not in known:
            dark.append(n)
    seen, out = set(), []
    for n in dark:                                     # stable order, no duplicates
        if n not in seen:
            seen.add(n); out.append(n)
    return out


def verify_contract(module_path, k: int = 8, witness: bool = False, induct: "int | None" = None) -> RefineResult:
    module_path = pathlib.Path(module_path)
    d = load(module_path)
    cpath = contract_of(module_path)
    res = RefineResult()
    if cpath is None:
        res.fail(f"no contract next to {module_path.name} (expected {module_path.stem}.contract.lp)")
        return res
    dark = dark_signals(cpath.read_text(), d)
    if dark:
        res.fail(f"{cpath.name} reads signal(s) {module_path.stem} does not declare: "
                 + ", ".join(dark)
                 + " -- a clause over a name with no atom can never fire, so the guarantee would be"
                   " VACUOUSLY satisfied and this run would be green on a broken design")
        return res
    td = pathlib.Path(tempfile.mkdtemp(prefix="aspfirst_contract_"))
    atexit.register(shutil.rmtree, td, ignore_errors=True)   # lives for the run, not forever
    spec = td / "spec.lp"
    spec.write_text(contract_as_spec(cpath.read_text()))
    stim = td / "stim.lp"
    stim.write_text(generated_stim(d, k))
    gpath = cpath.with_name(cpath.name[:-3] + ".ghost.lp")           # the contract's ghost init, for --induct
    if gpath.exists():
        (td / "spec.ghost.lp").write_text(gpath.read_text())
    r = refine(spec, stim, module_path, witness=witness, induct=induct, unit_scale=True)
    r.lines.insert(0, f"contract: {module_path.name} against {cpath.name} (generated stimulus, k={k})")
    return r
