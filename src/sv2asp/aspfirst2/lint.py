"""The ASP-first LINT: (1) the SUBSET gate -- `load` refuses any statement that is not a
vocabulary fact or a comb rule in the restricted grammar; (2) the STATIC checks of
`lib/aspfirst/aspfirst_lint.lp` (widths, drivers, pins, comb loops), run through clingo with the
`comb_head/1` / `dep/2` facts this module derives from the guarded rules. Findings come back as
`lint(...)` atoms; `sel_not_1bit` is a warning, everything else an error."""
from __future__ import annotations

import json
import atexit
import pathlib
import shutil
import subprocess
import tempfile

from .libgen import LIB_DIR
from .load import Design, SubsetError, load, load_text

WARN = {"sel_not_1bit"}


def clingo_bin() -> str:
    from .. import config
    b = config.load().tool("clingo")
    if not b:
        raise RuntimeError("clingo not found (CLINGO_BIN, sv2asp.toml [tools], or PATH)")
    return b


def derived_facts(d: Design) -> str:
    """Facts the static lint needs about the guarded rules: their heads and their same-instant
    dependencies (guards and reads)."""
    out = []
    for r in d.rules:
        out.append(f"comb_head({r.head}).")
        for s, _ in r.guards:
            out.append(f"dep({r.head}, {s}).")
        for s, _ in r.reads:
            out.append(f"dep({r.head}, {s}).")
    return "\n".join(sorted(set(out))) + ("\n" if out else "")


def run_clingo(files: list, extra_args: tuple = (), timeout: int = 120) -> tuple:
    """(exit_status, atoms) via `--outf=2`; atoms of the FIRST witness. `status` is
    'SATISFIABLE' / 'UNSATISFIABLE' / 'ERROR' (stderr appended to atoms as one line)."""
    p = subprocess.run([clingo_bin(), "--outf=2", "-q1", *extra_args, *[str(f) for f in files]],
                       capture_output=True, text=True, timeout=timeout)
    if p.returncode not in (10, 20, 30) or not p.stdout.strip():
        return "ERROR", [p.stderr.strip() or p.stdout.strip()]
    j = json.loads(p.stdout)
    status = j.get("Result", "ERROR")
    atoms: list = []
    if status.startswith("SATISFIABLE"):
        w = j["Call"][0].get("Witnesses", [])
        if w:
            atoms = list(w[-1]["Value"])
        status = "SATISFIABLE"
    return status, atoms


def comb_loops(d: Design) -> list:
    """`lint(comb_loop(N))` for every net on a combinational cycle -- computed HERE rather than in
    `aspfirst_lint.lp`, and this is a performance fix with a measurement behind it.

    The ASP form was a transitive closure computed by GROUNDING:

        reach(N, M) :- dep(N, M).
        reach(N, P) :- reach(N, M), dep(M, P).
        lint(comb_loop(N)) :- reach(N, N).

    which is quadratic in reachable pairs. On tens of nets that is invisible; on a 16x16 toroidal
    grid, where every cell depends on eight neighbours and nearly everything reaches nearly
    everything, `reach/2` grounds toward 4,353^2 pairs and the lint stopped finishing in ten minutes
    -- while the DESIGN itself grounded in 51k rules and under a hundred seconds. The check was
    costing far more than the thing it checks.

    Nothing here is being solved, only inspected: a depth-first walk over the same edges is linear,
    and it can name the CYCLE instead of only the fact of one."""
    edges: dict = {}

    wires = set(d.wires())          # ports AND nets: the ASP's `wire/2` covered both, and a loop can
                                    # run through an OUTPUT PORT. Filtering to `d.nets` alone missed
                                    # exactly that, and `test_aspfirst_lint_catches_each_finding`
                                    # caught it -- the check existed and was blind to a real case.

    def leaves(e) -> list:
        """The signals an expression reads (`wire`s, not constants or widths) -- `leaf_of/2` in the ASP."""
        if isinstance(e, str):
            return [e] if e in wires else []
        if isinstance(e, tuple):
            return [n for a in e[1:] for n in leaves(a)]
        return []

    for n, e in d.defs.items():
        edges[n] = leaves(e)
    for i in d.cell_insts():                       # the COMBINATIONAL paths through library cells
        if i.cell == "lata":                       # a transparent latch passes d and en through
            q = i.pins.get("q")
            if q:
                edges.setdefault(q, []).extend(x for x in (i.pins.get("d"), i.pins.get("en")) if x)
        elif i.cell == "spram":                    # a combinational read: rd depends on ra
            rd = i.pins.get("rd")
            if rd:
                edges.setdefault(rd, []).extend(x for x in (i.pins.get("ra"),) if x)

    WHITE, GREY, BLACK = 0, 1, 2
    colour: dict = {}
    on_cycle: set = set()
    for root in list(edges):
        if colour.get(root, WHITE) != WHITE:
            continue
        stack = [(root, iter(edges.get(root, ())))]
        path = [root]
        colour[root] = GREY
        while stack:
            node, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                colour[node] = BLACK
                stack.pop()
                path.pop()
                continue
            c = colour.get(nxt, WHITE)
            if c == GREY:                          # a back edge: everything from nxt onward is a cycle
                on_cycle.update(path[path.index(nxt):])
            elif c == WHITE:
                colour[nxt] = GREY
                stack.append((nxt, iter(edges.get(nxt, ()))))
                path.append(nxt)
    return [f"lint(comb_loop({n}))" for n in sorted(on_cycle)]


def ite_arm_widths(d: Design) -> list:
    """`lint(ite_arm_width(E))` -- the two arms of an `ite` must be the same width.

    Moved here from `aspfirst_lint.lp`, and this one rule was 100% of the lint's cost on a large
    design. It read:

        lint(ite_arm_width(E)) :- opform(E), E = ite(_, A, B), w(A, WA), w(B, WB), WA != WB.

    Everything before it grounded to 66,663 rules and finished; adding this single line did not
    finish in forty seconds. `w(A, WA), w(B, WB)` is a width-by-width join the grounder does not
    restrict by `E` first, so it forms a cross product against every `ite` in the design. With 256
    cells carrying two nested `ite`s each, that is the wall.

    In Python it is what it always was: look up each arm's width and compare. Linear, no join, and
    no dependence on how a grounder happens to order literals. The width walk is the PRINTER's --
    reused rather than reimplemented, so the two cannot disagree about what a term's width is."""
    from .printer import PrintError, width_of

    out = []

    def walk(t) -> None:
        if not isinstance(t, tuple):
            return
        if t[0] == "ite" and len(t) == 4:
            try:
                wa, wb = width_of(d, t[2]), width_of(d, t[3])
            except PrintError:
                wa = wb = None                      # an undeclared net: a different finding reports it
            if wa is not None and wa != wb:
                out.append(f"lint(ite_arm_width({_term_text(t)}))")
        for a in t[1:]:
            walk(a)

    for e in d.defs.values():
        walk(e)
    return sorted(set(out))


def _term_text(t) -> str:
    """A term as the ASP text the lint's other findings use, so messages read the same either way."""
    if isinstance(t, tuple):
        return f"{t[0]}(" + ",".join(_term_text(a) for a in t[1:]) + ")"
    return str(t)


def derived_clock_misuse(d: Design) -> list:
    """A DERIVED clock (a clock pin on a design-computed net) is supported on ff and arff
    only (the divided_counter entry's v1 scope). A memory or latch clocked by one is refused
    BY NAME -- never silently mis-clocked. A derived clock must also be one bit wide."""
    ports = {q.name for q in d.inputs()}
    out = []
    for i in d.insts:
        ck = i.pins.get("clk")
        if ck is None or ck in ports:
            continue
        if i.cell in ("spram", "farray"):
            out.append(f"lint(derived_clock_unsupported({i.name}, {i.cell}))")
        w = d.width_of(ck)
        if w != 1:
            out.append(f"lint(derived_clock_not_one_bit({ck}, {w}))")
    return out


def lint_design_full(d: Design, design_path: "str | pathlib.Path") -> tuple:
    """(errors, warnings, symfacts) -- the `lint(...)` findings, and the role facts of the SYMBOLIC
    reading (`bnd(E, W).` boundary terms freed per distinct term at width W, `dat(E).` boundary-
    capable ops that keep their data term) as program text; empty when no net is data."""
    with tempfile.TemporaryDirectory() as td:
        facts = pathlib.Path(td) / "derived.lp"
        facts.write_text(derived_facts(d))
        status, atoms = run_clingo([design_path, LIB_DIR / "aspfirst.lp", LIB_DIR / "aspfirst_lint.lp", facts])
    if status == "ERROR":
        return [f"clingo could not read the design: {atoms[0][:400]}"], [], ""
    findings = sorted(set(a for a in atoms if a.startswith("lint("))
                      | set(comb_loops(d)) | set(ite_arm_widths(d)) | set(derived_clock_misuse(d)))
    errs = [a for a in findings if not any(a.startswith(f"lint({w}(") for w in WARN)]
    warns = [a for a in findings if a not in errs]
    roles = sorted(a for a in atoms if a.startswith("bnd(") or a.startswith("dat("))
    symfacts = ("% roles of the boundary-capable ops (from the lint): bnd(E, W) freed per term, dat(E) kept as a term\n"
                + "".join(a + ".\n" for a in roles)) if roles or d.data else ""
    return errs, warns, symfacts


def lint_design(d: Design, design_path: "str | pathlib.Path") -> tuple:
    """(errors, warnings) -- lists of `lint(...)` atom strings."""
    errs, warns, _ = lint_design_full(d, design_path)
    return errs, warns


def lint_composed(path: "str | pathlib.Path") -> tuple:
    """Subset gate + composition + static lint. Returns (Composed | None, errors, warnings). The
    static lint runs on the COMPOSED (flattened) program, written to `comp.lp_path`; a SubsetError
    or ComposeError is reported as the single error and nothing is returned."""
    from .compose import ComposeError, compose, composed_lp
    try:
        comp = compose(path)
    except SubsetError as e:
        return None, [f"SUBSET: {e}"], []
    except ComposeError as e:
        return None, [f"COMPOSE: {e}"], []
    d = comp.design
    if comp.modules or d.param_exprs or d.lanes:
        # the program clingo sees is the COMPOSED / RESOLVED design (children flattened; parameter
        # expressions evaluated to numbers) -- never the raw file when it has params
        td = pathlib.Path(tempfile.mkdtemp(prefix="aspfirst_composed_"))
        atexit.register(shutil.rmtree, td, ignore_errors=True)   # lives for the run, not forever
        lp = td / f"{d.name}.composed.lp"
        lp.write_text(composed_lp(comp, src=str(path)))
        comp.lp_path = lp
    else:
        comp.lp_path = pathlib.Path(path)
    errs, warns, comp.symfacts = lint_design_full(d, comp.lp_path)
    return comp, errs, warns


def lint_file(path: "str | pathlib.Path") -> tuple:
    """Subset gate + static lint (over the composed program when the design instantiates authored
    modules). Returns (design | None, errors, warnings)."""
    comp, errs, warns = lint_composed(path)
    return (comp.design if comp else None), errs, warns


def report(path, errors: list, warnings: list) -> str:
    lines = [f"aspfirst lint: {path}"]
    for w in warnings:
        lines.append(f"  WARN  {w}")
    for e in errors:
        lines.append(f"  ERROR {e}")
    lines.append("  OK: in the authoring subset, no static findings" if not errors and not warnings
                 else f"  {len(errors)} error(s), {len(warnings)} warning(s)")
    return "\n".join(lines)


__all__ = ["lint_file", "lint_design", "load", "load_text", "derived_facts", "run_clingo", "report",
           "SubsetError", "clingo_bin"]
