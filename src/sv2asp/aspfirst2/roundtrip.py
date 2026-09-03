"""The ROUND TRIP: print the authored design to SystemVerilog, translate the print back with sv2asp
in BOTH modes, and compare the three programs' traces under ONE scenario, net for net, instant
for instant -- optionally with Icarus simulating the printed SV as the independent arbiter.

    authored (design.lp + lib)  ──┐
    sv2asp flat  (print)        ──┼── same scenario ──► val(net, V, T) for EVERY declared net
    sv2asp modular (print)      ──┤                     and every memory cell
    Icarus (print)              ──┘   (inputs read off the authored model; sampled before the edge)

Any disagreement is one of three suspects -- the library, the printer, the translator -- and the
simulator breaks the tie. The comparison projects both ASP sides from the SAME net list through
generated `#show` files, so the harness cannot hand the two sides different companions (the
`_assert_modular_matches_flat` lesson). Single-valuedness (`t34`) is composed on every side."""
from __future__ import annotations

import contextlib
import io
import json
import pathlib
import re
import shutil
import subprocess
import tempfile
from dataclasses import dataclass, field

from .libgen import LIB_DIR
from .lint import clingo_bin, lint_file
from .load import Design
from .lanes import axes_of, flat_index, members_of
from .printer import CELLS_SIM, enum_width, print_sv


@dataclass
class Result:
    ok: bool = False
    lines: list = field(default_factory=list)      # the report
    traces: dict = field(default_factory=dict)     # side -> {(net, T): value}
    sv: str = ""

    def report(self) -> str:
        return "\n".join(self.lines + [("ROUNDTRIP: OK" if self.ok else "ROUNDTRIP: FAILED")])

    def say(self, s: str) -> None:
        self.lines.append(s)


# ---------------------------------------------------------------------------------------------
# projections
# ---------------------------------------------------------------------------------------------



def _word_from_bits(w: int) -> str:
    """The word `B0..B{w-1}` spell, as a clingo term. PLAIN ARITHMETIC up to 30 bits: the
    translator ships only the @func library a design USES, so a projection that reconstructs a
    word with `@add`/`@shl` on a design that never adds is an "operation undefined" -- which
    clingo reports as an info line and DROPS THE RULE INSTANCE silently. That is how the
    packed-lane read came back `None` on its first try (G27c, 2026-09-02), and the per-bit
    fallback below has carried the same hazard since it was written. Above 30 bits a bare
    Number would wrap (hard rule 4), so the wide-safe @funcs stay -- and a design that wide
    uses them."""
    if w <= 30:
        return " + ".join(f"B{j}*{1 << j}" if j else "B0" for j in range(w))
    expr = "B0"
    for j in range(1, w):
        expr = f"@add(@shl(B{j}, {j}, {w}), {expr}, {w})"
    return expr


def _mem_insts(d: Design) -> list:
    # farray included (2026-08-25): the spram-only filter meant NO farray design ever had its
    # CELLS compared -- the same farray blind spot as induct.py's data-memory detection (stage-A
    # fix). Cells are state; a cell defect surfaces only indirectly through reads without this.
    return [i for i in d.insts if i.cell in ("spram", "farray")]


def projection(d: Design, side: str) -> str:
    """The `#show` file for one side: `o(net, V, T)` for every declared net (clocks excluded) and
    `om(inst, A, V, T)` for every memory cell. `side` is authored | flat | modular.

    The TRANSLATED sides also get a PER-BIT FALLBACK per multi-bit net: the translator
    classifies some nets per-bit (bitvec) and, by policy, emits their WORD atom only where a
    word consumer exists -- an internal per-bit net with only per-bit consumers has correct
    bit atoms and NO word atom, which the word-only projection read as a dark net
    (booth_production32's partial_product_16, journal step 52). The fallback reconstructs the
    word from the bit atoms with the translator's own @shl/@add (wide-safe, canonical
    encoding); on a word-form net there are no bit atoms and the fallback is silent, so the
    two rules never disagree."""
    ports = {q.name for q in d.inputs()}
    clocks = {i.pins.get("clk") for i in d.insts} & ports    # PRIMARY only: a derived clock
    top = translated_top(d.name)   # an ASP TERM, so a name ASP would read as a variable is quoted
                                                             # is a computed net and is compared
    out = ["% generated projection -- the SAME net list on every side of the round trip"]
    for n in d.wires():
        if n in clocks:
            continue
        atom = {"authored": f"val({n}, V, T)", "flat": f"val({n}, V, T)",
                "modular": f"val({top}, {n}, V, T)"}[side]
        w = d.width_of(n)
        # A MULTI-BIT LANE MEMBER ON A TRANSLATED SIDE. The print is `logic [N-1:0][W-1:0] L`
        # and the translator models that packed 2-D array as its FLAT BITS, `L(0)..L(N*W-1)`,
        # declaring the shape as `dims(L, packed(N), packed(W))`. So the translated atom
        # `L(i)` is BIT i, not member i: read as a member it returned bit 0 for member 0 --
        # `x(0): authored=2 modular=0`, silently, on every lane wider than one bit (the third
        # block's G27c, 2026-09-02). Member i is bits i*W .. i*W+W-1, and the declaration the
        # translator itself emits is what says which reading applies; a 1-bit lane has no
        # second packed dimension and bit i IS member i.
        lm = members_of(n, d.lanes) if side != "authored" else None
        if lm and isinstance(w, int) and w >= 2:
            L, i = lm[0], flat_index(lm[1], axes_of(d.lanes, lm[0]))
            pre = f"{top}, " if side == "modular" else ""
            packed = f"dims({pre}{L}, packed(_), packed({w}))"
            out.append(f"o({n}, V, T) :- {atom}, not dims({pre}{L}, packed(_), packed(_)).")
            bits = ", ".join(f"val({pre}{L}({i * w + j}), B{j}, T)" for j in range(w))
            out.append(f"o({n}, V, T) :- {packed}, {bits}, V = {_word_from_bits(w)}.")
            # the chained solve re-injects a lane REGISTER's state as bit atoms: the flat spelling
            out.append(f"oc({L}({i * w} + J), B, T) :- {packed}, J = 0..{w - 1}, val({pre}{L}({i * w} + J), B, T).")
            out.append("#defined dims/3. #defined dims/4.")
            continue
        out.append(f"o({n}, V, T) :- {atom}.")
        if side in ("flat", "modular") and isinstance(w, int) and 2 <= w <= 64:
            # a LANE MEMBER's per-bit atom is name(idx, bit), never name(idx)(bit) -- the
            # naive append produced a syntax error the first time a multi-bit lane net
            # (the regeneration run's popcount chain) reached this fallback
            if n.endswith(")") and "(" in n:
                base, rest = n.split("(", 1)
                bt = lambda i, _b=base, _c=rest[:-1]: f"{_b}({_c}, {i})"
            else:
                bt = lambda i, _n=n: f"{_n}({i})"
            bit = (lambda i: f"val({bt(i)}, B{i}, T)") if side == "flat" else                   (lambda i: f"val({top}, {bt(i)}, B{i}, T)")
            body = ", ".join(bit(i) for i in range(w))
            out.append(f"o({n}, V, T) :- {body}, V = {_word_from_bits(w)}.")
            # chain-only per-bit export: the incremental solve must re-inject a per-bit
            # REGISTER's state as bit atoms (its hold rule reads bits; an injected word feeds
            # nothing -- stage1_row_4/5 died at every chain boundary without this). The
            # comparator never reads oc/3.
            atom_i = {"flat": f"val({bt('I')}, B, T)",
                      "modular": f"val({top}, {bt('I')}, B, T)"}[side]
            out.append(f"oc({bt('I')}, B, T) :- {atom_i}.")
    for i in _mem_insts(d):
        atom = {"authored": f"val(cell({i.name}, A), V, T)", "flat": f"val({i.name}(A), V, T)",
                "modular": f"val({top}, {i.name}(A), V, T)"}[side]
        out.append(f"om({i.name}, A, V, T) :- {atom}.")
    out += ["#show o/3.", "#show om/4.", "#show oc/3.", "#defined oc/3."]
    return "\n".join(out) + "\n"


def _solve(files: list, timeout: int = 300) -> tuple:
    try:
        p = subprocess.run([clingo_bin(), "--outf=2", "-q1", f"--time-limit={timeout}",
                            *[str(f) for f in files]],
                           capture_output=True, text=True, timeout=timeout + 5)
    except subprocess.TimeoutExpired:
        # a refusal by name, not a traceback: the 256-cell grid ended the round trip with an
        # uncaught TimeoutExpired (G27b, 2026-09-02). clingo carries its own --time-limit so the
        # solver stops by itself even when the Python that spawned it is killed.
        return "TIMEOUT", {}, (f"the solve did not finish within {timeout}s -- the translated design "
                               f"grounds too much for one shot; see the methodology's budget chapter")
    if p.returncode & 1:                    # clingo sets bit 1 when INTERRUPTED: its --time-limit ran out
        return "TIMEOUT", {}, f"the solve did not finish within {timeout}s (clingo's own time limit)"
    if p.returncode not in (10, 20, 30) or not p.stdout.strip():
        return "ERROR", {}, (p.stderr or p.stdout)[-800:]
    j = json.loads(p.stdout)
    status = j.get("Result", "ERROR")
    trace: dict = {}
    if status.startswith("SATISFIABLE"):
        w = j["Call"][0].get("Witnesses", [])
        for a in (w[-1]["Value"] if w else []):
            m = re.match(r"o\((\w+(?:\([\d,]+\))?),(.+),(\d+)\)$", a)      # a net, or a lane member q(2)
            if m:
                trace[(m.group(1), int(m.group(3)))] = m.group(2)
                continue
            m = re.match(r"om\((\w+),(\d+),(.+),(\d+)\)$", a)
            if m:
                trace[(f"{m.group(1)}[{m.group(2)}]", int(m.group(4)))] = m.group(3)
        status = "SATISFIABLE"
    return status, trace, ""


def _solve_chained(files: list, scenario_text: str, k: int, proj_path, top: str, side: str,
                   step_timeout: int = 120) -> tuple:
    """The incremental (per-instant) solve of a TRANSLATED side (the user's direction,
    2026-08-25). The direct solve grounds the whole time axis at once, and on a design whose
    datapath reads many memory cells the candidate VALUE sets cross-product through every
    arithmetic op, instant over instant -- rv_ooo_b's ALU temps each grounded >1M val candidates
    and the solve never left grounding (Solving: 0.00s at the 300 s timeout). Grounding a
    2-instant window {t, t+1} instead, with instant t's atoms supplied as FACTS from the previous
    step, keeps every join singleton x singleton: the same unique trace (the scenario pins the
    inputs, init0 pins the state, t34 enforces single-valuedness), computed in k+1 small solves.
    Validated on rv_ooo_b: 0 mismatches against the authored side on every shared key, 13 s vs
    the direct solve's 300 s+ timeout. The window is 2 instants because async-reset rules read
    BOTH ends of the edge (signals at T and T+1)."""
    scen_body = "\n".join(ln for ln in scenario_text.splitlines()
                          if "time(" not in ln.replace(" ", "") or ".." not in ln)
    cell = lambda m, a: {"flat": f"{m}({a})", "modular": f"{top}, {m}({a})"}[side]
    net = lambda n: {"flat": f"{n}", "modular": f"{top}, {n}"}[side]
    init0 = [f for f in files if f.name.endswith("__init0.lp")]
    rest = [f for f in files if not f.name.endswith("__init0.lp")]
    trace: dict = {}
    facts = ""
    with tempfile.TemporaryDirectory() as td:
        step = pathlib.Path(td) / "step.lp"
        for t in range(k + 1):
            hi = min(t + 1, k)
            step.write_text(scen_body + f"\ntime(clk, {t}..{hi}).\n" + facts)
            fs = rest + (init0 if t == 0 else []) + [step, proj_path]
            try:
                p = subprocess.run([clingo_bin(), "--outf=2", "-q1", f"--time-limit={step_timeout}",
                                    *[str(f) for f in fs]],
                                   capture_output=True, text=True, timeout=step_timeout + 5)
            except subprocess.TimeoutExpired:
                return "TIMEOUT", {}, f"(chained, step {t}) the solve did not finish within {step_timeout}s"
            if p.returncode & 1:
                return "TIMEOUT", {}, f"(chained, step {t}) the solve did not finish within {step_timeout}s (clingo's own time limit)"
            if p.returncode not in (10, 20, 30) or not p.stdout.strip():
                return "ERROR", {}, f"(chained, step {t}) " + (p.stderr or p.stdout)[-600:]
            j = json.loads(p.stdout)
            status = j.get("Result", "ERROR")
            if not status.startswith("SATISFIABLE"):
                return status, {}, f"(chained, step {t})"
            w = j["Call"][0].get("Witnesses", [])
            nxt = []
            for a in (w[-1]["Value"] if w else []):
                m = re.match(r"o\((\w+(?:\([\d,]+\))?),(.+),(\d+)\)$", a)
                if m:
                    n, v, tt = m.group(1), m.group(2), int(m.group(3))
                    if tt == t or (t == k and tt == k):
                        trace[(n, tt)] = v
                    if tt == t + 1:
                        nxt.append(f"val({net(n)}, {v}, {tt}).")
                    continue
                m = re.match(r"om\((\w+),(\d+),(.+),(\d+)\)$", a)
                if m:
                    mn, ad, v, tt = m.group(1), m.group(2), m.group(3), int(m.group(4))
                    if tt == t or (t == k and tt == k):
                        trace[(f"{mn}[{ad}]", tt)] = v
                    if tt == t + 1:
                        nxt.append(f"val({cell(mn, ad)}, {v}, {tt}).")
                    continue
                m = re.match(r"oc\((\w+\([\d,]+\)),(.+),(\d+)\)$", a)
                if m and int(m.group(3)) == t + 1:
                    nxt.append(f"val({net(m.group(1))}, {m.group(2)}, {m.group(3)}).")
            facts = "\n".join(nxt) + "\n"
    return "SATISFIABLE", trace, ""


def _norm(v: str) -> str:
    """Trace values as canonical text: strip clingo's quotes on wide strings."""
    return v[1:-1] if v.startswith('"') else v


# ---------------------------------------------------------------------------------------------
# Icarus
# ---------------------------------------------------------------------------------------------

#: The simulators the round trip can arbitrate with, in the order `auto` tries them --
#: Verilator FIRST (the user, 2026-09-03: some companies only have Verilator, so it must work
#: correctly, and where both exist it is the one to prefer). Icarus is 4-state: it prints x
#: where a value depends on unreset state and that sample is not definite. Verilator is
#: 2-state: it prints 0 there, so its definiteness rule is the TWO-FILL rule in
#: `_verilator_runs` -- the bench runs once with every unreset bit at 0 and once at 1, and a
#: sample counts only where the two runs agree. A value that depends on power-on changes with
#: the fill and is skipped, the decision Icarus takes with x. It is an approximation in one
#: direction only (`q ^ q` on an unreset q is x in 4-state and 0 under both fills); no sample
#: Icarus would compare is ever skipped.
SIMULATORS = ("verilator", "icarus")


def _tools() -> tuple:
    return shutil.which("iverilog"), shutil.which("vvp")


def sim_available(sim: str) -> bool:
    if sim == "icarus":
        return all(_tools())
    if sim == "verilator":
        return shutil.which("verilator") is not None
    return False


def resolve_sim(sim: "str | None") -> "str | None":
    """`auto` -> the first installed simulator in SIMULATORS order (None when there is none);
    a named simulator is returned as named -- its absence is the caller's to report."""
    if sim == "auto":
        return next((s for s in SIMULATORS if sim_available(s)), None)
    return sim


def icarus_trace(d, sv_path, vecs, k, sample_at=4):
    """The bench under Icarus (4-state: an x/z sample is not definite). None when absent."""
    return _bench_trace(d, sv_path, vecs, k, sample_at, "icarus")


def verilator_trace(d, sv_path, vecs, k, sample_at=4):
    """The bench under Verilator (2-state: definite only where the two power-on fills agree)."""
    return _bench_trace(d, sv_path, vecs, k, sample_at, "verilator")


def _icarus_runs(tdp: pathlib.Path, sv_path) -> "list | str":
    iverilog, vvp = _tools()
    c = subprocess.run([iverilog, "-g2012", "-o", "sim", str(sv_path), str(CELLS_SIM), "tb.sv"],
                       cwd=tdp, capture_output=True, text=True)
    if c.returncode != 0:
        # the compiler's own words, not a guess: "simulator absent or did not compile" once
        # hid a testbench defect behind a line that read as a missing tool (2026-09-02)
        return (c.stderr or c.stdout).strip()[-600:] or "iverilog failed without a message"
    r = subprocess.run([vvp, "sim"], cwd=tdp, capture_output=True, text=True, timeout=300)
    return [r.stdout]


def _verilator_runs(tdp: pathlib.Path, sv_path) -> "list | str":
    """Compile ONCE (Verilator builds C++, the expensive half), run TWICE: `--x-initial unique`
    hands the power-on value of every unreset bit to the runtime, and `+verilator+rand+reset+0`
    / `+1` fill them with all zeros / all ones. The caller keeps a sample only where both runs
    agree (the two-fill rule, see SIMULATORS)."""
    vl = shutil.which("verilator")
    c = subprocess.run([vl, "--binary", "--timing", "-Wno-fatal", "--x-initial", "unique",
                        "--top-module", "tb", "-o", "sim", str(sv_path), str(CELLS_SIM), "tb.sv"],
                       cwd=tdp, capture_output=True, text=True, timeout=900)
    if c.returncode != 0:
        return (c.stderr or c.stdout).strip()[-600:] or "verilator failed without a message"
    outs = []
    for fill in ("0", "1"):
        r = subprocess.run([str(tdp / "obj_dir" / "sim"), f"+verilator+rand+reset+{fill}"],
                           cwd=tdp, capture_output=True, text=True, timeout=300)
        outs.append(r.stdout)
    return outs


def _parse_out(text: str, enum_of: dict) -> dict:
    got: dict = {}
    for line in text.splitlines():
        m = re.match(r"OUT (\d+) (\S+) (\S+) ([01xzXZ]+)$", line.strip())
        if m:
            bad = any(ch in "xzXZ" for ch in m.group(4))
            n, t = m.group(2), int(m.group(1))
            v = None if bad else m.group(3)
            if v is not None and n in enum_of:
                v = enum_of[n].get(int(v), v)
            got[(n, t)] = v
    return got


def _bench_trace(d: Design, sv_path: pathlib.Path, vecs: list, k: int, sample_at: int, sim: str) -> "dict | str | None":
    """Simulate the printed design: input vector T at time 10T, posedge at 10T+5, every net and
    memory cell sampled at 10T+sample_at (before the edge, so the sample at T is the model's
    val(., ., T)). Enum nets are read numerically and mapped back to their tags. None when the
    simulator is absent; the compiler's message (a str) when the design does not compile. A
    sample that is not definite -- x/z under Icarus, fill-dependent under Verilator -- is None."""
    if not sim_available(sim):
        return None
    # A design with no instances has no clock at all, and an instance with no `clk` pin
    # contributes None -- neither may reach the port connection below. PRIMARY clocks only:
    # a DERIVED clock (an internal net on a clock pin) is not driven by the bench -- it is an
    # ordinary observed net. And the pick is SORTED: `next(iter(set))` over a two-clock set
    # was nondeterministic across processes, and the losing order wired the bench to a
    # non-port, leaving the real clock undriven -- a flaky Icarus leg (found the day derived
    # clocks landed, latent since the harness was written).
    ports_in = {p.name for p in d.inputs()}
    clocks = ({i.pins.get("clk") for i in d.insts} - {None}) & ports_in
    ins = [p for p in d.inputs() if p.name not in clocks and p.name != "clk"]   # the bench drives clk itself; a design with no register never names it a clock
    obs = [n for n in d.wires() if n not in clocks and n not in {p.name for p in ins}]
    clk = sorted(clocks)[0] if clocks else None
    # LANES: a member `q(2)` is `q[2]` of an unpacked-array port/net in the SV; declared once per lane
    def sv_name(n: str) -> str:
        m = members_of(n, d.lanes)
        return f"{m[0]}{''.join(f'[{i}]' for i in m[1])}" if m else n
    def lane_of(n: str):
        m = members_of(n, d.lanes)
        return m[0] if m else None
    tb = ["module tb;", "  logic clk = 0;", "  always #5 clk = ~clk;"]
    declared: set = set()
    def lane_decl(ln: str) -> str:              # a lane is PACKED in the print: [N-1:0] or [N-1:0][W-1:0]
        N, W, _dr = d.lanes[ln]
        dims = "".join(f"[{a - 1}:0]" for a in axes_of(d.lanes, ln))
        return f"  logic {dims}{f'[{W - 1}:0]' if W > 1 else ''} {ln};"
    for p in ins:
        ln = lane_of(p.name)
        if ln:
            if ln not in declared:
                tb.append(lane_decl(ln))
                declared.add(ln)
        else:
            tb.append(f"  logic [{p.width - 1}:0] {p.name};")
    for p in d.outputs():
        ln = lane_of(p.name)
        if ln:
            if ln not in declared:
                tb.append(lane_decl(ln))
                declared.add(ln)
        else:
            tb.append(f"  wire [{p.width - 1}:0] {p.name};")
    port_names = []
    for p in [*ins, *d.outputs()]:
        nm = lane_of(p.name) or p.name
        if nm not in port_names:
            port_names.append(nm)
    conns_l = [f".{nm}({nm})" for nm in port_names]
    if clk and any(p.name == clk for p in d.inputs()):
        conns_l.insert(0, f".{clk}(clk)")
    conns = ", ".join(conns_l)
    tb.append(f"  {d.name} dut({conns});")
    tb.append("  initial begin")
    for t in range(k + 1):
        vec = vecs.get(t, {})
        for p in ins:
            v = vec.get(p.name.replace(" ", ""), vec.get(p.name))
            if v is not None:
                tb.append(f"    {sv_name(p.name)} = {p.width}'d{v};")
        tb.append(f"    #{sample_at};")
        for n in obs:
            ref = sv_name(n) if any(p.name == n for p in d.outputs()) else f"dut.{sv_name(n)}"
            # the member's name WITHOUT spaces: `y(0, 0)` would split into two tokens and every
            # sample of a multi-axis lane was dropped -- and the run still said "agrees" (2026-09-03)
            tb.append(f'    $display("OUT {t} {n.replace(" ", "")} %0d %b", {ref}, {ref});')
        for i in _mem_insts(d):
            for a in range(i.iparams["depth"]):
                tb.append(f'    $display("OUT {t} {i.name}[{a}] %0d %b", dut.{i.name}[{a}], dut.{i.name}[{a}]);')
        tb.append(f"    #{10 - sample_at};")
    tb += ["    $finish;", "  end", "endmodule"]
    with tempfile.TemporaryDirectory() as td:
        tdp = pathlib.Path(td)
        (tdp / "tb.sv").write_text("\n".join(tb))
        runs = _icarus_runs(tdp, sv_path) if sim == "icarus" else _verilator_runs(tdp, sv_path)
        if isinstance(runs, str):
            return runs
    enum_of = {}
    for n in d.wires():
        w = d.width_of(n)
        if isinstance(w, tuple):
            enum_of[n] = {v: l for l, v in d.enums[w[1]]}
        elif n in d.enums:
            # A REGISTER THAT CARRIES `enum_member` FACTS holds symbols on the authored side --
            # its value arrives through `tag(...)` -- while the simulator prints its encoding.
            # Keying the map on the enum-TYPED width alone missed it (`arch_reg(st, 2)` is a
            # plain width), so the first enum register through this round trip reported
            # `authored=two icarus=2` as a mismatch (G21, 2026-09-02).
            enum_of[n] = {v: l for l, v in d.enums[n]}
    parsed = [_parse_out(out, enum_of) for out in runs]
    got = dict(parsed[0])
    for other in parsed[1:]:                     # the two-fill rule: disagreement = not definite
        for key, v in list(got.items()):
            if v is not None and other.get(key) != v:
                got[key] = None
        for key in other:
            got.setdefault(key, None)
    return got


# ---------------------------------------------------------------------------------------------
# the round trip
# ---------------------------------------------------------------------------------------------

def _translate(sources: pathlib.Path, mode: str, out: str) -> tuple:
    """Run sv2asp's CLI in-process; (exit, captured_output)."""
    from .. import cli
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
        try:
            rc = cli.main(["--sources", str(sources), "--mode", mode, "--strict-coverage",
                           "--init-zero", "--no-x-init", "-o", out])
        except SystemExit as e:                     # argparse / cli exits
            rc = int(e.code or 0)
    return rc, buf.getvalue()


def scenario_for(d: Design, text: str, side: str) -> str:
    """The ONE scenario text re-addressed for a side: modular atoms are `val(top, sig, V, T)`,
    a memory cell is `val(cell(m, A), ..)` authored / `val(m(A), ..)` translated. Only the atom
    SHAPE changes; the stimulus, horizon and projections are the same text."""
    if side == "authored":
        return text
    top = translated_top(d.name)
    out = text
    for i in _mem_insts(d):
        cell = re.compile(r"\bval\(\s*cell\(\s*" + re.escape(i.name) + r"\s*,\s*")
        out = cell.sub((f"val({top}, {i.name}(" if side == "modular" else f"val({i.name}("), out)
        out = re.sub(r"(val\((?:" + re.escape(top) + r", )?" + re.escape(i.name) + r"\([^)]*)\)\)", r"\1)", out)
    if side == "modular":
        for n in d.wires():
            out = re.sub(r"\bval\(\s*" + re.escape(n) + r"\s*,", f"val({top}, {n},", out)
        # a LANE written with a variable index in the scenario -- `val(d(I), V, T)` -- has no literal member
        # name to match: prefix the lane base (`val(d(` -> `val(top, d(`), once
        for ln in d.lanes:
            out = re.sub(r"\bval\(\s*" + re.escape(ln) + r"\s*\(", f"val({top}, {ln}(", out)
            out = out.replace(f"val({top}, {top}, {ln}(", f"val({top}, {ln}(")   # (a member already prefixed above)
    # an INPUT lane is printed PACKED, so the translated program's port is the WORD `d` and its lane atoms
    # `d(I)` are DERIVED from it (the word->lane bridge). The scenario drives the members; pack them into
    # the word here -- the translator's own lane->word bridge shape -- so both readings agree.
    pre = f"{top}, " if side == "modular" else ""
    packs = []
    for ln, (N, W, dr) in d.lanes.items():
        if dr != "input":
            continue
        reads = ", ".join(f"val({pre}{ln}({i}), L{i}, T)" for i in range(N))
        steps, acc = [], "L0"
        for i in range(1, N):
            steps.append(f"S{i} = @shl(L{i}, {i * W}, {N * W})")
            steps.append(f"W{i} = @bor({acc}, S{i}, {N * W})")
            acc = f"W{i}"
        packs.append(f"val({pre}{ln}, {acc}, T) :- {reads}{', ' + ', '.join(steps) if steps else ''}.")
    if packs:
        out += "\n% round trip: the INPUT lanes packed into their word ports (the print is packed)\n" + "\n".join(packs) + "\n"
    return out


def translated_top(name: str) -> str:
    """The term the TRANSLATOR will use for the top instance.

    Two subsystems solve the same problem differently, and the round trip is where they meet.
    On the authored side a module name ASP would read as a variable is written QUOTED --
    `module("TopModule")` -- which is the only ASP escape there is. On the translated side
    sv2asp has always normalised identifiers instead, lowering a leading capital
    (`_types.PyslangFrontend._cid`), so the same block arrives as `topModule`.

    The comparison must therefore use the translator's convention here, not the authoring
    one. Reached for the authoring convention first, and the modular side derived nothing at
    all: every atom was addressed to an instance the translation had never heard of.
    """
    from ..frontend._types import _TypesMixin
    return _TypesMixin._cid(name)


def _horizon(scenario_text: str) -> int:
    m = re.search(r"#const\s+k\s*=\s*(\d+)", scenario_text)
    if not m:
        raise ValueError("the scenario must set `#const k = N.`")
    return int(m.group(1))


def roundtrip(design_path, scenario_path, mode: str = "behav", icarus: bool = False,
              keep: "str | None" = None, sample_at: int = 4, both: bool = False,
              incremental: bool = False, sim: "str | None" = None) -> Result:
    # ``sim`` names the arbiter: "verilator", "icarus", or "auto" (the first installed, in
    # SIMULATORS order); ``icarus=True`` is the older spelling of sim="icarus".
    # ``both`` re-adds the FLAT translation as a third side. Modular-only is the default (the
    # user's call, 2026-08-22, LESSONS par E16): the flat leg never discriminated in any round-trip
    # finding -- flat and modular share their front half, so defects of the class the round trip
    # catches (F25, F27) sit upstream of the emitter split and break both identically -- while
    # emitter parity has its own witnessed gates (hard rule 1, test_translate.py), and the extra
    # translation + solve cost a third of the round trip's wall time on a large design.
    res = Result()
    design_path, scenario_path = pathlib.Path(design_path), pathlib.Path(scenario_path)
    from .lint import lint_composed
    comp, errs, warns = lint_composed(design_path)
    d = comp.design if comp else None
    authored_lp = comp.lp_path if comp else design_path      # the RESOLVED program when the design has params
    for w in warns:
        res.say(f"lint WARN {w}")
    if errs or d is None:
        for e in errs:
            res.say(f"lint ERROR {e}")
        res.say("the design does not lint; nothing to round-trip")
        return res
    res.say(f"lint: OK ({design_path.name})")
    scenario_text = scenario_path.read_text()
    from .refine import const_collisions
    coll = const_collisions(d, [scenario_text])
    if coll:
        res.say(f"design name(s) {coll} are `#const`s of the scenario: clingo would rewrite them; rename")
        return res
    k = _horizon(scenario_text)

    work = pathlib.Path(keep) if keep else pathlib.Path(tempfile.mkdtemp(prefix="aspfirst_rt_"))
    work.mkdir(parents=True, exist_ok=True)
    try:
        sv_path = work / f"{d.name}.sv"
        sv = print_sv(d, mode=mode, src=str(design_path))
        sv_path.write_text(sv)
        res.sv = sv
        shutil.copy(CELLS_SIM, work / "cells_sim.sv")
        res.say(f"print: {sv_path if keep else sv_path.name} ({mode})")   # the path only when it will still exist

        # translate back, both modes
        sj = work / "sources.json"
        manifest = {"package_files": [{"path": "cells_sim.sv", "type": "file"}],
                    "sources": [{"path": sv_path.name, "type": "file"}],
                    "top": d.name}
        if any(i.cell == "lata" for i in d.insts):
            manifest["allow_latches"] = True        # the printed latch idiom is deliberate
        sj.write_text(json.dumps(manifest, indent=1))
        sides_run = ("authored", "flat", "modular") if both else ("authored", "modular")
        rc_m, log_m = _translate(sj, "modular", str(work / "mod") + "/")
        (work / "sv2asp_modular.log").write_text(log_m)
        rc_f, log_f = (0, "")
        if both:
            rc_f, log_f = _translate(sj, "emit", str(work / "flat.lp"))
            (work / "sv2asp_flat.log").write_text(log_f)
        if rc_f != 0 or rc_m != 0:
            res.say(("sv2asp: flat exit {}, modular exit {}".format(rc_f, rc_m) if both
                     else f"sv2asp: modular exit {rc_m}") + " -- the printed SV does not translate "
                    "cleanly" + (f" (see {work}/sv2asp_*.log)" if keep else " (re-run with --keep DIR for the files)"))
            for ln in (log_f + log_m).splitlines():
                if "UNSUPPORTED" in ln or "PROBLEM" in ln or "ERROR" in ln:
                    res.say("   " + ln.strip()[:200])
            return res
        res.say(("sv2asp: flat + modular translate" if both else "sv2asp: modular translates")
                + " with --strict-coverage, exit 0")

        # solve the three ASP sides under ONE scenario
        lib = LIB_DIR
        scens = {}
        for side in sides_run:
            scens[side] = work / f"scenario_{side}.lp"
            scens[side].write_text(scenario_for(d, scenario_text, side))
        sides = {
            "authored": [authored_lp, lib / "aspfirst.lp", lib / "aspfirst_init0.lp", lib / "aspfirst_t34.lp"],
            "modular": [*(p for p in sorted((work / "mod").glob("*.lp"))
                          if not p.name.endswith(("__scenario_stub.lp", "__xinit.lp")))],
        }
        if both:
            sides["flat"] = [work / "flat.lp",
                             *(p for p in [work / "flat__init0.lp", work / "flat__t34.lp"] if p.exists())]
        sides = {k: sides[k] for k in sides_run}
        traces: dict = {}
        for side, files in sides.items():
            proj = work / f"proj_{side}.lp"
            proj.write_text(projection(d, side))
            if incremental and side != "authored":
                status, trace, err = _solve_chained(files, scens[side].read_text(), k, proj,
                                                    top=translated_top(d.name), side=side)
            else:
                status, trace, err = _solve(files + [scens[side], proj])
            if status != "SATISFIABLE":
                res.say(f"{side}: {status} {err[:300]}" + (" (a t34 violation = some signal took two values)"
                                                           if status == "UNSATISFIABLE" else ""))
                return res
            traces[side] = trace
            res.say(f"{side}: SATISFIABLE, {len(trace)} (net, T) samples")
        res.traces = traces

        # compare authored vs flat vs modular on every key either side has
        ok = True
        keys = sorted(set().union(*(set(traces[s]) for s in sides_run)),
                      key=lambda kt: (kt[1], kt[0]))
        diffs = []
        for key in keys:
            vals = {s: (_norm(traces[s][key]) if key in traces[s] else None) for s in sides_run}
            if len(set(vals.values())) > 1:
                diffs.append((key, vals))
        if diffs:
            ok = False
            res.say(f"MISMATCH on {len(diffs)} (net, T) sample(s) between the ASP sides (first 12):")
            for (n, t), vals in diffs[:12]:
                res.say(f"   {n} @T={t}: " + "  ".join(f"{s}={v}" for s, v in vals.items()))
        else:
            res.say(f"ASP sides agree on all {len(keys)} samples (every net and memory cell, every T)")

        # the simulator
        want = sim or ("icarus" if icarus else None)
        sim = resolve_sim(want)
        if want and sim is None:
            res.say("simulator: none installed (verilator or iverilog) -- the round trip has no arbiter")
            ok = False
        if sim:
            vecs: dict = {}
            # the trace spells a member as clingo prints it (`q(0,0)`), the design as it was
            # declared (`q(0, 0)`): compare without spaces, or a multi-axis input is never driven
            # and every sample is x (2026-09-03)
            in_names = {p.name.replace(" ", "") for p in d.inputs()}
            for (n, t), v in traces["authored"].items():
                if n.replace(" ", "") in in_names:
                    vecs.setdefault(t, {})[n.replace(" ", "")] = _norm(v)
            got = (icarus_trace if sim == "icarus" else verilator_trace)(d, sv_path, vecs, k, sample_at=sample_at)
            if isinstance(got, str):
                res.say(f"{sim}: the printed design (or its testbench) did not compile -- " + got.replace("\n", " | "))
                got = None
            elif got is None:
                res.say(f"{sim}: not run (simulator absent)")
                ok = False
            else:
                # An UNRESET register (`ff`, `lata`) is X in the simulator at T=0 and 0 under the ASP's
                # init0 companion; a combinational net downstream can be DEFINITE in the simulator yet
                # derived from that X (a totality default arm turns X into its else-value), so T=0
                # is not a fair comparison for such a design. Excluded, and said.
                unreset = [i.name for i in d.cell_insts() if i.cell in ("ff", "lata")]
                if unreset:
                    res.say(f"{sim}: T=0 excluded from the comparison -- {len(unreset)} unreset register(s) "
                            f"({', '.join(unreset[:4])}{', ...' if len(unreset) > 4 else ''}): the simulator's X "
                            f"against init0's zero is a power-on convention, not a design difference")
                nondef = sum(1 for v in got.values() if v is None)
                if nondef:
                    res.say(f"{sim}: {nondef} sample(s) not definite -- skipped ("
                            + ("x/z in the 4-state simulator" if sim == "icarus" else
                               "2-state: the all-zeros and all-ones power-on fills disagree, so the value depends on unreset state")
                            + ")")
                idiffs, checked = [], 0
                for (n, t), v in got.items():
                    if v is None:
                        continue                                 # x/z: the simulator is not definite
                    if unreset and t == 0:
                        continue
                    key = (n, t)
                    a = traces["authored"].get(key)
                    if a is None:
                        continue                                 # ASP has no value: nothing to compare (F4/x)
                    checked += 1
                    if _norm(a) != str(v):
                        idiffs.append((key, _norm(a), v))
                if idiffs:
                    ok = False
                    res.say(f"{sim.upper()} MISMATCH on {len(idiffs)} definite sample(s) (first 12):")
                    for (n, t), a, v in idiffs[:12]:
                        res.say(f"   {n} @T={t}: authored={a} {sim}={v}")
                elif checked == 0:
                    # a comparison over NOTHING is not agreement: the bench's output names did not
                    # reach the parser once and the run read as green (the goals-must-be-reachable
                    # rule, applied to the simulator's half)
                    ok = False
                    res.say(f"{sim.upper()} COMPARED NO DEFINITE SAMPLE -- the bench's output lines matched no "
                            "observed net (a naming mismatch, or every sample x): not a round trip")
                else:
                    res.say(f"{sim} agrees on all {checked} definite samples")
        res.ok = ok
        return res
    finally:
        # the work directory is REMOVED unless --keep, on every path out -- the early returns (a print
        # that does not translate, a side that is UNSAT) used to leave it behind: 33 `aspfirst_rt_*` dirs
        # after one day of probes (2026-08-18). A failure report says how to keep the files.
        if not keep:
            shutil.rmtree(work, ignore_errors=True)
