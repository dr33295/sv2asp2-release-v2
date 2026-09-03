"""The REFINEMENT runner: spec -> ASP_0 -> ASP_1 -> ... -> ASP_n, each step checked in clingo.

    spec.lp     the block's contract: `bad(Tag, T)` monitors (a violation at T) and `goal(Tag, T)`
                reachability targets, over the block's PORTS -- plus any ghost / reference model
                the monitors need (a ghost count, a ghost queue). Property layer: anything goes.
    stim.lp     the legal stimulus: `#const k`, `time(clk, 0..k)`, the reset, the inputs as choices.
    level_i.lp  a design in the authoring subset in which the unrefined parts are `abstract(Net)`.
    level_i.inv.lp   the level's invariants:
                     assume(Tag, T)  -- an ASSUMPTION on the level's abstract parts, violated at T
                                        (asserted `:- assume(_, _)` while checking this level;
                                        becomes an OBLIGATION of the next level that drops it)
                     viol(Tag, T)    -- a claimed GUARANTEE about the level's concrete parts,
                                        violated at T (checked: required-violation must be UNSAT)

What `refine SPEC STIM CUR [--prev PREV]` establishes, in order:
  1. CUR is in the subset and lints; its abstract nets are counted (the loop's termination measure).
  2. CUR is a MONOTONE refinement of PREV: every def / rule / instance of PREV is kept verbatim,
     ports are identical, abstracts only shrink. (Refinement replaces `abstract(N)` by structure;
     re-implementing something already concrete is a NEW lineage, not a refinement.)
  3. SPEC: under STIM, with CUR's assumptions asserted, no `bad(_, _)` is reachable      -> UNSAT.
  4. REFINES PREV: every assumption PREV made that CUR no longer makes is DISCHARGED -- required-
     violation of those (renamed) monitors under CUR's assumptions                      -> UNSAT;
     assumptions CUR still makes are CARRIED (reported, not proven); PREV's guarantees re-checked.
  5. GUARANTEES: CUR's own `viol` monitors, required-violation                            -> UNSAT.
  6. GOALS: every `goal(Tag, _)` of the spec is still reachable                          -> SAT each.
  7. single-valuedness (t34) is composed into every solve; totality (cover) of the concrete part.
A SAT where UNSAT was expected is a COUNTEREXAMPLE, printed as a per-instant table of every
port and net (abstract ones starred) with the violated tags -- what an LLM gets back.
Zero abstract nets + every check green = printable (`print`).

`--induct K` adds k-INDUCTION on top (see induct.py): the checks above are the BASE (at a horizon
of at least K); the STEP starts from an ARBITRARY state (registers, cells and the monitors' GHOST
state free at T=0, inputs free), assumes the whole property set for K cycles and requires a
violation at K. UNSAT = inductive = holds for all time. A failed step is an INVARIANT REQUEST."""
from __future__ import annotations

import json
import pathlib
import re
import subprocess
import tempfile
import threading
import time
from dataclasses import dataclass, field

from .induct import (GHOST_PROJ, UNIQ_ON, ghost_cases, ghost_file_for, ghost_gating, ghost_lines, ghost_predicates, ghost_state_at, init_heads, init_membership, props_reading,
                     reserved_collisions,
                     pin_ghost_state, plan_step)
from .libgen import LIB_DIR
from .lint import clingo_bin, lint_composed
from .load import Design, term_to_str


@dataclass
class RefineResult:
    ok: bool = True
    lines: list = field(default_factory=list)
    abstract: list = field(default_factory=list)
    counterexamples: list = field(default_factory=list)      # (check name, table text)
    owed: list = field(default_factory=list)                 # obligations owed to Lean (symbolic reading)
    inductive: list = field(default_factory=list)            # --induct: tags proven inductive
    not_inductive: list = field(default_factory=list)        # --induct: tags with a step counterexample
    bounded_only: list = field(default_factory=list)         # v2: properties over the refmodel-gated oracle

    def say(self, s: str) -> None:
        self.lines.append(s)

    def fail(self, s: str) -> None:
        self.ok = False
        self.lines.append("  FAIL " + s)

    def warn(self, s: str) -> None:
        """Said, and visible, but not a failure: the author has to decide whether it is a gap."""
        self.lines.append(s)

    def report(self) -> str:
        out = list(self.lines)
        for name, table in self.counterexamples:
            out += [f"--- counterexample: {name} ---", table]
        tail = f"  ({len(self.owed)} obligation(s) owed to Lean: {self.owed})" if self.owed else ""
        out.append(("REFINE: OK" + tail) if self.ok else "REFINE: FAILED")
        return "\n".join(out)


# ---------------------------------------------------------------------------------------------
# solving
# ---------------------------------------------------------------------------------------------

def _solve(files: list, extra: str = "", consts: dict | None = None, timeout: int = 300) -> tuple:
    """(status, atoms) -- status SATISFIABLE / UNSATISFIABLE / ERROR(msg); atoms of the last witness."""
    with tempfile.TemporaryDirectory() as td:
        ex = pathlib.Path(td) / "extra.lp"
        ex.write_text(extra)
        args = [clingo_bin(), "--outf=2", "-q1", f"--time-limit={timeout}",     # the solver bounds ITSELF: it
                *[f"-c{k}={v}" for k, v in (consts or {}).items()],                # stops even if its parent is killed
                *[str(f) for f in files], str(ex)]
        try:
            p = subprocess.run(args, capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return f"TIMEOUT after {timeout}s", []
    if p.returncode & 1:                    # clingo's own --time-limit ran out (INTERRUPTED bit)
        return f"TIMEOUT after {timeout}s (clingo's own time limit)", []
    if p.returncode not in (10, 20, 30) or not p.stdout.strip():
        return f"ERROR: {(p.stderr or p.stdout).strip()[-600:]}", []
    j = json.loads(p.stdout)
    status = j.get("Result", "ERROR")
    atoms: list = []
    if status.startswith("SATISFIABLE"):
        w = j["Call"][0].get("Witnesses", [])
        atoms = list(w[-1]["Value"]) if w else []
        status = "SATISFIABLE"
    return status, atoms


def _solve_all(files: list, extra: str = "", consts: dict | None = None, project: str = "",
               limit: int = 4000, timeout: int = 600) -> tuple:
    """(status, [atoms of every witness]) -- with `project` = a predicate signature `name/arity`,
    the enumeration is PROJECTED onto it (`#project`), so the witnesses are the distinct values of
    that predicate and nothing else. `limit` caps the enumeration; the caller must SAY when it hit."""
    with tempfile.TemporaryDirectory() as td:
        ex = pathlib.Path(td) / "extra.lp"
        # ONE directive per signature: `#project a/1, b/2.` is not the same thing, and a malformed
        # directive makes clingo error -- which a caller that skips on a non-SAT status reads as
        # "nothing to report". A check that does not run must not look like a check that passed.
        ex.write_text(extra + "".join(f"\n#project {sig.strip()}." for sig in project.split(",") if sig.strip())
                      + ("\n" if project else ""))
        args = [clingo_bin(), "--outf=2", "-q0", f"--models={limit}", f"--time-limit={timeout}",   # -q0: EVERY witness (q1 keeps the last only)
                *(["--project=project"] if project else []),
                *[f"-c{k}={v}" for k, v in (consts or {}).items()], *[str(f) for f in files], str(ex)]
        try:
            p = subprocess.run(args, capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            return f"TIMEOUT after {timeout}s", []
    if p.returncode & 1:                    # clingo's own --time-limit ran out (INTERRUPTED bit)
        return f"TIMEOUT after {timeout}s (clingo's own time limit)", []
    if p.returncode not in (10, 20, 30) or not p.stdout.strip():
        return f"ERROR: {(p.stderr or p.stdout).strip()[-600:]}", []
    j = json.loads(p.stdout)
    status = j.get("Result", "ERROR")
    ws = [list(w["Value"]) for w in j["Call"][0].get("Witnesses", [])] if status.startswith("SATISFIABLE") else []
    return ("SATISFIABLE" if status.startswith("SATISFIABLE") else status), ws


class _Session:
    """Ground the step program ONCE, then answer SEVERAL queries against it.

    Measured on the gshare entry (128-cell PHT, two 7-bit inputs XORed into the index): grounding the
    step takes 114 s and SOLVING it takes 0.01 s. The search was never the cost. But the runner shelled
    out to a fresh clingo per query, so that same program was written out from scratch for the
    hypothesis check, the vacuity check, the whole-set step, and again for every per-tag step on a
    failure -- five or more identical groundings to ask five questions about one program.

    Only MONOTONE additions can be grounded incrementally (a grounded part cannot be withdrawn), and
    the queries happen to be monotone in exactly the right order: hypothesis, then + unique-states,
    then + "some property is violated at k". The one genuinely non-monotone choice -- WHICH properties
    -- becomes an assumable atom, `ind__want(J)`, pinned per solve. Nothing about any query's meaning
    changes; only how many times its program is written out.
    """

    def __init__(self, files: list, base: str, consts: dict | None = None, nprops: int = 0) -> None:
        import clingo

        self._clingo = clingo
        # the logger swallows grounder INFO chatter ("atom does not occur in any rule head") --
        # the clingo BINARY prints those to stderr where _solve's subprocess capture kept them
        # out of the report; the API path would print them straight to this process's stderr,
        # which made the session and no-session reports differ under 2>&1 capture.
        self._infos: list = []
        self.ctl = clingo.Control(["--models=1", *[f"-c{k}={v}" for k, v in (consts or {}).items()]],
                                  logger=lambda code, msg: self._infos.append((code, msg)))
        # The library carries its `@func`s in a `#script (python)` block, and the clingo MODULE is built
        # without embedded-script support (the binary has it; `ctl.load` reports "python support not
        # available"). The functions are ordinary Python, so they are lifted out of the block and handed
        # to the grounder as a CONTEXT instead -- the same functions, resolved the same way, just bound
        # from this process rather than from an interpreter clingo would have had to embed.
        ns: dict = {}
        texts = []
        for f in files:
            text = pathlib.Path(f).read_text()
            for blk in re.findall(r"#script\s*\(python\)(.*?)#end\.", text, re.S):
                exec(blk, ns)                                    # noqa: S102 - our own generated library
            texts.append(re.sub(r"#script\s*\(python\).*?#end\.", "", text, flags=re.S))
        self._ctx = type("Ctx", (), {k: staticmethod(v) for k, v in ns.items() if callable(v)})()
        # ONE part, grounded ONCE. The files must go in the SAME part as `base`: a part that is added
        # and never grounded contributes NOTHING, and the first version of this added each file as its
        # own part and grounded only `base` -- so the design, the library and the spec were all absent.
        # Every query then had no rules to violate, went UNSAT, and was reported INDUCTIVE. A false
        # proof that looked like a 3-minute speed-up, and only the teeth test could tell the difference.
        self.ctl.add("base", [], "\n".join([*texts, base]))
        self.ctl.ground([("base", [])], context=self._ctx)
        self._nprops = nprops

    def _run(self, assumptions: list, timeout: int) -> tuple:
        """One query under a TOTAL wall-clock deadline -- `_solve`'s contract, bound included.

        `_solve` runs clingo as a subprocess under `subprocess.run(timeout=...)`, so an expiry kills
        the child and returns the string `TIMEOUT after Ns`, which every caller already reports as
        "this check did not run". The in-process path had NO bound at all: a non-terminating search
        hung `refine` with no diagnostic -- a fail-loud regression (hard rule 2) in the very code
        path where an empty program once produced a false `INDUCTIVE at K=1`. This restores the
        contract literally, which is why no caller changed.

        The MECHANISM was chosen by measurement, not taste. The obvious `async_=True` +
        `wait(deadline)` + `model()` / `resume()` form works and is byte-identical on three entries,
        but it puts each solve on its own solver thread with the main thread polling, and this route
        runs MANY small solves per refine (six closure cases, per-property and per-case step
        queries): `ve146_serialdata --induct 1` went 58 s -> 267 s, worse than the 107 s subprocess
        path it replaced. A watchdog costs nothing per solve by comparison: the model loop stays
        SYNCHRONOUS -- the fast path, and the one whose witness collection was already correct --
        and a `threading.Timer` calls `Control.interrupt()` if the deadline passes. `interrupt()`
        acts on the active solve; the result then reports `interrupted`, which is clingo's own
        signal rather than a flag of ours racing the solve's completion.

        NOT bounded: GROUNDING. `ground()` takes no timeout, `interrupt()` affects the active solve,
        and a Python signal handler cannot preempt a C call -- so a pathological grounding still runs
        unbounded here where the subprocess path killed it. Grounding is deterministic work rather
        than search, but this IS a residual regression against `_solve`; closing it means running the
        session in a child process.
        """
        atoms: list = []
        sat = False
        watchdog = threading.Timer(timeout, self.ctl.interrupt)
        watchdog.daemon = True
        watchdog.start()
        try:
            with self.ctl.solve(assumptions=assumptions, yield_=True) as h:
                for m in h:
                    sat = True
                    atoms = [str(a) for a in m.symbols(shown=True)]
                res = h.get()
        except RuntimeError as e:                       # a malformed assumption / grounding error
            return f"ERROR: {e}", []
        finally:
            watchdog.cancel()
        if res.interrupted:                             # clingo's own signal, not a flag of ours
            return f"TIMEOUT after {timeout}s", []
        if res.unsatisfiable:
            return "UNSATISFIABLE", []
        return ("SATISFIABLE", atoms) if sat or res.satisfiable else ("ERROR: unknown", [])

    def solve_guards(self, on: "set[str]", all_guards: "list[str]", timeout: int = 300) -> tuple:
        """(status, atoms), same contract as `_solve`. Pins EVERY guard atom in ``all_guards`` by
        assumption -- True iff its text is in ``on`` -- so each bounded query is selected against
        the one grounding, with every other query's constraint switched off explicitly (a guard
        left free would let the solver choose it, which is sound for these queries but harder to
        reason about; pinned, the equivalence to the per-query _solve is immediate)."""
        return self._run([(self._clingo.parse_term(g), g in on) for g in all_guards], timeout)

    def solve(self, uniq: bool = False, step: bool = False, want: "set | None" = None,
              timeout: int = 300) -> tuple:
        """(status, atoms), same contract as `_solve`. The query is chosen entirely by ASSUMPTION:
        `uniq` turns the unique-states constraint on, `step` requires a violation at k, and `want`
        selects WHICH properties count as a violation (every other one assumed off)."""
        f = self._clingo.Function
        assumptions = [(f("ind__uniq"), uniq), (f("ind__step"), step)]
        for j in range(self._nprops):
            assumptions.append((f("ind__want", [self._clingo.Number(j)]), want is not None and j in want))
        return self._run(assumptions, timeout)


def _rename(text: str, mapping: dict) -> str:
    for a, b in mapping.items():
        text = re.sub(rf"\b{a}\(", f"{b}(", text)
    return text


# The author-facing violation vocabulary (the user's ruling, 2026-08-29): a specification
# may define its failure families as `failType(Name, T)` instead of `bad(Name, T)` -- the
# stance is "define the failure types", not "generate bad". One bridge rule feeds the
# runner's unchanged bad-machinery; _tags treats the two heads as one vocabulary.
FAILTYPE_BRIDGE = "bad(R, T) :- failType(R, T).\n#defined failType/2.\n"


def _tags(text: str, pred: str) -> list:
    """The distinct Tag names a monitor file defines for `pred(Tag, T)` -- read off every
    STATEMENT's head (a line may carry several statements: an earlier line-anchored regex
    silently skipped the second `goal(...)` on a line, and would have skipped a second `assume`,
    which is a hole in the discharge check -- found by the rv_mc_ctrl author, 2026-08-17). A
    VARIABLE tag (`assume(Tag, T) :- bad(Tag, T).` -- level 0 assuming the whole spec) is
    reported as `<every tag>` and matched with `_`; a parametrised tag `starved(I)` becomes
    `starved(_)`."""
    from .load import statements
    tags = []
    preds = (pred, "failType") if pred == "bad" else (pred,)
    for _, st in statements(text):
        head = st.split(":-", 1)[0].strip()
        pred_hit = next((q for q in preds if head.startswith(q + "(")), None)
        if pred_hit is None:
            continue
        pred = pred_hit
        # the first top-level argument, by a balanced scan (the head's OTHER argument may be `T+1`,
        # which the term parser does not read -- an earlier version skipped such heads silently)
        depth, i, start = 0, len(pred) + 1, len(pred) + 1
        while i < len(head):
            ch = head[i]
            if ch == "(":
                depth += 1
            elif ch == ")":
                if depth == 0:
                    break
                depth -= 1
            elif ch == "," and depth == 0:
                break
            i += 1
        raw = re.sub(r"\s+", "", head[start:i])
        if not raw:
            continue
        if raw[0].isupper() or raw[0] == "_":
            name = "<every tag>"
        else:
            name = re.sub(r"\b[A-Z_]\w*\b", "_", raw)
        if name not in tags:
            tags.append(name)
    return tags


def _clocks(d: Design, stim_text: str) -> set:
    """PRIMARY clocks only: clock-pin nets that are input ports (plus any axis a stimulus
    names). A DERIVED clock -- a clock pin on a design-computed net -- gets NO free time
    axis: its edges are value transitions on the master axis (the library's derived_clock
    rules), and it is an ordinary net everywhere else (projected, compared, tabled)."""
    ports = {q.name for q in d.inputs()}
    return ({i.pins.get("clk") for i in d.insts} & ports) \
        | set(re.findall(r"\btime\(\s*(\w+)\s*,", stim_text))


def _projection(d: Design, clocks: set) -> str:
    out = [f"o({n}, V, T) :- val({n}, V, T)." for n in d.wires() if n not in clocks]
    out += ["#show o/3.", "#show bad/2.", "#show goal/2.", "#show assume/2.", "#show viol/2.",
            "#show p_assume/2.", "#show p_viol/2.", "#show gap/2."]
    return "\n".join(out) + "\n"


def _table(d: Design, atoms: list, k: int, clocks: set) -> str:
    """The counterexample as a per-instant table (abstract nets starred) + the fired monitors."""
    cols = [n for n in d.wires() if n not in clocks]
    vals: dict = {}
    fired: list = []
    for a in atoms:
        # a NET may be a lane member `req(0)` and a monitor TAG may be functional `starved(2)`: the name
        # patterns accept one level of parentheses (a `\w+` here dropped both silently -- the same slip
        # as the round-trip reader's, found by the lane arbiter's counterexample table)
        m = re.match(r"o\((\w+(?:\([^()]*\))?),(.+),(\d+)\)$", a)
        if m:
            vals[(m.group(1), int(m.group(3)))] = m.group(2).strip('"')
            continue
        m = re.match(r"(bad|goal|assume|viol|p_assume|p_viol|gap)\((\w+(?:\([^()]*\))?),(\d+)\)$", a)
        if m:
            fired.append((int(m.group(3)), m.group(1), m.group(2)))
    hdr = ["T"] + [(n + "*" if n in d.abstracts else n) for n in cols]
    rows = [hdr]
    for t in range(k + 1):
        rows.append([str(t)] + [vals.get((n, t), "-") for n in cols])
    widths = [max(len(r[i]) for r in rows) for i in range(len(hdr))]
    lines = ["  ".join(c.rjust(w) for c, w in zip(r, widths)) for r in rows]
    fired.sort()
    viols = [(t, p, tag) for t, p, tag in fired if p != "goal"]
    goals = [(t, p, tag) for t, p, tag in fired if p == "goal"]
    if viols:
        lines.append("violated: " + ", ".join(f"{p}({tag}) @T={t}" for t, p, tag in viols)
                     + "   (p_assume/p_viol = the PREVIOUS level's assumption/guarantee, now an obligation)")
    if goals:
        lines.append("goals seen: " + ", ".join(f"{tag} @T={t}" for t, _, tag in goals))
    pv = sorted(m.group(1) + "=" + m.group(2) for a in atoms for m in [re.match(r"pval\((.+),(\d+)\)$", a)] if m)
    if pv:
        lines.append("  boundary (free per term): " + ", ".join(pv))
    return "\n".join(lines)


# ---------------------------------------------------------------------------------------------
# structural monotonicity
# ---------------------------------------------------------------------------------------------

def _structure(d: Design) -> dict:
    return {
        "ports": [(p.name, p.direction, p.width) for p in d.ports],
        "nets": {n.name: n.width for n in d.nets},
        "enums": {e: tuple(ms) for e, ms in d.enums.items()},
        "defs": {n: term_to_str(t) for n, t in d.defs.items()},
        "rules": {re.sub(r"\s+", " ", r.text) for r in d.rules},
        "insts": {i.name: (i.cell, tuple(sorted(i.pins.items())), tuple(sorted(i.iparams.items())))
                  for i in d.insts},
        "abstract": set(d.abstracts),
    }


def monotone(prev: Design, cur: Design) -> list:
    """Violations of monotone refinement (empty = OK)."""
    a, b = _structure(prev), _structure(cur)
    v = []
    if a["ports"] != b["ports"]:
        v.append("the port list changed (a refinement keeps the interface; change it in a new lineage)")
    for n, w in a["nets"].items():
        if b["nets"].get(n) != w:
            v.append(f"net {n} ({w}) was dropped or re-typed")
    for e, ms in a["enums"].items():
        if b["enums"].get(e) != ms:
            v.append(f"enum {e} changed")
    for n, t in a["defs"].items():
        if b["defs"].get(n) != t:
            v.append(f"def({n}, {t}) was dropped or changed")
    for r in a["rules"] - b["rules"]:
        v.append(f"comb rule dropped or changed: {r}")
    for i, sig in a["insts"].items():
        if b["insts"].get(i) != sig:
            v.append(f"instance {i} was dropped or changed")
    for m, shape in prev.arch_mems.items():
        if cur.arch_mems.get(m) != shape:
            v.append(f"architectural memory {m} {shape} was dropped or re-shaped (the spec names it)")
    prev_names = set(a["nets"]) | {p[0] for p in a["ports"]} | set(prev.arch_mems)
    for n in b["abstract"] - a["abstract"]:
        if n in prev_names:                # a NEW net may be introduced abstract (an abstract module's
            v.append(f"{n} became abstract (it was concrete in the previous level)")   # outputs); an old one may not go back
    return v


# ---------------------------------------------------------------------------------------------
# the runner
# ---------------------------------------------------------------------------------------------

def const_collisions(d: Design, texts: list) -> list:
    """Design names that a `#const` in a composed file would REWRITE. clingo substitutes a
    `#const baud = 2.` over the whole composed program, so a net named `baud` becomes `2` in
    every atom -- the checks stay sound (the renaming is uniform) but the counterexample table
    shows the net as absent and a monitor written against it means something else. Found by the
    uart_tx author, 2026-08-17. Reported as a lint error by refine and roundtrip."""
    consts = set()
    for t in texts:
        consts |= set(re.findall(r"#const\s+(\w+)\s*=", t))
    names = {d.name, *d.wires(), *(i.name for i in d.insts), *d.enums,
             *(l for ms in d.enums.values() for l, _ in ms)}
    return sorted(names & consts)


def _inv_for(design_path: pathlib.Path, explicit: "str | None") -> "pathlib.Path | None":
    if explicit:
        return pathlib.Path(explicit)
    cand = design_path.with_suffix(".inv.lp")
    return cand if cand.exists() else None


def refine(spec, stim, cur, prev=None, cur_inv=None, prev_inv=None, k: "int | None" = None,
           init_zero: bool = True, witness: bool = False, induct: "int | None" = None,
           free_reset: bool = False, unit_scale: bool = False) -> RefineResult:
    res = RefineResult()
    if stim is None:
        return _refine_stimless(spec, cur, cur_inv=cur_inv, induct=induct, init_zero=init_zero,
                                free_reset=free_reset)
    spec, stim, cur = pathlib.Path(spec), pathlib.Path(stim), pathlib.Path(cur)
    prev = pathlib.Path(prev) if prev else None
    cur_inv_p = _inv_for(cur, cur_inv)
    prev_inv_p = _inv_for(prev, prev_inv) if prev else None
    consts = {"k": k} if k is not None else {}
    kk = k if k is not None else int(re.search(r"#const\s+k\s*=\s*(\d+)", stim.read_text()).group(1))
    if induct is not None and induct < 1:
        res.fail("--induct K needs K >= 1")
        return res
    # With --induct K the bounded phase is the BASE CASE of the induction, and a base needs exactly K
    # instants from reset -- not the stimulus's whole horizon. The universal checks (spec, refines-prev,
    # guarantees, totality) run at k = K; the GOALS, which are existential and must reach what the
    # spec asks for, keep the stimulus's k. Running the base at the spec's k was BMC in disguise: on
    # the predictor 40 of 41 s were three bounded solves at k=10 that the proof makes unnecessary
    # (a bounded counterexample from reset is still one `refine` without --induct away).
    kg, goal_consts = kk, dict(consts)                  # the goals' horizon
    if induct is not None:
        kk, consts = induct, {"k": induct}
    res.say(f"refine: {cur.name}" + (f"  (prev {prev.name})" if prev else "") + f"  spec {spec.name}  stim {stim.name}  k={kk}"
            + (f"  (the induction's BASE: K instants from reset; goals at k={kg})" if induct is not None else ""))

    # 1. lint (over the COMPOSED program when the level instantiates authored modules)
    comp, errs, warns = lint_composed(cur)
    for w in warns:
        res.say(f"  lint WARN {w}")
    if errs or comp is None:
        for e in errs:
            res.fail(f"lint {e}")
        return res
    d = comp.design
    cur_file = comp.lp_path
    if comp.tree:
        res.say("  hierarchy: " + ", ".join(f"{ip}:{m}{' (abstract, contract assumed)' if ab else ''}"
                                             for ip, m, ab in comp.tree))
    res.abstract = list(d.abstracts)
    # A LANE abstracted whole is 256 names; listing them all buries the line it belongs to. Name the
    # first few and say how many are left -- the count is the fact, the names are the illustration.
    _ab = d.abstracts if len(d.abstracts) <= 8 else d.abstracts[:6] + [f"... and {len(d.abstracts) - 6} more"]
    res.say(f"  lint: OK; abstract: {len(d.abstracts)} net(s)"
            + (f" -- {', '.join(_ab)}" if d.abstracts else " -- fully concrete: printable"))
    # ARCHITECTURAL memories: state the spec may name. Every `cell(M, ..)` the spec reads must be an
    # arch_mem the level declares (built as an spram of that shape, or abstract) -- else the atom is
    # dark and every monitor over it is silently vacuous, which is exactly the hole this closes.
    if d.arch_mems:
        res.say("  architectural memories: " + ", ".join(
            f"{m} ({dp} x {w}, {'ABSTRACT: every cell free each instant' if m in d.abstract_mems() else 'built as ' + next((i.cell for i in d.cell_insts() if i.name == m), 'spram')})"
            for m, (dp, w) in d.arch_mems.items()))
    spec_mems = sorted(set(re.findall(r"\bcell\(\s*([a-z]\w*)\s*,", spec.read_text())))
    undeclared_mems = [m for m in spec_mems if m not in d.arch_mems]
    if undeclared_mems:
        res.fail(f"the spec reads memory cell(s) of {undeclared_mems}: a spec may name ARCHITECTURAL memories "
                 f"only -- declare `arch_mem(M, Depth, Width)` in the level and build it as `inst(M, spram)` "
                 f"of that shape or leave it `abstract(M)`; a spec must never name a private memory or a flop")
        return res
    texts = [spec.read_text(), stim.read_text(), comp.inv] + ([cur_inv_p.read_text()] if cur_inv_p else []) \
        + ([prev_inv_p.read_text()] if prev_inv_p else [])
    coll = const_collisions(d, texts)
    if coll:
        res.fail(f"design name(s) {coll} are `#const`s of the composed spec/stim/invariants: clingo would "
                 f"rewrite them to the constant's value in every atom. Rename the net(s).")
        return res

    # 2. monotone vs prev
    pd = None
    pcomp = None
    if prev:
        pcomp, perrs, _ = lint_composed(prev)
        if pcomp is None:
            res.fail(f"previous level does not lint: {perrs[:1]}")
            return res
        pd = pcomp.design
        v = monotone(pd, d)
        if v:
            for x in v:
                res.fail(f"not a monotone refinement of {prev.name}: {x}")
            return res
        refined = sorted(set(pd.abstracts) - set(d.abstracts))
        added = []
        if len(d.nets) > len(pd.nets):
            added.append(f"{len(d.nets) - len(pd.nets)} net(s)")
        if len(d.defs) > len(pd.defs):
            added.append(f"{len(d.defs) - len(pd.defs)} def(s)")
        if len(d.rules) > len(pd.rules):
            added.append(f"{len(d.rules) - len(pd.rules)} rule(s)")
        if len(d.insts) > len(pd.insts):
            added.append(f"{len(d.insts) - len(pd.insts)} instance(s)")
        res.say(f"  monotone vs {prev.name}: OK; refined {', '.join(refined) if refined else 'no abstract net'}"
                + (f"; added {', '.join(added)}" if added else ""))

    lib = LIB_DIR
    base = [cur_file, lib / "aspfirst.lp", lib / "aspfirst_abstract.lp", lib / "aspfirst_t34.lp", stim, spec]
    if init_zero:
        base.append(lib / "aspfirst_init0.lp")
    clocks = _clocks(d, stim.read_text())
    proj = _projection(d, clocks)
    # the OBLIGATION protocol (CDS slice 2): a monitor `obl(Tag, Have, Want, T)` says "at T the value Have
    # must equal Want" WITHOUT comparing them itself. The runner compares: two concrete values that differ
    # are a violation (a `bad`); a difference involving a TERM (the symbolic reading) is not decidable here
    # -- it is OWED to Lean and reported, never failed. Authors reference `obl_viol(Tag, T)` in an
    # `assume` when a level has not built the part the obligation is about.
    proj += ("obl_viol(Tag, T) :- obl(Tag, H, W, T), H != W, @issym(H) = 0, @issym(W) = 0.\n"
             "obl_owed(Tag, T) :- obl(Tag, H, W, T), H != W, @issym(H) = 1.\n"
             "obl_owed(Tag, T) :- obl(Tag, H, W, T), H != W, @issym(W) = 1.\n"
             "bad(Tag, T) :- obl_viol(Tag, T).\n"
             # a MODEL that is no longer definitional -- the previous level's (p_model) once this level
             # built the net, or a concrete child's (cmodel) -- is an obligation on the built value
             "obl(model(N), V2, V, T) :- p_model(N, V, T), val(N, V2, T).\n"
             "obl(model(N), V2, V, T) :- cmodel(N, V, T), val(N, V2, T).\n"
             # the spec reads a boundary's value with pval(P, V): a concrete boundary value is itself, and a
             # spec-declared boundary (`boundary(P, W)`) over a CONCRETE argument is evaluated here (a token
             # argument is freed per term by the symbolic companion)
             "pval(V, V) :- V = 0..255.\n"
             "pval(P, V) :- boundary(P, _), P = slc(A, L, W1), @issym(A) = 0, V = @slc(A, L, W1).\n"
             "pval(P, V) :- boundary(P, _), P = bit(A, I), @issym(A) = 0, V = @slc(A, I, 1).\n"
             "pval(P, V) :- boundary(P, _), P = eq(A, B), @issym(A) = 0, @issym(B) = 0, V = @eq(A, B).\n"
             "pval(P, V) :- boundary(P, _), P = ne(A, B), @issym(A) = 0, @issym(B) = 0, V = @ne(A, B).\n"
             "pval(P, V) :- boundary(P, _), P = lt(A, B, W1), @issym(A) = 0, @issym(B) = 0, V = @lt(A, B, W1).\n"
             "pval(P, V) :- boundary(P, _), P = ge(A, B, W1), @issym(A) = 0, @issym(B) = 0, V = @ge(A, B, W1).\n"
             "#defined boundary/2.\n"
             "#defined obl/4.  #defined p_model/3.  #defined cmodel/3.  #defined pval/2.  #show obl_owed/2.\n")
    obl_tags = _tags(spec.read_text(), "obl") + [f"model({m})" for m in _tags(spec.read_text(), "cmodel")]
    # the SYMBOLIC reading (CDS at authoring time): data nets carry terms, the boundary is free per term
    symbolic = bool(d.data)
    if symbolic:
        base.append(lib / "aspfirst_symbolic.lp")
        proj += comp.symfacts
        din = [pt.name for pt in d.inputs() if pt.name in d.data]
        touched = [n for n in din if re.search(rf"\bval\(\s*{re.escape(n)}\s*,", stim.read_text())]
        if touched:
            res.fail(f"symbolic reading: stim.lp mentions data input(s) {touched}; under data/1 an input is a fresh "
                     f"token per instant -- remove it from the stimulus (pin values only in the concrete reading)")
            return res
        bnd = re.findall(r"^bnd\((.+),(\d+)\)\.$", comp.symfacts, re.M)
        dat = re.findall(r"^dat\((.+)\)\.$", comp.symfacts, re.M)
        res.say(f"  symbolic reading: data {d.data}; boundary free per term (reaches control): "
                + (", ".join(f"{e} ({w} bit)" for e, w in bnd) if bnd else "none")
                + "; kept as terms (data only): " + (", ".join(dat) if dat else "none"))
    # --induct, v2 (METHODOLOGY tenets 2-5). Two scales:
    #   UNIT scale (contract.py): the v1 ghost path unchanged -- a unit contract's event-captured
    #   job ghost proves in seconds standalone; the enumeration wall is a composition-scale
    #   phenomenon and never reaches here.
    #   SPEC scale (the default): NO spec-side ghost state. A history predicate is legal only if
    #   EVERY rule defining it carries a literal `refmodel` (inert in the step; the bounded legs'
    #   independent oracle -- the two-readings split). Anything else is refused with the linkage
    #   message: define the symbol from the design's flops/memories as a derived view instead.
    #   Gating is per-rule and LITERAL -- write `refmodel` in each rule of the gated component;
    #   transitive gating is deliberately not inferred. Contracts are NEVER carried into the
    #   step: assume-guarantee is the only composition (the standalone proofs are the obligation).
    ghosts: dict = {}
    ghost_src: dict = {}
    ghost_text = ""
    ghost_missing: list = []
    gated_preds: set = set()
    goal_ghost_states: list = []                    # (goal, T, frozenset) seen in the base's goal witnesses
    if induct is not None:
        monitor_files = [spec] + ([cur_inv_p] if cur_inv_p else []) + ([prev_inv_p] if prev_inv_p else [])
        sources = [(f.name, f.read_text(), ghost_file_for(f)) for f in monitor_files]
        if comp.inv.strip() and unit_scale:
            sources.append(("contracts", comp.inv, None))
        inits: dict = {}
        for name, text, gfile in sources:
            # RESERVED vocabulary: the runner projects the ghost state as `ghost_state/2`.
            clash = reserved_collisions(text)
            if clash:
                res.fail(f"{name} defines {', '.join(clash)}, which the induction runner reserves for its own "
                         f"ghost-state projection -- rename the predicate (any other name is fine)")
                return res
            if unit_scale:
                g = ghost_predicates(text)
                for pn, ar in g.items():
                    ghosts[pn] = ar
                    ghost_src.setdefault(pn, name)
                if gfile is not None and gfile.exists():
                    gt = gfile.read_text()
                    ghost_text += f"% ---- {gfile.name} ----\n{gt.rstrip()}\n"
                    inits.update(init_heads(gt))
            else:
                gating = ghost_gating(text)
                ungated = sorted(pn for pn, (_ar, ok) in gating.items() if not ok)
                gated_preds |= {pn for pn, (_ar, ok) in gating.items() if ok}
                if ungated:
                    res.fail(f"induct: {name} defines spec-side ghost STATE outside refmodel: "
                             f"{', '.join(ungated)}. v2 has no spec-side ghost machinery -- LINK each "
                             f"symbol to the design's flops/memories (a derived view, defined at every "
                             f"instant), or gate every rule of an independent reference model with a "
                             f"literal `refmodel` (bounded legs only). METHODOLOGY tenets 2 and 4.")
                    return res
        if unit_scale and comp.ghost.strip():
            ghost_text += comp.ghost
            inits.update(init_heads(comp.ghost))
        for pn, ar in sorted(ghosts.items()):
            if inits.get(pn) != ar:
                src = ghost_src[pn]
                where = "the module's <m>.contract.ghost.lp" if src == "contracts" else ghost_file_for(pathlib.Path(src)).name
                ghost_missing.append(f"{pn}/{ar} (defined in {src}) has no init -- write it in {where}")
        if ghosts:
            proj += _ghost_projection(ghosts)
        if gated_preds:
            bounded_only = set()
            for _n, text, _g in sources:
                bounded_only |= props_reading(text, gated_preds)
            if bounded_only:
                res.say("  induct: BOUNDED-ONLY properties (they read the refmodel-gated reference "
                        "model, absent in the step): " + ", ".join(sorted(bounded_only))
                        + " -- checked by the bounded legs, excluded from the for-all-time claim")
                res.bounded_only = sorted(bounded_only)
    # the level's own invariants + what its children's CONTRACTS contribute (abstract child:
    # guarantee assumed / requirement owed; concrete child: both owed)
    cur_inv_text = (cur_inv_p.read_text() if cur_inv_p else "") + "\n" + comp.inv + FAILTYPE_BRIDGE
    prev_inv_text = ((prev_inv_p.read_text() if prev_inv_p else "") + "\n" + (pcomp.inv if pcomp else "")) if prev else ""
    # v2: the step NEVER carries concrete children's contracts (assume-guarantee is the only
    # composition). Why: a contract ghost that captures DATA operands makes the step's machinery
    # enumerate token candidates (rv_ooo_b: gh_outside at 3.2M ground instances, 900 s without
    # leaving grounding) -- the wall that opened v2. Each child is a separate obligation, proven
    # standalone; the bounded legs still check every contract unchanged.
    step_cur_inv_text = cur_inv_text if unit_scale else (cur_inv_p.read_text() if cur_inv_p else "")
    step_prev_inv_text = ((prev_inv_text if unit_scale else
                           (prev_inv_p.read_text() if prev_inv_p else "")) if prev else "")
    if not unit_scale and induct is not None and comp.inv.strip():
        kids = sorted({m for _, m, ab in comp.tree if not ab})
        res.say("  induct: unit contracts excluded from the step (v2 assume-guarantee): each concrete "
                "child is a SEPARATE obligation -- prove `contract <m>.lp --induct` for: " + ", ".join(kids)
                + "; caller obligations (require) stay bounded-only in composition")
    if comp.inv.strip():
        res.say(f"  contracts: assumed {_tags(comp.inv, 'assume') or '[]'}, owed {_tags(comp.inv, 'viol') or '[]'}"
                + (f", models {_tags(comp.inv, 'model')}" if _tags(comp.inv, 'model') else "")
                + (f", model obligations {_tags(comp.inv, 'cmodel')}" if _tags(comp.inv, 'cmodel') else ""))
    cur_models = _tags(cur_inv_text, "model")
    if cur_models:
        res.say(f"  models (abstract data outputs defined where the spec determines them): {cur_models}")
    prev_models = _tags(prev_inv_text, "model") if prev else []
    dropped_models = [m for m in prev_models if m not in cur_models]
    obl_tags += [f"model({m})" for m in dropped_models] + [f"model({m})" for m in _tags(comp.inv, "cmodel")]
    obl_tags = list(dict.fromkeys(obl_tags))            # a model may reach here twice (p_model AND a concrete child's cmodel)
    if dropped_models:
        res.say(f"  models built by this level (now obligations): {dropped_models}")
    assume = cur_inv_text + "\n:- assume(_, _).\n"           # the level's assumptions hold throughout
    # the previous level's invariants, renamed (assume -> p_assume, viol -> p_viol, model -> p_model), are
    # composed into EVERY solve from here on: p_model is what turns a built data output into an obligation,
    # and it must be present before the obligation check runs (an earlier version composed it only in the
    # "refines prev" section, after the obligation check -- which then read UNSAT as "discharged")
    ptext = _rename(prev_inv_text, {"assume": "p_assume", "viol": "p_viol", "model": "p_model"}) if prev and prev_inv_text.strip() else ""
    assume += ptext

    # ---- GROUND ONCE, ASK MANY (2026-08-22, the user's call -- the induct block's _Session
    # extended to the bounded legs). Measured on ve144_conwaylife: solving is ~0 and the refine's
    # wall time was the bounded queries each re-grounding a ~10^6-instance program. Every query
    # below becomes a CHOICE-GUARDED constraint in ONE grounding; each solve pins the guards by
    # assumption. Two horizons -> up to two sessions (--induct shortens the checks' k while the
    # goals keep the stimulus horizon). Any failure -> None -> the legs fall back to the per-query
    # _solve they always used, so the fallback path IS the old behaviour. ----
    goals = _tags(spec.read_text(), "goal")
    p_ass = _tags(prev_inv_text, "assume") if (prev and prev_inv_text.strip()) else []
    p_vio = _tags(prev_inv_text, "viol") if (prev and prev_inv_text.strip()) else []
    c_ass_g = _tags(cur_inv_text, "assume")
    rp_discharged = [t for t in p_ass if t not in c_ass_g]
    rp_arg = lambda t: "_" if t.startswith("<") else t          # `<every tag>` matches with `_`
    obl_guarded = list(obl_tags) if (obl_tags and symbolic) else []
    GUARDS = (["q__spec", "q__viol", "q__refp"]
              + [f"q__goal({g})" for g in goals]
              + [f"q__obl({t})" for t in obl_guarded])
    gq = ["{ q__spec }.", "{ q__viol }.", "{ q__refp }.",
          "some_bad :- bad(_, _).", ":- q__spec, not some_bad.",
          "some_v :- viol(_, _).", ":- q__viol, not some_v."]
    gq += [f"{{ q__goal({g}) }}." for g in goals]
    gq += [f":- q__goal({g}), not goal({g}, _)." for g in goals]
    gq += [f"{{ q__obl({t}) }}." for t in obl_guarded]
    gq += [f"some_o({t}) :- obl_owed({t}, _)." for t in obl_guarded]
    gq += [f":- q__obl({t}), not some_o({t})." for t in obl_guarded]
    gq += [f"some_p :- p_assume({rp_arg(t)}, _)." for t in rp_discharged]
    gq += [f"some_p :- p_viol({rp_arg(t)}, _)." for t in p_vio]
    gq += [":- q__refp, not some_p.", "#defined some_p/0.", "#defined obl_owed/2."]
    sessA = sessB = None
    try:
        gtext = assume + proj + "\n".join(gq) + "\n"
        sessA = _Session(base, gtext, consts)
        sessB = sessA if goal_consts == consts else _Session(base, gtext, goal_consts)
    except Exception:                                     # no clingo module / grounding error
        sessA = sessB = None                              # -> the per-query _solve path below

    # 3. spec
    st, atoms = (sessA.solve_guards({"q__spec"}, GUARDS) if sessA
                 else _solve(base, assume + proj + "some_bad :- bad(_, _).\n:- not some_bad.\n", consts))
    if st == "UNSATISFIABLE":
        res.say("  spec: OK -- no bad(_, _) reachable under the stimulus" +
                (" (with the level's assumptions)" if cur_inv_p and _tags(cur_inv_text, "assume") else ""))
    elif st == "SATISFIABLE":
        res.fail("spec: a bad(_, _) is REACHABLE")
        res.counterexamples.append(("spec", _table(d, atoms, kk, clocks)))
    else:
        res.fail(f"spec check did not run: {st}")

    # 3b. obligations OWED to Lean (the symbolic reading: two terms that are not the same symbol)
    if obl_tags and symbolic:
        for t in obl_tags:
            st, atoms = (sessA.solve_guards({f"q__obl({t})"}, GUARDS) if sessA
                         else _solve(base, assume + proj + f"some_o :- obl_owed({t}, _).\n:- not some_o.\n", consts))
            if st == "SATISFIABLE":
                res.owed.append(t)
                res.say(f"  obligation {t}: OWED to Lean -- the design's term and the spec's differ as symbols "
                        f"(not a violation; `--export lean` renders it)")
            elif st == "UNSATISFIABLE":
                res.say(f"  obligation {t}: discharged by identity (the same term on both sides)")
            else:
                res.fail(f"obligation {t}: check did not run: {st}")
    elif obl_tags:
        res.say(f"  obligations {obl_tags}: checked as bad (concrete reading)")

    # 4. refines prev
    if prev and prev_inv_text.strip():
        c_ass = c_ass_g
        carried = [t for t in p_ass if t in c_ass]
        discharged = rp_discharged
        obligations = discharged + p_vio
        if obligations:
            need = " ".join(f"some_p :- p_assume({rp_arg(t)}, _)." for t in discharged) + " " + \
                   " ".join(f"some_p :- p_viol({rp_arg(t)}, _)." for t in p_vio) + "\n:- not some_p.\n"
            st, atoms = (sessA.solve_guards({"q__refp"}, GUARDS) if sessA
                         else _solve(base, assume + proj + need, consts))
            if st == "UNSATISFIABLE":
                if "<every tag>" in discharged:
                    # level 0's blanket `assume(Tag, T) :- bad(Tag, T)`: what is proven here is
                    # "the spec holds under THIS level's own assumptions" -- say so, do not
                    # over-promise (three authors read `discharged ['<every tag>']` as "all done")
                    res.say(f"  refines {prev.name}: OK -- {prev.name}'s blanket assumption of the spec is "
                            f"discharged MODULO this level's own assumptions "
                            f"{c_ass if c_ass else '(none -- the spec holds outright)'}"
                            + (f"; re-checked guarantees {p_vio}" if p_vio else ""))
                else:
                    res.say(f"  refines {prev.name}: OK -- discharged {discharged or '{}'}"
                            + (f", re-checked guarantees {p_vio}" if p_vio else "")
                            + (f"; carried (still assumed) {carried}" if carried else ""))
            elif st == "SATISFIABLE":
                res.fail(f"does NOT refine {prev.name}: a dropped assumption / previous guarantee is violated")
                res.counterexamples.append(("refines-prev", _table(d, atoms, kk, clocks)))
            else:
                res.fail(f"refinement check did not run: {st}")
        else:
            res.say(f"  refines {prev.name}: nothing to discharge" + (f"; carried {carried}" if carried else ""))
    elif prev:
        res.say(f"  refines {prev.name}: the previous level states no invariants")

    # 5. own guarantees
    c_vio = _tags(cur_inv_text, "viol")
    if c_vio:
        st, atoms = (sessA.solve_guards({"q__viol"}, GUARDS) if sessA
                     else _solve(base, assume + proj + "some_v :- viol(_, _).\n:- not some_v.\n", consts))
        if st == "UNSATISFIABLE":
            res.say(f"  guarantees: OK -- {c_vio}")
        elif st == "SATISFIABLE":
            res.fail("a claimed guarantee (viol) is violated")
            res.counterexamples.append(("guarantee", _table(d, atoms, kk, clocks)))
        else:
            res.fail(f"guarantee check did not run: {st}")

    # 6. goals (sessB: the goals keep the stimulus horizon when --induct shortened the checks' k)
    for g in goals:
        st, atoms = (sessB.solve_guards({f"q__goal({g})"}, GUARDS) if sessB
                     else _solve(base, assume + proj + f":- not goal({g}, _).\n", goal_consts))
        if st == "SATISFIABLE":
            res.say(f"  goal {g}: reachable")
            if ghosts:
                for t in range(kg + 1):
                    st_t = ghost_state_at(atoms, t)
                    if symbolic:      # token-valued ghost atoms cannot be compared across instants
                        st_t = frozenset(x for x in st_t if re.match(r"^\w+(\([^()]*\))?$", x))
                    goal_ghost_states.append((g, t, st_t))
        elif st == "UNSATISFIABLE":
            res.fail(f"goal {g}: NOT reachable any more (the level or its assumptions exclude it)")
        else:
            res.fail(f"goal {g}: check did not run: {st}")

    # 6b. CONTRACT COVERAGE -- which outputs does the contract never pin?
    #
    # An output the contract leaves free and an output the contract deliberately leaves DON'T-CARE
    # produce identical artifacts: no monitor, no violation, a green run. Nothing distinguished them
    # until this check, and the difference is the whole of whether a specification is complete.
    #
    # It found the ttl74181 example's `cout`: constrained in arithmetic mode, silent in logic mode,
    # and the design then drove the arithmetic carry through unconditionally -- SATISFYING ITS
    # CONTRACT while misrepresenting a part whose datasheet says the carries are inhibited there.
    #
    # The question is asked where every output is ABSTRACT (level 0), because that is the spec on its
    # own: enumerate (inputs, output) under the contract, and an input assignment that admits TWO
    # values of the output is an assignment the contract does not pin.
    ab_outs = [q.name for q in d.outputs() if q.name in d.abstracts]
    if ab_outs:
        ins = [q.name for q in d.inputs() if q.name not in clocks]
        # BOUND THE WORK. The check enumerates (inputs, output) projections, so its cost is the size of
        # the input space -- fine for a 4-bit ALU, hopeless for a 32-bit datapath. Left unbounded it
        # turned a 23-minute suite into an 85-minute one, which is a regression the check's value does
        # not justify. Above the bound it says so rather than grinding or, worse, quietly sampling a
        # fraction and reporting "OK".
        bits, wide = 0, [n for n in ins if n in d.data]
        for n in ins:
            w = d.width_of(n)
            bits += w if isinstance(w, int) else 1
        # SEQUENTIAL CONTRACTS: the key is (inputs, GHOST STATE), and the ghost at T=0 comes from
        # the spec's own `.ghost.lp` INIT -- the same file the induction proves CLOSED (contains the
        # reset state, closed under the step), so enumerating init states IS enumerating every
        # reachable ghost state. This is what unblocked the check: the first attempt ran at k=0
        # without the init, and a sequential ghost at instant 0 can only come from the init (every
        # ghost rule defines T+1 from reset), so `need_ghost` made every query UNSAT and the check
        # reported NOT CHECKED forever. A sequential spec with no init beside it stays skipped, by
        # name. The combinational leg is proven (it found `ttl74181`'s `cout`, a real defect the
        # datasheet settled).
        # CITED FREEDOMS. `dontcare(Output, "the words from the specification")` in the spec declares
        # that an unpinned output is DELIBERATE and says which prose grants it. Without this every
        # unpinned output warned, including the correct ones -- fancytimer's `count` outside counting
        # and traffic_light's `clock` with no light on are both granted in as many words by their
        # prompts -- and a check that cries wolf on correct entries teaches people to skim past it,
        # which is how the one real gap gets skimmed past too. `spec_trace.py` is what stops a
        # citation being invented: it requires the quoted words to occur in SPECIFICATION.md. It
        # cannot judge whether those words MEAN what the citation claims; that residual is stated in
        # METHODOLOGY par 4.3 rather than papered over.
        cited = dict(re.findall(r'^\s*dontcare\(\s*([a-z_][a-z_0-9]*)\s*,\s*"([^"]*)"\s*\)\s*\.',
                                spec.read_text(), re.M))
        ginit = ghost_file_for(spec)
        # NOT `ghosts`: that dict is built only on the --induct path, and an empty dict here would
        # silently run the check with inputs-only keys -- the every-output-unpinned noise mode the
        # old gate existed to prevent. The coverage block detects the spec's ghosts itself.
        cov_ghosts = ghosts or ghost_predicates(spec.read_text())
        skip = ("%d data net(s)" % len(wide) if wide
                else f"a sequential contract with no ghost init beside the spec ({ginit.name})"
                if (cov_ghosts and not ginit.exists())
                else f"{bits}-bit input space" if bits > 20 else "")
        if skip:
            res.say(f"  contract coverage: not checked -- {skip}; it enumerates (inputs, output) pairs,"
                    f" so it is for narrow control interfaces")
            ab_outs = []
        loose: list = []
        checked: list = []
        capped: list = []       # hit the enumeration cap -- genuinely NOT checked, unlike a cited freedom
        for o in sorted(ab_outs):
            # NOT `proj`: that name is already bound in this scope and is used by the spec and
            # totality checks below. Rebinding it made totality solve against the coverage
            # projection instead of its own, and `test_aspfirst_amba_bridge_lineage` failed with
            # "some net has NO value at some instant" -- a real check, broken by a name collision.
            # THE KEY IS (inputs, GHOST STATE). A sequential contract pins its outputs from the inputs
            # AND the state it is in; keying on inputs alone made every sequential design report as
            # unpinned, because two models with the same inputs and DIFFERENT phases legitimately
            # differ. With the ghost in the key the question becomes the right one: in this state, on
            # this input, does the contract determine the output?
            # the ghost's own projection, built exactly as `plan_step` builds it -- `_projection` is a
            # DISPLAY projection and does not define `ghost_state/2`, so keying on it produced nothing
            # and the ghost silently stayed out of the key.
            gp = ""
            for gname, gar in sorted(cov_ghosts.items()):
                xs = ", ".join(f"X{j}" for j in range(gar - 1))
                gp += (f"{GHOST_PROJ}({gname}({xs}), T) :- {gname}({xs}, T).\n" if xs
                       else f"{GHOST_PROJ}({gname}, T) :- {gname}(T).\n")
            cov_proj = (gp + f"cov_in(ghost, G, T) :- {GHOST_PROJ}(G, T).\n") if cov_ghosts else ""
            cov_proj += "".join(f"cov_in({n}, V, T) :- val({n}, V, T).\n" for n in ins) \
                     + f"cov_out(V, T) :- val({o}, V, T).\n#show cov_in/3.\n#show cov_out/2.\n"
            # ONE instant (k = 0). The key is the input assignment, and two models sharing a key with
            # different output values is what "not pinned" means -- over a whole history the keys are
            # nearly all distinct, so a repeat never appears and the check would silently find nothing.
            # For a combinational contract this is exact; for a sequential one it catches the case that
            # matters here (an output no monitor mentions in some mode) and not history-dependent gaps.
            # REQUIRE A DEFINED GHOST. A sequential contract genuinely pins nothing before its ghost
            # exists -- that is the "nothing before the first reset" freedom every entry records -- so
            # without this every output of every sequential design reports as unpinned and the check
            # says only what the resolution record already said. The question worth asking is: GIVEN
            # the machine is in some defined state, is the output pinned?
            need_ghost = f":- not {GHOST_PROJ}(_, 0).\n" if cov_ghosts else ""
            COV_LIMIT = 4000
            st, ws = _solve_all([cur_file, lib / "aspfirst.lp", lib / "aspfirst_abstract.lp", stim, spec]
                               + ([ginit] if cov_ghosts and ginit.exists() else [])
                               + ([lib / "aspfirst_symbolic.lp"] if symbolic else []),
                               assume + ":- bad(_, _).\n:- viol(_, _).\n" + need_ghost + cov_proj,
                               dict(consts, k=0), project="cov_in/3, cov_out/2", limit=COV_LIMIT)
            if st != "SATISFIABLE":
                # NOT silent: a coverage query that did not run is not a coverage result. (The first
                # version returned quietly here on a malformed `#project`, and the check reported
                # "OK -- every output is pinned" while never having asked anything.)
                res.warn(f"  contract coverage: `{o}` NOT CHECKED -- the query returned {st[:60]}")
                continue
            if len(ws) >= COV_LIMIT:
                # TRUNCATED IS NOT CHECKED. The ghost widens the key space beyond the input-bit
                # budget's reach, and an enumeration cut off at the cap has sampled a fraction --
                # reporting over it would be the quiet-sampling failure the bound exists to prevent.
                res.warn(f"  contract coverage: `{o}` NOT CHECKED -- {len(ws)} projected models hit"
                         f" the enumeration cap; the (inputs x ghost) key space is too large")
                capped.append(o)
                continue
            checked.append(o)
            seen: dict = {}
            for atoms in ws:
                key = tuple(sorted(a for a in atoms if a.startswith("cov_in(")))
                vals = frozenset(a for a in atoms if a.startswith("cov_out("))
                seen.setdefault(key, set()).update(vals)
            wit = next((k for k, v in seen.items() if len(v) > 1), None)
            if wit is not None:
                where = ", ".join(a[len("cov_in("):-1].rsplit(",", 1)[0].replace(",", "=") for a in wit) or "any input"
                loose.append((o, where))
        for o, where in [x for x in loose if x[0] in cited]:
            res.say(f"  contract coverage: `{o}` is a CITED don't-care when {where}"
                    f' -- "{cited[o]}"')
        # A cited output was CHECKED but is not PINNED, so it must leave the pinned list too --
        # otherwise the OK line names it as pinned one line after reporting it as a freedom. The
        # same "count only what you actually established" slip as the enumeration-cap case above.
        loose = [x for x in loose if x[0] not in cited]
        checked = [o for o in checked if o not in cited]
        if loose:
            for o, where in loose:
                res.warn(f"  contract coverage: `{o}` is NOT pinned by the contract when {where}"
                         f" -- a DON'T-CARE needs a citation: add"
                         f' `dontcare({o}, "the words from the specification").` to the spec, or the'
                         f" contract is incomplete there")
        elif checked:
            # count only what was CHECKED -- the first version said "OK (4 outputs)" directly under
            # four NOT CHECKED cap lines, claiming outputs it had skipped.
            res.say(f"  contract coverage: OK -- {', '.join('`%s`' % o for o in checked)} pinned by"
                    f" the contract"
                    + (" in every (input, ghost-state) the stimulus and the init admit" if cov_ghosts
                       else " everywhere the stimulus reaches")
                    + (f"; {len(capped)} output(s) NOT checked (above)" if capped else ""))

    # 7. totality of the concrete part
    st, atoms = _solve([cur_file, lib / "aspfirst.lp", lib / "aspfirst_abstract.lp", lib / "aspfirst_init0.lp",
                        lib / "aspfirst_cover.lp", stim, spec] + ([lib / "aspfirst_symbolic.lp"] if symbolic else []),
                       assume + proj, consts)
    if st == "UNSATISFIABLE":
        res.say("  totality: OK -- every net has a value at every instant")
    elif st == "SATISFIABLE":
        res.fail("totality: some net has NO value at some instant (a guarded net missing an arm?)")
        res.counterexamples.append(("totality", _table(d, atoms, kk, clocks)))
    else:
        res.fail(f"totality check did not run: {st}")
    if witness:
        st, atoms = (sessA.solve_guards(set(), GUARDS) if sessA
                     else _solve(base, assume + proj, consts))
        if st == "SATISFIABLE":
            res.counterexamples.append(("witness (one trace of this level under the stimulus)",
                                        _table(d, atoms, kk, clocks)))
    if induct is not None:
        _induct(res, d, cur_file, spec, K=induct, clocks=clocks, ghosts=ghosts, ghost_src=ghost_src,
                bounded_only=set(res.bounded_only),
                ghost_text=ghost_text, ghost_missing=ghost_missing, goal_ghost_states=goal_ghost_states,
                cur_inv_text=step_cur_inv_text, prev_inv_text=step_prev_inv_text, prev=prev, free_reset=free_reset,
                init_zero=init_zero, symfacts=comp.symfacts if symbolic else "")
    if res.ok and not d.abstracts:
        res.say("  ==> fully concrete and every check green: `python -m sv2asp.aspfirst2 print` it")
    return res


# ---------------------------------------------------------------------------------------------
# k-induction (see induct.py for the semantics)
# ---------------------------------------------------------------------------------------------

def _ghost_projection(ghosts: dict) -> str:
    L = []
    for name, ar in sorted(ghosts.items()):
        xs = ", ".join(f"X{j}" for j in range(ar - 1))
        term = f"{name}({xs})" if xs else name
        args = f"{xs}, T" if xs else "T"
        L.append(f"{GHOST_PROJ}({term}, T) :- {name}({args}).")
    return "\n".join(L) + f"\n#show {GHOST_PROJ}/2.\n#defined {GHOST_PROJ}/2.\n"


def _scenarios(res: RefineResult, d, cur_file, spec, cur_inv_text: str, clocks: set,
               dat: set, symfacts: str, free_reset: bool,
               skip_state: frozenset = frozenset(), extra_resets: frozenset = frozenset()
) -> None:
    """Tenet 9: scenario(Name, State, Input, Expectation) -- a constrained abstract start plus
    one cycle plus a DIRECTED check of the natural operation. Two solves per scenario over the
    step's own 2-instant window (state free, inputs free, compliance assumed at T=0):
      A) + `:- not did(E).`  SAT required  = the situation is possible AND the natural operation
         happens (witness kept);
      B) + `:- did(E).`      UNSAT required = the natural operation CANNOT be violated from any
         compliant such state (a SAT here is a counterexample, printed).
    An A-UNSAT is disambiguated by re-solving without the expectation: still UNSAT = the
    state+input combination is impossible under the assumed properties (a spec/design
    contradiction); SAT = possible, but the natural operation never happens there."""
    scens = re.findall(r"^scenario\(\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*\)\s*\.",
                       spec.read_text(), re.M)
    if not scens:
        return
    lib = LIB_DIR
    symbolic = bool(symfacts)
    files = [cur_file, lib / "aspfirst.lp", lib / "aspfirst_abstract.lp", lib / "aspfirst_t34.lp", spec] \
        + ([lib / "aspfirst_symbolic.lp"] if symbolic else [])
    plan = plan_step(d, clocks, {}, 1, free_reset=free_reset, data=dat, free_state=True,
                     skip_state=skip_state, extra_resets=extra_resets)
    hyp = "% compliance at the window start\n:- bad(_, 0).\n:- viol(_, 0).\n:- assume(_, _).\n"
    proj = _projection(d, clocks)
    for name, state, inp, expect in scens:
        common = (cur_inv_text + "\n" + plan.text + proj + symfacts + hyp
                  + f":- not holds({state}, 0).\n:- not holds({inp}, 0).\n")
        stA, atomsA = _solve(files, common + f":- not did({expect}).\n", {"k": 1})
        if stA != "SATISFIABLE":
            if stA == "UNSATISFIABLE":
                stA2, _ = _solve(files, common, {"k": 1})
                why = (f"no compliant state satisfies {state}+{inp} (a spec/design contradiction)"
                       if stA2 == "UNSATISFIABLE" else
                       f"the situation is possible but the natural operation ({expect}) never happens")
                res.fail(f"scenario {name}: {why}")
            else:
                res.fail(f"scenario {name}: did not run: {stA}")
            continue
        stB, atomsB = _solve(files, common + f":- did({expect}).\n", {"k": 1})
        if stB == "UNSATISFIABLE":
            res.say(f"  scenario {name}: OK -- {state}+{inp} is possible, and the natural operation "
                    f"({expect}) cannot be violated")
        elif stB == "SATISFIABLE":
            res.fail(f"scenario {name}: VIOLABLE -- a compliant {state} with {inp} where {expect} fails")
            res.counterexamples.append((f"scenario {name} (a state where the natural operation fails)",
                                        _table(d, atomsB, 1, clocks)))
        else:
            res.fail(f"scenario {name}: the violability solve did not run: {stB}")


def _sym(v: str) -> bool:
    """A trace value that is a TERM (a token or a composed expression), not a number/constant."""
    return "(" in v


def _delivery_obligations(res: RefineResult, d, cur_file, spec, cur_inv_text: str, clocks: set,
                          dat: set, symfacts: str, free_reset: bool,
                          pin_high: frozenset = frozenset()) -> None:
    """The OWED-TO-LEAN protocol for the no-script certificate path (built for wallace32, whose
    product promise is a TERM comparison at 32 bits). The spec states `model(Port, Want, T)`
    rules -- the delivered value's REQUIRED form, typically reaching back through the window
    (`val(a, A, T-3)`) -- and declares `obligation_span(N)`: the window length the deepest
    lookback needs. ONE solve over that window (state free, inputs free, compliance assumed at
    the start, a model instance REQUIRED at the last instant):
      identical symbols        -> discharged by identity;
      differ, either a term    -> OWED to Lean (reported, recorded, never a failure);
      differ, both concrete    -> a real VIOLATION, with the witness table.
    UNSAT with the requirement is disambiguated: no model instance derivable = the obligation
    is UNREACHABLE (vacuous -- a loud failure), vs. the window itself contradictory."""
    texts = spec.read_text() + "\n" + cur_inv_text
    if not re.search(r"^model\(", texts, re.M):
        return
    m = re.search(r"^obligation_span\(\s*(\d+)\s*\)\s*\.", texts, re.M)
    if not m:
        res.fail("obligations: model(...) rules exist but no obligation_span(N) fact -- declare "
                 "the window length the deepest lookback needs (e.g. obligation_span(4) for T-3)")
        return
    span = int(m.group(1))
    K = max(1, span - 1)
    lib = LIB_DIR
    symbolic = bool(symfacts)
    files = [cur_file, lib / "aspfirst.lp", lib / "aspfirst_abstract.lp", lib / "aspfirst_t34.lp", spec] \
        + ([lib / "aspfirst_symbolic.lp"] if symbolic else [])
    plan = plan_step(d, clocks, {}, K, free_reset=free_reset, data=dat, free_state=True,
                     pin_high=pin_high)
    if plan.pinned:
        res.say(f"  obligations: enable/isolation input(s) held active for the value path: "
                f"{', '.join(sorted(plan.pinned))} (opaque_datapath)")
    hyp = ":- bad(_, 0).\n:- viol(_, 0).\n:- assume(_, _).\n"
    ask = (f"some_model :- model(_, _, {K}).\n:- not some_model.\n#show model/3.\n")
    prog = cur_inv_text + "\n" + plan.text + _projection(d, clocks) + symfacts + hyp + ask
    st, atoms = _solve(files, prog, {"k": K})
    if st == "UNSATISFIABLE":
        st2, _ = _solve(files, cur_inv_text + "\n" + plan.text + symfacts + hyp, {"k": K})
        res.fail("obligations: " + ("no model instance is derivable at the window's end -- the "
                 "obligation is UNREACHABLE (vacuous)" if st2 == "SATISFIABLE"
                 else f"the {span}-instant window is itself contradictory"))
        return
    if st != "SATISFIABLE":
        res.fail(f"obligations: the window solve did not run: {st}")
        return
    wants, haves = {}, {}
    for a in atoms:
        mm = re.match(r"model\((\w+),(.+),(\d+)\)$", a)
        if mm and int(mm.group(3)) == K:
            wants[mm.group(1)] = mm.group(2)
        mm = re.match(r"o\((\w+),(.+),(\d+)\)$", a)
        if mm and int(mm.group(3)) == K:
            haves[mm.group(1)] = mm.group(2)
    for name, want in sorted(wants.items()):
        have = haves.get(name)
        if have is None:
            res.fail(f"obligation model({name}): the design gives {name} no value at the "
                     f"window's end -- dark")
        elif have == want:
            res.say(f"  obligation model({name}): discharged by IDENTITY (the same term on both sides)")
        elif _sym(have) or _sym(want):
            res.say(f"  obligation model({name}): OWED to Lean -- the design's term and the "
                    f"spec's differ as symbols")
            res.owed.append(f"model({name})")
        else:
            res.fail(f"obligation model({name}): VIOLATED -- the design delivers {have}, the "
                     f"spec requires {want} (both concrete)")
            res.counterexamples.append((f"obligation model({name})", _table(d, atoms, K, clocks)))


def _statements(text: str) -> list:
    """Split .lp text into raw statements: a '.' at paren depth 0, outside % comments and
    quoted strings, ends one. Returns the statements WITH their trailing dots (comment-only
    stretches ride along with the following statement)."""
    out, buf, depth, i, n = [], [], 0, 0, len(text)
    in_q = False
    while i < n:
        c = text[i]
        if in_q:
            buf.append(c)
            if c == '\\':
                if i + 1 < n:
                    buf.append(text[i + 1]); i += 2; continue
            elif c == '"':
                in_q = False
            i += 1; continue
        if c == '%':
            j = text.find("\n", i)
            j = n if j < 0 else j
            buf.append(text[i:j]); i = j; continue
        buf.append(c)
        if c == '"':
            in_q = True
        elif c == '(':
            depth += 1
        elif c == ')':
            depth -= 1
        elif c == '.' and depth == 0:
            out.append("".join(buf)); buf = []
        i += 1
    if "".join(buf).strip():
        out.append("".join(buf))
    return out


def _opaque_variant(comp, d) -> tuple:
    """The `opaque_datapath.` directive's severed design for the CONTROL solves: every internal
    data net loses its def (or its register's q pin) and becomes `abstract(N)` -- the abstract
    companion then mints ONE fresh token per instant, so an en-gated or operand-isolated
    datapath grounds single-candidate instead of multiplying hold/load forks through the
    compressor tree. Sound for the control solves' UNSAT claims: the tokens over-approximate
    every computable value. Returns (path, severed_names, error)."""
    inputs = {q.name for q in d.inputs()}
    severed = [n for n in d.data if n not in inputs and n not in d.abstracts]
    for i in d.cell_insts():
        if i.cell in ("spram", "farray") and (i.pins.get("rd") in d.data or i.pins.get("wd") in d.data):
            return None, [], (f"opaque_datapath: data memory {i.name} is not supported under the "
                              f"directive yet -- remove the directive or keep the memory concrete")
    sev = set(severed)
    kept = []
    for stmt in _statements(comp.lp_path.read_text()):
        m = re.match(r"\s*(?:%[^\n]*\n\s*)*def\s*\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*,", stmt)
        if m and m.group(1) in sev:
            continue
        m = re.match(r"\s*(?:%[^\n]*\n\s*)*pin\s*\(\s*[A-Za-z_][A-Za-z0-9_]*\s*,\s*q\s*,\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)\s*\.", stmt)
        if m and m.group(1) in sev:
            continue
        kept.append(stmt)
    body = "".join(kept) + "\n% -- opaque_datapath: severed data nets, token-valued by the abstract companion --\n" \
        + "".join(f"abstract({n}).\n" for n in severed)
    fd, path = tempfile.mkstemp(suffix=".lp", prefix="opaque_")
    pathlib.Path(path).write_text(body)
    import os
    os.close(fd)
    return pathlib.Path(path), severed, None


def _opaque_pins(d) -> set:
    """The delivery obligation's pin set under `opaque_datapath`: every INPUT net wired to a
    data register's en pin, and every input conditioning an ite over data -- held 1 so the
    grounder prunes the idle branches and the real value path grounds single-candidate."""
    inputs = {q.name for q in d.inputs()}
    pins = set()
    for i in d.cell_insts():
        if i.cell in ("ff", "lata") and i.pins.get("q") in d.data:
            en = i.pins.get("en")
            if en in inputs:
                pins.add(en)
    for n, e in d.defs.items():
        if n in d.data and isinstance(e, tuple) and len(e) >= 2 and e[0] == "ite":
            c = e[1]
            if isinstance(c, str) and c in inputs:
                pins.add(c)
    return pins


def _reset_exempt_tags(spec_text: str, resets: set) -> list:
    """Tags every one of whose monitor rules is judged only where a RESET is ASSERTED (the
    body tests the reset low: `val(R, 0, ..)` or `not val(R, 1, ..)`). In a step that PINS
    the reset released such a monitor cannot fire, so listing it as inductive would be a
    VACUOUS claim -- exactly how the missq's emptyUnderReset stayed green over a stale
    in-flight bit (the user's review, 2026-08-31). These tags are excluded from a
    reset-pinned step's asks and reported NOT EXERCISED, the same shape as the
    bounded-only exclusion above them."""
    rules: dict = {}
    for m in re.finditer(r"^(?:bad|failType)\((\w+)[^.]*?:-(.*?)\.\s*$",
                         spec_text, re.M | re.S):
        rules.setdefault(m.group(1), []).append(m.group(2))
    out = []
    for t, bodies in rules.items():
        if bodies and all(
                any(re.search(rf"not\s+val\({re.escape(r)},\s*1\s*[,)]", b)
                    or re.search(rf"val\({re.escape(r)},\s*0\s*[,)]", b)
                    for r in resets)
                for b in bodies):
            out.append(t)
    return sorted(out)


def _refine_stimless(spec, cur, cur_inv=None, induct: "int | None" = None,
                     init_zero: bool = True, free_reset: bool = False) -> RefineResult:
    """The v2 CERTIFICATE path (tenet 4/9): no stimulus exists. lint -> the linkage lint -> a
    self-built reset BASE (from reset, inputs FREE, K instants: one solve, UNSAT = no property
    can fire on any input sequence from reset within the window) -> the normal-form STEP.
    Scripted legs do not run because no script exists to run them."""
    res = RefineResult()
    spec, cur = pathlib.Path(spec), pathlib.Path(cur)
    cur_inv_p = _inv_for(cur, cur_inv)
    K = induct if induct is not None else 1
    res.say(f"refine: {cur.name}  spec {spec.name}  NO STIMULUS (v2 certificate path: base from "
            f"reset with free inputs + the step, window K={K})")
    comp, errs, warns = lint_composed(cur)
    for w in warns:
        res.say(f"  lint WARN {w}")
    if errs or comp is None:
        for e in errs:
            res.fail(f"lint {e}")
        return res
    d = comp.design
    cur_file = comp.lp_path
    if comp.tree:
        res.say("  hierarchy: " + ", ".join(f"{ip}:{m}{' (abstract)' if ab else ''}" for ip, m, ab in comp.tree))
    res.say(f"  lint: OK; abstract: {len(d.abstracts)} net(s)")
    # an all-abstract composition has no cells, so the clock is learned from the children's
    # bindings recorded by compose -- without it there is no time axis and live(T) is vacuous
    clocks = _clocks(d, "") | set(getattr(comp, "clocks", ()) or ())
    hint_resets = frozenset(getattr(comp, "resets", ()) or ())
    symbolic = bool(d.data)
    symfacts = comp.symfacts if symbolic else ""
    dat = set(d.data)
    cur_inv_text = (cur_inv_p.read_text() if cur_inv_p else "") + FAILTYPE_BRIDGE
    # the v2 linkage lint over the spec and the level's inv (same rules as the scripted path)
    gated_preds: set = set()
    for name, text in [(spec.name, spec.read_text())] + ([(cur_inv_p.name, cur_inv_text)] if cur_inv_p else []):
        clash = reserved_collisions(text)
        if clash:
            res.fail(f"{name} defines {', '.join(clash)}, reserved by the induction runner -- rename")
            return res
        gating = ghost_gating(text)
        ungated = sorted(pn for pn, (_a, ok) in gating.items() if not ok)
        gated_preds |= {pn for pn, (_a, ok) in gating.items() if ok}
        if ungated:
            res.fail(f"induct: {name} defines spec-side ghost STATE outside refmodel: "
                     f"{', '.join(ungated)}. LINK each symbol to the design's flops/memories, or gate "
                     f"every rule with a literal `refmodel`. METHODOLOGY tenets 2 and 4.")
            return res
    bounded_only = props_reading(spec.read_text(), gated_preds) | props_reading(cur_inv_text, gated_preds)
    if bounded_only:
        res.say("  BOUNDED-ONLY properties (over the refmodel-gated vocabulary; no script exists, so "
                "they are NOT CHECKED AT ALL in this path): " + ", ".join(sorted(bounded_only)))
    # assume-guarantee in the CERTIFICATE path: an ABSTRACT child's contract is the child --
    # its guarantees are ASSUMED in every leg (base, step, scenarios) and its requires are
    # CHECKED as the queue's obligations (viol joins the property set). Concrete children's
    # contract text stays excluded here, the v2 doctrine: each is proven standalone by
    # `contract <m>.lp --induct` (and a contract ghost would re-open the rv_ooo_b grounding
    # wall). Without the assumed half, an abstract composition is windows with no glass:
    # every monitor vacuous, caught only by the scenarios -- which is how this gap was found.
    inv_abstract = getattr(comp, "inv_abstract", "")
    if inv_abstract.strip():
        cur_inv_text = cur_inv_text + "\n" + inv_abstract
        res.say("  contracts (abstract instances): guarantees ASSUMED "
                + str(_tags(inv_abstract, "assume") or "[]")
                + ", requires CHECKED " + str(_tags(inv_abstract, "viol") or "[]"))
    kids = sorted({m for _, m, ab in comp.tree if not ab})
    if comp.inv.strip() and kids:
        res.say("  concrete children's contracts excluded (v2 assume-guarantee): prove "
                "`contract <m>.lp --induct` for: " + ", ".join(kids))
    if induct is None:
        res.say("  nothing further to run: the stimless path is the certificate path -- pass --induct K")
        res.ok = False
        return res
    lib = LIB_DIR
    ctrl_file, opq_pins, opq_severed = cur_file, set(), frozenset()
    if getattr(d, "opaque_datapath", False):
        opq_path, severed, oerr = _opaque_variant(comp, d)
        if oerr:
            res.fail(oerr)
            return res
        ctrl_file, opq_pins = opq_path, _opaque_pins(d)
        opq_severed = frozenset(severed)
        res.say(f"  opaque datapath (directive): {len(severed)} internal data net(s) are per-instant "
                f"tokens in the control solves; the delivery obligation computes the real terms with "
                f"the enable/isolation inputs pinned active ({', '.join(sorted(opq_pins)) or 'none found'})")
    files = [ctrl_file, lib / "aspfirst.lp", lib / "aspfirst_abstract.lp", lib / "aspfirst_t34.lp", spec] \
        + ([lib / "aspfirst_symbolic.lp"] if symbolic else [])
    proj = _projection(d, clocks)
    # ---- the BASE: from reset, inputs free, one solve. Horizon K+1: reset occupies instant 0,
    # so K LIVE steps need instants 1..K+1 -- these are exactly the "K steps from reset" the
    # step's diameter argument cites; a shorter base checks nothing and makes that argument
    # unsound (caught by this path's own sabotage witness: a held register passed via the
    # diameter route until the base could actually see a live step-pair). ----
    base_h = K + 1
    plan_b = plan_step(d, clocks, {}, base_h, free_reset=True, data=dat, free_state=False,
                       extra_resets=hint_resets)
    rst = "".join(f"val({r}, 0, 0).\n" + "".join(f"val({r}, 1, {i}).\n" for i in range(1, base_h + 1))
                  for r in plan_b.resets)
    base_files = files + ([lib / "aspfirst_init0.lp"] if init_zero else [])
    ask = ("someviol :- bad(_, _).\nsomeviol :- viol(_, _).\n:- not someviol.\n#show bad/2.\n#show viol/2.\n"
           ":- assume(_, _).\n#defined assume/2.\n")   # abstract children's guarantees HOLD in the base too
    # ---- LIVE MUST BE POSSIBLE. Every monitor is guarded by `live(T)`; if no instant can be
    # live, no monitor can fire, no scenario can have a compliant state, and the base and the
    # step both come back UNSAT -- read as "INDUCTIVE". A reset-less block once certified a
    # false property this way (G26); a design that ties its reset would do the same. The
    # question is asked of the base's own program, so it costs one small solve and cannot
    # drift from what the base actually runs. ----
    st_l, _ = _solve(base_files, cur_inv_text + "\n" + plan_b.text + rst + proj + symfacts
                     + "someLive :- live(_).\n:- not someLive.\n:- assume(_, _).\n#defined assume/2.\n",
                     {"k": base_h})
    if st_l == "UNSATISFIABLE":
        res.fail("live: NO instant can be live within the base window -- every monitor is guarded "
                 "by live(T), so nothing could ever fire and the certificate would be vacuous. A "
                 "contract with no reset must derive live(T) at every instant (the compiler does); a "
                 "design must release the reset it declares.")
        return res
    if st_l != "SATISFIABLE":
        res.fail(f"live: did not run: {st_l}")
        return res
    res.say("  live: OK -- some instant is judged within the base window (the monitors can fire)")
    st, atoms = _solve(base_files, cur_inv_text + "\n" + plan_b.text + rst + proj + symfacts + ask, {"k": base_h})
    if st == "UNSATISFIABLE":
        res.say(f"  base: OK -- from reset, no property can fire on ANY input sequence within {K} live step(s)")
    elif st == "SATISFIABLE":
        fired = sorted({a for a in atoms if a.startswith(("bad(", "viol("))})
        res.fail(f"base: a property fires from reset -- {', '.join(fired[:6])}")
        res.counterexamples.append(("base (from reset, inputs free)", _table(d, atoms, base_h, clocks)))
        return res
    else:
        res.fail(f"base: did not run: {st}")
        return res
    # ---- the STEP: the normal form ----
    _induct(res, d, ctrl_file, spec, K=induct, clocks=clocks, ghosts={}, ghost_src={},
            ghost_text="", ghost_missing=[], goal_ghost_states=[],
            cur_inv_text=cur_inv_text, prev_inv_text="", prev=None, free_reset=free_reset,
            init_zero=init_zero, symfacts=symfacts, bounded_only=set(bounded_only),
            skip_state=opq_severed, extra_resets=hint_resets)
    _scenarios(res, d, ctrl_file, spec, cur_inv_text, clocks, dat, symfacts, free_reset,
               skip_state=opq_severed, extra_resets=hint_resets)
    _delivery_obligations(res, d, cur_file, spec, cur_inv_text, clocks, dat, symfacts, free_reset,
                          pin_high=frozenset(opq_pins))
    return res


def _induct(res: RefineResult, d: Design, cur_file, spec: pathlib.Path, K: int, clocks: set, ghosts: dict,
            ghost_src: dict, ghost_text: str, ghost_missing: list, goal_ghost_states: list,
            cur_inv_text: str, prev_inv_text: str, prev, free_reset: bool, init_zero: bool,
            symfacts: str = "", bounded_only: set = frozenset(),
            skip_state: frozenset = frozenset(), extra_resets: frozenset = frozenset()
) -> None:
    lib = LIB_DIR
    symbolic = bool(symfacts)
    plan = plan_step(d, clocks, ghosts, K, free_reset=free_reset, data=set(d.data) if symbolic else set(),
                     skip_state=skip_state, extra_resets=extra_resets)
    regs = ", ".join(f"{q}({w})" for q, w in plan.regs)
    if plan.tokens:
        regs += ("; " if regs else "") + "as tokens: " + ", ".join(plan.tokens)
    mems = ", ".join(f"{m}[{dp}x{w}]" for m, dp, w in plan.mems)
    res.say(f"  induct K={K}: state freed at T=0: {regs or 'no registers'}"
            + (f"; cells {mems}" if mems else "")
            + f"; inputs free every instant: {' '.join(plan.inputs) or 'none'}"
            + (f"; reset held released: {' '.join(plan.resets)}" if plan.resets and not free_reset else "")
            + (f"; reset FREE from T=1: {' '.join(plan.resets)}" if plan.resets and free_reset else "")
            + (f"; reset net(s) {' '.join(plan.reset_nets)} are DERIVED, so free like their inputs"
               if plan.reset_nets else ""))
    for e in plan.errors:
        res.fail(f"induct: {e}")
    if ghosts:
        res.say("  induct: ghost state " + ", ".join(f"{p}/{a} ({ghost_src[p]})" for p, a in sorted(ghosts.items())))
    else:
        res.say("  induct: no ghost state (no history predicate in the monitors)")
    for m in ghost_missing:
        res.fail(f"induct: ghost predicate {m}")
    if plan.errors or ghost_missing:
        res.fail("induct: not run")
        return

    # -- the property set and the environment
    assumed = _tags(cur_inv_text, "assume")
    bad_all = _tags(spec.read_text(), "bad") + ([] if symbolic else _tags(spec.read_text(), "obl"))
    blanket = "<every tag>" in assumed
    # v2: BOUNDED-ONLY properties (over the refmodel-gated oracle) are excluded from the step's
    # asks -- their rules are inert there, so "inductive" would be a vacuous claim. They stay in
    # the bounded legs, and the report already names them.
    port_resets = ({i.pins.get("rstL") for i in d.insts if i.pins.get("rstL")}
                   & {q.name for q in d.ports})
    reset_exempt = [] if free_reset or not port_resets else \
        _reset_exempt_tags(spec.read_text(), port_resets)
    bad_props = [] if blanket else [t for t in bad_all if t not in assumed and t not in bounded_only
                                    and t not in reset_exempt]
    if reset_exempt:
        res.say(f"  induct: reset-exempt monitor(s) NOT EXERCISED in this step (reset held "
                f"released, so they can never fire here): {reset_exempt} -- run the induction "
                f"with --free-reset to bind them")
    viol_props = [t for t in _tags(cur_inv_text, "viol") if t not in bounded_only]
    p_props: list = []
    ptext = ""
    if prev and prev_inv_text.strip():
        ptext = _rename(prev_inv_text, {"assume": "p_assume", "viol": "p_viol", "model": "p_model"})
        p_ass = _tags(prev_inv_text, "assume")
        p_props = [("p_assume", t) for t in p_ass if t not in assumed and not t.startswith("<")] \
                + [("p_viol", t) for t in _tags(prev_inv_text, "viol")]
    props = [("bad", t) for t in bad_props] + [("viol", t) for t in viol_props] + p_props
    res.say("  induct: property set -- " + "; ".join(x for x in [
        f"bad {bad_props}" if bad_props else ("bad [] (the level assumes the whole spec)" if blanket else "bad []"),
        f"viol {viol_props}" if viol_props else "",
        f"prev's {[f'{p}({t})' for p, t in p_props]}" if p_props else ""] if x)
        + f"; environment (assumed at every instant): {assumed or '[]'}")
    if not props:
        res.say("  induct: nothing to prove inductively at this level -- it assumes the spec and claims nothing")
        return

    arg = lambda t: t                                              # tags are already patterns (`starved(_)`)
    hyp = ("% the induction hypothesis: the whole property set holds at T = 0..K-1; the environment throughout\n"
           ":- assume(_, _).\n:- bad(_, T), T < k.\n:- viol(_, T), T < k.\n:- p_assume(_, T), T < k.\n:- p_viol(_, T), T < k.\n")
    step_files = [cur_file, lib / "aspfirst.lp", lib / "aspfirst_abstract.lp", lib / "aspfirst_t34.lp", spec] \
        + ([lib / "aspfirst_symbolic.lp"] if symbolic else [])
    common = cur_inv_text + "\n" + ptext + "\n" + ghost_text + "\n" + plan.text + _projection(d, clocks) + symfacts
    kc = {"k": K}

    # -- THE GHOST INIT IS AN INDUCTIVE INVARIANT OF THE GHOST, and that is proven, not sampled:
    #      (a) the ghost state right after RESET is in the init's domain, and
    #      (b) from ANY state in the domain, under the property set, the ghost state one step later is
    #          in the domain again.
    #    With the base case this puts every ghost state of every reachable window inside the domain the
    #    step quantifies over -- which is what "the step covers any correct state" has to mean.
    #    Each is ONE query: `init_membership` reads the init's choice rules as a MEMBERSHIP CONDITION
    #    (`gh_outside(Why)` when the instant-1 state is outside), so no state is ever enumerated. The
    #    previous version enumerated the successor states and tested each: fine at 8 or 78 states, but it
    #    scales with the GHOST'S STATE SPACE -- a specification with a 1000-cycle position counter has
    #    160,000 -- which is exactly the enumeration induction exists to avoid. Where the init uses a
    #    shape the transformation does not cover, we say so and fall back to the goal-witness SAMPLE.
    if ghosts:
        dat = set(d.data) if symbolic else set()
        memb, unsupported_init = init_membership(ghost_text, ghosts, symbolic=symbolic)
        plan0 = plan_step(d, clocks, ghosts, 0, free_reset=free_reset, data=dat)
        init_prog = cur_inv_text + "\n" + ghost_text + "\n" + plan0.text + symfacts
        if unsupported_init:
            res.say(f"  induct: the ghost init uses {len(unsupported_init)} statement(s) this runner cannot read as a "
                    f"membership condition ({unsupported_init[0][:70]}...) -- closure is NOT established; falling "
                    f"back to the goal-witness sample")
            seen: dict = {}
            for g, t, state in goal_ghost_states:
                seen.setdefault(state, (g, t))
            bad_states = []
            for state, (g, t) in seen.items():
                st0, _ = _solve(step_files, init_prog + pin_ghost_state(state, ghosts, exact=not symbolic), {"k": 0})
                if st0 != "SATISFIABLE":
                    bad_states.append((state, g, t, st0))
            for state, g, t, st0 in bad_states[:3]:
                res.fail(f"induct: the ghost init does NOT produce a ghost state the base reaches "
                         f"(goal {g} @T={t}: {', '.join(sorted(state)) or 'empty'}) -- "
                         + ("the init domain is too SMALL: the step would skip real windows (UNSOUND); widen it"
                            if st0 == "UNSATISFIABLE" else st0))
            if bad_states:
                res.fail("induct: not run")
                return
            res.say(f"  induct: ghost init produces every ghost state of the goal witnesses ({len(seen)} distinct)")
        else:
            ask = memb + "\n:- not gh_outside(_).\n#show gh_outside/1.\n"
            # from RESET: the registers are NOT freed (the reset defines them -- a freed DATA register would
            # be a fresh token beside the reset's 0, two values); reset asserted at 0, released at 1
            plan_r = plan_step(d, clocks, ghosts, 1, free_reset=True, data=dat, free_state=False)
            rst_facts = "".join(f"val({r}, 0, 0). val({r}, 1, 1).\n" for r in plan_r.resets)
            plan1 = plan_step(d, clocks, ghosts, 1, free_reset=free_reset, data=dat)
            hyp0 = ("% the ghost state at T=0 is in the domain (the init generates it) and the property set holds\n"
                    ":- assume(_, _).\n:- bad(_, 0).\n:- viol(_, 0).\n:- p_assume(_, 0).\n:- p_viol(_, 0).\n")
            queries = [("contains the reset state",
                        cur_inv_text + "\n" + plan_r.text + rst_facts + _projection(d, clocks) + symfacts + ask),
                       ("is CLOSED under the step",
                        cur_inv_text + "\n" + ptext + "\n" + ghost_text + "\n" + plan1.text
                        + _projection(d, clocks) + symfacts + hyp0 + ask)]
            # CASES, read off the ghost's own guards (the border of a counter, the values of a phase): the
            # closure and the step are proven per case -- smaller queries, and a failure names its case
            # instead of a blur over the whole state space. The cases partition the ghost state at T=0.
            cases = ghost_cases(spec.read_text(), ghosts) or [("all", "")]
            for what, prog in queries:
                per_case = cases if what.startswith("is CLOSED") else [("all", "")]
                failed = False
                for label, sel in per_case:
                    st, atoms = _solve(step_files, prog + "\n" + sel + "\n", {"k": 1})
                    if st == "UNSATISFIABLE":
                        continue
                    if st == "SATISFIABLE":
                        why = sorted({a for a in atoms if a.startswith("gh_outside(")})
                        # NAME THE QUERY THAT FAILED. This message used to hardcode "is NOT closed under
                        # the step", but it runs for BOTH queries, so a failure of "contains the reset
                        # state" was reported as a closure failure -- a diagnostic pointing at the wrong
                        # rules, which is worse than no diagnostic. Cost an hour on examples/spec2rtl/am2901
                        # before the two queries were separated by hand and measured apart.
                        phrase = {"is CLOSED under the step": "is NOT closed under the step",
                                  "contains the reset state": "does NOT contain the reset state"}[what]
                        res.fail(f"induct: the ghost init {phrase} (case {label}): the ghost reaches a "
                                 f"state the init cannot produce -- {', '.join(why) or 'see the table'}. The init "
                                 f"domain is too SMALL: the step would skip real windows (UNSOUND); widen it")
                        res.counterexamples.append((f"induct closure, case {label}", _table(d, atoms, 1, clocks)
                                                    + "\n" + "\n".join(ghost_lines(atoms, 1))))
                    else:
                        res.fail(f"induct: the ghost-init closure query did not run (case {label}): {st}")
                    failed = True
                    break
                if failed:
                    res.fail("induct: not run")
                    return
                res.say(f"  induct: ghost init {what} -- proven"
                        + (f" in {len(per_case)} case(s): {'; '.join(l for l, _ in per_case)}" if len(per_case) > 1
                           else " in one query (no state enumerated)"))

    # ONE grounding for the whole K-horizon family (see _Session): the vacuity check, the
    # unique-states check and the step all ask about the SAME program, and the runner used to write
    # it out from scratch for each. A ghost-case SPLIT keeps the old query-per-solve path -- each
    # case's selector is a constraint that would have to be WITHDRAWN again, which incremental
    # grounding cannot do, and a split is the rare shape, so it pays the old cost rather than
    # complicating the common one.
    names = [f"{t}" if p == "bad" else (f"viol({t})" if p == "viol" else f"{p}({t})") for p, t in props]
    cases = (ghost_cases(spec.read_text(), ghosts) if ghosts else []) or [("all", "")]
    # The session grounds ONE program containing every query's rules, each switched by an assumable
    # atom. It must be one part: a later `ground()` does NOT see an earlier part's FACTS (clingo
    # simplifies them away), which silently made the unique-states constraint and the step's own
    # requirement inert -- the step then found no violation and the runner called it INDUCTIVE. A
    # FALSE PROOF, caught by `test_aspfirst_induct_soundness_and_teeth`, which is why that test exists.
    switches = ("{ ind__uniq }.\n{ ind__step }.\n"
                + "".join(f"ind__prop({j}).\n" for j in range(len(props)))
                + "{ ind__want(J) : ind__prop(J) }.\n"
                + "".join(f"ind__hit({j}) :- {p}({arg(t)}, k).\n" for j, (p, t) in enumerate(props))
                + "ind__any :- ind__hit(J), ind__want(J).\n"
                + ":- not ind__any, ind__step.\n#defined ind__hit/1.\n")
    sess = (_Session(step_files, common + hyp + plan.unique + switches, kc, nprops=len(props))
            if len(cases) == 1 else None)
    all_j = list(range(len(props)))

    def require(ps):
        return "".join(f"some_k :- {p}({arg(t)}, k).\n" for p, t in ps) + ":- not some_k.\n"

    # -- vacuity: some window satisfies the hypothesis at all (WITHOUT the unique-states constraint,
    #    which legitimately empties the step once K exceeds the reachable diameter)
    st, _ = (sess.solve(uniq=False, step=False) if sess else _solve(step_files, common + hyp, kc))
    if st == "UNSATISFIABLE":
        res.fail("induct: the hypothesis is UNSATISFIABLE -- no start state satisfies the property set for "
                 f"{K} cycle(s): contradictory assumptions, or a ghost init too small. The step would be vacuous.")
        return
    if st != "SATISFIABLE":
        res.fail(f"induct: the step did not run: {st}")
        return
    # The diameter shortcut and the unique-states constraint quantify over the REGISTER state
    # signature. An all-abstract composition has no registers -- its state lives in the abstract
    # children's exported nets -- so an empty signature makes every instant-pair "the same state"
    # and the shortcut would declare INDUCTIVE without the step ever running (a false proof,
    # found on the first abstract-composed certificate). With no signature: no shortcut, and the
    # step runs without the unique-states constraint (dropping it loses completeness, never
    # soundness).
    has_state_sig = bool(plan.regs or plan.tokens or plan.mems)
    if has_state_sig:
        st, _ = (sess.solve(uniq=True, step=False) if sess
                 else _solve(step_files, common + plan.unique + UNIQ_ON + hyp, kc))
        if st == "UNSATISFIABLE":
            res.inductive = names
            res.say(f"  induct: INDUCTIVE at K={K} -- {names}: no simple path of {K} cycles satisfies the set, "
                    f"i.e. K exceeds the reachable diameter and the base already covers every reachable state")
            return

    # -- the step: whole set first (one solve), then per tag when it fails. Under a session the tag
    #    selection is the one non-monotone choice, so it is an ASSUMPTION over `ind__want/1` rather
    #    than a re-grounded constraint.
    failing_case, atoms = None, []
    for label, sel in cases:
        st, atoms = (sess.solve(uniq=has_state_sig, step=True, want=set(all_j)) if sess else
                     _solve(step_files, common + (plan.unique + UNIQ_ON if has_state_sig else "")
                            + hyp + require(props) + "\n" + sel + "\n", kc))
        if st == "UNSATISFIABLE":
            continue
        if st != "SATISFIABLE":
            res.fail(f"induct: the step did not run (case {label}): {st}")
            return
        failing_case = label
        break
    if failing_case is None:
        res.inductive = names
        res.say(f"  induct: INDUCTIVE at K={K} -- {names}: with the base, they hold for ALL time"
                " (inputs free every instant" + ("; reset released after T=0)" if plan.resets and not free_reset else ")")
                + (f"; proven in {len(cases)} case(s): {'; '.join(l for l, _ in cases)}" if len(cases) > 1 else ""))
        return
    case_sel = dict(cases)[failing_case]
    if len(cases) > 1:
        res.say(f"  induct: the step FAILS in case {failing_case} (of {len(cases)}: {'; '.join(l for l, _ in cases)})")
    for j, ((p, t), name) in enumerate(zip(props, names)):
        st, atoms = (sess.solve(uniq=True, step=True, want={j}) if sess else
                     _solve(step_files, common + plan.unique + UNIQ_ON + hyp + require([(p, t)]) + "\n" + case_sel + "\n", kc))
        if st == "UNSATISFIABLE":
            res.inductive.append(name)
        elif st == "SATISFIABLE":
            res.not_inductive.append(name)
            table = _table(d, atoms, K, clocks)
            table += "\n" + "\n".join(ghost_lines(atoms, K)) if ghosts else ""
            table += (f"\n  ==> an INVARIANT REQUEST, not a bug report: this window starts from a state that satisfies "
                      f"every invariant for {K} cycle(s) and still reaches {name} at T={K}. Either the start state is "
                      f"reachable (a real bug: run the base at a longer k) or it is not, and this level owes the "
                      f"`viol` that excludes it -- relate the design's state at T=0 to the ghost (a gluing "
                      f"invariant), or state the progress argument as safety.")
            res.counterexamples.append((f"induct {name} (a {K}-cycle window from an arbitrary state)", table))
        else:
            res.fail(f"induct {name}: did not run: {st}")
    if res.not_inductive:
        res.fail(f"induct: NOT inductive at K={K} -- {res.not_inductive}"
                 + (f"; inductive relative to the set: {res.inductive}" if res.inductive else ""))
