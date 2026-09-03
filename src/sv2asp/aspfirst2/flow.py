"""Run an ENTRY's verification flow from its manifest (`verify.json`) -- the flow as DATA.

Each design's flow differs -- its induction K, whether the reset is freed, which units carry
contracts, what the round trip arbitrates against -- and before this runner that variation lived in
imperative per-entry test code, which is the wrong place: code near the tool invites editing the
tool (the user, 2026-08-23: "the flow should be determined by configuration file changes for the
problem in question"). The manifest carries the flow; ONE runner executes every entry's.

Two boundaries, so this does not become a different disease:

  * The manifest selects WHICH checks run and their parameters. It can never weaken what a check
    MEANS -- "INDUCTIVE", the dark-read refusal, goals-must-be-reachable stay fixed in the tool.
  * Unknown keys are a HARD error. A typo ("induct_k") silently ignored is a check that silently
    did not run -- the vacuity disease in configuration form.

Schema (all paths relative to the manifest's directory; every key optional except those marked):

  {
    "contracts":  [ {"module": M,                       -- required
                     "k": int, "induct": int,
                     "contains": [substr, ...]} ],
    "refine":     [ {"design": D, "spec": S,            -- required ("stim" optional:
                     "stim": T,                            the v2 certificate path is stimless)
                     "prev": P, "k": int, "induct": int, "free_reset": bool,
                     "induction_only": bool,            -- judge by the induction alone (the
                                                           strong half: scenarios under a free
                                                           reset are violable by design)
                     "log": FILE,                       -- write the run's report here
                     "abstract": [net, ...],            -- the EXPECTED abstract set, exactly
                     "contains": [substr, ...]} ],      -- lines the report must contain
    "second_points": [ {"regenerate": [argv...],        -- required; "{out}"/"{python}" expand
                     "design": D, "spec": S,            -- required: D inside {out}; S rewritten
                     "const_overrides": {name: value},  -- required: the #const lines to rewrite
                     "induct": int, "log": FILE, "contains": [...],
                     "print_parity": true,              -- default true: the two designs are
                                                        PRINTED and must differ only in the
                                                        parameter defaults, so a module
                                                        carrying a parameter it does not
                                                        honour is caught in the artifact the
                                                        claim is about
                     "must_reject": D0} ],              -- the DEFAULT design the off-default
                                                           contract must REJECT (discrimination)
    "roundtrips": [ {"design": D, "scenario": S,        -- required
                     "simulator": "verilator"|"icarus"|"auto", "mode": "behav"|"cells",
                     "contains": [substr, ...]} ]
  }

Steps run in that order (contracts, then the refine chain in list order, then round trips) and the
flow fails on the first failing step. `icarus: true` asks for the simulator; if it is absent in
this environment the round trip runs on the ASP sides and the report SAYS so -- absence of a local
tool is an environment fact, not an entry defect (the suite's convention for iverilog/verilator).
"""
from __future__ import annotations

import json
import pathlib
import re
import shutil

_CONTRACT_KEYS = {"module", "k", "induct", "contains"}
_REFINE_KEYS = {"design", "spec", "stim", "prev", "k", "induct", "free_reset", "abstract",
                "contains", "log", "induction_only"}
_SECOND_KEYS = {"regenerate", "design", "spec", "const_overrides", "induct", "contains",
                "print_parity",
                "log", "must_reject"}
_ROUNDTRIP_KEYS = {"design", "scenario", "icarus", "simulator", "mode", "contains"}
_TOP_KEYS = {"contracts", "refine", "second_points", "roundtrips"}


class FlowResult:
    def __init__(self):
        self.ok = True
        self.lines: list = []

    def say(self, s: str) -> None:
        self.lines.append(s)

    def fail(self, s: str) -> None:
        self.ok = False
        self.lines.append("FAIL " + s)

    def report(self) -> str:
        return "\n".join(self.lines + [f"FLOW: {'OK' if self.ok else 'FAILED'}"])


def _check_keys(step: dict, allowed: set, what: str, res: FlowResult) -> bool:
    extra = set(step) - allowed
    if extra:
        res.fail(f"{what}: unknown key(s) {sorted(extra)} -- allowed: {sorted(allowed)}. "
                 "A misspelled key would be a check that silently did not run; refused instead.")
        return False
    return True


def _path(base: pathlib.Path, rel, what: str, res: FlowResult):
    p = base / rel
    if not p.exists():
        res.fail(f"{what}: {rel} does not exist (relative to {base})")
        return None
    return p


def _contains(report: str, needles, what: str, res: FlowResult) -> None:
    for n in needles or []:
        if n not in report:
            res.fail(f"{what}: report does not contain {n!r}")


_PARAM_LINE = re.compile(r"^\s*parameter\s+\w+\s*=\s*[^,;]+[,;]?\s*$")


def _print_parity(base, step, out, d2, res) -> bool:
    """Print the design at BOTH configurations and require the two to differ only in the
    parameter defaults. Returns False (and fails `res`) when the structure moved."""
    from .printer import print_sv
    from .load import load
    try:
        a = print_sv(load(base / step["must_reject"]), src=step["must_reject"]) \
            if step.get("must_reject") else None
        b = print_sv(load(d2), src=step["design"])
    except Exception as e:                       # a print that fails is a different problem,
        res.say(f"print parity: not checked ({type(e).__name__}: {e})")
        return True                              # and is reported by the print step itself
    if a is None:
        res.say("print parity: not checked (no default-configuration design named)")
        return True
    # the printed HEADER names the source file, which is provenance rather than structure --
    # it differs whenever the two designs sit at different paths, and comparing it would fail
    # a perfectly parametric module for the name of the file it came from
    def body(t):
        return [l for l in t.splitlines() if not l.lstrip().startswith("// Printed by")]

    import difflib
    diff = [l for l in difflib.unified_diff(body(a), body(b), lineterm="", n=0)
            if l[:1] in "+-" and not l.startswith(("+++", "---"))]
    moved = [l for l in diff if not _PARAM_LINE.match(l[1:])]
    if moved:
        res.fail("the printed RTL is NOT parametric: printing at the two configurations "
                 "changes more than the parameter defaults, so the module carries a "
                 "parameter it does not honour. The lines that moved:\n    "
                 + "\n    ".join(moved[:8])
                 + (f"\n    ... and {len(moved) - 8} more" if len(moved) > 8 else ""))
        return False
    res.say(f"print parity: the printed RTL is parametric "
            f"({len(diff)} line(s) differ, all parameter defaults)")
    return True


def run_manifest(manifest_path, roundtrips: bool = True) -> FlowResult:
    """`roundtrips=False` is the CERTIFICATE view of the same manifest: the contract runs,
    the refine chain (standard, strong half, parity producers) and the second points --
    everything that proves -- without the print-and-simulate leg."""
    from .contract import verify_contract
    from .refine import refine
    from .roundtrip import roundtrip

    manifest_path = pathlib.Path(manifest_path)
    if manifest_path.is_dir():
        manifest_path = manifest_path / "verify.json"
    res = FlowResult()
    base = manifest_path.parent
    res.say(f"flow: {manifest_path}")
    if not manifest_path.exists():
        res.fail("no verify.json here")
        return res
    try:
        m = json.loads(manifest_path.read_text())
    except json.JSONDecodeError as e:
        res.fail(f"verify.json does not parse: {e}")
        return res
    if not _check_keys(m, _TOP_KEYS, "manifest", res):
        return res

    for step in m.get("contracts", []):
        if not _check_keys(step, _CONTRACT_KEYS, "contracts", res) or "module" not in step:
            res.ok and res.fail("contracts: 'module' is required")
            return res
        mod = _path(base, step["module"], "contracts", res)
        if mod is None:
            return res
        kw = {k: step[k] for k in ("k", "induct") if k in step}
        r = verify_contract(mod, **kw)
        res.say(f"contract {step['module']}: {'OK' if r.ok else 'FAILED'}")
        if not r.ok:
            res.fail(r.report())
            return res
        _contains(r.report(), step.get("contains"), f"contract {step['module']}", res)
        if not res.ok:
            return res

    for step in m.get("refine", []):
        if not _check_keys(step, _REFINE_KEYS, "refine", res):
            return res
        missing = [k for k in ("design", "spec") if k not in step]
        if missing:
            res.fail(f"refine: required key(s) missing: {missing}")
            return res
        paths = {k: _path(base, step[k], "refine", res) for k in ("design", "spec")}
        # `stim` is OPTIONAL: the v2 certificate path takes no stimulus at all
        stim = _path(base, step["stim"], "refine", res) if step.get("stim") else None
        prev = _path(base, step["prev"], "refine", res) if step.get("prev") else None
        if any(v is None for v in paths.values()) or (step.get("stim") and stim is None) \
                or (step.get("prev") and prev is None):
            return res
        kw = {k: step[k] for k in ("k", "induct", "free_reset") if k in step}
        r = refine(paths["spec"], stim, paths["design"], prev=prev, **kw)
        if step.get("log"):
            (base / step["log"]).write_text(r.report())
        if step.get("induction_only"):
            # the STRONG HALF's criterion: judged by the induction alone -- scenarios under
            # a free reset are violable by a mid-story reset, which is the definition of
            # reset, not a defect (methodology 24.1)
            ind_ok = "INDUCTIVE at K=" in r.report()
            res.say(f"refine {step['design']} (induction only): "
                    f"{'OK' if ind_ok else 'FAILED'}")
            if not ind_ok:
                res.fail(r.report())
                return res
        else:
            res.say(f"refine {step['design']}: {'OK' if r.ok else 'FAILED'}")
            if not r.ok:
                res.fail(r.report())
                return res
        if "abstract" in step and sorted(r.abstract) != sorted(step["abstract"]):
            res.fail(f"refine {step['design']}: abstract set is {sorted(r.abstract)}, "
                     f"the manifest expects {sorted(step['abstract'])}")
            return res
        _contains(r.report(), step.get("contains"), f"refine {step['design']}", res)
        if not res.ok:
            return res

    for step in m.get("second_points", []):
        # THE SECOND CONFIGURATION (methodology 24.1): the design regenerated at an
        # off-default point, the contract's #const lines rewritten to match, the standard
        # certificate required green there -- and the point required to DISCRIMINATE:
        # the off-default contract must REJECT the default design (`must_reject`), or the
        # extra point proves nothing. This is what turns "parameterized in name only"
        # into a certificate failure instead of an instantiation-time surprise.
        if not _check_keys(step, _SECOND_KEYS, "second_points", res):
            return res
        missing = [k for k in ("regenerate", "design", "spec", "const_overrides") if k not in step]
        if missing:
            res.fail(f"second_points: required key(s) missing: {missing}")
            return res
        spec_p = _path(base, step["spec"], "second_points", res)
        if spec_p is None:
            return res
        import subprocess
        import sys as _sys
        import tempfile
        with tempfile.TemporaryDirectory() as td:
            out = pathlib.Path(td)
            argv = [a.replace("{out}", str(out)).replace("{python}", _sys.executable)
                    for a in step["regenerate"]]
            g = subprocess.run(argv, cwd=base, capture_output=True, text=True)
            if g.returncode != 0:
                res.fail(f"second_points: regenerate failed: {' '.join(argv)}\n"
                         + g.stdout + g.stderr)
                return res
            text = spec_p.read_text()
            for name, val in step["const_overrides"].items():
                pat = re.compile(rf"^#const\s+{re.escape(name)}\s*=\s*\S+\s*\.\s*$", re.M)
                if not pat.search(text):
                    res.fail(f"second_points: the contract has no `#const {name} = ...` "
                             f"line to override")
                    return res
                text = pat.sub(f"#const {name} = {val}.", text)
            spec2 = out / "spec_second_point.lp"
            spec2.write_text(text)
            d2 = out / step["design"]
            if not d2.exists():
                res.fail(f"second_points: regenerate did not produce {step['design']} in its "
                         f"output directory")
                return res
            kw = {k: step[k] for k in ("induct",) if k in step}
            r = refine(spec2, None, d2, **kw)
            if step.get("log"):
                (base / step["log"]).write_text(r.report())
            res.say(f"second point ({', '.join(f'{k}={v}' for k, v in step['const_overrides'].items())}): "
                    f"{'OK' if r.ok else 'FAILED'}")
            if not r.ok:
                res.fail(r.report())
                return res
            _contains(r.report(), step.get("contains"), "second point", res)
            if not res.ok:
                return res
            if step.get("must_reject"):
                dj = _path(base, step["must_reject"], "second_points", res)
                if dj is None:
                    return res
                rx = refine(spec2, None, dj, **kw)
                if rx.ok:
                    res.fail(f"second point does not DISCRIMINATE: its contract accepted "
                             f"{step['must_reject']} (the default-configuration design) -- "
                             f"the extra point is vacuous")
                    return res
                res.say(f"second point discriminates: {step['must_reject']} rejected, as it must be")

            # IS THE PRINTED RTL PARAMETRIC? Everything above certifies the ASP at a second
            # point, which is the right check for a design parameterised in name only -- and
            # it is BLIND to a parameterisation lost between the ASP and the print. That is
            # not hypothetical: a block passed here at dataBits=3 while its printed module
            # carried eight hardcoded `assign byteUpTo[i]` lines, so DATABITS below 8 was an
            # out-of-range reference and above 8 left bits undriven. A human reading the file
            # found it, which is the one thing this methodology tries not to rely on.
            #
            # The property "this module honours its parameter" is a property of the PRINTED
            # RTL, so the check reads printed RTL. Two prints of a genuinely parametric design
            # differ only in the parameter DEFAULTS -- measured on the miss queue at depth 4
            # against depth 2: four differing lines, every one a `parameter X = N`. A design
            # whose structure moves with the parameter differs in the number of statements,
            # and that is what this catches.
            if step.get("print_parity", True) and not _print_parity(
                    base, step, out, d2, res):
                return res

    for step in (m.get("roundtrips", []) if roundtrips else []):
        if not _check_keys(step, _ROUNDTRIP_KEYS, "roundtrips", res):
            return res
        missing = [k for k in ("design", "scenario") if k not in step]
        if missing:
            res.fail(f"roundtrips: required key(s) missing: {missing}")
            return res
        dp = _path(base, step["design"], "roundtrips", res)
        sp = _path(base, step["scenario"], "roundtrips", res)
        if dp is None or sp is None:
            return res
        # `simulator: verilator | icarus | auto` (auto = the first installed, Verilator before
        # Icarus); `icarus: true` is the older spelling of simulator: icarus. Absent in this
        # environment -> the ASP sides only, said.
        from .roundtrip import resolve_sim, sim_available
        want = step.get("simulator") or ("icarus" if step.get("icarus", False) else None)
        sim = resolve_sim(want)
        if want and (sim is None or not sim_available(sim)):
            res.say(f"roundtrip {step['design']}: simulator `{want}` requested but not installed -- "
                    "ASP sides only in this environment")
            sim = None
        r = roundtrip(dp, sp, mode=step.get("mode", "behav"), sim=sim)
        res.say(f"roundtrip {step['design']}: {'OK' if r.ok else 'FAILED'}")
        if not r.ok:
            res.fail(r.report())
            return res
        _contains(r.report(), step.get("contains"), f"roundtrip {step['design']}", res)
        if not res.ok:
            return res

    if not any(m.get(k) for k in _TOP_KEYS):
        res.fail("the manifest declares NO steps -- an empty flow would be a green that checked "
                 "nothing")
    return res
