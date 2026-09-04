"""`python -m sv2asp.aspfirst2 {lint,print,roundtrip} ...` -- see the package docstring."""
from __future__ import annotations

import argparse
import pathlib
import subprocess
import sys


def _toolchain() -> list:
    from ..issue_report import toolchain_lines
    return toolchain_lines()


def _run_reported(a, argv) -> int:
    """Run the command with its output captured, then write the issue report beside the
    verdict. The report carries the ENVIRONMENT and the OUTPUT -- never the design: a
    user's block is theirs, exactly as the tool's internals are the maintainer's, so a
    diagnosis travels as a minimised probe the user chooses to attach."""
    import contextlib
    import datetime
    import io
    buf = io.StringIO()
    rc = 1
    try:
        with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
            rc = _dispatch(a)
    except SystemExit as e:                       # argparse and friends
        rc = int(e.code or 0)
    except Exception:
        import traceback
        traceback.print_exc(file=buf)
        rc = 1
    text = buf.getvalue()
    sys.stdout.write(text)
    from ..issue_report import write_issue_report
    write_issue_report(a.report, tool="sv2asp2", argv=list(argv or sys.argv[1:]), rc=rc, text=text)
    return rc


def main(argv: list | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python -m sv2asp.aspfirst2",
                                 description="ASP-first design: lint, print to SystemVerilog, round-trip.")
    sub = ap.add_subparsers(dest="cmd", required=True)
    l = sub.add_parser("lint", help="subset gate + static checks")
    l.add_argument("design")
    p = sub.add_parser("print", help="print the design as SystemVerilog")
    p.add_argument("design")
    p.add_argument("--mode", choices=("cells", "behav"), default="behav")
    p.add_argument("-o", "--out", help="output .sv (default: stdout)")
    r = sub.add_parser("roundtrip", help="print, translate back with sv2asp (modular; --both-modes adds flat), "
                                         "compare traces under the scenario; optionally Icarus")
    r.add_argument("design")
    r.add_argument("scenario")
    r.add_argument("--mode", choices=("cells", "behav"), default="behav")
    r.add_argument("--icarus", action="store_true", help="arbitrate with Icarus (= --sim icarus)")
    r.add_argument("--verilator", action="store_true", help="arbitrate with Verilator (= --sim verilator)")
    r.add_argument("--sim", choices=("verilator", "icarus", "auto"),
                   help="the simulator that arbitrates the round trip; `auto` takes the first "
                        "installed, Verilator before Icarus")
    r.add_argument("--keep", help="directory to keep the printed .sv and translations in")
    r.add_argument("--both-modes", action="store_true",
                   help="also translate FLAT and compare it as a third side (translator development;"
                        " modular-only is the default -- LESSONS par E16)")
    r.add_argument("--incremental", action="store_true",
                   help="solve the TRANSLATED side(s) per instant, feeding each solved instant back"
                        " as facts -- for designs whose direct grounding cross-products candidate"
                        " values through the datapath (a many-cell operand network); same unique"
                        " trace, k+1 small solves instead of one impossible grounding")
    ex = sub.add_parser("expand", help="the design in the translator's EMITTED SCHEMA -- the form you read; "
                                        "self-contained and runnable like a translation")
    ex.add_argument("design")
    ex.add_argument("-o", "--out", help="output .lp (default: stdout); <out stem>__init0.lp is written too")
    ct = sub.add_parser("contract", help="verify an authored module STANDALONE against its own "
                                          "<module>.contract.lp (guarantee as bad, require assumed)")
    ct.add_argument("module")
    ct.add_argument("-k", type=int, default=8)
    ct.add_argument("--witness", action="store_true")
    ct.add_argument("--induct", type=int, metavar="K", help="k-induction on the module against its contract")
    rf = sub.add_parser("refine", help="check one refinement step: spec, stimulus, the current level "
                                        "(and the previous one)")
    rf.add_argument("spec")
    rf.add_argument("stim_or_cur", help="v2 certificate path: `refine SPEC LEVEL --induct K` "
                                        "(no stimulus); with three positionals the middle one "
                                        "is a v1-style stimulus")
    rf.add_argument("cur", nargs="?")
    rf.add_argument("--prev")
    rf.add_argument("--inv", help="the current level's invariants (default <cur>.inv.lp if present)")
    rf.add_argument("--prev-inv", help="the previous level's invariants (default <prev>.inv.lp)")
    rf.add_argument("-k", type=int, help="override the stimulus horizon")
    rf.add_argument("--witness", action="store_true", help="also print one trace of the level under the stimulus")
    rf.add_argument("--induct", type=int, metavar="K",
                    help="k-induction: the checks above as the BASE, plus a STEP from an arbitrary state "
                         "(state and ghost free at T=0, inputs free) assuming the property set for K cycles; "
                         "UNSAT = holds for all time")
    rf.add_argument("--free-reset", action="store_true",
                    help="with --induct: let the reset nets toggle from T=1 on in the step (default: held released)")
    ex2 = sub.add_parser("export", help="the DATA obligations of a level under a (pinned) scenario, as Lean theorems "
                                         "over the @func models (CDS slice 2)")
    ex2.add_argument("spec")
    ex2.add_argument("scenario")
    ex2.add_argument("level")
    ex2.add_argument("-o", "--out", required=True, help="the .lean file to write")
    ex2.add_argument("-k", type=int)
    ex2.add_argument("--namespace")
    ce = sub.add_parser("certificate", help="run the ENTRY's whole CERTIFICATE from its "
                                            "verify.json -- the standard run, the strong half "
                                            "(--free-reset, induction only), any parity "
                                            "producers, and the second configuration with its "
                                            "discrimination check; reports written where the "
                                            "manifest's `log` keys say")
    ce.add_argument("entry", help="the entry directory, or the manifest file itself")
    vf = sub.add_parser("verify", help="run an ENTRY's whole flow from its verify.json manifest -- "
                                        "contracts, the refine chain, round trips; the flow as data")
    vf.add_argument("entry", help="the entry directory, or the manifest file itself")
    cp = sub.add_parser("compile", help="the specification-language front end: a controlled-English "
                                        ".cnl (its .cnl.core is written beside it) plus the .yaml "
                                        "signature, compiled to the ASP contract")
    cp.add_argument("spec", help="the <block>.cnl (or a generated .cnl.core)")
    cp.add_argument("signature", help="the <block>.yaml signature")
    cp.add_argument("-o", "--out", default="spec.lp", help="the contract file to write (default spec.lp)")
    cp.add_argument("--strict", action="store_true",
                    help="exit nonzero if anything was refused (refusals are always printed)")
    ld = sub.add_parser("ladder", help="the HUMAN-GATED ladder: each artifact of the route is a step, "
                                       "and no step begins until a person has read and approved the "
                                       "one before it")
    ld.add_argument("action", choices=["status", "init", "built", "explained", "verified"],
                    help="status (default view); init a fresh ladder; or move a step. "
                         "`approved` is deliberately absent -- a person sets that, by editing the file")
    ld.add_argument("entry", help="the entry directory, or the ladder.yaml itself")
    ld.add_argument("step", nargs="?", help="the step to move")
    ld.add_argument("--note", default="", help="the read-back text, for `explained`")
    sc = sub.add_parser("schema", help="print the ASP schema this tool accepts and emits -- "
                                       "the design language, the contract's vocabulary and "
                                       "the linkage shape, so a design can be WRITTEN in it "
                                       "rather than inferred from an example")
    sc.add_argument("--design", action="store_true", help="only the design language")
    sc.add_argument("--contract", action="store_true", help="only the contract's vocabulary")
    sc.add_argument("--linkage", action="store_true", help="only the linkage shape")
    sub.add_parser("keywords", help="print the controlled English's vocabulary, with the "
                                    "STRUCTURAL words -- the ones that must carry their "
                                    "`@` sigil -- marked")
    sub.add_parser("doctor", help="check the environment this tool needs -- python, the "
                                  "clingo binary and its embedded-Python support, Icarus -- "
                                  "reporting where each one resolved from and, for anything "
                                  "missing, the exact command to install it")
    # every verb takes it, so it reads naturally AFTER the subcommand -- a parent-parser
    # option would have to precede the verb, which nobody types
    for _sp in sub.choices.values():
        _sp.add_argument("--report", metavar="FILE",
                         help="write an ISSUE REPORT for the maintainer: the tool version, "
                              "the resolved toolchain, the command, the exit status and the "
                              "full output -- everything needed to diagnose a refusal, and "
                              "nothing from your design (attach a minimised probe yourself)")
    a = ap.parse_args(argv)

    if getattr(a, "report", None):
        return _run_reported(a, argv)
    return _dispatch(a)


def _doctor() -> int:
    """What the tool needs, what it found, and what to do about what it did not. The
    environment question is the one a user answers least reliably from memory ("I think
    clingo is installed"), so this asks the machine instead -- and it probes clingo the
    way the tool USES it: a `#script (python)` block, not just `--version`, because a
    clingo without embedded Python passes every naive check and fails every real solve."""
    import shutil
    import tempfile
    sysname = sys.platform
    hint = {"darwin": "brew install {}", "linux": "apt install {} (or your distro's package)"}
    ok = True
    print("sv2asp2 doctor -- the environment this tool needs\n")
    print(f"  python           {sys.version.split()[0]}  ({sys.executable})")
    if sys.version_info < (3, 11):
        ok = False
        print("                   TOO OLD -- 3.11 or newer is required")
    for mod in ("clingo", "pyslang", "lark", "yaml"):
        try:
            __import__(mod)
            print(f"  python: {mod:9} present")
        except ImportError:
            ok = False
            print(f"  python: {mod:9} MISSING -- pip install "
                  f"{'pyyaml' if mod == 'yaml' else mod}")
    try:
        from ..config import load as _cfg
        cfg = _cfg()
    except Exception:
        cfg = None
    def _where(tool: str):
        p = None
        if cfg is not None:
            try:
                p = cfg.tool(tool)
            except Exception:
                p = None
        return p or shutil.which(tool)
    # the round trip's ARBITER: either simulator will do, Verilator preferred (2026-09-03, the
    # user: some companies only have Verilator). Missing only when NEITHER is installed.
    sims = []
    for tool, flag in (("verilator", "--version"), ("iverilog", "-V")):
        path = _where(tool)
        if not path:
            continue
        try:
            v = subprocess.run([path, flag], capture_output=True, text=True, timeout=8)
            ver = (v.stdout or v.stderr).splitlines()[0]
        except Exception:
            ver = "(present, but did not answer)"
        print(f"  {tool:16} {ver}   ({path})")
        sims.append("verilator" if tool == "verilator" else "icarus")
    if sims:
        print(f"  round trip       arbiter: {sims[0]}" + (f" (also {sims[1]})" if len(sims) > 1 else ""))
    else:
        ok = False
        cmd = hint.get(sysname, "install {}").format("verilator")
        print(f"  simulator        MISSING -- the round trip's arbiter: verilator (preferred) or iverilog\n"
              f"                   install one with: {cmd}\n"
              f"                   (or, if it is already installed somewhere unusual, "
              f"put its path in sv2asp.toml's [tools])")
    for tool, pkg, why in (("clingo", "clingo", "the solver: every certificate runs on it"),):
        path = None
        if cfg is not None:
            try:
                path = cfg.tool(tool)
            except Exception:
                path = None
        path = path or shutil.which(tool)
        if not path:
            ok = False
            cmd = hint.get(sysname, "install {}").format(pkg)
            print(f"  {tool:16} MISSING -- {why}\n"
                  f"                   install it with: {cmd}\n"
                  f"                   (or, if it is already installed somewhere unusual, "
                  f"put its path in sv2asp.toml's [tools])")
            continue
        try:
            v = subprocess.run([path, "--version" if tool == "clingo" else "-V"],
                               capture_output=True, text=True, timeout=8)
            ver = (v.stdout or v.stderr).splitlines()[0]
        except Exception:
            ver = "(present, but did not answer)"
        print(f"  {tool:16} {ver}   ({path})")
    # the probe that matters: clingo must run an embedded `#script (python)` block
    cl = (cfg.tool("clingo") if cfg else None) or shutil.which("clingo")
    if cl:
        with tempfile.NamedTemporaryFile("w", suffix=".lp", delete=False) as f:
            f.write("#script (python)\nfrom clingo import Number\n"
                    "def double(x): return Number(x.number * 2)\n"
                    "def main(prg):\n    prg.ground([('base', [])])\n    prg.solve()\n"
                    "#end.\nv(@double(21)).\n")
            probe = f.name
        try:
            r = subprocess.run([cl, "-q0", "--outf=0", probe], capture_output=True,
                               text=True, timeout=30)
            if "v(42)" in r.stdout:
                print("  clingo: scripts   OK -- the binary runs embedded Python")
            else:
                ok = False
                print("  clingo: scripts   FAILING -- this clingo has no embedded-Python "
                      "support.\n                   Every solve carries a `#script (python)` "
                      "block, so nothing will\n                   work. Install a build that "
                      "has it (Homebrew, or conda-forge).")
        except Exception as e:
            ok = False
            print(f"  clingo: scripts   could not be probed ({type(e).__name__})")
    print("\n" + ("READY -- run a certificate to be sure (see the book's Part C)"
                  if ok else "NOT READY -- fix the items above, then re-run `doctor`"))
    return 0 if ok else 1


def _grounds(path) -> str | None:
    """Does the contract we just emitted actually GROUND? Returns the error, or None.

    `compile` reported its refusals and never looked at its own output, so a clean exit
    could hand back an artifact clingo will not read. The case that showed it: a boundary
    declaration whose position variable was bound in the claim's rule and free in the
    separate rule the declaration became. Clingo does not skip an unsafe rule -- it stops
    grounding and takes the WHOLE program down, so nothing downstream of the contract could
    run at all, and the compile that produced it exited 0.

    Safety is a SYNTACTIC property, so the contract grounds on its own: `val/3` and the rest
    are undefined here, which makes most rules ground to nothing and the check cheap. Those
    undefined atoms produce info messages, never errors, so only `error:` lines count.
    """
    try:
        from .lint import clingo_bin
        cl = clingo_bin()
    except Exception:
        return None                      # no clingo: the certificate will say so soon enough
    try:
        r = subprocess.run([cl, "--text", str(path)], capture_output=True, text=True,
                           timeout=120)
    except (OSError, subprocess.TimeoutExpired):
        return None
    errs = [l.strip() for l in (r.stderr or "").splitlines() if "error:" in l]
    if not errs:
        return None
    notes = [l.strip() for l in (r.stderr or "").splitlines() if "note:" in l]
    return "; ".join(errs[:2] + notes[:2])


def _keywords() -> int:
    """The vocabulary, with the structural words marked.

    Cited by the skill and by the methodology as the sigil rule's discoverability story, and
    for a while cited by both while not existing -- which is worse than an undocumented
    command, because a reader who types it and gets `invalid choice` stops trusting the rest
    of the page. Both lists come from the grammar file, so this cannot drift from the rule
    the desugarer enforces.
    """
    from .dsl.cnl import GRAMMATICAL, STRUCTURAL
    print("STRUCTURAL -- these carry a required `@`. A bare one is refused with the exact")
    print("spelling to use; an unknown `@wehn` is refused by name. They are what gives a")
    print("sentence its skeleton, so the shape is visible before the words are read.\n")
    for k in sorted(STRUCTURAL):
        print(f"    @{k}")
    print("\nGRAMMATICAL -- ordinary English, written plain. Articles are quantifiers all")
    print("the same: `a`/`an` in trigger position means EACH such instance, `the` claims")
    print("uniqueness and needs the licence that makes it true.\n")
    for k in sorted(GRAMMATICAL):
        print(f"    {k}")
    print(f"\n{len(STRUCTURAL)} structural, {len(GRAMMATICAL)} grammatical. The full surface,")
    print("with every condition pattern and its examples, is lib/dsl/grammar.ebnf.")
    return 0


def _dispatch(a) -> int:
    if a.cmd == "schema":
        from .schema import render
        picked = (a.design, a.contract, a.linkage)
        print(render(*(picked if any(picked) else (True, True, True))))
        return 0
    if a.cmd == "keywords":
        return _keywords()
    if a.cmd == "doctor":
        return _doctor()
    if a.cmd == "lint":
        from .lint import lint_file, report
        d, errs, warns = lint_file(a.design)
        print(report(a.design, errs, warns))
        return 1 if errs else 0
    if a.cmd == "print":
        from .lint import lint_composed, report
        from .load import load
        from .printer import print_hier, print_sv
        comp, errs, warns = lint_composed(a.design)
        if errs or comp is None:
            print(report(a.design, errs, warns), file=sys.stderr)
            print("refusing to print a design that does not lint", file=sys.stderr)
            return 1
        sv = print_hier(a.design, mode=a.mode) if comp.modules else print_sv(load(a.design), mode=a.mode, src=a.design)
        if a.out:
            pathlib.Path(a.out).write_text(sv)
            print(f"wrote {a.out}")
        else:
            sys.stdout.write(sv)
        return 0
    if a.cmd == "expand":
        from .expand import expand
        from .lint import lint_file, report
        d, errs, warns = lint_file(a.design)
        if errs or d is None:
            print(report(a.design, errs, warns), file=sys.stderr)
            return 1
        text, init0 = expand(d, src=a.design)
        if a.out:
            out = pathlib.Path(a.out)
            out.write_text(text)
            print(f"wrote {out}")
            if init0:
                i0 = out.with_name(out.stem + "__init0.lp")
                i0.write_text(init0)
                print(f"wrote {i0}")
        else:
            sys.stdout.write(text)
        return 0
    if a.cmd == "compile":
        from .dsl.check import check
        from .dsl.cnl import CnlError
        from .dsl.emit import Emitter
        from .dsl.signature import SignatureError, load as load_sig
        try:
            sig = load_sig(pathlib.Path(a.signature))
        except SignatureError as e:
            # A REFUSAL, NOT A TRACEBACK. The schema's messages name the field, list its
            # values and say why the choice matters -- all of which is wasted if it arrives
            # as a stack trace, and a stack trace also reads as "the tool broke" rather than
            # "your signature is wrong". A crash standing where a refusal belongs has now
            # cost this route twice.
            print(f"PROBLEM: {e}")
            return 1
        sp = pathlib.Path(a.spec)
        try:
            em = Emitter(sp, sig)
        except CnlError as e:
            # THE SURFACE'S REFUSALS ARE REFUSALS. The sigil rule and the frozen patterns
            # both raise here, and both name the line and the spelling to use -- all of
            # which is thrown away by arriving as a stack trace, which also reads as "the
            # tool broke" rather than "this sentence is not in the language". Third time
            # this pattern has cost the route something.
            print(f"PROBLEM: {e}")
            return 1
        sp = sp
        # THE CHECKS RUN HERE, not only when someone thinks to run them. A rule that
        # catches a malformed specification is worth nothing if the command an author
        # actually types never consults it -- an undeclared index domain was reported by
        # `check` and sailed through `compile`, which is the command everybody uses
        # (the second block's finding, 2026-09-01).
        core = sp.with_suffix(".cnl.core") if sp.suffix == ".cnl" else sp
        findings = check(core, sig) if core.exists() else []
        for f in findings:
            print(f"PROBLEM: {f}")
        text, refused = em.contract_file()
        out = pathlib.Path(a.out)
        out.write_text(text)
        print(f"wrote {out} ({len(text.splitlines())} lines)")
        if em.reset:
            # THE RESOLVED SENSE, IN WORDS, beside the windows. Validation stops a
            # misspelling; this makes the CHOICE visible to a person reading the output, so
            # a polarity that is spelled correctly and simply wrong is caught by the reader
            # rather than by a certificate that comes back green on the reset window.
            on = 1 if em.reset.get("polarity") == "active_low" else 0
            print(f"reset {em.reset['name']}: {em.reset.get('polarity')} -- claims are "
                  f"judged where {em.reset['name']} == {on}, and silenced otherwise")
        for w in sorted(getattr(em, "windows", []) or []):
            print(f"window demanded of the design: {w}")
        for r in refused:
            print(f"REFUSED: {r}")
        ground = _grounds(out)
        if ground:
            print(f"PROBLEM: the emitted contract does not ground: {ground}")
        return 1 if (findings or ground or (refused and a.strict)) else 0
    if a.cmd == "ladder":
        from .ladder import Ladder, LadderError, STEPS
        p = pathlib.Path(a.entry)
        p = p if p.is_file() else p / "ladder.yaml"
        try:
            if a.action == "init":
                Ladder.create(p, p.parent.name, {})
                print(f"created {p} -- fill in each step's `artifact`")
                return 0
            lad = Ladder.load(p)
            if a.action != "status":
                if not a.step:
                    print(f"which step? one of {[n for n, _, _ in STEPS]}", file=sys.stderr)
                    return 2
                lad.advance(a.step, a.action, a.note)
            print(lad.report())
            return 0
        except LadderError as e:
            print(f"ladder: {e}", file=sys.stderr)
            return 1
    if a.cmd == "verify":
        from .flow import run_manifest
        res = run_manifest(a.entry)
        print(res.report())
        return 0 if res.ok else 1
    if a.cmd == "certificate":
        from .flow import run_manifest
        res = run_manifest(a.entry, roundtrips=False)
        print(res.report())
        return 0 if res.ok else 1
    if a.cmd == "contract":
        from .contract import verify_contract
        res = verify_contract(a.module, k=a.k, witness=a.witness, induct=a.induct)
        print(res.report())
        return 0 if res.ok else 1
    if a.cmd == "refine":
        from .refine import refine
        stim, cur = (a.stim_or_cur, a.cur) if a.cur else (None, a.stim_or_cur)
        res = refine(a.spec, stim, cur, prev=a.prev, cur_inv=a.inv, prev_inv=a.prev_inv, k=a.k, witness=a.witness,
                     induct=a.induct, free_reset=a.free_reset)
        print(res.report())
        return 0 if res.ok else 1
    if a.cmd == "export":
        from .export import ExportError, export_lean
        try:
            print(export_lean(a.spec, a.scenario, a.level, a.out, k=a.k, namespace=a.namespace))
        except ExportError as e:
            print(f"export: {e}", file=sys.stderr)
            return 1
        return 0
    if a.cmd == "roundtrip":
        from .roundtrip import roundtrip
        sim = a.sim or ("verilator" if a.verilator else "icarus" if a.icarus else None)
        res = roundtrip(a.design, a.scenario, mode=a.mode, keep=a.keep, sim=sim,
                        both=a.both_modes, incremental=a.incremental)
        print(res.report())
        return 0 if res.ok else 1
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
