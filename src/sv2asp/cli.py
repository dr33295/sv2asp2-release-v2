"""sv2asp command-line entry point."""

from __future__ import annotations

import argparse
import os
import pathlib
import sys

from . import completion as comp
from . import coverage as cov
from . import snapshot as snap
from . import sources as srcs
from .frontend.pyslang_frontend import PyslangFrontend, SvSourceError
from .ir.nodes import Loc
from .stages.stage2_analysis import analyze
from .stages.stage3_emit import (emit, emit_modular, init_zero_lp, init_zero_modular,
                                 scenario_stub, xinit_lp, xinit_modular, xinit_uncovered)
from . import compose
from . import state_inventory


def _parse_overrides(items: list[str]) -> dict[str, int]:
    out: dict[str, int] = {}
    for it in items:
        k, _, v = it.partition("=")
        out[k.strip()] = int(v)
    return out


def _parse_defines(items: list[str]) -> dict[str, str]:
    out: dict[str, str] = {}
    for it in items:
        k, _, v = it.partition("=")
        out[k.strip()] = v.strip()
    return out


#: Emit-time findings about the WHOLE emitted program rather than one source line. They
#: cannot be attributed to a coverage line, so `--strict-coverage` counts them directly.
_PROGRAM_LEVEL = ("UNSAFE RULE", "COMBINATIONAL LOOP")


def main(argv: list[str] | None = None) -> int:
    """Translate, or REFUSE if the source does not compile (Fix 73).

    A slang error is not a coverage problem: slang recovers and hands back a tree, so there is
    no construct to report -- the construct the tool would see never existed. Exit 2 (distinct
    from 1, an unsupported/unaccounted construct) and print slang's own message, which names
    the file and column."""
    try:
        return _main(argv)
    except SvSourceError as e:
        sys.stderr.write(f"REFUSED: {e}\n")
        return 2


def _main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="sv2asp", description="SystemVerilog -> ASP translator")
    ap.add_argument("files", nargs="*", help="SystemVerilog source file(s) (or use --sources)")
    ap.add_argument("--sources", default=None, metavar="JSON",
                    help="JSON manifest of source paths (file/folder); folders are expanded to all SV files")
    ap.add_argument("--config", default=None, metavar="TOML",
                    help="tool configuration file (tool paths, @func/primitive plugins); "
                         "default discovery: $SV2ASP_CONFIG, ./sv2asp.toml, ~/.config/sv2asp/config.toml")
    ap.add_argument("--top", default=None, help="name of the top module to translate")
    ap.add_argument("-I", "--incdir", action="append", default=[], metavar="DIR",
                    help="`include search path (for .svh headers / default params)")
    ap.add_argument("-D", "--define", action="append", default=[], metavar="NAME=VAL",
                    help="preprocessor +define+ macro")
    ap.add_argument("-p", "--param", action="append", default=[], metavar="NAME=VALUE",
                    help="override a parameter (resolved concretely before translation)")
    ap.add_argument("-k", "--horizon", type=int, default=None, help="BMC horizon (#const k)")
    ap.add_argument("--style", choices=["v1", "v2"], default=None,
                    help="boolean encoding: v1=positive-definite, v2=excluded-middle (NAF)")
    ap.add_argument("--primary-clock", default=None, metavar="CLK",
                    help="name of the design's free-running master clock (the multi-clock master-tick "
                         "reference; used for the scenario-stub time(clk,0..k) and validation)")
    ap.add_argument("--mode", choices=["emit", "reset-snapshot", "modular"], default=None,
                    help="emit=flat single file; modular=per-module spec set (default); reset-snapshot="
                         "run the reset sequence and write a T=0 bridge. Default INFERS from -o: a "
                         "folder/'/'-suffixed target -> modular, a *.lp file (or stdout) -> flat.")
    ap.add_argument("--reset-seq", default=None, metavar="FILE",
                    help="designer-provided reset/init input sequence (.lp) for reset-snapshot mode")
    ap.add_argument("--reset-cycles", type=int, default=2,
                    help="auto-fallback: cycles to hold reset asserted when --reset-seq is omitted")
    ap.add_argument("--no-single-valued", action="store_true",
                    help="suppress the __t34.lp companion (F9: the constraint that a signal "
                         "holds ONE value per instant). Off by default -- without it a "
                         "scenario contradicting the design yields a model where a signal "
                         "is two values at once, reported SATISFIABLE")
    ap.add_argument("--no-x-init", action="store_true",
                    help="suppress the __xinit.lp companion (exact-X power-on choices for "
                         "unreset 4-state registers; ON by default -- see docs/guide/SV2ASP_USAGE.md \u00a73 "
                         "and notes/design/X_SEMANTICS.md)")
    ap.add_argument("--init-zero", action="store_true",
                    help="also write <top>__init0.lp: a CONCRETE power-on state, every unreset "
                         "state element pinned to 0. For TESTING -- it gives one deterministic "
                         "model. Zero is arbitrary and is NOT what the hardware does (an "
                         "uninitialised array or unreset register reads x), which is why it is "
                         "opt-in: the translation carries no initial state (F4), and a tool that "
                         "supplies one by default has gone back to inventing it")
    ap.add_argument("--no-bitvec", action="store_true",
                    help="disable the per-bit representation for wide bit-structural signals "
                         "(default: ON — range-guarded rules instead of the O(N^2) @shl/@bor chain; "
                         "see BIT_VECTOR_REPRESENTATION.md)")
    ap.add_argument("--completion", action="store_true",
                    help="emit the explicit Clark/HLR completion in ASP (witness der/3 + decoupled "
                         "val<->der, inputs open) for Route-2 all-inputs proofs (combinational; flat mode)")
    ap.add_argument("--completion-smt", action="store_true",
                    help="emit the classical Clark/HLR completion as SMT-LIB QF_BV (each combinational "
                         "signal a bit-vector function of inputs) for all-inputs proofs in an SMT solver")
    ap.add_argument("--scenario-stub", action="store_true",
                    help="modular mode: also write <top>__scenario_stub.lp, a fill-in scenario "
                         "skeleton (instance-qualified inputs/init/observe in the right val shape)")
    ap.add_argument("--dump-params", nargs="?", const="-", default=None, metavar="FILE",
                    help="parameter-extraction phase: resolve all params across files -> JSON "
                         "(default stdout) and exit (does not translate)")
    ap.add_argument("-o", "--out", default=None, help="output .lp / bridge (default: stdout)")
    ap.add_argument("--coverage", default=None, metavar="FILE",
                    help="write the line-coverage report (default: stderr summary)")
    # F10: a PROBLEM now exits NON-ZERO BY DEFAULT. It used not to: `--strict-coverage`
    # was opt-in, so a design the tool could not lower was emitted anyway and the CLI
    # returned 0 -- the signal a Makefile, a CI step or a harness actually checks said
    # SUCCESS, over a PARTIAL lowering whose targets had no rules at all. Measured on a
    # plain RISC-V decoder: SATISFIABLE with none of its three output ports having a value
    # at any instant, and every property over it passing vacuously.
    ap.add_argument("--strict-coverage", action="store_true",
                    help="(default since F10; kept for compatibility, now a no-op)")
    ap.add_argument("--allow-problems", action="store_true",
                    help="exit 0 even when constructs could not be lowered, and keep the "
                         "PARTIAL output. For deliberate exploration only -- the emitted "
                         "program is INCOMPLETE and properties over it may pass vacuously")
    ap.add_argument("--allow-latches", action="store_true",
                    help="permit level-sensitive latch cells (LATA/LATB). OFF by default: a "
                         "latch is transparent while enabled, i.e. a combinational path rather "
                         "than a register, and is usually instantiated by mistake. Latches are "
                         "never INFERRED regardless of this flag.")
    ap.add_argument("--log", default=None, metavar="FILE",
                    help="write a REPORT of the run (every problem and warning, with the "
                         "verdict) to FILE. stderr scrolls away and is easy to miss in a "
                         "build; a file can be read after the fact, diffed between runs, "
                         "and grepped by CI for the VERDICT line")
    ap.add_argument("--strict-warnings", action="store_true",
                    help="exit non-zero on WARNINGs too (a faithful translation whose result "
                         "needs review, e.g. a case with no `default`, which leaves its output "
                         "unbound on the uncovered values). For shops whose RTL rules mandate "
                         "a default on every case.")
    args = ap.parse_args(argv)

    # Site configuration first: tool paths + design plugins (extra @funcs, vendor primitive
    # cells) register before any translation runs. See config.py for the file format.
    # A design tree is self-sufficient: an sv2asp.toml NEXT TO the sources manifest is
    # found regardless of the current working directory.
    from . import config as _config
    cfg_path = args.config
    if cfg_path is None and not os.environ.get("SV2ASP_CONFIG") and args.sources:
        cand = pathlib.Path(args.sources).resolve().parent / "sv2asp.toml"
        if cand.is_file():
            cfg_path = str(cand)
    cfg_site = _config.load(cfg_path)
    cfg_site.apply_plugins()

    # Resolve the mode. Modular (per-module spec set) is the default; it writes a FILE SET, so it needs
    # a folder target. When --mode is omitted we INFER from -o: a folder/'/'-suffixed target -> modular,
    # a single *.lp file (or stdout, which can't hold a set) -> flat. An explicit --mode always wins.
    mode = args.mode
    if mode is None:
        mode = "modular" if (args.out and _is_dir_target(args.out)) else "emit"

    # Resolve sources + config: a JSON manifest (file/folder paths) and/or positional files.
    # Explicit CLI flags override manifest values; built-in defaults fill the rest.
    cfg = srcs.load(args.sources) if args.sources else None
    files = list(args.files)
    if cfg:
        files = list(cfg.files) + files
    if not files:
        ap.error("no sources: pass file(s) positionally or --sources JSON")

    params = dict(cfg.params) if cfg else {}
    params.update(_parse_overrides(args.param))  # CLI -p overrides manifest
    top = args.top or (cfg.top if cfg else None)
    style = args.style or (cfg.style if cfg else None) or "v1"
    horizon = args.horizon if args.horizon is not None else (cfg.horizon if cfg else None) or 8
    primary_clock = args.primary_clock or (cfg.primary_clock if cfg else None)
    clock_hierarchy = dict(cfg.clock_hierarchy) if cfg else {}
    incdirs = (list(cfg.incdirs) if cfg else []) + list(args.incdir)
    defines = dict(cfg.defines) if cfg else {}
    defines.update(_parse_defines(args.define))

    defn_files = list(cfg.defn_files) if cfg else []
    stubs = dict(cfg.stubs) if cfg else {}

    fe = PyslangFrontend(param_overrides=params, top=top, incdirs=incdirs, defines=defines, stubs=stubs)
    fe._allow_latches = _latches_enabled(args.allow_latches,
                                         cfg.allow_latches if cfg else None)
    # exact-X companion: manifest "x_init": false OR --no-x-init disables (design-intrinsic
    # policy lives in sources.json -- the allow_latches convention; the flag is per-run)
    x_init_on = _x_init_enabled(args.no_x_init, cfg.x_init if cfg else None)

    # Phase 1 (extraction): resolve every parameter across all files and dump it.
    if args.dump_params is not None:
        import json
        table = fe.param_table(files, defn_files=defn_files)
        text = json.dumps(table, indent=2, sort_keys=True)
        if args.dump_params == "-":
            sys.stdout.write(text + "\n")
        else:
            with open(args.dump_params, "w") as f:
                f.write(text + "\n")
            sys.stderr.write(f"wrote {args.dump_params}\n")
        return 0
    if defn_files:
        sys.stderr.write(f"definition files (packages/params): "
                         f"{', '.join(p.split('/')[-1] for p in defn_files)}\n")

    # modular mode: translate each module ONCE (per param-tuple) into instance-parameterised specs
    # + an instance manifest, composed at solve time. Writes a FILE SET, so -o must be a folder.
    if mode == "modular":
        if not (args.out and _is_dir_target(args.out)):
            ap.error("--mode modular writes a file set; -o must be a folder (e.g. -o out/)")
        m = fe.parse_modular(files, defn_files=defn_files)
        os.makedirs(args.out, exist_ok=True)
        files = dict(emit_modular(m, bitvec=not args.no_bitvec, clock_hierarchy=clock_hierarchy))
        if args.scenario_stub:
            files[f"{m['top']}__scenario_stub.lp"] = scenario_stub(m, k=horizon, primary_clock=primary_clock)
        if x_init_on:
            xi = xinit_modular(m, not args.no_bitvec, files)
            if xi:
                files[f"{m['top']}__xinit.lp"] = xi
        # the CONCRETE power-on state, opt-in -- see the flat path for why it is not a default.
        if args.init_zero:
            iz = init_zero_modular(m, not args.no_bitvec)
            if iz:
                files[f"{m['top']}__init0.lp"] = iz
        if not args.no_single_valued:
            files[f"{m['top']}__t34.lp"] = _T34_MODULAR
        # The STATE INVENTORY -- what state this design has and what defines each piece.
        # The translation carries no initial state, so the set of things needing one has to be
        # stated where a consumer can read it; otherwise a forgotten flop is dark and silent.
        _inv = [state_inventory.render(d, spec=n, text=files.get(f"{n}.lp", ""))
                for n, d in sorted(m["specs"].items())]
        files[f"{m['top']}__state.lp"] = "".join(_inv)
        # F4 -- STATE WITH NO POWER-ON POLICY, the same check the flat path runs and for the
        # same reason. Same shared function on both sides (hard rule 1): the walk that decides
        # what gets a power-on treatment is checked against the state vector the EMITTED RULES
        # actually carry, so a stateful construct nobody thought about is loud, not dark.
        _nopon = [(None,
                   f"STATE WITH NO POWER-ON POLICY: `{n}.{s}` is held across a tick by the "
                   f"emitted rules but no power-on treatment covers it -- not a choice, not even "
                   f"a comment saying why. The translation carries no initial state (F4), so it "
                   f"is dark at t=0 and every property over it passes VACUOUSLY")
                  for n, d in sorted(m["specs"].items())
                  for s in xinit_uncovered(d, files.get(f"{n}.lp", ""), not args.no_bitvec)]
        for name, text in sorted(files.items()):
            with open(os.path.join(args.out, name), "w") as f:
                f.write(text)
            sys.stderr.write(f"wrote {os.path.join(args.out, name)}\n")
        # fail-loud: surface any spec that flagged a construct (frontend flags) AND any emit-time
        # `% PROBLEM:` marker (a construct emit_modular cannot yet faithfully translate -- e.g. a memory
        # or lane domain whose supporting facts are not emitted). Both must fail --strict-coverage, else a
        # silently-dropped construct passes (hard rule 2: no silent miss).
        # F1 -- THE COMPOSED-LEVEL LOOP CHECK. `_check_comb_loops` runs per spec, so two
        # modules that are each acyclic can still close a combinational cycle through the
        # PARENT's port bridges. Flat mode reports such a loop; modular (the DEFAULT) did
        # not, so the most common compile silently accepted a design synthesis rejects.
        #
        # It is reported FOR THE DESIGNER first: a combinational loop is an RTL BUG, and
        # naming the cycle is what lets them fix it. The soundness consequence is real but
        # secondary -- while the loop exists the program is not tight, so Fages does not
        # apply and no completion-route claim over it is licensed. Same wording as the flat
        # path, because it is the same finding (hard rule 1: the modes must agree).
        composed_loops: list = list(_nopon)
        try:
            _isa, _se, _be = compose.load(pathlib.Path(args.out))
            _cyc = compose.find_cycle(compose.build_graph(_isa, _se, _be))
            if _cyc:
                _path = " -> ".join(f"{i}.{t}" for i, t in _cyc)
                composed_loops = [(None,
                    f"COMBINATIONAL LOOP (composed): {_path} form a cycle within one time "
                    f"index. Synthesis forbids this, and the completion route's soundness "
                    f"rests on the program being tight -- the design is translated, but "
                    f"this must be fixed in the RTL")]
        except Exception as e:   # noqa: BLE001 -- a checker fault must not pass as "clean"
            composed_loops = [(None, f"composed loop check could not run: {e!r}")]
        # F2/F7 -- DARK READS: a rule that reads a signal NOTHING derives. The consumer is
        # emitted, the producer is not, and the signal has no value at any instant, so every
        # property over it passes vacuously while the tool exits 0. Checked GENERALLY over
        # the emitted program rather than per construct, because three separate findings
        # (`$rose` dropped, an unpacked array bridged as a word, an unlowerable block) were
        # the same shape arriving by different routes. Inputs are excluded: the scenario
        # drives them, and that boundary is what the design layer is a function of.
        try:
            # externally driven signals, from the FRONTEND rather than the emitted text:
            # a struct-typed input port emits no `port(..., input)` fact for its fields
            # (the F6 under-declaration), so the text alone cannot tell.
            _ext = {}
            for _sp, _d in m["specs"].items():
                _names = set()
                for _sg in _d.signals:
                    _dir = getattr(_sg, "direction", None)
                    _txt = (getattr(getattr(_sg, "loc", None), "text", "") or "").lstrip()
                    if _dir == "input" or _txt.startswith("input"):
                        _names.add(_sg.name)
                        _names.add(_sg.name.split("(", 1)[0])
                _ext[_sp] = _names
            _dark = compose.find_dark_reads(pathlib.Path(args.out), _ext)
            if _dark:
                _shown = ", ".join(f"{i}.{t}" for i, t in _dark[:6])
                _more = f" (+{len(_dark) - 6} more)" if len(_dark) > 6 else ""
                composed_loops.append((None,
                    f"DARK READ: {len(_dark)} signal(s) are READ but never DERIVED -- "
                    f"{_shown}{_more}. Their consumers were emitted and their producers "
                    f"were not, so they have no value at any instant and every property "
                    f"over them passes VACUOUSLY"))
        except Exception as e:   # noqa: BLE001
            composed_loops.append((None, f"dark-read check could not run: {e!r}"))
        flagged = [(loc, r) for d in m["specs"].values() for loc, r in d.flagged]
        flagged += composed_loops
        emit_problems = [ln[len("% PROBLEM:"):].strip()
                         for text in files.values() for ln in text.splitlines()
                         if ln.startswith("% PROBLEM:")]
        nprob = len(flagged) + len(emit_problems)
        sys.stderr.write(f"modular: {len(m['specs'])} spec(s) + manifest for top '{m['top']}'"
                         f"{f'; {nprob} PROBLEM(s)' if nprob else ''}\n")
        for loc, r in flagged:
            # a PROGRAM-LEVEL finding (the composed loop) has no single source line to
            # attach to -- it is a property of the whole composition
            where = f"{loc.file}:{loc.line}  " if loc is not None else "<composed>  "
            sys.stderr.write(f"  UNSUPPORTED {where}{r}\n")
        for r in emit_problems:
            sys.stderr.write(f"  UNSUPPORTED {r}\n")
        mwarn = [(loc, r) for d in m["specs"].values() for loc, r in d.warned]
        mwarn += [(None, ln[len("% WARNING ("):].rstrip(")"))
                  for text in files.values() for ln in text.splitlines()
                  if ln.startswith("% WARNING (")]
        for loc, r in mwarn:
            sys.stderr.write(f"  WARNING {f'{loc.file}:{loc.line}  ' if loc is not None else ''}{r}\n")
        if args.log:
            _probs = [(f"{l.file}:{l.line}" if l is not None else "<composed>", r)
                      for l, r in flagged] + [("<emit>", r) for r in emit_problems]
            _warns = [(f"{l.file}:{l.line}" if l is not None else "", r) for l, r in mwarn]
            _write_log(args.log, design=m["top"], mode="modular",
                       problems=_probs, warnings=_warns,
                       verdict=("OK" if not nprob else
                                f"FAILED -- {nprob} problem(s); the emitted program must "
                                f"not be used as a faithful translation"))
        if nprob and not args.allow_problems:
            # TWO DIFFERENT FAILURES, and the message must not confuse them -- a diagnostic
            # that names the wrong thing sends the reader to the wrong file.
            #   * an unlowered CONSTRUCT: the emitted program is INCOMPLETE; its targets
            #     have no rules and every property over them passes vacuously.
            #   * a composed LOOP: the design translated FINE and the program says what the
            #     RTL says -- the RTL is what is broken, and synthesis rejects it too.
            n_loops = len(composed_loops)
            n_lower = nprob - n_loops
            if n_lower:
                sys.stderr.write(
                    f"ERROR: {n_lower} construct(s) could not be lowered -- the emitted "
                    f"program is INCOMPLETE and its unlowered targets have NO rules. Files "
                    f"were written to '{args.out}' and must not be used; delete them, or "
                    f"re-run with --allow-problems if that is what you want.\n")
            n_pon = sum(1 for _l, r in composed_loops
                        if r.startswith("STATE WITH NO POWER-ON POLICY"))
            n_loops -= n_pon
            if n_pon:
                sys.stderr.write(
                    f"ERROR: {n_pon} state element(s) have NO power-on policy (F4). The design "
                    f"layer carries no initial state, so nothing gives these a value at t=0 and "
                    f"every property over them passes VACUOUSLY. This is a TRANSLATOR gap -- a "
                    f"stateful construct the power-on walk does not know about.\n")
            n_dark = sum(1 for _l, r in composed_loops if r.startswith("DARK READ"))
            n_loops -= n_dark
            if n_dark:
                sys.stderr.write(
                    f"ERROR: a signal is READ but never DERIVED (F2/F7). The translation "
                    f"emitted a consumer whose producer is missing, so that signal has no "
                    f"value at any instant and properties over it pass VACUOUSLY. This is a "
                    f"TRANSLATOR gap, not an RTL defect -- the construct above is one this "
                    f"tool does not yet lower in modular mode.\n")
            if n_loops:
                sys.stderr.write(
                    f"ERROR: {n_loops} combinational loop(s) in the COMPOSED design. This is "
                    f"an RTL defect -- synthesis rejects it too -- and the cycle is named "
                    f"above so it can be fixed at the source. The translation itself is "
                    f"faithful, but while the loop exists the program is not tight, so no "
                    f"completion-route claim over it is licensed.\n")
            return 1
        return 1 if (mwarn and args.strict_warnings) else 0

    # reset-snapshot operates on a single design (--top selects it; else the first).
    # emit mode translates EVERY module in the sources (or one if --top given).
    if mode == "reset-snapshot" or top is not None:
        results = [fe.parse(files, defn_files=defn_files)]
    else:
        results = fe.parse_all(files, defn_files=defn_files)
    multiple = len(results) > 1

    if multiple and args.out and not _is_dir_target(args.out):
        ap.error(f"{len(results)} modules to translate; --out must be a folder (e.g. -o out/)")

    problems = 0
    dark_reads = 0     # counted separately: a program-level finding, not a source line
    warnings = 0
    log_problems: list = []   # (where, what) for --log; flat mode loops over designs
    log_warnings: list = []
    for result in results:
        analysis = analyze(result.design, bitvec=not args.no_bitvec)
        emit_problems: list = []
        if mode == "reset-snapshot":
            snap_design = emit(result.design, analysis, k=horizon, style=style,
                               default_init=True, problems=emit_problems, primary_clock=primary_clock,
                               clock_hierarchy=clock_hierarchy)
            seq_text = None
            if args.reset_seq:
                with open(args.reset_seq) as f:
                    seq_text = f.read()
            text = snap.reset_snapshot(result.design, snap_design, k=horizon,
                                       reset_seq_text=seq_text, reset_cycles=args.reset_cycles)
            suffix = "_reset_state.lp"
        else:
            # F4: no initial state in the design layer. What the translation emits is the
            # transition relation; power-on comes from __xinit.lp (symbolic) or __init0.lp
            # (concrete), both replaceable and neither part of the translation.
            text = emit(result.design, analysis, k=horizon, style=style,
                        default_init=False, problems=emit_problems,
                        primary_clock=primary_clock, clock_hierarchy=clock_hierarchy)
            suffix = ".lp"
            if args.completion_smt:    # classical completion (SMT-LIB QF_BV) -- a transform on emit()
                text, suffix = comp.completion_smt(text, k=horizon), ".smt2"
            elif args.completion:      # explicit completion in ASP
                text = comp.completion_asp(text)

        # F14 -- DARK READS IN FLAT. The check existed only in the composed/modular path, so a
        # construct that failed to lower inside a SUBMODULE left the parent reading an atom
        # nothing derives, and flat reported `coverage: OK` with exit 0. `_check_underivable_reads`
        # does not catch it: that asks whether a name is neither DECLARED nor derived, and a
        # flattened submodule signal is declared. Same decision function as the modular check
        # (`compose.dark_terms`) so the two modes cannot drift -- hard rule 1.
        if mode != "reset-snapshot" and suffix == ".lp":
            # what only the FRONTEND knows is externally driven, mirroring the modular call:
            # a struct-typed input port emits no `port(..., input)` fact for its FIELDS.
            _ext = {sg.name for sg in result.design.signals
                    if getattr(sg, "direction", None) == "input"
                    or (getattr(getattr(sg, "loc", None), "text", "") or "").lstrip().startswith("input")}
            _ext |= {n.split("(", 1)[0] for n in _ext}
            try:
                _fdark = compose.find_dark_reads_flat(text, _ext)
            except Exception as e:  # noqa: BLE001 -- a checker fault must not pass as "clean"
                _fdark = []
                emit_problems.append((Loc("<emitted>", 0),
                                      f"dark-read check could not run: {e!r}"))
            if _fdark:
                _shown = ", ".join(_fdark[:6])
                _more = f" (+{len(_fdark) - 6} more)" if len(_fdark) > 6 else ""
                emit_problems.append((Loc("<emitted>", 0),
                    f"DARK READ: {len(_fdark)} signal(s) are READ but never DERIVED -- "
                    f"{_shown}{_more}. Their consumers were emitted and their producers were "
                    f"not, so they have no value at any instant and every property over them "
                    f"passes VACUOUSLY"))
            # F22 -- SPLIT DRIVERS. A signal driven both as a whole word and per element by
            # INDEPENDENT rules (neither one the lane<->word bridge) has two drivers that can
            # disagree, and `t34` cannot see it: `val(y, ..)` and `val(y(2), ..)` are different
            # atoms. Structural, and shared with modular (`compose.split_drivers`).
            try:
                _split = compose.split_drivers(text)
            except Exception as e:  # noqa: BLE001 -- a checker fault must not pass as "clean"
                _split = []
                emit_problems.append((Loc("<emitted>", 0),
                                      f"split-driver check could not run: {e!r}"))
            if _split:
                emit_problems.append((Loc("<emitted>", 0),
                    f"SPLIT DRIVERS: {len(_split)} signal(s) are driven BOTH as a whole word and "
                    f"per element by independent rules -- {', '.join(_split[:6])}"
                    f"{f' (+{len(_split) - 6} more)' if len(_split) > 6 else ''}. The two can "
                    f"DISAGREE and nothing arbitrates them, so a word consumer and a per-bit "
                    f"consumer of the same signal see different values"))
        # F4 -- STATE WITH NO POWER-ON POLICY. The design layer no longer supplies an initial
        # value for anything, so an element the power-on walk never considered is dark at t=0
        # and every property over it passes VACUOUSLY. Membership is re-derived from the
        # EMITTED RULES rather than from the walk's own list of construct kinds, which is what
        # makes this a check and not a restatement (see `xinit_uncovered`). Runs regardless of
        # --no-x-init: suppressing the companion does not make the state go away.
        if mode != "reset-snapshot":
            for _s in xinit_uncovered(result.design, text, not args.no_bitvec):
                emit_problems.append((Loc("<power-on>", 0),
                    f"STATE WITH NO POWER-ON POLICY: `{_s}` is held across a tick by the emitted "
                    f"rules but no power-on treatment covers it -- not a choice, not even a "
                    f"comment saying why. The translation carries no initial state (F4), so it "
                    f"is dark at t=0 and every property over it passes VACUOUSLY"))
        _write(text, result.design.name, suffix, args.out)
        # exact-X power-on companion (default ON): only for the plain-.lp routes and only when
        # writing files -- in stdout mode a second program would corrupt the stream.
        if suffix == ".lp" and args.out and x_init_on and mode != "reset-snapshot":
            xi = xinit_lp(result.design, not args.no_bitvec, text)
            if xi:
                if _is_dir_target(args.out):
                    _write(xi, result.design.name, "__xinit.lp", args.out)
                else:
                    # -o was a FILE: the companion is a sibling, never the design file itself
                    sib = (args.out[:-3] if args.out.endswith(".lp") else args.out) + "__xinit.lp"
                    with open(sib, "w") as f:
                        f.write(xi)
        # the CONCRETE power-on state, opt-in (--init-zero). Never composed unless asked for:
        # zero is arbitrary, and supplying it unasked is the defect F4 removed.
        if suffix == ".lp" and args.out and args.init_zero and mode != "reset-snapshot":
            iz = init_zero_lp(result.design, not args.no_bitvec)
            if iz:
                if _is_dir_target(args.out):
                    _write(iz, result.design.name, "__init0.lp", args.out)
                else:
                    sib = (args.out[:-3] if args.out.endswith(".lp") else args.out) + "__init0.lp"
                    with open(sib, "w") as f:
                        f.write(iz)
                    sys.stderr.write(f"wrote {sib}\n")
        # F9: the single-valuedness guard, same placement discipline as __xinit.lp above
        if suffix == ".lp" and args.out:
            _inv = state_inventory.render(result.design, text=text)
            if _is_dir_target(args.out):
                _write(_inv, result.design.name, "__state.lp", args.out)
            else:
                # -o was a FILE: the companion is a SIBLING. _write ignores the suffix for a
                # file target, so calling it here would overwrite the design program itself.
                _sib = (args.out[:-3] if args.out.endswith(".lp") else args.out) + "__state.lp"
                with open(_sib, "w") as f:
                    f.write(_inv)
        if suffix == ".lp" and args.out and not args.no_single_valued \
                and mode != "reset-snapshot":
            if _is_dir_target(args.out):
                _write(_T34_FLAT, result.design.name, "__t34.lp", args.out)
            else:
                sib = (args.out[:-3] if args.out.endswith(".lp") else args.out) + "__t34.lp"
                with open(sib, "w") as f:
                    f.write(_T34_FLAT)
                    sys.stderr.write(f"wrote {sib}\n")

        # A construct is SAFE only if fully translated. Anything the frontend flagged or the
        # emitter could not handle becomes a forced coverage problem -- never a silent OK.
        tag = f"[{result.design.name}] " if multiple else ""
        # A SYNTHETIC location (`<stub:mul8>`, `<emitted>`) means the finding is not
        # attributable to any source line -- it is about the manifest or the emitted program as
        # a whole. Coverage cannot map those, so they would be dropped silently; they are
        # counted and printed directly instead. Deduplicated because the frontend re-checks
        # per module.
        _synth, _mapped = [], []
        for loc, reason in (*result.design.flagged, *emit_problems):
            (_synth if str(loc.file).startswith("<") else _mapped).append((loc, reason))
        forced = tuple((loc.file, loc.line, reason) for loc, reason in _mapped)
        coverage = cov.compute(result.source_files, result.spans, forced, result.live_lines)
        sys.stderr.write(tag + coverage.report() + "\n")
        # WARNINGS: a faithful translation whose RESULT the reader must know about (e.g. a
        # selector its arms do not cover -> the output is unbound there). Not coverage
        # problems -- nothing was dropped -- but loud, and promotable to an error for shops
        # whose RTL rules mandate a `default` on every case.
        _warns = [*result.design.warned,
                  *((None, ln[len("% WARNING ("):].rstrip(")"))
                    for ln in text.splitlines() if ln.startswith("% WARNING ("))]
        for loc, r in _warns:
            where = f"{loc.file}:{loc.line}  " if loc is not None else ""
            sys.stderr.write(f"  WARNING {where}{r}\n")
        warnings += len(_warns)
        log_warnings += [(f"{l.file}:{l.line}" if l is not None else "", r) for l, r in _warns]
        # PROGRAM-LEVEL findings are properties of the EMITTED PROGRAM as a whole, not of any
        # one source line, so they have no coverage line to attach to and would otherwise pass
        # the gate silently. Count them directly -- neither an ungroundable program nor one
        # with a combinational loop may ever exit 0.
        _seen: set = set()
        for loc, r in _synth:
            if (loc.file, r) in _seen:
                continue
            _seen.add((loc.file, r))
            sys.stderr.write(f"  PROBLEM {loc.file}  {r}\n")
            problems += 1
            if r.startswith("DARK READ"):
                dark_reads += 1
            log_problems.append((str(loc.file), r))
        if not coverage.ok:
            problems += len(coverage.problems)
            log_problems += [(f"{getattr(c, 'file', '?')}:{getattr(c, 'line', '?')}",
                              getattr(c, "text", str(c)).strip())
                             for c in coverage.problems]

    if args.log:
        _fail = (problems and not args.allow_problems) or (warnings and args.strict_warnings)
        _write_log(args.log, design=", ".join(sorted({r.design.name for r in results})), mode="flat",
                   problems=log_problems, warnings=log_warnings,
                   verdict=(f"FAILED -- {problems} problem(s), {warnings} warning(s); the "
                            f"emitted program must not be used as a faithful translation"
                            if _fail else "OK"))
    if warnings and args.strict_warnings:
        sys.stderr.write(f"ERROR: {warnings} warning(s) (--strict-warnings)\n")
        return 1
    if problems and not args.allow_problems:
        # TWO DIFFERENT FAILURES, and the message must not confuse them -- a diagnostic that
        # names the wrong thing sends the reader to the wrong file. The modular path has made
        # this split since F1; flat said "source line(s)" for everything, which is simply wrong
        # for a finding about the emitted PROGRAM.
        if problems - dark_reads:
            sys.stderr.write(f"ERROR: {problems - dark_reads} unsupported/unaccounted source "
                             f"line(s) -- the emitted program is INCOMPLETE (F10). Re-run with "
                             f"--allow-problems if that is what you want.\n")
        if dark_reads:
            sys.stderr.write(
                "ERROR: a signal is READ but never DERIVED (F2/F7/F14). The translation "
                "emitted a consumer whose producer is missing, so that signal has no value at "
                "any instant and properties over it pass VACUOUSLY. This is a TRANSLATOR gap, "
                "not an RTL defect -- typically a construct inside a SUBMODULE that did not "
                "lower, whose consumer in the parent was emitted anyway.\n")
        return 1
    return 0


# F9 -- the SINGLE-VALUEDNESS guard. Nothing in the emitted program said that a signal has
# ONE value at an instant, so a scenario CONTRADICTING the design yielded a model in which
# one signal held two values and the run reported SATISFIABLE. `primitives_demo`'s own
# committed scenario does it: it pins a latch output to 0 where the design makes the latch
# transparent and derives 1, and `lq` comes out both 0 and 1 at three separate instants.
# Every property over such a signal is unreliable and nothing says a word.
#
# It ships as its OWN FILE rather than inside the design, because it carries a constraint
# (not a definite rule) and the design layer must stay positive-definite -- that is what
# keeps the program tight and the completion sound. A constraint has no head, so
# stratification is immediate.
#
# One rule per mode, because the atom shapes differ: modular carries the instance.
_T34_MODULAR = """% sv2asp -- the SINGLE-VALUEDNESS guard (F9).
% A signal holds exactly ONE value at each instant. Two rules with the same head -- or a
% scenario pin contradicting what the design derives -- would otherwise ground cleanly and
% give a model in which the signal is both values at once.
%
% If this fires: look for a second driver, or a scenario fact that disagrees with the
% design. Both are real defects; neither was reported before this file existed.
:- val(Inst, Sig, V1, T), val(Inst, Sig, V2, T), V1 != V2.
"""

_T34_FLAT = """% sv2asp -- the SINGLE-VALUEDNESS guard (F9). See the modular companion for the reasoning.
:- val(Sig, V1, T), val(Sig, V2, T), V1 != V2.
"""


def _write_log(path: str, *, design: str, mode: str, problems: list, warnings: list,
               verdict: str) -> None:
    """The run's findings, as a file.

    stderr scrolls away, is interleaved with other tools' output in a build, and is easy to
    miss entirely -- which is how F10 stayed unnoticed: the diagnostic WAS printed, and the
    exit code said success, so nobody read it. A log is re-readable after the fact,
    diffable between runs, and greppable by CI. The VERDICT line is last and machine-stable
    so a build step can test it directly.
    """
    lines = [f"sv2asp report", f"design : {design}", f"mode   : {mode}",
             f"problems: {len(problems)}   warnings: {len(warnings)}", ""]
    if problems:
        lines.append("PROBLEMS (each one means the emitted program is not a faithful, "
                     "complete translation):")
        for where, what in problems:
            lines.append(f"  [PROBLEM] {where}  {what}" if where else f"  [PROBLEM] {what}")
        lines.append("")
    if warnings:
        lines.append("WARNINGS (translated faithfully; a property the reader should know):")
        for where, what in warnings:
            lines.append(f"  [WARNING] {where}  {what}" if where else f"  [WARNING] {what}")
        lines.append("")
    lines.append(f"VERDICT: {verdict}")
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")
    sys.stderr.write(f"wrote {path}\n")


def _is_dir_target(out: str) -> bool:
    return os.path.isdir(out) or out.endswith(os.sep) or out.endswith("/")


def _x_init_enabled(no_x_init_flag: bool, manifest_x_init: bool | None) -> bool:
    """The x-init option combine: EITHER side may disable, NEITHER can force on -- the flag is
    a per-run opt-out, the manifest records the per-design decision, and absence of a manifest
    means the default (on). Mirrored in Lean as `Xinit.xInitEnabled`; checked against THIS
    function on every combination (proofs/gen_xinit_lean.py)."""
    return (not no_x_init_flag) and (manifest_x_init is None or manifest_x_init)


def _latches_enabled(flag: bool, manifest: bool | None) -> bool:
    """The allow_latches combine: EITHER side may enable (opt-IN, default off) -- dual to
    x-init's opt-out shape. Mirrored as `Xinit.latchesEnabled`, checked the same way."""
    return flag or bool(manifest)


def _write(text: str, name: str, suffix: str, out: str | None) -> None:
    if not out:
        sys.stdout.write(text)
        return
    out_path = out
    if _is_dir_target(out):
        os.makedirs(out, exist_ok=True)
        out_path = os.path.join(out, name + suffix)
    with open(out_path, "w") as f:
        f.write(text)
    sys.stderr.write(f"wrote {out_path}\n")


if __name__ == "__main__":
    raise SystemExit(main())
