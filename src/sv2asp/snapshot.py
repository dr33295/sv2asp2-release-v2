"""Reset-snapshot mode: run a reset sequence, snapshot the settled state, write a bridge.

The reset/initialization of a real design is a **designer-specified sequence that drives
the primary inputs in a specific order** (assert reset, release, pulse an init strobe, load
config over a bus, ...). The designer supplies that sequence (`--reset-seq FILE`); we drive
the design's own logic with it, let it settle, and snapshot every state element (registers
+ memory cells) at the final cycle. The snapshot is written as a **bridge file** of
`val(s, V, 0).` facts that a subsequent BMC run includes to initialize T=0. This generalizes
beyond reset-to-0 (init FSMs, non-zero reset values, multi-step protocols). For trivial
designs an auto fallback (assert reset for N cycles, inputs idle) is used. Default when no
bridge is used: assume 0.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import tempfile

from .ir.nodes import Design

_NAME = re.compile(r"[A-Za-z_]\w*")   # leading identifier of a val term (base name; functor or not)


def _auto_harness(design: Design, clock: str, reset_sig: str, reset_active: str,
                  inputs: list[str], reset_cycles: int) -> str:
    """Fallback reset sequence for trivial designs: assert reset N cycles, inputs idle."""
    asserted = 0 if reset_active == "low" else 1
    lines = [
        "% ---- reset-snapshot harness (auto fallback; no --reset-seq given) ----",
        f"val({reset_sig}, {asserted}, T) :- time({clock}, T), T <= {reset_cycles}.",
        f"val({reset_sig}, {1 - asserted}, T) :- time({clock}, T), T > {reset_cycles}.",
    ]
    for sig in inputs:
        lines.append(f"val({sig}, 0, T) :- time({clock}, T).  % idle input (bit)")
    return "\n".join(lines) + "\n"


def reset_snapshot(design: Design, design_text: str, *, k: int,
                   reset_seq_text: str | None = None, reset_cycles: int = 2,
                   clingo: str | None = None) -> str:
    """Run the designer's reset sequence (or an auto fallback) and return a bridge file.

    ``reset_seq_text`` is the designer-provided input-driving sequence (an .lp fragment
    that drives the primary inputs over time, referencing ``time(clk, T)``). The settled
    internal state at cycle ``k`` becomes the T=0 bridge.
    """
    if clingo is None:
        from . import config as _config
        clingo = _config.load().tool("clingo")
    if clingo is None:
        raise RuntimeError("clingo not found via CLINGO_BIN, sv2asp.toml [tools], or PATH; "
                           "needed for reset-snapshot")

    seqs = design.seq
    if not seqs or seqs[0].reset is None:
        raise RuntimeError("design has no reset; cannot run a reset sequence")
    clock = seqs[0].clock
    reset = seqs[0].reset
    state = {s.reg for s in seqs} | {m.name for m in design.mems}

    if reset_seq_text is not None:
        harness = "% ---- designer-provided reset sequence ----\n" + reset_seq_text
    else:
        inputs = [s.name for s in design.signals
                  if s.is_port and s.direction == "input"
                  and s.name not in (clock, reset.signal)]
        harness = _auto_harness(design, clock, reset.signal, reset.active, inputs, reset_cycles)
    # the run supplies the time domain (the design no longer bakes it in)
    time_domain = f"% ---- run horizon ----\n#const k = {k}.\ntime({clock}, 0..k).\n"
    prog = design_text + "\n" + time_domain + "\n" + harness

    with tempfile.NamedTemporaryFile("w", suffix=".lp", delete=False) as f:  # noqa: SIM115
        f.write(prog)
        path = f.name

    out = subprocess.run([clingo, "--outf=0", path], capture_output=True, text=True).stdout
    if "UNSATISFIABLE" in out or "SATISFIABLE" not in out:
        raise RuntimeError(f"reset-snapshot run did not settle (clingo):\n{out[:500]}")

    # snapshot: every state-signal atom at time k, re-stamped to T=0. The term may be a FUNCTOR --
    # a lane q(I) or a memory cell mem(A) / mem(A1,A2) -- so we match the leading base name against the
    # state set and rewrite only the trailing time field, leaving the (possibly nested) term intact.
    facts: list[str] = []
    seen: set[str] = set()
    suffix = f",{k})"
    for token in out.split():
        if not (token.startswith("val(") and token.endswith(suffix)):
            continue
        base = _NAME.match(token, 4)                      # identifier right after "val("
        if base is None or base.group(0) not in state:
            continue
        fact = token[: -len(suffix)] + ",0)."             # restamp time k -> 0, keep term + value
        if fact not in seen:
            seen.add(fact)
            facts.append(fact)

    facts.sort()
    seq_src = "designer reset sequence" if reset_seq_text is not None else f"auto reset ({reset_cycles} cyc)"
    header = (
        f"% Reset-state snapshot bridge for {design.name} "
        f"(via {seq_src}, settled @T={k}).\n"
        f"% Include this with a --no-default-init design to initialize T=0 from the post-reset state.\n"
    )
    return header + "\n".join(facts) + "\n"
