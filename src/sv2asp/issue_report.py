"""The issue report every command can write (`--report FILE`): the environment and the tool's
own output -- never the design. Shared by the v2 route's verbs (`sv2asp2 ... --report`) and the
translator's CLI (`sv2asp ... --report`), which had no such flag until a field reporter had to
assemble the header by hand (2026-09-03)."""
from __future__ import annotations

import datetime
import pathlib
import shutil
import subprocess
import sys


def toolchain_lines() -> list:
    """What the tool actually resolved, the way it resolves it -- the first question any
    diagnosis asks, and the one users answer least reliably from memory."""
    out = [f"python           {sys.version.split()[0]}  ({sys.executable})"]
    try:
        from .config import load as _cfg
        cfg = _cfg()
    except Exception:
        cfg = None
    for tool, probe in (("clingo", ["--version"]), ("verilator", ["--version"]), ("iverilog", ["-V"]), ("lean", ["--version"])):
        path = None
        if cfg is not None:
            try:
                path = cfg.tool(tool)
            except Exception:
                path = None
        path = path or shutil.which(tool)
        if not path:
            out.append(f"{tool:16} NOT FOUND")
            continue
        try:
            v = subprocess.run([path, *probe], capture_output=True, text=True, timeout=8)
            first = (v.stdout or v.stderr).splitlines()[0] if (v.stdout or v.stderr) else "?"
        except subprocess.TimeoutExpired:
            first = "(present, but did not answer --version in 8s)"
        except Exception as e:
            first = f"(could not run: {type(e).__name__})"
        out.append(f"{tool:16} {first}   ({path})")
    return out


def write_issue_report(path, *, tool: str, argv: list, rc: int, text: str) -> None:
    """Write the report. `tool` names the entry point (sv2asp / sv2asp2); `text` is the captured
    output of the run; `argv` the command as typed."""
    try:
        import importlib.metadata as _md
        ver = _md.version("sv2asp")
    except Exception:
        try:
            from . import __version__ as ver
        except Exception:
            ver = "unknown"
    lines = [f"# {tool} issue report",
             "# Send this file to the maintainer, with a MINIMISED probe if you can make",
             "# one. It carries the environment and the tool's own output -- not your design",
             "# (a refusal may quote the one source line it names).",
             "",
             f"when             {datetime.datetime.now().isoformat(timespec='seconds')}",
             f"tool version     {ver}",
             f"command          {tool} {' '.join(argv)}",
             f"exit status      {rc}",
             "", "## toolchain", *toolchain_lines(),
             "", "## output", text.rstrip() or "(no output)"]
    pathlib.Path(path).write_text("\n".join(lines) + "\n")
    print(f"\nissue report written to {path}", file=sys.stderr)
