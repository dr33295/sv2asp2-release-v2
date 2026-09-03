"""Line-coverage map: account for EVERY source line (the auditability guarantee).

Every line of every input file is classified into one of:
  emitted     - design RTL translated to ASP (assign / always block)
  decl        - a declaration / module header (consumed by the schema)
  property    - SVA / verification (the property layer: recognized, handled
                separately, NOT a defect)
  structural  - blank line or comment
  unsupported - a design construct we recognized but cannot translate yet -> PROBLEM
  unaccounted - a code line covered by no construct                       -> PROBLEM

For *correct, in-scope design RTL* the only non-design categories should be
`property` (SVA) and `structural`. Any `unsupported`/`unaccounted` line is a real
gap and (with --strict-coverage) fails the run. `property` is never a failure.
"""

from __future__ import annotations

import os
from dataclasses import dataclass

from .frontend.base import Span

_CAT_FROM_SPAN = {"design": "emitted", "decl": "decl", "header": "decl",
                  "property": "property", "unknown": "unsupported"}
# priority when several spans overlap a line (more specific wins)
_PRIORITY = {"emitted": 5, "unsupported": 4, "property": 3, "decl": 2}
# the two categories that represent a genuine gap
_PROBLEM = {"unsupported", "unaccounted"}


@dataclass(frozen=True)
class LineStatus:
    file: str
    line: int
    status: str
    text: str


@dataclass(frozen=True)
class Coverage:
    lines: tuple[LineStatus, ...]

    @property
    def problems(self) -> tuple[LineStatus, ...]:
        """Genuine gaps: unsupported design constructs or uncovered code lines."""
        return tuple(ls for ls in self.lines if ls.status in _PROBLEM)

    @property
    def ok(self) -> bool:
        return not self.problems

    def summary(self) -> dict[str, int]:
        out: dict[str, int] = {}
        for ls in self.lines:
            out[ls.status] = out.get(ls.status, 0) + 1
        return out

    def report(self) -> str:
        s = self.summary()
        head = "  ".join(f"{k}={s[k]}" for k in sorted(s))
        verdict = "OK (no design omissions)" if self.ok else f"{len(self.problems)} PROBLEM line(s)"
        body = [f"coverage: {head}  -> {verdict}"]
        for ls in self.problems:
            body.append(f"  {ls.status.upper()} {ls.file.split('/')[-1]}:{ls.line}  {ls.text}")
        return "\n".join(body)


def _is_comment_only(line: str, in_block: bool) -> tuple[bool, bool]:
    """Return (is_comment_or_blank, in_block_after). Tracks /* */ block state."""
    s = line.strip()
    if in_block:
        return (True, "*/" not in s) if "*/" not in s else (True, False)
    if not s:
        return True, False
    if s.startswith("//"):
        return True, False
    if s.startswith("`"):  # preprocessor directive (`include/`define/`ifdef) -- consumed by the PP
        return True, False
    if s.startswith("/*"):
        return True, "*/" not in s
    return False, False


def compute(source_files: tuple[str, ...], spans: tuple[Span, ...],
            forced_problems: tuple[tuple[str, int, str], ...] = (),
            live_lines: dict[str, frozenset[int]] | None = None) -> Coverage:
    # Key by realpath: pyslang may report cwd-relative names even for absolute input.
    by_file: dict[str, dict[int, str]] = {}
    for sp in spans:
        cat = _CAT_FROM_SPAN.get(sp.category, "unsupported")
        d = by_file.setdefault(os.path.realpath(sp.file), {})
        for ln in range(sp.start, sp.end + 1):
            if _PRIORITY.get(cat, 0) >= _PRIORITY.get(d.get(ln, ""), 0):
                d[ln] = cat

    # forced problems: a construct the frontend FLAGGED or the emitter could not translate.
    # These OVERRIDE the span category (a flagged `assign` line otherwise reads as `emitted`),
    # so a partial/failed translation can never report OK -- the auditability guarantee.
    reasons: dict[tuple[str, int], str] = {}
    for file, line, reason in forced_problems:
        by_file.setdefault(os.path.realpath(file), {})[line] = "unsupported"
        reasons[(os.path.realpath(file), line)] = reason

    out: list[LineStatus] = []
    for f in source_files:
        try:
            with open(f) as fh:
                text_lines = fh.read().splitlines()
        except OSError:
            continue
        spanmap = by_file.get(os.path.realpath(f), {})
        live = (live_lines or {}).get(os.path.realpath(f))
        in_block = False
        for i, raw in enumerate(text_lines, start=1):
            comment, in_block = _is_comment_only(raw, in_block)
            if i in spanmap:
                status = spanmap[i]
            elif comment:
                status = "structural"
            elif live is not None and i not in live:
                # real-looking text with NO token in the parse = `ifdef-excluded (or otherwise dropped)
                # -> not part of THIS build, so structural (not a silent-miss `unaccounted`).
                status = "structural"
            else:
                status = "unaccounted"
            reason = reasons.get((os.path.realpath(f), i))
            text = f"{raw.strip()}  [{reason}]" if reason else raw.strip()
            out.append(LineStatus(f, i, status, text))
    return Coverage(lines=tuple(out))
