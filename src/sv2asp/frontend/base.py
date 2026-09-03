"""The Frontend abstraction (dependency-inversion seam).

A frontend turns a set of SystemVerilog source files into an IR ``Design`` plus
a list of source files (for the coverage pass). pyslang is one implementation;
Surelog/UHDM or Verible could be swapped in without touching the stages/emitter.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Protocol

from ..ir.nodes import Design


@dataclass(frozen=True)
class Span:
    """Source span of a top-level construct, for the coverage map.

    ``category`` in {design, decl, header, flagged}. ``kind`` is the raw CST kind.
    """

    file: str
    start: int
    end: int
    category: str
    kind: str


@dataclass(frozen=True)
class FrontendResult:
    design: Design
    source_files: tuple[str, ...]
    spans: tuple[Span, ...] = ()
    # line numbers (per source file) that contributed a real token to the parse -- a line that is NOT
    # live is blank / comment / `directive / `ifdef-EXCLUDED, so it is structural (not `unaccounted`).
    live_lines: dict[str, frozenset[int]] = field(default_factory=dict)


class Frontend(Protocol):
    def parse(self, files: list[str]) -> FrontendResult:
        """Compile ``files`` (for cross-file binding) and lower to an IR Design."""
        ...
