"""THE ONE READER (and writer) of a lane reference's TEXT.

A lane member is spelled `x(3)`; a rolled reference inside a `def_lane` is `x(I)`, `x(I-1)`,
`x(I+1 \\ B)` (a wrap within the block of size B), with the offset and the block a number or a
parameter name. Until 2026-09-03 that spelling was known to four separate regular expressions --
the printer, two in the round trip, the bench generator -- and to the loader, which WROTE the
rolled text. A dimension added to three of four readers is the two-emitter split in miniature,
which is why every reader and the one writer now live here. Multi-dimensional members
(`x(2, 3)`, `x(R+1 \\ side, C)`) are parsed by the same function: an index list.
"""
from __future__ import annotations

import re
from dataclasses import dataclass

_IDX = re.compile(r"^\s*(?:(\d+)|([A-Za-z_]\w*)\s*([+-]\s*\w+)?)\s*(?:\\\s*(\w+))?\s*$")
_REF = re.compile(r"^(\w+)\((.+)\)$")


@dataclass(frozen=True)
class Index:
    """One index of a lane reference: a NUMBER (`const`), or a VARIABLE with an offset and an
    optional wrap block. `off` and `mod` are an int, or a parameter NAME as text ("+side",
    "-1"; "cells")."""
    const: int | None = None
    var: str | None = None
    off: str = ""            # "+1", "-side", "" -- the text after the variable
    mod: str | None = None   # the wrap block: "256", "cells", or None

    @property
    def is_const(self) -> bool:
        return self.const is not None


@dataclass(frozen=True)
class LaneRef:
    base: str
    idx: tuple[Index, ...]

    @property
    def is_member(self) -> bool:
        """Every index a number: a concrete member such as `x(3)` / `x(2, 3)`."""
        return all(i.is_const for i in self.idx)

    @property
    def members(self) -> tuple[int, ...]:
        return tuple(i.const for i in self.idx)


def parse_ref(text: str) -> LaneRef | None:
    """`x(3)` / `x(I)` / `x(I-1)` / `x(I+1 \\ B)` / `x(2, 3)` -> LaneRef, else None. The base's
    membership of the design's lanes is the CALLER's check (this reads text, it does not know
    the design)."""
    m = _REF.match(text)
    if not m:
        return None
    base, inner = m.group(1), m.group(2)
    idx = []
    for part in inner.split(","):
        im = _IDX.match(part)
        if not im:
            return None
        num, var, off, mod = im.groups()
        if num is not None:
            idx.append(Index(const=int(num)))
        else:
            idx.append(Index(var=var, off=(off or "").replace(" ", ""), mod=mod))
    return LaneRef(base, tuple(idx))


def member(base: str, *idx: int) -> str:
    """The member NAME the unrolled design uses: `x(3)`, `x(2, 3)`."""
    return f"{base}({', '.join(str(i) for i in idx)})"


def rolled(base: str, *idx: Index) -> str:
    """The rolled reference text the loader writes for the printer: `x(I-1)`, `x(I+1 \\ B)`."""
    parts = []
    for i in idx:
        if i.is_const:
            parts.append(str(i.const))
        else:
            parts.append(f"{i.var}{i.off}" + (f" \\ {i.mod}" if i.mod is not None else ""))
    return f"{base}({', '.join(parts)})"


def members_of(text: str, lanes) -> tuple[str, tuple[int, ...]] | None:
    """(base, index tuple) if `text` is a concrete member of a lane in `lanes` with the lane's
    number of axes, else None."""
    r = parse_ref(text)
    if r is None or r.base not in lanes or not r.is_member or len(r.idx) != len(axes_of(lanes, r.base)):
        return None
    return r.base, r.members


def member_of(text: str, lanes) -> tuple[str, int] | None:
    """(base, i) if `text` is a 1-D concrete member of a lane in `lanes`, else None -- the
    question the round trip and the bench ask."""
    r = parse_ref(text)
    if r is None or r.base not in lanes or len(r.idx) != 1 or not r.is_member:
        return None
    return r.base, r.idx[0].const


class LaneTable(dict):
    """`name -> (N, width, direction)` as it always was -- N the TOTAL member count -- plus
    `axes[name]`, the extents per axis: `(N,)` for a one-dimensional lane, `(side, side)` for a
    grid. A lane with more than one axis has members `g(r, c)` in row-major order (the first axis
    slowest), which is how SystemVerilog flattens packed dimensions and how the translator reads a
    nested generate back (2026-09-03)."""

    def __init__(self, *a, **k):
        super().__init__(*a, **k)
        self.axes: dict = {}
        src = a[0] if a and isinstance(a[0], LaneTable) else None
        if src is not None:
            self.axes = dict(src.axes)


def axes_of(lanes, name: str) -> tuple:
    """The per-axis extents of a lane; `(N,)` when the table carries none for it."""
    ax = getattr(lanes, "axes", {}).get(name)
    return tuple(ax) if ax else (lanes[name][0],)


def members(axes: tuple):
    """Every member index tuple of a lane with these axes, row-major (first axis slowest)."""
    import itertools
    return itertools.product(*(range(n) for n in axes))


def flat_index(idx: tuple, axes: tuple) -> int:
    """Row-major flat position of member `idx`: `pack` order, and the translator's bit order."""
    f = 0
    for i, n in zip(idx, axes):
        f = f * n + i
    return f
