"""IR type system: atom shapes, signal kinds, and width references.

Mirrors the catalog's schema vocabulary (docs/reference/SV_TRANSLATION_CATALOG.md Group 3),
not all of SystemVerilog. Widths may be symbolic (a ``ParamRef``) so the schema
can be emitted as ``type(s, bit, W) :- param(width, W).`` per catalog Section 3.10.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum


class Shape(Enum):
    """Atom shape for a signal's ``val`` predicate (decided in Stage 2)."""

    BIT = "bit"  # val(S, V, T) -- a width-1 word; the label drives the v1/v2 boolean encoding
    WORD = "word"  # val(S, V, T)
    TAG = "tag"  # val(S, Tag, T)            -- deferred past M1
    ADDRESSED = "addressed"  # memory: val(mem(A[, A2]), V, T) -- address in the functor (like a lane),
    #                          BUT a RUNTIME address over addr(mem, A) (init/hold/RMW), not a static lane
    INDEXED = "indexed"  # lane signal: val(S(I), V, T) -- the lane index lives in the signal functor
    #                      (2-D generate -> S(I, J)); the per-lane value V keeps its own shape


class Kind(Enum):
    """Signedness/interpretation kind. Drives @func variant selection (Section 3.3)."""

    BIT = "bit"  # unsigned 2-state
    SIGNED = "signed"  # signed 2-state
    ENUM = "enum"  # deferred past M1


@dataclass(frozen=True)
class ParamRef:
    """A symbolic width: the value of parameter ``name`` at grounding time."""

    name: str


# A width is either a concrete int or a symbolic parameter reference.
Width = int | ParamRef


@dataclass(frozen=True)
class IRType:
    """Declared type of a scalar/vector signal.

    ``kind``/``width`` are the *interpretation* (signed/unsigned, bit count) the emitter needs.
    ``sv_base``/``four_state`` preserve the *declared SV type* for fidelity/provenance — the base
    keyword or ``typedef`` name (``logic``/``bit``/``int``/``data_t``) and 2-state vs 4-state — which
    kind/width otherwise collapse (``logic[7:0]`` and ``bit[7:0]`` both interpret as ``bit, 8``).
    Empty ``sv_base`` = a synthetic signal with no SV declaration (e.g. a hoisted ``gcond``)."""

    kind: Kind
    width: Width
    sv_base: str = ""        # declared base keyword / typedef name (lowercased), "" if synthetic
    four_state: bool = False  # True for 4-state (logic/reg/integer), False for 2-state (bit/int/byte)


@dataclass(frozen=True)
class ElementType:
    """Element type of an unpacked array (catalog Section 3.5)."""

    name: str
    kind: Kind
    width: Width
    #: 2-state vs 4-state, for the same reason `IRType` carries it: an uninitialised 4-state
    #: cell reads x at power-on and gets a power-on CHOICE, while LRM 6.8 gives a 2-state cell
    #: the default 0. `name` cannot answer this -- it is synthetic (`<mem>_elem`), not the
    #: declared SV base -- so the bit is carried explicitly (F4).
    four_state: bool = False
