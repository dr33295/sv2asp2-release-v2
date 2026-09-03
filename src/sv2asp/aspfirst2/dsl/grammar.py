"""The grammar's single source -- the EBNF -- and the drift check that keeps it single.

The user's correction, after a wrong turn worth recording: the grammar STAYS in EBNF, the
notation people read and the methodology renders; lark is the ENGINE, consuming a
mechanical translation (`dsl/ebnf.py`) performed at import. For one day the lark dialect
was made the source and the EBNF was archived -- readable notation traded for tool
notation nobody asked for. Both consumers are mechanical either way; only one way keeps
the source legible.

`lib/dsl/grammar.ebnf` is the source, and BOTH consumers are now mechanically derived: lark
builds the parser from it at import (expr.py), and the methodology's grammar chapter is
rendered from it by `--write`. The predecessor (`grammar.ebnf`, archived) was one honest
step short -- the document was generated but the parser only conformed by hand, which is
the two-artifacts drift this route keeps eliminating, one level down.

The check below fails when the document and the file have come apart. The drift it guards
against is the kind nobody is looking for: an author explaining a construct in the document
has no reason to think about a parser, and vice versa; each edit is locally reasonable, and
the pair ends up disagreeing with no symptom until a specification is accepted that the
document forbids.
"""
from __future__ import annotations

import pathlib

_ROOT = pathlib.Path(__file__).resolve().parents[4]
SOURCE = _ROOT / "lib" / "dsl" / "grammar.ebnf"
DOCUMENT = _ROOT / "docs" / "spec2rtl2" / "ROUTE_METHODOLOGY.md"
_ANCHOR = "expr       ::= conj"
_SURFACE_START = "# ==== surface: the controlled-English sentence patterns"
_SURFACE_END = "# ---- expressions: the sublanguage the parser is built from"
_SURFACE_DOC_ANCHOR = "SKEYWORDS ::="


def productions(text: str | None = None) -> str:
    """The grammar itself: the source from its first rule onward (the file's prose header
    stays in the file; the declaration-shape comments are part of the grammar's story and
    are kept)."""
    raw = text if text is not None else SOURCE.read_text()
    return raw[raw.index(_ANCHOR):].rstrip() + "\n"


def surface_slice(text: str | None = None) -> str:
    """The surface section: keyword lists, surface terminals, and the condition patterns
    with their executable examples. dsl/cnl.py compiles its matchers from this; Chapter 35
    renders it verbatim."""
    raw = text if text is not None else SOURCE.read_text()
    return raw[raw.index(_SURFACE_START):raw.index(_SURFACE_END)].rstrip() + "\n"


def surface_in_document() -> str:
    doc = DOCUMENT.read_text()
    i = doc.index(_SURFACE_DOC_ANCHOR)
    return doc[i:doc.index("```", i)].rstrip() + "\n"


def surface_body(text: str | None = None) -> str:
    """The renderable part of the surface slice: from the keyword lists onward (the
    section's prose header stays in the file, like the core's)."""
    sl = surface_slice(text)
    return sl[sl.index(_SURFACE_DOC_ANCHOR):].rstrip() + "\n"


def surface_drift() -> list:
    import difflib
    try:
        a, b = surface_body().splitlines(), surface_in_document().splitlines()
    except ValueError:
        return ["the document does not contain the surface section's anchor at all"]
    if a == b:
        return []
    return list(difflib.unified_diff(a, b, "lib/dsl/grammar.ebnf (surface)",
                                     "ROUTE_METHODOLOGY.md", lineterm=""))


def render_surface_into_document() -> bool:
    doc = DOCUMENT.read_text()
    i = doc.index(_SURFACE_DOC_ANCHOR)
    j = doc.index("```", i)
    new = doc[:i] + surface_body() + doc[j:]
    if new == doc:
        return False
    DOCUMENT.write_text(new)
    return True


def in_document() -> str:
    doc = DOCUMENT.read_text()
    i = doc.index(_ANCHOR)
    return doc[i:doc.index("```", i)].rstrip() + "\n"


def drift() -> list:
    import difflib
    try:
        a, b = productions().splitlines(), in_document().splitlines()
    except ValueError:
        return ["the document does not contain the grammar's anchor at all"]
    if a == b:
        return []
    return list(difflib.unified_diff(a, b, "lib/dsl/grammar.ebnf",
                                     "ROUTE_METHODOLOGY.md", lineterm=""))


def render_into_document() -> bool:
    doc = DOCUMENT.read_text()
    i = doc.index(_ANCHOR)
    j = doc.index("```", i)
    new = doc[:i] + productions() + doc[j:]
    if new == doc:
        return False
    DOCUMENT.write_text(new)
    return True


if __name__ == "__main__":
    import sys
    if "--lark" in sys.argv:
        from . import ebnf
        print(ebnf.to_lark(SOURCE.read_text()))
        raise SystemExit(0)
    if "--write" in sys.argv:
        c = render_into_document()
        su = render_surface_into_document()
        print("document updated" if (c or su) else "document already current")
        raise SystemExit(0)
    d = drift() + surface_drift()
    if d:
        print("GRAMMAR DRIFT -- the document and lib/dsl/grammar.ebnf disagree:")
        print("\n".join(d))
        raise SystemExit(1)
    print(f"grammar OK: {len(productions().splitlines())} core + "
          f"{len(surface_body().splitlines())} surface lines, document matches")
