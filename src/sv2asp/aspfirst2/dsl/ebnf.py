"""EBNF to lark, mechanically -- so the grammar can stay in the notation people read.

The user's requirement, stated after a wrong turn: the grammar's single source is the EBNF
in `lib/dsl/grammar.ebnf`, and lark is the ENGINE, not the notation. Lark does not read
`::=`-EBNF natively, so this module translates it -- at import, every time -- which makes
the translation part of the parser rather than a second artifact that could drift.

The mapping is small because the EBNF is regular:

    name ::= ...      a production (lowercase) or a terminal (UPPERCASE)
    { X }             ( X )*
    [ X ]             ( X )?
    "..."             a literal, unchanged
    /.../             a terminal regex, unchanged
    |  ( )            unchanged

Only the expression section is translated: productions from `expr` up to the terminals
block, plus the terminals themselves. The declaration section is commentary for the
structural pass and stays commentary.
"""
from __future__ import annotations

import re


class EbnfError(Exception):
    """The EBNF file said something this translator does not understand. Refused by name,
    because a guessed grammar is a language nobody defined."""


def _split_productions(text: str) -> list:
    """(name, rhs) pairs, in order. A production runs until the next `name ::=` line."""
    out, name, buf = [], None, []
    for raw in text.splitlines():
        # comments are WHOLE LINES only. Splitting at any `#` is quote-blind and ate the
        # "##" delay literal at its first character -- the grammar's own operator, halved
        # by the tool reading it.
        line = "" if raw.lstrip().startswith("#") else raw.rstrip()
        if not line.strip():
            continue
        m = re.match(r"^([A-Za-z]\w*)\s*::=\s*(.*)$", line)
        if m:
            if name:
                out.append((name, " ".join(buf)))
            name, buf = m.group(1), [m.group(2)]
        elif name:
            buf.append(line.strip())
    if name:
        out.append((name, " ".join(buf)))
    return out


_TOK = re.compile(r'''
      (?P<lit>"(?:[^"\\]|\\.)*")
    | (?P<rx>/(?:[^/\\]|\\.)+/)
    | (?P<name>[A-Za-z]\w*)
    | (?P<open>\{)|(?P<close>\})
    | (?P<oopen>\[)|(?P<oclose>\])
    | (?P<gopen>\()|(?P<gclose>\))
    | (?P<alt>\|)
    | (?P<ws>\s+)
''', re.X)


def _rhs_to_lark(rhs: str, terminals: set) -> str:
    out, i = [], 0
    while i < len(rhs):
        m = _TOK.match(rhs, i)
        if not m:
            raise EbnfError(f"cannot read {rhs[i:i+25]!r}")
        i = m.end()
        kind = m.lastgroup
        if kind == "ws":
            continue
        if kind == "lit":
            out.append(m.group())
        elif kind == "rx":
            out.append(m.group())
        elif kind == "name":
            n = m.group()
            out.append(n.upper() if n in terminals or n.isupper() else n)
        elif kind == "open":
            out.append("(")
            out.append("__STAR__")
        elif kind == "close":
            # close the repetition opened by { : find the matching __STAR__ marker
            out.append(")*")
        elif kind == "oopen":
            out.append("(")
            out.append("__OPT__")
        elif kind == "oclose":
            out.append(")?")
        elif kind == "gopen":
            out.append("(")
        elif kind == "gclose":
            out.append(")")
        elif kind == "alt":
            out.append("|")
    # the markers only recorded intent; position of * / ? is already at the close
    return " ".join(x for x in out if x not in ("__STAR__", "__OPT__"))


def to_lark(ebnf_text: str) -> str:
    prods = _split_productions(ebnf_text)
    if not prods:
        raise EbnfError("no productions at all")
    terminals = {n for n, _ in prods if n.isupper()}
    lines = ["// GENERATED from lib/dsl/grammar.ebnf by dsl/ebnf.py -- never edited.",
             "?start: expr"]
    for name, rhs in prods:
        lhs = name.upper() if name in terminals else name
        lines.append(f"{lhs}: {_rhs_to_lark(rhs, terminals)}")
    lines += ["%import common.WS", "%ignore WS"]
    return "\n".join(lines) + "\n"
