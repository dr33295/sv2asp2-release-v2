"""Expressions, parsed by a GENERATED parser from the language's single grammar source.

The grammar lives in `lib/dsl/spec.lark` and nothing else defines the language: lark builds
the parser from that file at import, and the methodology's grammar chapter is rendered from
the same file. The predecessor here was a hand-written recursive-descent parser that
CONFORMED to the grammar by care -- the same two-artifacts drift this route keeps
eliminating, one level down, and the reason it is gone.

What this module still owns is the E node -- the small tree the emitter consumes -- and the
transformer that rebuilds lark's tree into it. Keeping E unchanged meant swapping the parser
changed no downstream code, and the certificate suite doubled as the swap's regression
harness.
"""
from __future__ import annotations

import dataclasses
import pathlib
import re

import lark


class ExprError(Exception):
    """An expression the language does not admit. Always says where and what was expected."""


@dataclasses.dataclass
class E:
    """One node. `op` says which, `kids` are its operands, `text` is what was written."""
    op: str                     # and or not cmp arith call ifcall field index name num quant delay
    kids: list
    text: str = ""

    def __repr__(self) -> str:
        return f"{self.op}({self.text or ''}{',' if self.kids else ''}" \
               f"{','.join(map(repr, self.kids))})"

    def walk(self):
        yield self
        for k in self.kids:
            yield from k.walk()


from . import ebnf as _ebnf

_GRAMMAR = pathlib.Path(__file__).resolve().parents[4] / "lib" / "dsl" / "grammar.ebnf"
# THE PARSER IS BUILT FROM THE EBNF: the single source stays in the notation people read,
# and lark is the engine -- dsl/ebnf.py translates at import, every time, so the
# translation is part of the parser rather than a second artifact that could drift.
# the CORE slice only: the file also carries the surface section's live productions now,
# and those belong to dsl/cnl.py's compiler, not to this parser
from . import grammar as _grammar_mod
_PARSER = lark.Lark(_ebnf.to_lark(_grammar_mod.productions()), start="start", parser="earley")


class _ToE(lark.Transformer):
    """lark's tree, rebuilt as E nodes. The rule names are the EBNF's production names --
    the converter invents nothing -- so this transformer reads like the grammar."""

    def expr(self, kids):
        e = kids[0]
        for k in kids[1:]:
            e = E("or", [e, k])
        return e

    def conj(self, kids):
        e = kids[0]
        for k in kids[1:]:
            e = E("and", [e, k])
        return e

    def candq(self, kids):
        return kids[0]

    def notq(self, kids):
        return E("not", [kids[0]])

    def cmp(self, kids):
        if len(kids) == 1:
            return kids[0]
        return E("cmp", [kids[0], kids[2]], str(kids[1]))

    def _fold(self, kids):
        e = kids[0]
        i = 1
        while i < len(kids):
            e = E("arith", [e, kids[i + 1]], str(kids[i]))
            i += 2
        return e

    arith = _fold
    term = _fold

    def unary(self, kids):
        return kids[0]

    def notx(self, kids):
        return E("not", [kids[0]])

    def delay(self, kids):
        if len(kids) == 2:
            n = str(kids[0])
            return E("delay", [kids[1]], f"{n}:{n}")
        return E("delay", [kids[2]], f"{kids[0]}:{kids[1]}")

    def bound(self, kids):
        return str(kids[0])

    def postfix(self, kids):
        e = kids[0]
        for kind, payload in kids[1:]:
            if kind == "field":
                e = E("field", [e], payload)
            elif kind == "index":
                e = E("index", [e, payload])
            else:
                if e.op == "name":
                    e = E("call", payload, e.text)
                elif e.op == "field":
                    e = E("ifcall", [e.kids[0]] + payload, e.text)
                else:
                    raise ExprError("only a name or an interface predicate takes arguments")
        return e

    def trailer(self, kids):
        return kids[0]

    def fieldtr(self, kids):
        return ("field", str(kids[0]))

    def calltr(self, kids):
        return ("call", list(kids))

    def indextr(self, kids):
        return ("index", kids[0])

    def primary(self, kids):
        return kids[0]

    def parenx(self, kids):
        return kids[0]

    def num(self, kids):
        return E("num", [], str(kids[0]))

    def var(self, kids):
        return E("name", [], str(kids[0]))

    namek = var
    named = var

    def wherep(self, kids):
        return ("where", kids[0])

    def scopep(self, kids):
        return ("scope", kids[0])

    def quantifier(self, kids):
        quant, kind, var = str(kids[0]), str(kids[1]), str(kids[2])
        where = scope = None
        for k in kids[3:]:
            tag, val = k
            if tag == "where":
                where = val
            else:
                scope = val
        return E("quant", [where, scope], f"{quant}:{kind}:{var}")


_TO_E = _ToE()


def parse_expr(s: str) -> E:
    try:
        tree = _PARSER.parse(s)
    except lark.exceptions.LarkError as e:
        first = str(e).splitlines()[0] if str(e) else "unreadable expression"
        raise ExprError(first)
    got = _TO_E.transform(tree)
    if isinstance(got, tuple):
        raise ExprError("a trailer with nothing to trail")
    return got


def strip_delay(s: str):
    """A leading `##N` or `##[a:b]`, and what follows it. Returns (lo, hi, rest)."""
    m = re.match(r"\s*\#\#\s*\[\s*(\d+)\s*:\s*(\w+)\s*\]\s*(.*)$", s, re.S)
    if m:
        return int(m.group(1)), m.group(2), m.group(3)
    m = re.match(r"\s*\#\#\s*(\d+)\s*(.*)$", s, re.S)
    if m:
        return int(m.group(1)), int(m.group(1)), m.group(2)
    return None, None, s


def split_claim(s: str):
    """A claim's three parts: antecedent, arrow, consequent. `always P` has no antecedent."""
    body = " ".join(l.strip() for l in s.splitlines() if l.strip())
    if body.startswith("always "):
        return None, "always", body[len("always "):]
    for arrow in ("|->", "|=>"):
        depth = 0
        for i in range(len(body)):
            if body[i] == "(":
                depth += 1
            elif body[i] == ")":
                depth -= 1
            elif depth == 0 and body.startswith(arrow, i):
                return body[:i].strip(), arrow, body[i + len(arrow):].strip()
    return None, None, body
