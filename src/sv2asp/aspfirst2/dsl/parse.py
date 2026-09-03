"""Reading a `.spec` into a structure: declarations, their scopes, and where names are used.

This is a STRUCTURAL parser, and the limit is deliberate. It recovers the shape of a
specification -- which declarations exist, which quantifier scopes enclose which lines, where
each variable is bound and where it is used -- without building a full expression tree. That
shape is exactly what the cross-file checks and the scope and lifetime rules need, and it is
the half that can be built and trusted before the semantics of every operator is settled.

Two things about the file's shape matter and are worth stating before the code:

* **Indentation carries meaning.** A declaration owns the more-indented lines beneath it, and a
  quantifier block (`each entry E:`) owns the declarations beneath it. That is how a specification
  says several claims are about the same object, so the parser must keep it.
* **Scope is either parenthesised or indented**, never implicit. A `some entry E where P ( ... )`
  binds E across the parentheses; a `each entry E:` block binds it across everything beneath.
  Anywhere else, the binder's reach is its own `where` clause and nothing more.
"""
from __future__ import annotations

import dataclasses
import pathlib
import re

KEYWORDS = ("@assume", "@index", "@state", "@define", "@behavior", "@property", "@scenario")
_QUANT = re.compile(r"\b(each|some)\s+(\w+)\s+([A-Z]\w*)")
_VAR = re.compile(r"\b([A-Z]\w*)\b")
_IFACE_USE = re.compile(r"\b([a-z]\w*)\.(\w+)\s*(\(\s*([A-Z]\w*)\s*\))?")
_FIELD_USE = re.compile(r"\b([A-Z]\w*)\.(\w+)")
# words that look like variables but are not: operators, and the language's own vocabulary
_NOT_VARS = {"T", "K", "N"}


@dataclasses.dataclass
class Node:
    kind: str                 # a keyword, "quantifier", or "file"
    name: str                 # the declaration's name, or the binder's variable
    line: int                 # 1-based line of the header
    header: str               # the header line, comments stripped
    body: list                # the raw lines beneath it, comments stripped
    children: list            # nested declarations (a quantifier block's claims)
    binds: list               # variables this node binds over its children and body

    def text(self) -> str:
        return "\n".join([self.header] + self.body)

    def walk(self):
        yield self
        for c in self.children:
            yield from c.walk()


PROSE = re.compile(r"^(meaning|phrasing|description)\s*:")


def _strip(line: str) -> str:
    """Remove a trailing comment.

    `#` starts a comment and `##` is the DELAY operator, so the two collide and the split has
    to be written carefully: `## [1:depth]` is notation, `# a note` is not. Getting this wrong
    silently truncates every timed claim in a file at its delay -- which is what happened, and
    the symptom was a lifetime check that never fired because the part of the claim it was
    about had been cut off before it ever saw it.
    """
    i = 0
    while i < len(line):
        if line[i] == "#":
            if i + 1 < len(line) and line[i + 1] == "#":
                i += 2                      # the delay operator, not a comment
                continue
            return line[:i].rstrip()
        i += 1
    return line.rstrip()


def notation_of(node) -> str:
    """A node's text with its PROSE removed -- the part that is notation rather than English.

    A `meaning:` line is written for a person and may say anything: name a file, quote a
    predicate, mention an interface it does not use. Checking it as though it were notation
    reports things that are not there, which is worse than checking nothing.
    """
    keep, in_prose = [node.header], False
    for line in node.body:
        if PROSE.match(line):
            in_prose = True
            continue
        if in_prose and not re.match(r"^(holds when|kind\s*:)", line):
            continue
        in_prose = False
        keep.append(line)
    return "\n".join(keep)


def parse(path) -> Node:
    path = pathlib.Path(path)
    raw = path.read_text().splitlines()
    root = Node("file", path.name, 0, "", [], [], [])
    stack = [(-1, root)]                       # (indent of the owner's header, node)

    for n, line in enumerate(raw, 1):
        text = _strip(line)
        if not text.strip():
            continue
        indent = len(text) - len(text.lstrip())
        word = text.strip().split(None, 1)[0]
        starts = word in KEYWORDS or (word in ("each", "some") and text.rstrip().endswith(":"))
        while len(stack) > 1 and indent <= stack[-1][0]:
            stack.pop()
        if starts:
            if word in KEYWORDS:
                rest = text.strip().split(None, 2)
                name = rest[1] if len(rest) > 1 else ""
                node = Node(word, re.split(r"[(:\s]", name)[0], n, text.strip(), [], [], [])
            else:                              # a quantifier block: `each entry E:`
                m = _QUANT.search(text)
                node = Node("quantifier", m.group(3) if m else "", n, text.strip(), [], [],
                            [m.group(3)] if m else [])
            stack[-1][1].children.append(node)
            stack.append((indent, node))
        else:
            stack[-1][1].body.append(text.strip())
    return root


def binders_in(text: str) -> list:
    """Every variable a quantifier binds in this text, with whether it carries a SCOPE.

    The distinction is the language's, not a convenience: a quantifier with a scope is a witness
    binder and the scope says what it binds over; one without is a proposition, and its variable
    means nothing past its own `where` clause.
    """
    out = []
    for m in _QUANT.finditer(text):
        tail = text[m.end():]
        out.append((m.group(3), m.group(1), _scope_at(tail) is not None
                    or tail.rstrip().endswith(":"), m.start()))
    return out


def _scope_at(tail: str):
    """Where this quantifier's SCOPE opens in `tail`, or None if it has none.

    A scope's parenthesis is preceded by whitespace; a call's follows its name directly. That
    is not a trick -- it is how the two are told apart by eye as well, and it is why
    `joinable(E)` inside a `where` clause is not mistaken for a scope. The rule is lexical, so
    it costs nothing and cannot be fooled by how deeply the condition nests.
    """
    depth = 0
    for i, ch in enumerate(tail):
        if ch == "(":
            if depth == 0 and i > 0 and tail[i - 1].isspace():
                return i
            depth += 1
        elif ch == ")":
            depth = max(0, depth - 1)
    return None


def variables_in(text: str) -> set:
    """Capitalised words used as variables, minus the instants and the language's own names."""
    return {v for v in _VAR.findall(text) if v not in _NOT_VARS and not v.isupper()}


def interface_uses(text: str) -> list:
    """Every `iface.verb(Var)` in the text: (interface, verb, bound variable or None, position)."""
    return [(m.group(1), m.group(2), m.group(4), m.start()) for m in _IFACE_USE.finditer(text)]


def field_uses(text: str) -> list:
    """Every `Var.field`: (variable, field, position)."""
    return [(m.group(1), m.group(2), m.start()) for m in _FIELD_USE.finditer(text)]


def scope_span(text: str, at: int):
    """Where a quantifier's scope begins and ends, given where the quantifier starts.

    Two shapes, and both must be recognised or a correctly written rule is reported as broken:
    a parenthesised scope runs to its matching close, and a `:` scope runs to the end of the
    declaration -- which is what makes `each entry E:` bind over every claim beneath it.
    """
    tail = text[at:]
    open_at = _scope_at(tail)
    if open_at is not None:
        depth, i = 0, at + open_at
        for j in range(i, len(text)):
            if text[j] == "(":
                depth += 1
            elif text[j] == ")":
                depth -= 1
                if depth == 0:
                    return (at, j)
        return (at, len(text))
    line_end = text.find("\n", at)
    head = text[at:] if line_end < 0 else text[at:line_end]
    if head.rstrip().endswith(":") or ":" in head:
        return (at, len(text))
    return None
