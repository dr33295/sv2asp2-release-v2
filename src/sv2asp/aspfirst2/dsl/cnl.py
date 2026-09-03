"""The controlled-English surface, desugared to the symbolic core.

The architecture is the doctrine's own (`phrasing:` writ large): every sentence pattern of
methodology Chapter 35 translates MECHANICALLY to the symbolic notation, and the existing
pipeline -- checker, emitter, certificate -- runs on the result unchanged. The core stays
dumpable, so an author can always see what their English became.

This is a CONTROLLED grammar. A sentence outside the frozen patterns is refused by name,
never guessed at: free English is the disease the route exists to cure, and a translator
that guesses is free English with extra steps.
"""
from __future__ import annotations

import re


# THE VOCABULARY AND THE CONDITION PATTERNS COME FROM THE SINGLE GRAMMAR SOURCE
# (2026-08-31, the user: "We need to keep a single grammar source"). lib/dsl/grammar.ebnf's
# surface section defines the keyword lists (SKEYWORDS structural, GKEYWORDS grammatical)
# and every condition pattern, in match order, each with executable examples. This module
# COMPILES those productions to the matchers it runs and binds each to its handler by
# name -- a production with no handler, or a handler with no production, refuses to import.
# The sigil rule: structural keywords must be written `@when`-style; the desugarer strips
# every sigil before matching, so the generated core is untouched by the spelling.

from . import grammar as _grammar
from .ebnf import _split_productions


class CnlError(Exception):
    """A sentence the frozen patterns do not cover. Says which declaration and which line."""


class SurfaceError(Exception):
    """The surface section of the grammar file and this module disagree -- refused at
    import, because a pattern with no meaning (or a meaning with no pattern) is drift."""


# ---------------------------------------------------------------- the shape compiler
def _lex_shape(rhs: str) -> list:
    toks, i = [], 0
    while i < len(rhs):
        c = rhs[i]
        if c.isspace():
            i += 1
        elif c == '"':
            j = rhs.index('"', i + 1)
            toks.append(("lit", rhs[i + 1:j]))
            i = j + 1
        elif c in "[]()|~":
            toks.append((c, c))
            i += 1
        else:
            m = re.match(r"[A-Za-z]\w*", rhs[i:])
            if not m:
                raise SurfaceError(f"unreadable shape at {rhs[i:i+20]!r}")
            toks.append(("name", m.group(0)))
            i += len(m.group(0))
    return toks


def _parse_seq(toks: list, i: int, stop: tuple) -> tuple:
    items = []
    while i < len(toks) and toks[i][0] not in stop:
        k, v = toks[i]
        if k == "lit":
            items.append(("lit", v)); i += 1
        elif k == "name":
            items.append(("term", v)); i += 1
        elif k == "~":
            items.append(("glue", None)); i += 1
        elif k == "[":
            inner, i = _parse_seq(toks, i + 1, ("]",))
            items.append(("opt", inner)); i += 1
        elif k == "(":
            arms, arm = [], []
            i += 1
            while toks[i][0] != ")":
                if toks[i][0] == "|":
                    arms.append(arm); arm = []; i += 1
                else:
                    seq, i = _parse_seq(toks, i, ("|", ")"))
                    arm.extend(seq)
            arms.append(arm)
            items.append(("alt", arms)); i += 1
        else:
            raise SurfaceError(f"unexpected {v!r} in shape")
    return items, i


def _lit_rx(text: str) -> str:
    return re.escape(text[1:] if text.startswith("@") else text)


def _term_rx(name: str, terminals: dict) -> str:
    kind, val = terminals[name]
    if kind == "rx":
        return val if re.compile(val).groups else "(" + val + ")"
    return "(" + "|".join(re.escape(x) for x in val) + ")"


def _item_rx(item, terminals: dict) -> str:
    k, v = item
    if k == "lit":
        return _lit_rx(v)
    if k == "term":
        return _term_rx(v, terminals)
    if k == "alt":
        rendered, all_lit = [], True
        for arm in v:
            if len(arm) != 1:
                raise SurfaceError("an alternation arm must be one token")
            ak, av = arm[0]
            all_lit = all_lit and ak == "lit"
            rendered.append(_lit_rx(av) if ak == "lit" else _term_rx(av, terminals))
        return "(?:" + "|".join(rendered) + ")"
    raise SurfaceError(f"cannot render {k}")


def _seq_rx(items: list, terminals: dict) -> str:
    out, glue_next = [], True          # True: no separator before the first item
    idx = 0
    for idx, item in enumerate(items):
        k, v = item
        if k == "glue":
            glue_next = True
            continue
        last = all(x[0] == "glue" for x in items[idx + 1:])
        if k == "opt":
            inner = _seq_rx(v, terminals)
            if last and out:
                rx = "(?: " + inner + ")?"     # trailing optional: leading space inside
                out.append(("" if glue_next else "") + rx)
                glue_next = False
                continue
            rx = "(?:" + inner + " )?"         # else: trailing space inside
            out.append(("" if glue_next else " ") + rx)
            glue_next = True                   # the space is already inside the group
            continue
        rx = _item_rx(item, terminals)
        out.append(("" if glue_next else " ") + rx)
        glue_next = False
    return "".join(out)


# ---------------------------------------------------------------- loading the section
def _load_surface(text: str | None = None) -> tuple:
    """(structural, grammatical, patterns) from the grammar file's surface section.
    patterns = [(name, compiled_regex, examples)]; examples = [(entity|None, sample,
    expected)] parsed from the `ex:` comment lines under each production."""
    slice_ = _grammar.surface_slice(text)
    prods = dict(_split_productions(slice_))

    def words(rhs: str) -> tuple:
        return tuple(m.group(1) for m in re.finditer(r'"([^"]+)"', rhs))

    structural = tuple(w[1:] for w in words(prods["SKEYWORDS"]))
    grammatical = words(prods["GKEYWORDS"])

    terminals = {}
    for name, rhs in prods.items():
        if name.startswith("cond") or name in ("SKEYWORDS", "GKEYWORDS"):
            continue
        rhs = rhs.strip()
        if rhs.startswith("/"):
            terminals[name] = ("rx", rhs[1:rhs.rindex("/")])
        else:
            terminals[name] = ("alts", list(words(rhs)))

    patterns, cur, examples = [], None, {}
    for raw in slice_.splitlines():
        m = re.match(r"^(cond\w+)\s*::=\s*(.*)$", raw)
        if m:
            cur = m.group(1)
            examples[cur] = []
            continue
        m = re.match(r'^#\s+ex(?:\(entity=(\w+)\))?:\s+"([^"]*)"\s+=>\s+(.*)$', raw)
        if m and cur:
            examples[cur].append((m.group(1), m.group(2), m.group(3).rstrip()))
    for name, rhs in prods.items():
        if not name.startswith("cond"):
            continue
        items, _ = _parse_seq(_lex_shape(rhs), 0, ())
        patterns.append((name, re.compile(_seq_rx(items, terminals)), examples.get(name, [])))
    return structural, grammatical, patterns


STRUCTURAL, GRAMMATICAL, _PATTERNS = _load_surface()
KEYWORDS = STRUCTURAL + GRAMMATICAL

# the declaration openers are @-words of the file format, not of the sentence vocabulary
_CONSTRUCTS = ("assume", "state", "define", "behavior", "property", "scenario", "index")

_BARE_STRUCTURAL = re.compile(r"(?<!@)\b(" + "|".join(STRUCTURAL) + r")\b")


def sigil_problems(text: str) -> list:
    """The sigil rule, checked BEFORE stripping (afterwards nobody can tell which words
    carried one). Comment lines are free English and exempt; everything else is the
    controlled surface."""
    probs = []
    for n, raw in enumerate(text.splitlines(), 1):
        line = raw.rstrip()
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        for m in re.finditer(r"@(\w+)", line):
            w = m.group(1)
            if w not in KEYWORDS and w not in _CONSTRUCTS:
                probs.append(f"line {n}: '@{w}' is not a keyword of the surface"
                             f" (`sv2asp2 keywords` lists the vocabulary)")
        for m in _BARE_STRUCTURAL.finditer(line):
            # a structural keyword APPLIED to something is a relation, not the keyword:
            # `next(P)` is the pointer vocabulary's successor, and demanding `@next(P)`
            # there would be demanding the temporal marker in a value position. A counter
            # that simply advances had no spelling at all until this carve-out (the second
            # block's finding, 2026-09-01).
            if line[m.end():m.end() + 1] == "(":
                continue
            probs.append(f"line {n}: the structural keyword '{m.group(1)}' must be"
                         f" written '@{m.group(1)}'")
    return probs


def _strip_sigils(text: str) -> str:
    return re.sub(r"@(\w+)",
                  lambda m: m.group(1) if m.group(1) in KEYWORDS else m.group(0), text)


# entry adjectives with meanings of their own: `live` is existence, `prefetch`/`demand` are
# the entry's current class, `non-X` negates. Block vocabulary -- noted as such in the
# grammar file.
def _adjs(words: str, v: str) -> list:
    out = []
    for w in (words or "").split():
        w = w.strip()
        if not w or w in ("entry", "entries"):
            continue
        if w == "live":
            out.append(f"exists({v})")
        elif w == "demanding" or w == "demand":
            out.append(f"demanding({v})")
        elif w == "prefetch":
            out.append(f"!demanding({v})")
        elif w.startswith("non-"):
            out.append(f"!{w[4:]}({v})")
        else:
            out.append(f"{w}({v})")
    return out


def _attrs(text: str) -> str:
    """`E.w` where w is not an entry attribute is the value vocabulary: E.lineData is
    lineData(E). Only `address` and `tag` are attributes an entry carries."""
    # `address`, `tag`, `isDemand` and `data` are PAYLOAD fields -- `D.data` is the forward's
    # data wire, and rewriting it into vocabulary `data(D)` minted a free window the solver
    # cheerfully abused. Everything else (`E.lineData`) is the value vocabulary.
    return re.sub(r"\b([A-Z]\w*)\.(?!address\b|tag\b|isDemand\b|data\b)(\w+)\b",
                  lambda m: f"{m.group(2)}({m.group(1)})", text)


#: FACTS ABOUT THE FILE BEING DESUGARED, read by every handler's context. `desugar`
#: fills this before it dispatches and it is not reentrant -- one file at a time, which is
#: what lets the five handlers keep their (name, lines) signatures. Two things live here,
#: both of them things the miss queue never needed and the second block did: the file's
#: OWN reset expression (an active-high `reset` is not the worked example's `!resetN`),
#: and the scalar `@state` names, which an effect may assign.
_FILE: dict = {"reset": None, "states": ()}


class _Ctx:
    def __init__(self, reset_guard: str | None = None, states: tuple | None = None):
        self.payload = {}          # var -> interface, for `accepted` and class adjectives
        self.entity = None         # the current entity var, for `it`
        self.fresh = 0
        self.reset_guard = reset_guard if reset_guard is not None else _FILE["reset"]
        self.states = states if states is not None else _FILE["states"]

    def new(self) -> str:
        self.fresh += 1
        return f"X{self.fresh}"


def _cond(line: str, ctx: _Ctx) -> str:
    """One condition clause to symbolic. The patterns come from the grammar file, in its
    order; first match wins."""
    t = _attrs(line.strip().rstrip("."))
    for name, rx, _ in _PATTERNS:
        m = rx.fullmatch(t)
        if m:
            return HANDLERS[name](m, ctx)
    raise CnlError(f"no frozen pattern covers the condition: {line.strip()!r}")


# ---------------------------------------------------------------- the handlers
# What each pattern MEANS in the core. Bound to the grammar file's productions by name;
# the import-time check below refuses a mismatch in either direction.

def _h_valid_class_request_is_repeat(m, ctx):
    ctx.payload[m.group(2)] = "request"
    return f"request.valid({m.group(2)}) && repeatDemand({m.group(2)})"


def _h_valid_class_request_arrives(m, ctx):
    ctx.payload[m.group(2)] = "request"
    return f"request.valid({m.group(2)}) && {m.group(2)}.isDemand == " \
           f"{1 if m.group(1) == 'demand' else 0}"


def _h_class_arrives(m, ctx):
    ctx.payload[m.group(2)] = "request"
    out = f"request.valid({m.group(2)}) && {m.group(2)}.isDemand == " \
          f"{1 if m.group(1) == 'demand' else 0}"
    if m.group(3):
        out += f" && {m.group(2)}.address == {m.group(3)}"
    return out


def _h_non_repeat_demand_valid(m, ctx):
    ctx.payload[m.group(1)] = "request"
    return f"request.valid({m.group(1)}) && {m.group(1)}.isDemand == 1 " \
           f"&& !repeatDemand({m.group(1)})"


def _h_iface_valid_not_accepted(m, ctx):
    ctx.payload[m.group(2)] = m.group(1)
    return f"{m.group(1)}.valid({m.group(2)}) && !accepted({m.group(2)})"


def _h_still_valid_unchanged(m, ctx):
    return f"request.valid({m.group(1)}) && $stable({m.group(1)})"


def _h_iface_var_arrives(m, ctx):
    ctx.payload[m.group(2)] = m.group(1)
    return f"{m.group(1)}.arrives({m.group(2)})"


def _h_iface_arrives(m, ctx):
    return f"{m.group(1)}.arrives"


def _h_no_iface(m, ctx):
    return f"!{m.group(1)}.arrives"


def _h_iface_taken(m, ctx):
    ctx.payload[m.group(2)] = m.group(1)
    return f"{m.group(1)}.taken({m.group(2)})"


def _h_fill_eventually(m, ctx):
    return f"s_eventually({m.group(1)}.arrives(F) && F.address == {m.group(2)})"


def _h_entry_with_address_exists(m, ctx):
    v = ctx.new()
    return "some entry " + v + " where " + \
           " && ".join(_adjs(m.group(1), v) + [f"{v}.address == {m.group(2)}"])


def _h_entry_that_verb_exists(m, ctx):
    v = ctx.new()
    return f"some entry {v} where {m.group(1)}({v}) && {v}.address == {m.group(2)}"


def _h_no_entry_has(m, ctx):
    v = ctx.new()
    return "!some entry " + v + " where " + \
           " && ".join(_adjs(m.group(1), v) + [f"{v}.address == {m.group(2)}"])


def _h_no_entry_verb(m, ctx):
    v = ctx.new()
    return "!some entry " + v + " where " + \
           " && ".join(_adjs(m.group(1), v) + [f"{m.group(2)}({v})"])


def _h_entry_has(m, ctx):
    v = ctx.new()
    return "some entry " + v + " where " + \
           " && ".join(_adjs(m.group(1), v) + [f"{v}.address == {m.group(2)}"])


def _h_one_or_more_exist(m, ctx):
    v = ctx.new()
    return "some entry " + v + " where " + " && ".join(_adjs(m.group(1), v))


def _h_is_demand(m, ctx):
    return f"{m.group(1)}.isDemand == 1"


def _h_is_prefetch(m, ctx):
    return f"{m.group(1)}.isDemand == 0"


def _h_is_repeat(m, ctx):
    return f"repeatDemand({m.group(1)})"


def _h_is_not_repeat(m, ctx):
    return f"!repeatDemand({m.group(1)})"


def _h_exists(m, ctx):
    return f"exists({m.group(1)})"


def _h_is_not_adj(m, ctx):
    return f"!{m.group(2)}({m.group(1)})"


def _h_is_adj(m, ctx):
    w = m.group(2)
    return f"!{w[4:]}({m.group(1)})" if w.startswith("non-") else f"{w}({m.group(1)})"


def _h_bare_is_adj(m, ctx):
    if ctx.entity is None:
        raise CnlError("`is ...` with nothing to refer to")
    w = m.group(1)
    return f"!{w[4:]}({ctx.entity})" if w.startswith("non-") else f"{w}({ctx.entity})"


def _h_var_verb(m, ctx):
    v = m.group(1) or ctx.entity
    if v is None:
        raise CnlError("`it` with nothing to refer to")
    return f"{m.group(2)}({v})"


def _h_while(m, ctx):
    return _cond(m.group(1), ctx)


def _h_must_be_gone(m, ctx):
    return f"!exists({m.group(1)})"


def _h_iface_ready(m, ctx):
    return f"{m.group(1)}.ready"


def _h_iface_high(m, ctx):
    return f"{m.group(1)}.high"


def _h_iface_must_not_valid(m, ctx):
    return f"!{m.group(1)}.valid"


def _h_iface_low(m, ctx):
    return f"!{m.group(1)}.high"


def _h_must_be_num(m, ctx):
    return f"{m.group(1)} == {m.group(2)}"


def _h_field_equals(m, ctx):
    return f"{m.group(1)}.{m.group(2)} == {m.group(3)}"


def _h_expr_equals(m, ctx):
    return f"{m.group(1)} == {m.group(2)}"


def _h_bare_name(m, ctx):
    return m.group(0)          # a nullary definition or counter: roomForDemand, liveEntries


def _h_comparison(m, ctx):
    return m.group(0)          # already-symbolic comparisons pass through


HANDLERS = {
    "condValidClassRequestIsRepeat": _h_valid_class_request_is_repeat,
    "condValidClassRequestArrives": _h_valid_class_request_arrives,
    "condClassArrives": _h_class_arrives,
    "condNonRepeatDemandValid": _h_non_repeat_demand_valid,
    "condIfaceValidNotAccepted": _h_iface_valid_not_accepted,
    "condStillValidUnchanged": _h_still_valid_unchanged,
    "condIfaceVarArrives": _h_iface_var_arrives,
    "condIfaceArrives": _h_iface_arrives,
    "condNoIface": _h_no_iface,
    "condIfaceTaken": _h_iface_taken,
    "condFillEventually": _h_fill_eventually,
    "condEntryWithAddressExists": _h_entry_with_address_exists,
    "condEntryThatVerbExists": _h_entry_that_verb_exists,
    "condNoEntryHas": _h_no_entry_has,
    "condNoEntryVerb": _h_no_entry_verb,
    "condEntryHas": _h_entry_has,
    "condOneOrMoreExist": _h_one_or_more_exist,
    "condIsDemand": _h_is_demand,
    "condIsPrefetch": _h_is_prefetch,
    "condIsRepeat": _h_is_repeat,
    "condIsNotRepeat": _h_is_not_repeat,
    "condExists": _h_exists,
    "condIsNotAdj": _h_is_not_adj,
    "condIsAdj": _h_is_adj,
    "condBareIsAdj": _h_bare_is_adj,
    "condVarVerb": _h_var_verb,
    "condWhile": _h_while,
    "condMustBeGone": _h_must_be_gone,
    "condIfaceReady": _h_iface_ready,
    "condIfaceHigh": _h_iface_high,
    "condIfaceMustNotValid": _h_iface_must_not_valid,
    "condIfaceLow": _h_iface_low,
    "condMustBeNum": _h_must_be_num,
    "condFieldEquals": _h_field_equals,
    "condExprEquals": _h_expr_equals,
    "condBareName": _h_bare_name,
    "condComparison": _h_comparison,
}

def _require_bound(patterns: list) -> None:
    """Refuse a file/handler mismatch and a pattern with no witness -- called at import
    on the real file, and by the gate on sabotaged copies."""
    file_names = {n for n, _, _ in patterns}
    if file_names != set(HANDLERS):
        raise SurfaceError(
            "the grammar file and the handlers disagree: "
            f"file-only {sorted(file_names - set(HANDLERS))}, "
            f"handler-only {sorted(set(HANDLERS) - file_names)}")
    no_example = [n for n, _, ex in patterns if not ex]
    if no_example:
        raise SurfaceError(f"patterns with no executable example: {no_example}")


_require_bound(_PATTERNS)

SURFACE_EXAMPLES = [(n, ent, sample, expected)
                    for n, _, exs in _PATTERNS for ent, sample, expected in exs]


def _join(lines: list, ctx: _Ctx) -> str:
    """Condition lines to one expression: leading `and` conjoins, `or` disjoins with the
    previous item, `either` opens a group every following `or` extends."""
    items, either = [], False
    for raw in lines:
        t = raw.strip()
        if not t:
            continue
        if t.startswith("and either "):
            either = True
            items.append([_cond(t[len("and either "):], ctx)])
        elif t.startswith("either "):
            either = True
            items.append([_cond(t[len("either "):], ctx)])
        elif t.startswith("or "):
            if not items:
                raise CnlError("`or` with nothing before it")
            items[-1].append(_cond(t[3:], ctx))
        elif t.startswith("and "):
            items.append([_cond(t[4:], ctx)])
        else:
            items.append([_cond(t, ctx)])
    parts = []
    for it in items:
        parts.append(it[0] if len(it) == 1 else "(" + " || ".join(it) + ")")
    return " && ".join(parts)


# ================================================================== declarations
def _blocks(text: str) -> list:
    """(kind, name, body-lines) per declaration; passthrough lines keep kind None."""
    out, cur = [], None
    for raw in text.splitlines():
        line = raw.rstrip()
        if line.lstrip().startswith("#"):
            continue
        m = re.match(r"^@(\w+)\s+(\w+)(?:\([A-Z]\w*(?:,\s*[A-Z]\w*)*\))?\s*$", line)
        if m:
            cur = (m.group(1), m.group(2), [])
            out.append(cur)
            continue
        m = re.match(r"^@(state|index)\s+(.*)$", line)
        if m:
            # `@index` was accepted by the core and documented as core notation, but the
            # desugarer did not know it, so a block needing N of something could not
            # declare the domain at the surface at all. The miss queue never noticed
            # because `entry` is built-in vocabulary (the second block's finding,
            # 2026-09-01).
            out.append((None, None, [f"@{m.group(1)} {m.group(2)}"]))
            cur = None
            continue
        if line.strip().startswith("disable iff"):
            out.append((None, None, [line.strip()]))
            cur = None
            continue
        if cur is not None:
            cur[2].append(line)
        elif line.strip():
            raise CnlError(f"a line belonging to no declaration: {line.strip()!r}")
    return out


def _define(name: str, lines: list) -> str:
    ctx = _Ctx()
    body = [l for l in lines if l.strip()]
    text = " ".join(l.strip() for l in body)
    m = re.match(r"^there is (\w+) when (.*)$", text)
    if m:
        return f"@define {name}\n  holds when {m.group(2)}"
    m = re.match(rf"^{name} when (.*)$", text)
    if m:
        return f"@define {name}\n  holds when {m.group(1)}"
    m = re.match(r"^([A-Z]\w*) is (\w+) while (.*)$", text)
    if m:
        v, cond = m.group(1), m.group(3)
        ctx.entity = v
        parts = re.split(r"\s+or\s+", cond)
        return f"@define {name}({v})\n  holds when " + \
               " || ".join(_cond(p, ctx) for p in parts)
    m = re.match(r"^([A-Z]\w*) is (?:a )?(\w+) when (.*)$", text)
    if m:
        v = m.group(1)
        ctx.entity = v
        rest = [m.group(3)] + [l.strip() for l in body[1:]] if "\n" else None
    # the multi-line `V is a NAME when` / `V is NAME when` shape
    first = body[0].strip()
    m = re.match(rf"^([A-Z]\w*) is (?:a )?{name} when$", first)
    if m:
        v = m.group(1)
        ctx.entity = v
        return f"@define {name}({v})\n  holds when " + _join(body[1:], ctx)
    m = re.match(rf"^([A-Z]\w*) is {name} when$", first)
    if m:
        v = m.group(1)
        ctx.entity = v
        return f"@define {name}({v})\n  holds when " + _join(body[1:], ctx)
    raise CnlError(f"@define {name}: no frozen shape matches {first!r}")


def _property(name: str, lines: list) -> str:
    ctx = _Ctx()
    body = [l.strip() for l in lines if l.strip()]
    text = " ".join(body)

    # A QUANTIFIER OVER A DECLARED DOMAIN, as a block. Every quantifier pattern in this
    # file names `entry`, the miss queue's built-in kind, so a block that declares its own
    # domain -- `@index bit : dataBits` -- had nothing that could range over it, and the
    # claim the domain exists to carry could not be written at the surface at all. The
    # core has always taken `each bit J ( ... )`; this is its English (the second block's
    # G8, 2026-09-02).
    m = re.match(r"^every (\w+) ([A-Z]\w*)\s*:$", body[0]) if body else None
    if m:
        kind, var = m.group(1), m.group(2)
        ctx.entity = var
        inner = body[1:]
        if not inner:
            raise CnlError(f"@property {name}: `every {kind} {var}:` with nothing under it")
        if inner[0].startswith("when "):
            ant_lines, cons_lines, in_then = [], [], False
            for l in inner:
                if l == "then" or l.startswith("then "):
                    in_then = True
                    rest = l[4:].strip() if l.startswith("then ") else ""
                    if rest:
                        cons_lines.append(rest)
                    continue
                (cons_lines if in_then else ant_lines).append(
                    l[5:] if l.startswith("when ") else l)
            arrow, cons = _consequent(cons_lines, ctx, f"@property {name}")
            claim = f"{_join(ant_lines, ctx)}\n    {arrow} " + cons
        else:
            if inner[0].startswith("always "):          # the explicit spelling, same meaning
                inner = [inner[0][len("always "):]] + inner[1:]
            claim = "always " + _join(inner, ctx)
        return f"@property {name}\n  each {kind} {var} (\n    {claim}\n  )"

    m = re.match(r"^every ([\w -]*?)entry ([A-Z]\w*) must, within the next (\w+) cycles?, "
                 r"be (\w+), stop (\w+), or end$", text)
    if m:
        v = m.group(2)
        ant = " && ".join([f"exists({v})"] + _adjs(m.group(1), v))
        return (f"@property {name}\n  each entry {v} (\n    {ant}\n"
                f"    |-> ##[1:{m.group(3)}] ( (exists({v}) && {m.group(4)}({v})) "
                f"|| !{m.group(5)}({v}) || !exists({v}) )\n  )")

    m = re.match(r"^a live entry must never be in more than one of these states at once: "
                 r"(\w+) (\w+) (\w+)$", text)
    if m:
        a, b, c = m.groups()
        return (f"@property {name}\n  each entry E (\n    exists(E)\n"
                f"    |-> !({a}(E) && {b}(E)) && !({a}(E) && {c}(E)) "
                f"&& !({b}(E) && {c}(E))\n  )")

    m = re.match(r"^once a live entry stops wanting a fetch "
                 r"it must not want another fetch before it ends$", text)
    if m:
        return (f"@property {name}\n  each entry E (\n    exists(E) && !wantsFetch(E)\n"
                f"    |=> !exists(E) || !wantsFetch(E)\n  )")

    m = re.match(r"^when forward(?: ([A-Z]\w*))? answers entry ([A-Z]\w*)\s+then (.*)$", text)
    if m:
        d = m.group(1) or "D"
        e = m.group(2)
        ctx.entity = e
        cons = " && ".join(_cond(p, ctx) for p in re.split(r"\s+and\s+", m.group(3)))
        delayed = ""
        if "must be gone next cycle" in m.group(3):
            cons, delayed = f"!exists({e})", "##1 "
        return (f"@property {name}\n  forward.valid({d})\n"
                f"  |-> each entry {e} where corresponds({d}, {e}): {delayed}{cons}")

    m = re.match(r"^every forward must answer exactly one ([\w -]*?)entry$", text)
    if m:
        conds = " && ".join(["corresponds(D, E)"] + _adjs(m.group(1), "E"))
        return (f"@property {name}\n  forward.valid(D)\n"
                f"  |-> exactly(1, some entry E where {conds})")

    m = re.match(r"^every forwarded entry must be (\w+)$", text)
    if m:
        return (f"@property {name}\n  forward.valid(D)\n"
                f"  |-> each entry E where corresponds(D, E): {m.group(1)}(E)")

    m = re.match(r"^two different ([\w -]*?)entries must never have the same address$", text)
    if m:
        a = " && ".join(["E != P"] + _adjs(m.group(1), "E") + _adjs(m.group(1), "P"))
        return (f"@property {name}\n  each entry E, each entry P (\n"
                f"    {a} |-> E.address != P.address\n  )")

    m = re.match(r"^when (?:a |an )?memoryRequest for address ([A-Z]\w*) is taken (.*)$", text)
    if m:
        return (f"@property {name}\n  memoryRequest.taken({m.group(1)})\n"
                f"  |-> " + _cond(m.group(2), ctx))

    m = re.match(r"^while any ([\w -]*?)entry (\w+) every memoryRequest presented "
                 r"must belong to a ([\w -]*?)entry$", text)
    if m:
        u = " && ".join(_adjs(m.group(1), "U") + [f"{m.group(2)}(U)"])
        e = " && ".join([f"E.address == A"] + _adjs(m.group(3), "E"))
        return (f"@property {name}\n  memoryRequest.valid(A) && some entry U where {u}\n"
                f"  |-> some entry E where {e}")

    m = re.match(r"^(\w+) must never exceed (\w+)$", text)
    if m:
        return f"@property {name}\n  always {m.group(1)} <= {m.group(2)}"

    if body[0] == "during reset":
        # THE FILE'S OWN RESET, not the worked example's. `disable iff (X)` already says
        # "X means reset is asserted" -- active-low resets spell it `!resetN`, active-high
        # ones `reset` -- so the guard is read from the file rather than hardcoded. The
        # literal `!resetN` here meant a block whose reset is named anything else got
        # `resetN is neither a port, a reset, nor a definition` (the second block's
        # finding, 2026-09-01).
        cons = " && ".join(_cond(l, ctx) for l in body[1:])
        g = ctx.reset_guard or "!resetN"
        # ONCE, not twice: `enable iff` already says where the claim is judged, so
        # repeating the guard as the antecedent restated it in the emitted rule --
        # idempotent, but it reads as a defect to anyone reviewing the contract, and a
        # contract is meant to be read (the second block's G6, 2026-09-02).
        return (f"@property {name}\n  enable iff ({g})\n  always {cons}")

    if body[0].startswith("always "):
        # A PROPERTY WITH NO TRIGGER. The core has had `always <expr>` from the start; the
        # surface reached it only inside an `@every ... :` block with no `when`, so at top
        # level "the state is always one of the three" had to be written under a
        # tautological trigger (`@when x == 0 || x == 1`), which lowers correctly and tells
        # a reader nothing (the third block's G22, 2026-09-02). Explicit, sigiled, rather
        # than "a bare condition means always": a bare line that silently means ALWAYS is
        # the implicit reading this route keeps deciding against.
        lines = [body[0][len("always "):]] + [l[4:] if l.startswith("and ") else l
                                               for l in body[1:]]
        return f"@property {name}\n  always " + " && ".join(_cond(l, ctx) for l in lines)

    if body[0].startswith("when "):
        # `when P / and P / then Q` -- the general conditional property
        ant_lines, cons_lines, in_then = [], [], False
        for l in body:
            if l == "then" or l.startswith("then "):
                in_then = True
                rest = l[4:].strip() if l.startswith("then ") else ""
                if rest:
                    cons_lines.append(rest)
                continue
            (cons_lines if in_then else ant_lines).append(
                l[5:] if l.startswith("when ") else l)
        ant = _join(ant_lines, ctx)
        arrow, cons = _consequent(cons_lines, ctx, f"@property {name}")
        return f"@property {name}\n  {ant}\n  {arrow} {cons}"

    raise CnlError(f"@property {name}: no frozen shape matches {body[0]!r}")


def _assume(name: str, lines: list) -> str:
    ctx = _Ctx()
    body = [l.strip() for l in lines if l.strip()]
    if len(body) > 3:
        raise CnlError(f"@assume {name}: {len(body) - 3} line(s) beyond the frozen shapes -- "
                       f"nothing may be dropped silently")
    if body[0].startswith("for every entry "):
        v = body[0].split()[-1]
        ctx.entity = v
        ant = _cond(body[1], ctx)
        cons = _cond(body[2], ctx)
        return f"@assume {name}\n  each entry {v} ( {ant} |-> {cons} )"
    if body[0].startswith("while "):
        ant = _cond(body[0][6:], ctx)
        nxt = body[1]
        if nxt.startswith("next cycle "):
            return f"@assume {name}\n  {ant}\n  |=> " + _cond(nxt[len('next cycle '):], ctx)
    if body[0].startswith("when "):
        ant = _cond(body[0][5:], ctx)
        cons_line = body[1]
        cons = _cond(cons_line[5:] if cons_line.startswith("then ") else cons_line, ctx)
        return f"@assume {name}\n  {ant}\n  |-> {cons}"
    raise CnlError(f"@assume {name}: no frozen shape matches {body[0]!r}")


# ================================================================== behaviours
def _next_cycle(text: str, ctx: _Ctx) -> str:
    """`next cycle CLAUSE` / `CLAUSE next cycle` -- the clause, with `is` as CAPTURE."""
    t = text.strip()
    if t.startswith("next cycle "):
        t = t[len("next cycle "):]
    if t.endswith(" next cycle"):
        t = t[:-len(" next cycle")]
    m = re.fullmatch(r"end ([A-Z]\w*)", t)
    if m:
        return f"end {m.group(1)}"
    m = re.fullmatch(r"([A-Z]\w*)\.(\w+) is (\S+)", t)
    if m:
        return f"{m.group(1)}.{m.group(2)} = {m.group(3)}"
    # A SCALAR `@state` MAY BE ASSIGNED. The miss queue never needed this -- its every
    # effect is a predicate on an object (`E is demanding`) or a field capture
    # (`E.tag is R.tag`), because it has no scalar state -- so a block whose state IS a
    # scalar FSM had no way to say so at the surface, though the core accepted
    # `##1 phase = receiving` all along (the second block's finding, 2026-09-01).
    m = re.fullmatch(r"(\w+)(\[[^\]]+\])? (?:is|=) (.+)", t)
    if m and m.group(1) in (ctx.states or ()):
        # the right-hand side is an EXPRESSION, so a counter can advance
        # (`bitIndex = bitIndex + 1`) and an indexed window can be written
        # (`capturedBit[bitIndex] = in`) -- both refused while the pattern demanded a
        # single bare token
        return f"{m.group(1)}{m.group(2) or ''} = {m.group(3)}"
    parts = re.split(r"\s+and\s+", t)
    out = []
    for p in parts:
        p = p.strip()
        if re.fullmatch(r"[a-z]\w*", p) and ctx.entity:
            out.append(f"{p}({ctx.entity})")     # "...is demanding and wantsFetch"
        else:
            out.append(_cond(p, ctx))
    return " && ".join(out)


def _consequent(cons_lines: list, ctx: _Ctx, where: str) -> tuple:
    """A property's consequent, and the ARROW it needs.

    `then next cycle Q` is the same clause a scenario already took, and only the declaration
    keyword differed -- so a requirement that is both reset-exempt and about the next cycle
    ("after a reset cycle the phase is idle") had no spelling at all: the exempt form could
    not carry a next-cycle clause and the form that could was not exempt (the second block's
    G11, 2026-09-02).

    A consequent is next-cycle as a whole or not at all. Half of one would need two arrows,
    and silently taking the first line's would make the others mean an instant nobody wrote.
    """
    nxt = [l.startswith("next cycle ") for l in cons_lines]
    if any(nxt) and not all(nxt):
        raise CnlError(f"{where}: `next cycle` on some consequents and not others -- "
                       "a claim is about one instant, so say it of all of them or none")
    if all(nxt) and nxt:
        return "|=>", " && ".join(
            _cond(l[len("next cycle "):], ctx) for l in cons_lines)
    return "|->", " && ".join(_cond(l, ctx) for l in cons_lines)


def _entity_effect_block(lines: list, ctx: _Ctx) -> tuple:
    """`the ADJ entry E that VERBs for A / with X` followed by verb lines: a scoped-each
    effect. Returns (scope-header, ##1-conjunction)."""
    head = lines[0].strip()
    m = re.fullmatch(r"the ([\w -]*?)entry ([A-Z]\w*) that (\w+) for (\S+)", head)
    conds, v = None, None
    if m:
        v = m.group(2)
        conds = _adjs(m.group(1), v) + [f"{m.group(3)}({v})", f"{v}.address == {m.group(4)}"]
    else:
        m = re.fullmatch(r"the ([\w -]*?)entry ([A-Z]\w*) with (\S+)", head)
        if m:
            v = m.group(2)
            conds = _adjs(m.group(1), v) + [f"{v}.address == {m.group(3)}"]
    if conds is None:
        raise CnlError(f"no frozen entity shape: {head!r}")
    ctx.entity = v
    effects = []
    for l in lines[1:]:
        t = l.strip().lstrip("and ").strip()
        if not t:
            continue
        t = re.sub(r" next cycle$", "", t)
        m = re.fullmatch(r"stops? (\w+)ing a fetch", t)
        if m:
            effects.append(f"!wantsFetch({v})")
            continue
        m = re.fullmatch(r"stops? being (\w+)", t)
        if m:
            effects.append(f"!{m.group(1)}({v})")
            continue
        m = re.fullmatch(r"becomes ([\w-]+)", t)
        if m:
            effects.append(f"{m.group(1)}({v})")
            continue
        m = re.fullmatch(r"is no longer ([\w-]+)", t)
        if m:
            effects.append(f"!{m.group(1)}({v})")
            continue
        m = re.fullmatch(r"remembers (\S+) as its (\w+)", t)
        if m:
            effects.append(f"{m.group(2)}({v}) = {m.group(1)}")
            continue
        raise CnlError(f"no frozen entity-effect shape: {l.strip()!r}")
    where = " && ".join(conds)
    return f"each entry {v} where {where}", " && ".join(effects)


def _behavior(name: str, lines: list) -> str:
    ctx = _Ctx()
    body = [l for l in lines if l.strip()]
    text = "\n".join(l.strip() for l in body)

    # the biconditional: paragraphs of `a valid CLASS request R is ready exactly when ...`
    if "is ready exactly when" in text:
        out = []
        para = re.split(r"\n\s*\n", "\n".join(l.strip() for l in lines))
        for p in para:
            pls = [l for l in p.splitlines() if l.strip()]
            if not pls:
                continue
            m = re.match(r"a valid (demand|prefetch) request ([A-Z]\w*) is ready exactly when",
                         pls[0].strip())
            if not m:
                raise CnlError(f"@behavior {name}: no frozen shape {pls[0].strip()!r}")
            klass, v = m.group(1), m.group(2)
            ctx.payload[v] = "request"
            cond = _join(pls[1:], ctx)
            cls = f"request.valid({v}) && {v}.isDemand == {1 if klass == 'demand' else 0}"
            suffix = klass.capitalize()
            out.append(f"@behavior {name}{suffix}\n  {cls} && ({cond})\n  -> ready on request")
            out.append(f"@property {name}{suffix}Only\n  {cls} && request.ready\n"
                       f"  |-> {cond}")
        return "\n\n".join(out)

    # A QUANTIFIER OVER A DECLARED DOMAIN, as a block -- the same opener `@property`
    # takes. It was built for properties only, so a behaviour whose effect is per position
    # ("for every bit, hold it unless this is its turn") had no spelling: G8 was fixed in
    # one half of the language and not the other (the second block's report, 2026-09-02).
    domain = None
    m = re.match(r"^every (\w+) ([A-Z]\w*)\s*:$", body[0].strip()) if body else None
    if m:
        domain = (m.group(1), m.group(2))
        ctx.entity = m.group(2)
        body = body[1:]
        if not body:
            raise CnlError(f"@behavior {name}: `every {m.group(1)} {m.group(2)}:` "
                           "with nothing under it")

    # split trigger / effects at the `then` line
    trig_lines, eff_lines, in_then = [], [], False
    for l in body:
        t = l.strip()
        if t == "then":
            in_then = True
            continue
        if not in_then:
            trig_lines.append(t[5:] if t.startswith("when ") else t)
        else:
            eff_lines.append(l.rstrip())
    if not in_then:
        raise CnlError(f"@behavior {name}: no `then`")

    # fairness annotation: recorded, checking is Phase 3
    fairness = None
    eff_lines2 = []
    for l in eff_lines:
        m = re.match(r"\s*choose fairly among (.*)$", l)
        if m:
            fairness = m.group(1).strip()
        else:
            eff_lines2.append(l)
    eff_lines = eff_lines2

    # a NAMED per-instance entity in the trigger becomes an EACH wrapper -- the 35.1 ruling:
    # "when an entry is filled and not demanding, end it" speaks about every such entry, and
    # a witness reading would let one ending discharge all. The witness needs `choose`.
    wrapper = None            # (quant, var, conds)
    population = None         # "one or more ADJ entries exist" -- the choose constructs' pool
    trig_parts = []
    for t in trig_lines:
        t2 = t[4:] if t.startswith("and ") else t
        m = re.fullmatch(r"one or more ([\w -]*?)entr(?:y|ies) exist", t2)
        if m:
            population = m.group(1)
            continue
        m = re.fullmatch(r"(?:a |an )?([\w -]*?)entry ([A-Z]\w*) (?:has (\S+)|is ([\w -]+))",
                         _attrs(t2))
        if m and any(re.search(rf"\b{m.group(2)}\b", e) for e in eff_lines):
            v = m.group(2)
            ctx.entity = v
            conds = _adjs(m.group(1), v)
            if m.group(4):
                conds += _adjs(m.group(4).replace(" and not ", " non-")
                               .replace(" and ", " "), v)
            wrapper = ("each", v, " && ".join(conds))
            if m.group(3):
                trig_parts.append(f"{v}.address == {m.group(3)}")
            continue
        trig_parts.append(t)
    trigger = _join(trig_parts, ctx) if trig_parts else ""

    # the effect items
    items, i = [], 0
    create_var = None
    while i < len(eff_lines):
        t = eff_lines[i].strip()
        if not t:
            i += 1
            continue
        m = re.fullmatch(r"accept ([A-Z]\w*)", t)
        if m:
            items.append(f"accept {m.group(1)}")
        elif re.fullmatch(r"([A-Z]\w*) is not accepted", t):
            items.append(f"refuse {t.split()[0]}")
        elif t == "fetchStall is high":
            items.append("hold fetchStall high")
        elif t == "keep the existing entry":
            pass                                    # an explicit no-op; the frames carry it
        elif re.fullmatch(r"end ([A-Z]\w*) next cycle", t):
            items.append(f"##1 end {t.split()[1]}")
        elif t.startswith("create entry "):
            m = re.fullmatch(r"create entry ([A-Z]\w*) for address (\S+?)"
                             r"(?: with tag (\S+))?", t)
            if not m:
                raise CnlError(f"no frozen create shape: {t!r}")
            create_var = m.group(1)
            ctx.entity = create_var
            caps = [f"{create_var}.address = {m.group(2)}"]
            if m.group(3):
                caps.append(f"{create_var}.tag = {m.group(3)}")
            items.append(f"create entry {create_var}: " + ", ".join(caps))
        elif t.startswith("next cycle "):
            items.append("##1 " + _next_cycle(t, ctx))
        elif t.startswith("choose one "):
            m = re.fullmatch(r"choose one ([\w -]*?)entry ([A-Z]\w*)", t)
            if not m:
                raise CnlError(f"no frozen choose shape: {t!r}")
            v = m.group(2)
            ctx.entity = v
            wrapper = ("some", v, " && ".join(_adjs(m.group(1), v)))
            population = None          # the witness subsumes the existence line
        elif t.startswith("choose exactly one "):
            m = re.fullmatch(r"choose exactly one (?:such )?entry ([A-Z]\w*)", t)
            if not m:
                raise CnlError(f"no frozen choose shape: {t!r}")
            v = m.group(1)
            ctx.entity = v
            # `such` -- the anaphor: the population the trigger announced
            if population is None:
                raise CnlError("`such` with no antecedent description")
            conds = " && ".join(_adjs(population, v))
            inner, i2 = [], i + 1
            while i2 < len(eff_lines):
                nx = eff_lines[i2].strip()
                if nx.startswith("send forward"):
                    send, i2 = _send(eff_lines, i2, ctx)
                    inner.append(send)
                    continue
                if re.fullmatch(r"end ([A-Z]\w*) next cycle", nx):
                    inner.append(f"##1 end {nx.split()[1]}")
                    i2 += 1
                    continue
                break
            body_txt = "\n         ".join(inner)
            items.append(f"exactly(1,\n       some entry {v} where {conds} (\n"
                         f"         {body_txt}\n       ))")
            i = i2 - 1
            # the trigger keeps the population as a proposition -- "one or more exist"
            pv = ctx.new()
            pop = "some entry " + pv + " where " + " && ".join(_adjs(population, pv))
            trigger = f"{trigger} && {pop}" if trigger else pop
            population = None
        elif t.startswith("drive "):
            m = re.fullmatch(r"drive (\w+) with (\S+)", t)
            if not m:
                raise CnlError(f"no frozen drive shape: {t!r}")
            items.append(f"drive {m.group(1)} with {_attrs(m.group(2))}")
        elif t.startswith("every "):
            m = re.fullmatch(r"every ([\w -]*?)entry stops being (\w+) next cycle", t)
            if not m:
                raise CnlError(f"no frozen every-effect shape: {t!r}")
            v = ctx.new()
            w = " && ".join(_adjs(m.group(1), v))
            items.append(f"each entry {v} where {w}: ##1 !{m.group(2)}({v})")
        elif t.startswith("the "):
            j = i
            while j + 1 < len(eff_lines) and not re.match(
                    r"^\s*(accept|create|next cycle|end |drive|send|choose|every|the )",
                    eff_lines[j + 1]):
                j += 1
            scope, conj = _entity_effect_block(eff_lines[i:j + 1], ctx)
            items.append(f"{scope}:\n       ##1 {conj}")
            i = j
        else:
            raise CnlError(f"@behavior {name}: no frozen effect shape: {t!r}")
        i += 1

    if population is not None:
        pv = ctx.new()
        pop = "some entry " + pv + " where " + " && ".join(_adjs(population, pv))
        trigger = f"{trigger} && {pop}" if trigger else pop
    header = f"@behavior {name}"
    eff = "\n     ".join(items)
    out_lines = []
    if fairness:
        out_lines.append(f"  # choose fairly among {fairness}: THE FAIRNESS OBLIGATION,")
        out_lines.append(f"  # named where it arises (Chapter 35.5). Checking is Phase 3;")
        out_lines.append(f"  # the per-object bound rests on it (Chapter 34).")
    if domain and wrapper:
        raise CnlError(f"@behavior {name}: quantified over both a declared domain and an "
                       "entry -- say one of them, so which object the effect is about is "
                       "written rather than inferred")
    if domain:
        kind, v = domain
        return (header + ("\n" + "\n".join(out_lines) if out_lines else "") +
                f"\n  each {kind} {v} (\n    {trigger}\n    -> {eff}\n  )")
    if wrapper:
        quant, v, w = wrapper
        inner_trig = trigger or f"exists({v})"
        return (header + ("\n" + "\n".join(out_lines) if out_lines else "") +
                f"\n  {quant} entry {v} where {w} (\n    {inner_trig}\n    -> {eff}\n  )")
    return header + ("\n" + "\n".join(out_lines) if out_lines else "") + f"\n  {trigger}\n  -> {eff}"


def _send(lines: list, i: int, ctx: _Ctx) -> tuple:
    """`send forward answering E / with tag X / and data Y` joined into one command."""
    m = re.fullmatch(r"send forward answering ([A-Z]\w*)", lines[i].strip())
    if not m:
        raise CnlError(f"no frozen send shape: {lines[i].strip()!r}")
    v = m.group(1)
    fields, j = [], i + 1
    while j < len(lines):
        t = lines[j].strip()
        fm = re.fullmatch(r"(?:with|and) (\w+) (\S+)", t)
        if not fm:
            break
        fields.append(f"{fm.group(1)} = {_attrs(fm.group(2))}")
        j += 1
    return f"send on forward answering {v} with " + ", ".join(fields), j


# ================================================================== scenarios
def _scenario(name: str, lines: list) -> str:
    ctx = _Ctx()
    body = [l.strip() for l in lines if l.strip()]
    given, when, then_, mode, wrapper = [], [], [], None, []
    arrow = "|->"

    # A QUANTIFIER OVER A DECLARED DOMAIN, as a block -- the same opener `@property` and
    # `@behavior` take. Built for one declaration kind at a time, it reached the third one
    # last and as a CRASH rather than a refusal: the opener matched no given/when/then, so
    # `mode` stayed None and the dispatch dict raised KeyError. A per-position CLAIM was
    # expressible and a per-position EFFECT was expressible; a per-position REACHABILITY
    # QUESTION -- "every data bit is one, then a stop bit" -- was not (the second block's
    # G16, 2026-09-02).
    domain = None
    m = re.match(r"^every (\w+) ([A-Z]\w*)\s*:$", body[0]) if body else None
    if m:
        domain = (m.group(1), m.group(2))
        ctx.entity = m.group(2)
        body = body[1:]
        if not body:
            raise CnlError(f"@scenario {name}: `every {m.group(1)} {m.group(2)}:` with "
                           "nothing under it")

    for l in body:
        if l == "given" or l.startswith("given "):
            mode = "g"
            l = l[6:].strip()
        elif l.startswith("when "):
            mode = "w"
            l = l[5:].strip()
        elif l == "then next cycle" or l.startswith("then next cycle"):
            mode = "t"
            arrow = "|=>"
            l = l[len("then next cycle"):].strip()
        elif l == "then" or l.startswith("then "):
            mode = "t"
            l = l[5:].strip()
        if not l:
            continue
        if l.startswith("and "):
            l = l[4:]
        m = re.fullmatch(r"(?:a |an )?([\w -]*?)entry ([A-Z]\w*)(?: (\w+))?", _attrs(l))
        if mode == "g" and m:
            v = m.group(2)
            conds = _adjs(m.group(1), v)
            if m.group(3):
                conds.append(f"{m.group(3)}({v})")
            wrapper.append((v, conds))
            ctx.entity = v
            continue
        # a sentence may carry inline `and`; splitting only on line breaks fed the whole
        # sentence to the entity matcher, which read "prefetch R arrives and no joinable" as
        # a stack of adjectives
        if mode is None:
            # every line of a scenario belongs to `given`, `when` or `then`. A line before
            # any of them used to reach the dispatch dict with a None key and raise
            # KeyError -- a crash where a refusal belongs, which is the class this route
            # treats as always reportable
            raise CnlError(f"@scenario {name}: {l.strip()!r} comes before any `@given`, "
                           "`@when` or `@then`, so nothing says which part of the story it "
                           "belongs to")
        {"g": given, "w": when, "t": then_}[mode].extend(re.split(r"\s+and\s+", l))
    ant = [c for c in [_join(given, ctx) if given else "", _join(when, ctx) if when else ""]
           if c]
    cons_parts = []
    for l in then_:
        m = re.fullmatch(r"memoryRequest may present (\S+) before (\S+)", " ".join(then_))
        if m:
            cons_parts = [f"memoryRequest.valid({_attrs(m.group(1))})"]
            ordering = m.group(2)
            break
        m = re.fullmatch(r"([A-Z]\w*) is not accepted", l)
        if m:
            cons_parts.append(f"!accepted({m.group(1)})")
            continue
        cons_parts.append(_cond(l, ctx))
    cons = " && ".join(cons_parts)
    inner = f"{' && '.join(ant)}\n    {arrow} {cons}"
    if domain and wrapper:
        raise CnlError(f"@scenario {name}: quantified over both a declared domain and an "
                       "entry -- say one of them, so which object the story is about is "
                       "written rather than inferred")
    if domain:
        kind, v = domain
        return f"@scenario {name}\n  each {kind} {v} (\n    {inner}\n  )"
    if wrapper:
        heads = ", ".join(f"some entry {v}" for v, _ in wrapper)
        conds = " && ".join(c for _, cs in wrapper for c in cs)
        return (f"@scenario {name}\n  {heads} where {conds} (\n    {inner}\n  )")
    return f"@scenario {name}\n  {inner}"


# ================================================================== the assembler
def desugar(text: str) -> str:
    probs = sigil_problems(text)
    if probs:
        raise CnlError("the sigil rule:\n  " + "\n  ".join(probs))
    text = _strip_sigils(text)
    m = re.search(r"^\s*disable iff\s*\((.*)\)\s*$", text, re.M)
    _FILE["reset"] = m.group(1).strip() if m else None
    # an INDEXED state is still a state: the subscript sits between the name and the
    # colon, and missing it left  unassignable
    _FILE["states"] = tuple(re.findall(r"^@state\s+(\w+)(?:\[\w+\])?\s*:", text, re.M))
    out = ["# DESUGARED from the controlled-English surface by dsl/cnl.py -- the symbolic",
           "# core, dumpable and diffable. Edit the .cnl, never this.", ""]
    for kind, name, body in _blocks(text):
        if kind is None:
            out.append(body[0])
            out.append("")
            continue
        fn = {"assume": _assume, "define": _define, "property": _property,
              "behavior": _behavior, "scenario": _scenario}.get(kind)
        if fn is None:
            raise CnlError(f"@{kind} is not a declaration the surface lowers")
        out.append(fn(name, body))
        out.append("")
    core = "\n".join(out)

    # THE IMPLICIT VOCABULARY, declared. The surface uses entry-state words -- demanding,
    # wantsFetch, filled, corresponds -- without ceremony; the core requires every window
    # DECLARED so the emitter can demand it of the design. The declarations are derived by
    # scanning the core itself, so a new word in a sentence becomes a declared window
    # rather than a refusal.
    defined = set(re.findall(r"@define (\w+)", core)) | set(
        re.findall(r"@state (\w+)", core))
    builtin = {"exists", "exactly", "atMost", "atLeast", "s_eventually", "accepted",
               "next", "address", "opposite"}
    vocab = {}
    # DECLARATION lines are not vocabulary uses: `@state phase : counter(0..4)` names a
    # DOMAIN, and reading `counter(...)` there as a window minted a definition the
    # specification never had (present in the miss queue's committed core since it was
    # first generated -- unused, so harmless, but a generated artifact must not invent
    # vocabulary from a type keyword; found while fixing the second block's gaps).
    scan = "\n".join(l for l in core.splitlines()
                     if not re.match(r"\s*@(state|index)\b", l))
    for m in re.finditer(r"(?<![\w.$])([a-z]\w*)\(([^()]*)\)", scan):
        w, args = m.group(1), m.group(2)
        if w in defined or w in builtin:
            continue
        vocab.setdefault(w, args.count(",") + 1)
    if vocab:
        decls = ["", "# ---- implicit vocabulary: windows the surface's sentences imply,",
                 "# ---- declared here so the design must mount them"]
        for w in sorted(vocab):
            params = ", ".join("EDX"[i] for i in range(vocab[w]))
            decls.append(f"@define {w}({params})")
            decls.append(f"  kind: condition")
            decls.append(f"  meaning: entry-state vocabulary, implicit in the surface")
            decls.append("")
        core += "\n".join(decls)
    return core


if __name__ == "__main__":
    import sys
    if "--keywords" in sys.argv:
        print(" ".join(("@" + w if w in STRUCTURAL else w) for w in KEYWORDS))
        raise SystemExit(0)
    import pathlib
    print(desugar(pathlib.Path(sys.argv[1]).read_text()))
