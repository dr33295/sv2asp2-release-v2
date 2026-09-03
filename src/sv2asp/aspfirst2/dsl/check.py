"""The cross-file and semantic checks a specification must pass before anything is proven.

Two families, and the difference matters more than the count.

The CROSS-FILE checks exist only because the signature and the specification are separate
files. A name that resolves, a verb its interface actually has, a payload field that is really
a port -- none of these can be asked of either file alone, and every one of them would
otherwise become a silent invention at compile time.

The SEMANTIC checks come from the four decisions (methodology Chapter 33), and they share a
property worth stating: what they catch does not fail. A specification that gets one wrong
still compiles, still certifies, and simply means less than it says. Both are cheap and
syntactic -- properties of the text -- which is precisely why they are worth having, because a
solver would never report either: the contract that results is perfectly satisfiable and merely
about the wrong thing.
"""
from __future__ import annotations

import re

from . import parse as P

VERBS = {"readyValid": {"valid", "ready", "taken"},
         "validOnly":  {"valid", "arrives"}}
LEVEL_VERBS = {"high", "low"}
_ARROW = re.compile(r"\|->|\|=>|->")
_DELAY = re.compile(r"##")


class Finding:
    def __init__(self, rule: str, line: int, message: str):
        self.rule, self.line, self.message = rule, line, message

    def __str__(self) -> str:
        return f"line {self.line}: [{self.rule}] {self.message}"


def _field_port(iface: str, field: str) -> str:
    return iface + field[0].upper() + field[1:]


def check(spec_path, signature: dict) -> list:
    """Every finding, in file order. An empty list means the specification is well formed as far
    as these rules reach -- which is not the same as correct, and never claims to be."""
    root = P.parse(spec_path)
    # an @index domain has no lifetime: addresses and slots do not come and go, so asking
    # whether one still exists is a question about nothing. Only object kinds are asked.
    indexes = {n.name for n in root.walk() if n.kind == "@index"}
    #: a declared domain's extent, for checking that a subscript ranges over the right one
    extents = {}
    for n in root.walk():
        if n.kind == "@index":
            m = re.search(r"@index\s+(\w+)\s*:\s*(\S+)", n.header)
            if m:
                extents[m.group(1)] = m.group(2)
    ifaces = {i["name"]: i for i in signature.get("interfaces", [])}
    ports = {q["name"]: q for q in signature.get("ports", [])}
    levels = {q["name"] for q in signature.get("ports", []) if q.get("role") == "level"}
    out = []

    # ---- an indexed window's DOMAIN must be declared. `@state capturedBit[bit] : flag`
    # compiled happily with `bit` never declared, so the only way to write indexed state
    # was to leave its domain undeclared -- the thing the index discipline exists to
    # refuse. Found with the sibling defect that made `@index` unwritable at the surface
    # (the second block, 2026-09-01): together they made the wrong form the only form.
    # ---- an ARRAY PORT indexed by a domain of a different size. The subscript would
    # range over the wrong extent -- too few positions leaves part of the port unclaimed,
    # too many asks about elements that do not exist -- and neither shows up as an error:
    # the contract is satisfiable either way and simply says less, or something else,
    # than the author meant (the shape question, 2026-09-02).
    arrays = {q["name"]: q for q in signature.get("ports", []) if q.get("elements")}
    if arrays:
        for node in root.walk():
            if node.kind == "file":
                continue
            text_n = P.notation_of(node)
            kind_of = {v: k for _, k, v in
                       [(a, b, c) for a, b, c in
                        re.findall(r"\b(each|some)\s+(\w+)\s+([A-Z]\w*)", text_n)]}
            for port, var in re.findall(r"\b(\w+)\[([A-Z]\w*)\]", text_n):
                if port not in arrays or var not in kind_of:
                    continue
                want, got = str(arrays[port]["elements"]), extents.get(kind_of[var])
                if got is not None and str(got) != want:
                    out.append(Finding("extent", node.line,
                                       f"`{port}[{var}]` indexes an array port of {want} "
                                       f"element(s) with `{kind_of[var]}`, whose extent is "
                                       f"{got} -- the subscript would range over the wrong "
                                       f"domain, and a contract that does so is satisfiable "
                                       f"while claiming something other than you wrote"))

    # WHAT A QUANTIFIER RANGES OVER MUST BE DECLARED TOO. The subscript rule below catches
    # `@state x[nosuchDomain]`; a QUANTIFIER naming an undeclared kind fell straight through
    # it, and the consequence is silent rather than loud: an unknown kind is read as an
    # OBJECT kind, so `each nosuchDomain J` lowers to `nosuchDomainExists(J, T)` -- a window
    # no linkage will ever mount, nothing derives the atom, and every claim under the
    # quantifier is vacuously true. Green because it is dead.
    object_kinds = {"entry"}
    for n in root.walk():
        t = P.notation_of(n)
        object_kinds |= set(re.findall(r"\bcreate\s+(\w+)\s+[A-Z]", t))
        m = re.search(r"@state\s+\w+\s*(?:\[\w+\])?\s*:\s*(?:set|transaction|index)\s+of\s+(\w+)",
                      n.header)
        if m:
            object_kinds.add(m.group(1))
    for node in root.walk():
        if node.kind == "file":
            continue
        text = P.notation_of(node)
        for var, _quant, _scoped, _at in P.binders_in(text):
            kind = _kind_of(text, var)
            if kind and kind not in indexes and kind not in object_kinds:
                out.append(Finding("domain", node.line,
                                   f"`each {kind} {var}` ranges over `{kind}`, which no "
                                   f"`@index {kind} : <extent>` declares and no object is "
                                   f"created of. An unknown kind is read as an OBJECT kind, "
                                   f"so this quantifier asks the design for a window nothing "
                                   f"mounts -- and every claim under it is then vacuously "
                                   f"true rather than refused"))

    for node in root.walk():
        if node.kind != "@state":
            continue
        m = re.search(r"@state\s+\w+\[(\w+)\]", node.header)
        if m and m.group(1) not in indexes:
            out.append(Finding("index", node.line,
                               f"`{m.group(1)}` subscripts this state but no `@index "
                               f"{m.group(1)} : <extent>` declares it -- an indexed window "
                               f"must say what it is indexed BY, or nothing bounds the "
                               f"domain the design has to mount"))

    for node in root.walk():
        if node.kind in ("file",):
            continue
        text = P.notation_of(node)
        enclosing = _enclosing_binders(root, node)

        # ---- cross-file: names, verbs, direction ------------------------------------------
        iface_bound = {}
        for name, verb, var, _ in P.interface_uses(text):
            if name in ifaces:
                allowed = VERBS[ifaces[name]["protocol"]]
                if verb not in allowed:
                    out.append(Finding("verb", node.line,
                        f"`{name}.{verb}` -- {name} is {ifaces[name]['protocol']}, whose verbs "
                        f"are {sorted(allowed)}. A verb its protocol does not have would "
                        f"resolve to wires that are not in the signature"))
                if var:
                    iface_bound[var] = name
            elif name in levels:
                if verb not in LEVEL_VERBS:
                    out.append(Finding("verb", node.line,
                        f"`{name}.{verb}` -- {name} is a level output, whose verbs are "
                        f"{sorted(LEVEL_VERBS)}"))
            elif name in ports:
                out.append(Finding("name", node.line,
                    f"`{name}.{verb}` -- {name} is a port, not an interface. A property speaks "
                    f"of an interface by name, or of a level output with high/low"))
            elif name not in ("s_eventually",) and not name.startswith("$"):
                out.append(Finding("name", node.line,
                    f"`{name}.{verb}` -- nothing in the signature declares {name!r}"))

        for m in re.finditer(r"\b(drive|send on|ready on)\s+(\w+)", text):
            verb, target = m.group(1), m.group(2)
            i = ifaces.get(target)
            if i is None and target not in ports:
                out.append(Finding("name", node.line,
                    f"`{verb} {target}` -- nothing in the signature declares {target!r}"))
            elif i is not None:
                if verb in ("drive", "send on") and i["side"] != "sends":
                    out.append(Finding("direction", node.line,
                        f"`{verb} {target}` -- {target} is a {i['side']} interface. Its wires "
                        f"belong to the environment; constraining one is an @assume"))
                if verb == "ready on" and i["side"] != "receives":
                    out.append(Finding("direction", node.line,
                        f"`ready on {target}` -- {target} is a {i['side']} interface, so there "
                        f"is nothing here to be ready for"))

        # ---- cross-file: a payload field must really be a port ----------------------------
        for var, field, _ in P.field_uses(text):
            iface = iface_bound.get(var)
            if iface is None:
                continue                        # an object's attribute, not an interface payload
            want = _field_port(iface, field)
            if want not in ports:
                out.append(Finding("field", node.line,
                    f"`{var}.{field}` -- {var} is bound to the {iface} interface, which has no "
                    f"port {want!r}. A misspelled field would otherwise become a fresh free "
                    f"variable, and the claim would hold for a reason nobody intended"))

        # ---- one variable, two binders: shadowing, and it is always a mistake -------------
        binders = P.binders_in(text)
        seen = {}
        shadowed = set()
        for var, quant, scoped, at in binders:
            if var in seen:
                shadowed.add(var)
                out.append(Finding("shadow", node.line,
                    f"`{var}` is bound twice in one rule -- once by the `{seen[var]}` and again "
                    f"by the `{quant}`. They are two different objects that happen to share a "
                    f"letter, so the thing the trigger tested is not the thing the rule acts "
                    f"on. Bind one of them once, enclosing the whole rule, or give them "
                    f"different names"))
            seen[var] = quant

        # ---- semantic 10a: a variable outside its quantifier's scope ----------------------
        for var, quant, scoped, at in binders:
            if var in shadowed:
                continue                        # already reported, and the spans are meaningless
            if scoped:
                span = P.scope_span(text, at)
                if span is None:
                    continue
                for use in re.finditer(rf"\b{var}\b", text):
                    if not (span[0] <= use.start() <= span[1]):
                        out.append(Finding("scope", node.line,
                            f"`{var}` is used outside the scope of the `{quant}` that binds it. "
                            f"Move the quantifier so it encloses the whole rule, or bind {var} "
                            f"where it is used"))
                        break
            else:
                arrow = _ARROW.search(text, at)
                if arrow and re.search(rf"\b{var}\b", text[arrow.end():]):
                    out.append(Finding("scope", node.line,
                        f"`{quant} ... {var}` has no scope, so it is a PROPOSITION -- it reports "
                        f"only that such a thing exists and hands you nothing to carry across "
                        f"the arrow. Write `{'each' if quant == 'some' else quant} ... ( ... )` "
                        f"with the whole rule inside the parentheses, or use `each` if the claim "
                        f"is about all of them"))

        # ---- semantic 10b: an object mentioned at two instants must say if it still exists --
        if node.kind in ("@property", "@scenario"):
            objects = {v for v, _, _, _ in P.binders_in(text)
                       if _kind_of(text, v) not in indexes}
            bound = set(enclosing) | objects
            after = _after_delay(text)
            for var in sorted(bound):
                # `exists(E)` in the ANTECEDENT says it exists now, which is not the question.
                # The rule is about the later instant, so the mention must be in that part.
                if after and re.search(rf"\b{var}\b", after) and f"exists({var})" not in after:
                    out.append(Finding("lifetime", node.line,
                        f"`{var}` is spoken of at a later instant without the claim saying "
                        f"whether it still exists. If it can end in between, the object that "
                        f"REPLACED it can discharge this obligation -- add `exists({var})`"))
    return out


def _paren_span(text: str, start: int):
    i = text.find("(", start)
    if i < 0:
        return None
    depth = 0
    for j in range(i, len(text)):
        if text[j] == "(":
            depth += 1
        elif text[j] == ")":
            depth -= 1
            if depth == 0:
                return (start, j)
    return (start, len(text))


def _after_delay(text: str):
    """The part of a claim that speaks about a later instant: after `##` or after `|=>`."""
    m = _DELAY.search(text) or re.search(r"\|=>", text)
    return text[m.start():] if m else None


def _enclosing_binders(root: P.Node, target: P.Node) -> list:
    def walk(node, carried):
        if node is target:
            return carried
        for c in node.children:
            got = walk(c, carried + node.binds)
            if got is not None:
                return got
        return None
    return walk(root, []) or []


def _kind_of(text: str, var: str):
    """The kind a binder ranges over -- `entry` in `each entry E`, `address` in `each address A`."""
    m = re.search(rf"\b(?:each|some)\s+(\w+)\s+{var}\b", text)
    return m.group(1) if m else None
