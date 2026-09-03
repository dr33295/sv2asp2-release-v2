"""The signature's schema: what a `<block>.yaml` must contain, checked before anything is read.

The signature is the compiler's SYMBOL TABLE -- the `.spec` names no wires, so `request.valid(R)`
and `R.address` resolve only through it. That makes a half-understood signature worse than a
missing one: the compiler would silently resolve some names and invent others.

So every rule here refuses BY NAME, and unknown keys are a hard error rather than a shrug. A
typo in a key is not a harmless extra: `role: opaqe` on an address would leave the compiler
believing the payload is numeric, and a 26-bit address read as a number is 67 million values in
the grounder instead of one equality bit. The failure would look like a performance problem,
days later, in a different file.
"""
from __future__ import annotations

import pathlib

import yaml

PROTOCOLS = ("readyValid", "validOnly")
SIDES = ("receives", "sends")
ROLES = ("valid", "ready", "opaque", "numeric", "level")
PAYLOAD_RULES = ("stable_until_taken", "reprioritisable")
# A control wire may be active low. `full` is a ready wire read the other way up, and
# an integrator wiring it straight to a ready input gets every refusal backwards --
# so the sense is declared beside the role rather than left to the name to imply.
ACTIVE = ("high", "low")
# THE RESET'S SENSE IS READ, so an unvalidated spelling is a different specification that
# still certifies. `polarity` decides which way `disable iff` runs for every monitor in the
# contract: active_low gives `live(T) :- val(reset, 1, T)`, active_high the complement. A
# near-miss -- `active-low`, `activeLow` -- used to fall through to the active_high default,
# so a block with an active-low reset had every claim enabled exactly where it should have
# been silenced, and the certificate then ran the property set over the reset window. The
# methodology itself documented the camelCase spelling, so a reader FOLLOWING THE DOCUMENT
# hit it. A wrong `role` is slow; a wrong polarity is a different specification.
POLARITIES = ("active_high", "active_low")
EDGES = ("posedge", "negedge")
# not consumed by the compiler today, and validated anyway: an unvalidated field that is not
# read yet is a trap waiting for the release that starts reading it
SYNCHRONOUS = ("yes", "no", "unspecified")
DISCIPLINES = ("once", "recurring")

_TOP = {"metadata", "parameters", "clocks_and_resets", "interfaces", "ports", "registers",
        "functional_description"}
_META = {"block_name", "version", "status", "description"}
_PARAM = {"name", "type", "default", "description"}
_CLOCK = {"name", "type", "edge", "polarity", "synchronous", "discipline", "description"}
_IFACE = {"name", "protocol", "side", "payload", "description"}
_PORT = {"name", "direction", "width", "clock", "interface", "role", "active",
         "elements", "description"}


class SignatureError(Exception):
    """A malformed signature. Always names the file, the place, and what was expected."""


def _keys(where: str, got: dict, allowed: set) -> None:
    unknown = set(got) - allowed
    if unknown:
        raise SignatureError(f"{where}: unknown key(s) {sorted(unknown)}; "
                             f"the keys here are {sorted(allowed)}")


def load(path) -> dict:
    """Read a signature and check it, or refuse by name. Returns the document."""
    path = pathlib.Path(path)
    doc = yaml.safe_load(path.read_text())
    if not isinstance(doc, dict):
        raise SignatureError(f"{path}: the signature must be a mapping")
    _keys(str(path), doc, _TOP)
    for section in ("metadata", "interfaces", "ports"):
        if section not in doc:
            raise SignatureError(f"{path}: no `{section}` -- a signature without it cannot "
                                 f"resolve anything the specification says")
    _keys(f"{path}: metadata", doc["metadata"], _META)
    if not doc["metadata"].get("block_name"):
        raise SignatureError(f"{path}: metadata has no block_name")

    params = set()
    for pdef in doc.get("parameters") or []:
        _keys(f"{path}: parameter {pdef.get('name')}", pdef, _PARAM)
        if not pdef.get("name"):
            raise SignatureError(f"{path}: a parameter has no name")
        params.add(pdef["name"])

    clocks, resets = set(), set()
    for c in doc.get("clocks_and_resets") or []:
        _keys(f"{path}: clock/reset {c.get('name')}", c, _CLOCK)
        kind = c.get("type")
        if kind not in ("clock", "reset"):
            raise SignatureError(f"{path}: {c.get('name')!r} has type {kind!r}; "
                                 f"a clocks_and_resets entry is a 'clock' or a 'reset'")
        nm = c.get("name")
        for field, allowed, why in (
                ("polarity", POLARITIES, "it decides which way `disable iff` runs for every "
                                         "monitor in the contract"),
                ("edge", EDGES, "it says which edge the design is sampled on"),
                ("synchronous", SYNCHRONOUS, "it records whether the reset is sampled or "
                                             "immediate"),
                ("discipline", DISCIPLINES, "`once` is the standard convention -- asserted "
                                            "before cycle 1 and never again; `recurring` "
                                            "allows re-assertion at a cost the author "
                                            "accepts")):
            if field in c and c[field] not in allowed:
                raise SignatureError(
                    f"{path}: {nm!r} has {field} {c[field]!r}; the values are "
                    f"{list(allowed)}. {why[0].upper()}{why[1:]}, so a near-miss spelling "
                    f"would be accepted as the default and mean something else")
        if kind == "reset" and "polarity" not in c:
            raise SignatureError(
                f"{path}: reset {nm!r} declares no polarity; it must say "
                f"{list(POLARITIES)}. Left out, the sense would be assumed, and the "
                f"assumption decides where every claim in the contract is judged")
        if kind == "clock" and "edge" not in c:
            raise SignatureError(
                f"{path}: clock {nm!r} declares no edge; it must say {list(EDGES)}")
        (clocks if kind == "clock" else resets).add(c["name"])
    if not clocks:
        raise SignatureError(f"{path}: no clock -- the whole contract is indexed by one")

    ifaces = {}
    for i in doc["interfaces"]:
        _keys(f"{path}: interface {i.get('name')}", i, _IFACE)
        for field, allowed in (("protocol", PROTOCOLS), ("side", SIDES)):
            if i.get(field) not in allowed:
                raise SignatureError(f"{path}: interface {i.get('name')!r} has {field} "
                                     f"{i.get(field)!r}; the choices are {list(allowed)}")
        if "payload" in i and i["payload"] not in PAYLOAD_RULES:
            raise SignatureError(f"{path}: interface {i['name']!r} has payload {i['payload']!r}; "
                                 f"the choices are {list(PAYLOAD_RULES)}")
        ifaces[i["name"]] = i

    seen, roles = set(), {}
    for q in doc["ports"]:
        _keys(f"{path}: port {q.get('name')}", q, _PORT)
        name = q.get("name")
        if not name:
            raise SignatureError(f"{path}: a port has no name")
        if name in seen:
            raise SignatureError(f"{path}: port {name!r} is declared twice")
        seen.add(name)
        if q.get("direction") not in ("input", "output"):
            raise SignatureError(f"{path}: port {name!r} has direction {q.get('direction')!r}")
        if q.get("active", "high") not in ACTIVE:
            raise SignatureError(f"{path}: port {name!r} is active {q['active']!r}; "
                                 f"the choices are {list(ACTIVE)}")
        if q.get("role") not in ROLES:
            raise SignatureError(f"{path}: port {name!r} has role {q.get('role')!r}; "
                                 f"the roles are {list(ROLES)}. The role decides how the payload "
                                 f"is read -- `opaque` is a token compared for equality, "
                                 f"`numeric` gets a value domain -- so a wrong one is a cost, "
                                 f"not a typo")
        w = q.get("width")
        if not (isinstance(w, int) and w > 0) and w not in params:
            raise SignatureError(f"{path}: port {name!r} has width {w!r}, which is neither a "
                                 f"positive integer nor a declared parameter {sorted(params)}")
        # AN ARRAY PORT SAYS SO. `width` is the width of ONE element and `elements` how
        # many there are, and the pair is what gives a subscript its meaning: on an array
        # port `x[J]` is element J, on a plain one it is bit J. Without the declaration a
        # subscript could only guess, and it guessed BIT -- so an element index compiled
        # silently into a bit index (the shape question, 2026-09-02).
        n = q.get("elements")
        if n is not None and not ((isinstance(n, int) and n > 0) or n in params):
            raise SignatureError(f"{path}: port {name!r} has elements {n!r}, which is "
                                 f"neither a positive integer nor a declared parameter "
                                 f"{sorted(params)}")
        if q.get("clock") not in clocks:
            raise SignatureError(f"{path}: port {name!r} names clock {q.get('clock')!r}, "
                                 f"which is not declared; the clocks are {sorted(clocks)}")
        iface = q.get("interface")
        if iface not in ("-", None) and iface not in ifaces:
            raise SignatureError(f"{path}: port {name!r} belongs to interface {iface!r}, "
                                 f"which is not declared")
        if iface in ifaces:
            roles.setdefault(iface, set()).add(q["role"])

    # an interface must carry the wires its protocol promises, or the verbs the specification
    # is allowed to use on it would resolve to nothing
    for nm, i in ifaces.items():
        have = roles.get(nm, set())
        if "valid" not in have:
            raise SignatureError(f"{path}: interface {nm!r} has no port with role 'valid'")
        if i["protocol"] == "readyValid" and "ready" not in have:
            raise SignatureError(f"{path}: interface {nm!r} is readyValid and has no port with "
                                 f"role 'ready' -- so nothing could ever be accepted on it")
        if i["protocol"] == "validOnly" and "ready" in have:
            raise SignatureError(f"{path}: interface {nm!r} is validOnly yet has a 'ready' port; "
                                 f"a validOnly interface cannot refuse, which is the point of it")
    return doc


if __name__ == "__main__":
    import sys
    try:
        d = load(sys.argv[1])
    except SignatureError as e:
        print(f"signature: {e}")
        raise SystemExit(1)
    print(f"signature OK: {d['metadata']['block_name']}, "
          f"{len(d['interfaces'])} interface(s), {len(d['ports'])} port(s)")
