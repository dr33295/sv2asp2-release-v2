"""Lowering a specification to ASP: the first point at which the compiler produces something
a solver runs, rather than something it inspects.

WHAT IS EMITTED, and what is not. This lowers the CLAIMS -- `@property`, `@assume`, and the
`@define`s they rest on -- into the contract's `failType` rules. Behaviours are not lowered
here; that is a later stage, and pretending otherwise would produce a contract that certifies
while saying less than the specification does.

THE SHAPE OF A CLAIM. ASP has no implication, so `P |-> Q` becomes two rules: one deriving a
name for "Q holds here", and one deriving the failure when P holds and that name does not.
Writing it any other way -- negating Q inline -- gets the quantifiers wrong the moment Q
contains one, which is why the indirection is not decoration.

THE PART THAT DESERVES SUSPICION is the pointer vocabulary. `next`, `address` and `opposite`
are relations in the language and modular arithmetic in the contract, and nothing about the
translation is self-evidently right. That is exactly what the verdict differential is for: the
generated contract and the hand-written one must agree about the same design, and disagree the
same way about a broken one.
"""
from __future__ import annotations

import re

from . import expr as X
from . import parse as P


class EmitError(Exception):
    """A construct this stage cannot lower. Refused by name -- never guessed at."""


def wellformed_problems(text: str) -> list:
    """The generated contract's own wellformedness, checked before it leaves the emitter.
    Both problems here are the two faces of ONE incident (2026-08-31): a renaming let a
    fresh helper collide with a claim's reserved main name, so two lowerings shared one
    head -- and one rule NEGATED ITS OWN HEAD in its body, which is unstratified nonsense
    wearing a contract. Reading the output caught it once; this check catches it every
    time, so it can never again depend on somebody reading."""
    probs = []
    heads = {}
    shared = {"failType", "boundary", "pval", "holds", "did", "scenario", "live",
              "entryId", "gtime"}
    for i, l in enumerate(text.splitlines()):
        m = re.match(r"(\w+)\(", l)
        if not m or ":-" not in l:
            continue
        h = m.group(1)
        if re.search(rf"\bnot\s+{re.escape(h)}\(", l.split(":-", 1)[1]):
            probs.append(f"line {i + 1}: `{h}` negates itself in its own body")
        heads.setdefault(h, []).append(i)
    for h, ls in heads.items():
        if h in shared or len(ls) < 2:
            continue
        # one lowering emits a head's rules together (a disjunction's branches are
        # adjacent); the same head defined again far away is two lowerings sharing a name
        if max(ls) - min(ls) > len(ls) + 2:
            probs.append(f"`{h}` is defined in two separated places (lines {min(ls) + 1} "
                         f"and {max(ls) + 1}) -- two lowerings sharing one name")
    return probs


class Emitter:
    def __init__(self, spec_path, signature: dict):
        import pathlib as _pl
        sp = _pl.Path(spec_path)
        if sp.suffix == ".cnl":
            # the controlled-English surface: desugared to the symbolic core FIRST, and the
            # core written BESIDE the source as `<name>.cnl.core` -- committed, so drift in
            # what the English means shows up as a git diff, and dumpable, so an author can
            # always see what their sentences became.
            from .cnl import desugar
            core = desugar(sp.read_text())
            cp = sp.with_suffix(".cnl.core")
            if not cp.exists() or cp.read_text() != core:
                cp.write_text(core)
            spec_path = cp
        self.root = P.parse(spec_path)
        self.sig = signature
        self.ports = {q["name"]: q for q in signature.get("ports", [])}
        self.ifaces = {i["name"]: i for i in signature.get("interfaces", [])}
        self.params = {p["name"]: p.get("default") for p in signature.get("parameters") or []}
        self.reset = next((c for c in signature.get("clocks_and_resets") or []
                           if c.get("type") == "reset"), None)
        # a reset is readable like a port even though it is declared elsewhere: a property
        # about reset has to be able to say `!reset_n`
        self.signals = {c["name"] for c in signature.get("clocks_and_resets") or []}
        self.defines = {}          # name -> its `holds when` expression, when it has one
        self.windows = {}          # name -> ("pointer"|"value"|..., its declared domain)
        self.indexes = {}          # name -> its extent
        self._n = 0
        self._decl = None          # the declaration being lowered, for human-shaped names
        self._used_names = set()
        self._port_sample = {}
        self.moduli = {}
        self.demanded = set()
        self.payload_of = {}
        self.spans = {}
        # WHAT THE CONTRACT'S PREAMBLE NEEDS, initialised here rather than lazily where it
        # is set. `_used_eq` was set only on the equality-theory path and read
        # unconditionally when the file was assembled, so a specification that never
        # compares two OPAQUE values crashed instead of compiling -- and every block the
        # suite had ever compiled happened to contain such a comparison, so nothing caught
        # it. Found in the field, on a framing FSM whose ports are all levels and small
        # numerics (2026-09-01). A flag a method reads unconditionally exists from
        # construction; the `getattr(..., False)` spelling its neighbour used hides this
        # class of defect instead of preventing it.
        self.enum_members = {}     # an enum's member name -> the window that declares it
        self._used_bit = False     # did any lowering take a bit of a port?
        self._capture = False      # lowering the right-hand side of an effect?
        self._capture_at = None    # ... and the instant its event happened at
        self._used_eq = False      # did any lowering declare an opaque equality boundary?
        self._any_input = False    # did any scenario use the free-input slot?
        self._writers = {}
        self._live = "live"        # the guard the declaration being built is judged under
        self.value_windows = set()  # (name, key count) for every window read as a VALUE
        self._quant_dom = {}        # a quantified variable -> the literal that binds it
        self._create_kinds = {}
        self._bound_at = {}
        self._defined = {}
        self._open = []
        self._quantified = set()
        self.moduli = {}
        self._scan()

    # ------------------------------------------------------------------ the declarations
    def _scan(self) -> None:
        for n in self.root.walk():
            if n.kind == "@define":
                body = P.notation_of(n)
                m = re.search(r"holds when\s+(.*)", body, re.S)
                ps = re.match(r"@define\s+\w+\s*\(([^)]*)\)", n.header)
                self.defines[n.name] = (m.group(1).strip() if m else None,
                                        [a.strip() for a in ps.group(1).split(",")] if ps else [])
            elif n.kind == "@state":
                m = re.search(r"@state\s+(\w+)(\[(\w+)\])?\s*:\s*(\w+)"
                              r"(?:\((\w+)\))?(?:\s*\{([^}]*)\})?", n.header)
                if m:
                    self.windows[m.group(1)] = (m.group(4), m.group(3))
                    if m.group(4) == "pointer" and m.group(5):
                        self.moduli[m.group(1)] = m.group(5)
                    if m.group(6):
                        # AN ENUM'S MEMBERS ARE VALUES. The declaration parsed and the
                        # comparison parsed, but the member list was never captured, so
                        # `phase == presenting` failed to resolve the NAME -- an FSM phase,
                        # the most natural enum there is, could only be written as magic
                        # numbers (the second block's finding, 2026-09-01). A member lowers
                        # to itself: an ASP constant, exactly as the translator represents
                        # an enum tag, so `phase == presenting` becomes `phase(V, T), V =
                        # presenting`.
                        for mem in (x.strip() for x in m.group(6).split(",")):
                            if mem:
                                self.enum_members[mem] = m.group(1)
            elif n.kind == "@index":
                m = re.search(r"@index\s+(\w+)\s*:\s*(\w+)", n.header)
                if m:
                    self.indexes[m.group(1)] = m.group(2)

    def _carried(self, lits) -> list:
        """The bound variables a helper's body mentions, which it must therefore CARRY.

        A helper made for `not exists(E)` whose head is just `h(T)` throws E away, and the
        rule becomes unsafe -- or worse, safe and about the wrong thing. The head has to name
        every variable that was bound outside it and used inside.
        """
        text = " ".join(lits)
        return sorted({v for v in (self._quantified | set(self.payload_of))
                       if re.search(rf"\b{v}\b", text)})

    def _domains(self, carried) -> list:
        """The IDENTITY domain for each carried variable -- a binder, and deliberately NOT the
        existence window.

        A helper whose body only mentions a variable under negation needs something positive to
        bind it, or clingo refuses the rule. The first version bound with `entryExists(E, T)`,
        under a comment claiming the addition could not change the verdict. It could: for a
        disjunct whose whole content is "the entry is GONE" (`!exists(E)` at the later
        instant), demanding existence makes the escape underivable, and the lifetime clause
        fired on every entry that was correctly freed. The binder must be the IDENTITY domain
        of decision 33.1 -- the slot, which persists whether occupied or not -- projected from
        the existence window over the whole window, so it is defined for exactly the ids the
        claim can be about."""
        out = []
        for v in carried:
            kind = self._kind_of_var(v)
            if kind is None:
                continue
            if kind in self.indexes:
                out.append(f"{v} = 0..{self.indexes[kind]}-1")
            else:
                self.demanded.add(f"{kind}Exists")
                self._defined.setdefault(f"{kind}Id",
                    f"{kind}Id(V) :- {kind}Exists(V, T).")
                out.append(f"{kind}Id({v})")
        return out

    def _mentions_reset(self, lits) -> bool:
        """Does this claim NAME the reset signal? Chapter 33's fourth decision exempts a
        property that does from the file's `disable iff`, and the exemption is about naming
        the reset -- not about one spelling of it."""
        if not self.reset:
            return False
        pat = re.compile(r"\bval\(" + re.escape(self.reset["name"]) + r"\s*[,)]")
        return any(pat.search(l) for l in lits)

    def _exempt(self, lits) -> None:
        """Judge the declaration being built at EVERY instant, not only the live ones.

        `@during reset` reached this through `enable iff`. The same requirement written
        `@when reset == 1` did not, and compiled to a rule needing the reset both high and
        low at one instant: it appears in the contract, is counted as a monitor, and can
        never fire. A monitor that is green because it is dead is the failure this route
        works hardest against, so the exemption follows the MEANING (the second block's
        G12, 2026-09-02). Behaviours had no exempt form at all.
        """
        if self._mentions_reset(lits):
            self._live = "gtime"

    def _lv(self, at: str = "T") -> str:
        """`live(T)` normally; `gtime(T)` where the declaration named the reset."""
        return f"{self._live}({at})"

    def _rule(self, head: str, body: list) -> str:
        """One generated rule. Any binding that is OPEN -- the K of a ranged delay, say -- goes
        into every rule made while it is open, because a helper referring to `T+K` without it is
        an unsafe rule and clingo will not take a guess at what was meant."""
        # every helper's own instant must be BOUND, and `T` appearing only inside `T+K` does
        # not bind it. One positive time literal per generated rule settles it -- slightly
        # noisier than strictly necessary, and the alternative is a rule clingo refuses.
        m = re.search(r"[,(]\s*(T(?:\+\w+)?)\)\s*$", head)
        floor = [f"gtime({m.group(1)})"] if m else []
        return f"{head} :- {', '.join(floor + self._open + body)}."

    # THE NAMES ARE FOR PEOPLE (the user, 2026-08-31: "the names have to be in lower
    # camel case and be human like"). An auxiliary atom is named for the declaration it
    # serves and the ROLE it plays in it -- allocateDemandCreated, forwardIsCorrectBody --
    # never a bare counter; a value variable is named for what it samples -- RAddress,
    # EntryTag, LiveEntries (ASP requires the capital) -- with a numeric suffix only on a
    # genuine collision inside one declaration.
    _ROLES = {"any_": "Any", "holds_": "Holds", "q_": "Found", "no_": "Counterex",
              "h_": "Body", "did_": "Did", "new_": "Created", "one_": "One",
              "two_": "Two", "anyw_": "Wanted", "satw_": "Served",
              "anyx_": "Candidates", "satx_": "Fulfilled"}

    def _fresh(self, stem: str, hint: str | None = None) -> str:
        if stem == "V":
            base = (hint[0].upper() + hint[1:]) if hint else None
            if base:
                return self._uniq(base)
            self._n += 1
            return f"V{self._n}"
        role = self._ROLES.get(stem)
        if role and self._decl:
            return self._uniq(self._decl + role)
        self._n += 1
        return f"{stem}{self._n}"

    def _uniq(self, base: str) -> str:
        k = 1
        name = base
        while name in self._used_names:
            k += 1
            name = f"{base}{k}"
        self._used_names.add(name)
        return name

    # ------------------------------------------------------------------ lowering one expression
    def lower(self, e: X.E, t: str, neg=False) -> tuple:
        """Return (literals, aux_rules). `t` is the instant. Literals conjoin."""
        if e.op == "and":
            a, ra = self.lower(e.kids[0], t)
            b, rb = self.lower(e.kids[1], t)
            return a + b, ra + rb
        if e.op == "or":
            # a disjunction needs a name of its own: ASP conjoins in a body, it does not disjoin
            name = self._fresh("any_")
            rules = []
            branches = []
            for k in e.kids:
                lits, r = self.lower(k, "T")
                rules += r
                branches.append(lits)
            carried = self._carried([l for b in branches for l in b])
            args = ", ".join(carried + ["T"])
            for lits in branches:
                rules.append(self._rule(f"{name}({args})", self._domains(carried) + lits))
            return [f"{name}({', '.join(carried + [t])})"], rules
        if e.op == "not":
            lits, rules = self.lower(e.kids[0], t)
            if len(lits) == 1 and lits[0].startswith("val("):
                return [f"not {lits[0]}"], rules
            lits, rules = self.lower(e.kids[0], "T")
            name = self._fresh("holds_")
            carried = self._carried(lits)
            args = ", ".join(carried + ["T"])
            return ([f"not {name}({', '.join(carried + [t])})"],
                    rules + [self._rule(f"{name}({args})", self._domains(carried) + lits)])
        if e.op == "cmp":
            return self._cmp(e, t)
        if e.op == "field":
            return self._interface(e, t)
        if e.op == "call":
            return self._call(e, t)
        if e.op == "name":
            return self._name(e, t)
        if e.op == "quant":
            return self._quant(e, t)
        if e.op == "delay":
            lo, hi = e.text.split(":")
            if lo != hi:
                raise EmitError(f"a ranged delay `##[{lo}:{hi}]` inside a condition is not "
                                f"lowered here -- put it at the head of the consequent, where "
                                f"it becomes a witness over the window")
            base = re.sub(r"\+\d+$", "", t)
            off = int(re.search(r"\+(\d+)$", t).group(1)) if "+" in t else 0
            return self.lower(e.kids[0], f"{base}+{off + int(lo)}")
        if e.op == "ifcall":
            lits, rules = self._interface(X.E("field", [e.kids[0]], e.text), t)
            if len(e.kids) > 1 and e.kids[1].op != "name":
                # a VALUE argument: `memoryRequest.valid(D.address)` says the interface is
                # valid AND its payload equals this value -- routing, so identity
                iface = e.kids[0].text
                data = [q for q in self.ports.values()
                        if q.get("interface") == iface and q.get("role") in ("opaque", "numeric")]
                if len(data) != 1:
                    raise EmitError(f"`{iface}.{e.text}(...)` with a value needs exactly one "
                                    f"payload port")
                v, vl, vr = self.value(e.kids[1], t)
                return lits + vl + [f"val({data[0]['name']}, {v}, {t})"], rules + vr
            if len(e.kids) > 1 and e.kids[1].op == "name":
                self.payload_of[e.kids[1].text] = e.kids[0].text
                # the variable's BINDING INSTANT: `R.tag` in a delayed effect means the tag
                # of the request that TRIGGERED, not whatever sits on the wire later. Without
                # this, `##1 E.tag = R.tag` compared the new entry against the NEXT cycle's
                # request -- and the base failed on a design that captured correctly.
                self._bound_at[e.kids[1].text] = t
            return lits, rules
        raise EmitError(f"cannot lower {e.op} ({e.text!r})")

    # ------------------------------------------------------------------ quantifiers
    def domain_of(self, kind: str, var: str, t: str) -> str:
        """What a quantifier ranges over.

        An INDEX domain is a range of numbers, fixed and always there. An OBJECT kind ranges
        over what EXISTS at this instant, which is a window the design must mount -- so the
        compiler demands it whether or not the author ever writes `exists`. That demand is
        invisible in the source text, which is why it is made here rather than left implied.
        """
        if kind in self.indexes:
            lit = f"{var} = 0..{self.indexes[kind]}-1"
            # REMEMBERED, because a rule built later may have to bind this variable itself.
            # A quantifier binds its variable in the rule the claim becomes; an auxiliary
            # rule split out of that claim -- a boundary declaration, say -- is a DIFFERENT
            # rule, and the binding does not travel with the variable name.
            self._quant_dom[var] = lit
            return lit
        self.demanded.add(f"{kind}Exists")
        self._quant_dom[var] = f"{kind}Exists({var}, @T@)"
        return f"{kind}Exists({var}, {t})"

    def _quant(self, e: X.E, t: str) -> tuple:
        q, kind, var = e.text.split(":")
        where, scope = e.kids
        self._quantified.add(var)
        lits = [self.domain_of(kind, var, "T")]
        rules = []
        for part in (where, scope):
            if part is None:
                continue
            pl, pr = self.lower(part, "T")
            lits += pl
            rules += pr
        name = self._fresh("q_")
        rules.append(self._rule(f"{name}(T)", lits))
        if q == "some":
            return [f"{name}({t})"], rules
        # `each` as a CONDITION means "no counterexample", which is the honest reading of a
        # universal inside a body: ASP has no universal, and this is how one is spelled.
        neg = self._fresh("no_")
        counter = [self.domain_of(kind, var, "T")]
        if where is not None:
            wl, wr = self.lower(where, "T")
            counter += wl
            rules += wr
        if scope is not None:
            sl, sr = self.lower(scope, "T")
            rules += sr
            hold = self._fresh("h_")
            rules.append(self._rule(f"{hold}({var}, T)",
                                    self._domains([var]) + sl))
            counter.append(f"not {hold}({var}, T)")
        rules.append(self._rule(f"{neg}(T)", counter))
        return [f"not {neg}({t})"], rules

    def _name(self, e: X.E, t: str) -> tuple:
        n = e.text
        if n in self.defines:
            body, params = self.defines[n]
            if params:
                raise EmitError(f"`{n}` takes {len(params)} argument(s) and is used with none")
            if body is None:
                # a parameterless definition with no `holds when` is DECLARED VOCABULARY: the
                # design must mount it, exactly like a window
                self.demanded.add(n)
                return [f"{n}({t})"], []
            lits, rules = self.lower(X.parse_expr(body), t)
            return [f"{self._named(n, lits, rules)}({t})"], rules
        if n in self.ports or n in self.signals:
            return [f"val({n}, 1, {t})"], []
        raise EmitError(f"`{n}` is neither a port, a reset, nor a definition")

    def _named(self, n: str, lits, rules) -> str:
        # a definition used five times is still one rule. Emitting it per use would be sound
        # and unreadable, and the contract is meant to be read.
        if n not in self._defined:
            self._defined[n] = f"{n}(T) :- {', '.join(lits)}."
        return n

    def _interface(self, e: X.E, t: str) -> tuple:
        base = e.kids[0]
        if base.op != "name":
            raise EmitError("an interface predicate applies to an interface name")
        nm, verb = base.text, e.text
        if nm in self.ifaces:
            if verb == "taken":
                # a handshake: the offer is made AND accepted. Two wires, one word.
                v, _ = self._interface(X.E("field", [base], "valid"), t)
                r, _ = self._interface(X.E("field", [base], "ready"), t)
                return v + r, []
            role = {"valid": "valid", "ready": "ready", "arrives": "valid",
                    "sends": "valid", "high": "valid"}.get(verb)
            if role is None:
                raise EmitError(f"`{nm}.{verb}` is not a verb this stage lowers")
            port = next((q for q in self.ports.values()
                         if q.get("interface") == nm and q.get("role") == role), None)
            if port is None:
                raise EmitError(f"the {nm} interface has no {role} port")
            # an active-low wire asserts its role at 0 -- the reason the signature declares it
            on = 0 if port.get("active", "high") == "low" else 1
            return [f"val({port['name']}, {on}, {t})"], []
        if nm in self.ports and verb in ("high", "low"):
            return [f"val({nm}, {1 if verb == 'high' else 0}, {t})"], []
        raise EmitError(f"`{nm}.{verb}` -- {nm} is neither an interface nor a level port")

    def _call(self, e: X.E, t: str) -> tuple:
        if e.text in self.defines:
            body, params = self.defines[e.text]
            args = [self.value(k, t)[0] for k in e.kids]
            if body is None:
                # declared vocabulary again, this time with arguments: `wantsFetch(E)` is a
                # window over entries, and the design mounts it
                self.demanded.add(e.text)
                return [f"{e.text}({', '.join(args)}, {t})"], []
            if len(params) != len(e.kids):
                raise EmitError(f"`{e.text}` takes {len(params)} argument(s), given "
                                f"{len(e.kids)}")
            sub = body
            for formal, actual in zip(params, [k.text for k in e.kids]):
                sub = re.sub(rf"\b{formal}\b", actual, sub)
            return self.lower(X.parse_expr(sub), t)
        if e.text == "opposite":
            a, la, ra = self.value(e.kids[0], t)
            b, lb, rb = self.value(e.kids[1], t)
            m = self._modulus(e.kids[0].text if e.kids[0].op == "name" else None)
            return la + lb + [f"{b} = ({a} + {m}) \\ (2*{m})"], ra + rb
        if e.text == "accepted" and e.kids and e.kids[0].op == "name":
            iface = self.payload_of.get(e.kids[0].text)
            if iface is None:
                raise EmitError(f"`accepted({e.kids[0].text})` -- nothing binds "
                                f"{e.kids[0].text} to an interface")
            return self._interface(X.E("field", [X.E("name", [], iface)], "taken"), t)
        if e.text == "s_eventually":
            raise EmitError("`s_eventually` is an OBLIGATION, not a rule -- reduce it to a "
                            "bound, a ranking, or a work-conservation argument. This refusal "
                            "is by design (TRANSLATION.md 4.4), not a gap")
        if e.text == "exists":
            v = e.kids[0]
            if v.op != "name":
                raise EmitError("`exists` applies to a bound variable")
            kind = self._kind_of_var(v.text)
            if kind is None:
                raise EmitError(f"`exists({v.text})` -- nothing binds {v.text} to an object kind")
            return [self.domain_of(kind, v.text, t)], []
        if e.text in ("exactly", "atMost", "atLeast"):
            return self._cardinality(e, t)
        if e.text == "$stable":
            v = e.kids[0]
            if v.op == "name" and v.text in self.payload_of:
                # `$stable(R)` on a whole payload means EVERY payload wire of that interface.
                # The signature knows which those are, and a specification should not have to
                # list them -- listing them is how one gets forgotten when a wire is added.
                iface = self.payload_of[v.text]
                lits = []
                extra = []
                for q in self.ports.values():
                    if q.get("role") == "numeric" and q.get("interface") == iface:
                        w = self._fresh("V", q["name"])
                        lits += [f"val({q['name']}, {w}, T)", f"val({q['name']}, {w}, T+1)"]
                    elif q.get("role") == "opaque" and q.get("interface") == iface:
                        # stability of an opaque payload is EQUALITY, not identity: every data
                        # input is a fresh token each instant, so identity across instants is
                        # false by construction -- the finding CERTIFICATE.md recorded for any
                        # compiler lowering $stable on a data signal
                        w1 = self._fresh("V", q["name"])
                        w2 = self._fresh("V", q["name"] + "Next")
                        pair = [f"val({q['name']}, {w1}, T)", f"val({q['name']}, {w2}, T+1)"]
                        got, more = self._eq_theory(w1, w2, pair[:1], pair[1:], 1)
                        lits += got
                        extra += more
                if not lits:
                    raise EmitError(f"`$stable({v.text})` -- the {iface} interface carries no "
                                    f"payload that could be stable")
                return lits, extra
            a, la, ra = self.value(v, "T")
            b, lb, rb = self.value(v, "T+1")
            if self._sort(v) == "opaque":
                lits, extra = self._eq_theory(a, b, la, lb, 1)
                return lits, ra + rb + extra
            return la + lb + [f"{a} = {b}"], ra + rb
        raise EmitError(f"`{e.text}(...)` cannot appear as a condition on its own")

    # ------------------------------------------------------------------ values and comparisons
    def value(self, e: X.E, t: str) -> tuple:
        """A VALUE, as (term, literals, rules): what a comparison compares."""
        if e.op == "num":
            return e.text, [], []
        if e.op == "name":
            n = e.text
            if n in self.windows:
                v = self._fresh("V", n)
                return v, [f"{n}({v}, {t})"], []
            if n in self.ports:
                v = self._fresh("V", n)
                return v, [f"val({n}, {v}, {t})"], []
            if n in self.signals:
                # A CLOCK OR RESET IS A SIGNAL WITH A VALUE. It was readable as a truth
                # (`@when reset`) and refused as a value (`reset == 1`), which is an
                # asymmetry with nothing behind it -- and it fell exactly on the spelling a
                # person reaches for when stating what happens during reset.
                v = self._fresh("V", n)
                return v, [f"val({n}, {v}, {t})"], []
            if n in self.params:
                return n, [], []
            if n in self.enum_members:
                return n, [], []          # a declared member is the constant itself
            if n in self._quantified:
                return n, [], []          # an index or object variable is its own value
            if n in self.payload_of:
                # a payload variable IS the value on its interface's wire, so using it as a
                # value binds it there. Left unbound it is a name floating free, and the first
                # rule that mentions it outside a vocabulary atom -- a boundary declaration,
                # say -- is unsafe. With several payload wires the binding is ambiguous, and
                # the field form says which one is meant.
                iface = self.payload_of[n]
                at = self._bound_at.get(n, t)
                data = [q for q in self.ports.values()
                        if q.get("interface") == iface and q.get("role") == "opaque"]
                if len(data) == 1:
                    return n, [f"val({data[0]['name']}, {n}, {at})"], []
                return n, [], []          # a handle; vocabulary atoms bind it
            raise EmitError(f"`{n}` is not something with a value here")
        if e.op == "arith":
            a, la, ra = self.value(e.kids[0], t)
            b, lb, rb = self.value(e.kids[1], t)
            return f"({a} {e.text} {b})", la + lb, ra + rb
        if e.op == "call":
            return self._value_call(e, t)
        if e.op == "field":
            base, field = e.kids[0], e.text
            if base.op != "name":
                raise EmitError("a field belongs to a bound variable")
            var = base.text
            v = self._fresh("V", var + field[0].upper() + field[1:])
            iface = self.payload_of.get(var)
            if iface:
                port = iface + field[0].upper() + field[1:]
                if port not in self.ports:
                    raise EmitError(f"`{var}.{field}` -- the {iface} interface has no port "
                                    f"{port!r}")
                return v, [f"val({port}, {v}, {self._bound_at.get(var, t)})"], []
            kind = self._kind_of_var(var)
            if kind is None:
                raise EmitError(f"`{var}.{field}` -- nothing binds {var}")
            # an object's attribute is a window over that object: `E.address` is the design
            # telling us the line an entry holds, mounted by the linkage like any other
            w = kind + field[0].upper() + field[1:]
            self.demanded.add(w)
            self.value_windows.add((w, 1))     # keyed by the object
            return v, [f"{w}({var}, {v}, {t})"], []
        if e.op == "index":
            base, idx = e.kids
            if base.op == "name" and self.ports.get(base.text, {}).get("elements"):
                # AN ARRAY PORT'S SUBSCRIPT IS AN ELEMENT, not a bit: an ordinary
                # addressed read, `val(port(J), V, T)`, keeping the port's role -- so an
                # opaque element is a token that compares through the equality theory and
                # is never enumerated. Simpler than the bit case, which needs a boundary
                # precisely because a bit is a decision COMPUTED from a value.
                at = self._capture_at if (self._capture and self._capture_at) else t
                a, la, ra = self.value(idx, at)
                v = self._fresh("V", base.text)
                return v, la + [f"val({base.text}({a}), {v}, {t})"], ra
            if base.op == "name" and base.text in self.ports:
                # A PORT MAY BE INDEXED: `out_byte[J]` is the bit of the wire, and a block
                # whose promise relates a multi-bit port to per-bit state has no other way
                # to say so (the user's ruling, 2026-09-02). It is lowered as a BOUNDARY --
                # `bit(V, J)`, the runner's own term -- so the bit stays a control decision
                # ABOUT data rather than an enumeration OF it: one free bit per distinct
                # (value, position), never 2^width values in the grounder.
                at = self._capture_at if (self._capture and self._capture_at) else t
                a, la, ra = self.value(idx, at)
                # ONE SAMPLE PER PORT PER INSTANT. A fresh sample per READ -- `val(q, Q, T),
                # val(q, Q2, T)` -- is the same value twice in every model (a port has exactly
                # one value per instant), but the grounder cannot know that: each sample ranges
                # over the whole port domain, so k reads of a 9-bit port joined 512^k -- two
                # reads of a grid took a certificate from 7 s to never (the third block's G25,
                # 2026-09-02). Reusing the variable keeps every model and removes the join; the
                # read literal is still emitted per read, so a hoisted rule stays safe.
                w = self._port_sample.get((base.text, t))
                if w is None:
                    w = self._port_sample[(base.text, t)] = self._fresh("V", base.text)
                b = self._fresh("V", base.text + "Bit")
                self._used_bit = True
                read = [f"val({base.text}, {w}, {t})"]
                # THE POSITION MUST BE BOUND IN THIS RULE. `a` is often a quantifier's
                # variable, bound in the claim's own rule -- and the boundary declaration is
                # a SEPARATE rule, where the same name is free. Emitted without its domain
                # the rule is unsafe, and clingo does not skip an unsafe rule: it stops
                # grounding and takes the whole program with it, so a contract that compiled
                # clean could not be run at all (the second block's G17, 2026-09-02).
                bind = [self._quant_dom[v].replace("@T@", t)
                        for v in sorted(self._quant_dom)
                        if re.search(rf"\b{v}\b", a)]
                unbound = [v for v in sorted(self._quantified)
                           if re.search(rf"\b{v}\b", a) and v not in self._quant_dom]
                if unbound:
                    raise EmitError(
                        f"the bit position {a!r} names {unbound[0]}, which nothing here "
                        f"says the range of -- the boundary declaration is its own rule and "
                        f"must bind every variable it uses")
                bnd = self._rule(f"boundary(bit({w}, {a}), 1)", read + la + bind)
                return b, read + la + [f"pval(bit({w}, {a}), {b})"], ra + [bnd]
            if base.op != "name" or base.text not in self.windows:
                raise EmitError("only a declared window or a port may be indexed")
            # the SUBSCRIPT is a read even when the window it indexes is the target: which
            # position an effect writes is decided by the index's value at the event, not
            # by what the index will hold after it
            a, la, ra = self.value(idx, self._capture_at
                                   if (self._capture and self._capture_at) else t)
            v = self._fresh("V", base.text)
            return v, la + [f"{base.text}({a}, {v}, {t})"], ra
        raise EmitError(f"cannot take the value of {e.op}")

    def _value_call(self, e: X.E, t: str) -> tuple:
        """The pointer vocabulary, and `$past`. Everything else is refused by name."""
        f = e.text
        if f == "next":
            a, la, ra = self.value(e.kids[0], t)
            m = self._modulus(e.kids[0].text if e.kids[0].op == "name" else None)
            return f"(({a} + 1) \\ (2*{m}))", la, ra
        if f == "address":
            a, la, ra = self.value(e.kids[0], t)
            m = self._modulus(e.kids[0].text if e.kids[0].op == "name" else None)
            return f"({a} \\ {m})", la, ra
        if f in self.defines and self.defines[f][0] is None:
            # declared vocabulary in a VALUE position: `lineData(E)` names what the design
            # holds for E, mounted by the linkage like any other window
            self.demanded.add(f)
            self.value_windows.add((f, len(e.kids)))
            args = [self.value(k, t)[0] for k in e.kids]
            v = self._fresh("V", f)
            return v, [f"{f}({', '.join(args)}, {v}, {t})"], []
        if f == "$past":
            if t != "T+1":
                raise EmitError("`$past` is only meaningful one instant after the thing it "
                                "refers to")
            return self.value(e.kids[0], "T")
        raise EmitError(f"`{f}(...)` is not a value this stage lowers")

    def _cardinality(self, e: X.E, t: str) -> tuple:
        """`exactly(1, some entry E where P)` without an aggregate: one such thing exists, and
        no two distinct ones do. Counting with `#count` would be shorter and is what this route
        forbids -- an aggregate over a population is the enumeration the whole method avoids.

        Above one the pattern needs N+1 distinct variables and grows accordingly, so it is
        refused by name rather than emitted and regretted later."""
        how, n = e.text, e.kids[0]
        if n.op != "num":
            raise EmitError(f"`{how}` needs a literal count")
        k = int(n.text)
        if k != 1:
            raise EmitError(f"`{how}({k}, ...)` -- only a count of one is lowered. Counting to "
                            f"{k} without an aggregate needs {k + 1} distinct variables in one "
                            f"rule, which grows as the population does")
        inner = e.kids[1]
        if inner.op != "quant":
            raise EmitError(f"`{how}` counts a quantified population")
        q, kind, var = inner.text.split(":")
        self._quantified.add(var)          # this rule's own binding, not a leak from another's
        where, scope = inner.kids
        rules, one = [], self._fresh("one_")
        lits = [self.domain_of(kind, var, "T")]
        for part in (where, scope):
            if part is not None:
                pl, pr = self.lower(part, "T")
                lits += pl
                rules += pr
        rules.append(self._rule(f"{one}(T)", lits))
        two, other = self._fresh("two_"), var + "2"
        # a WORD-BOUNDARY rename, never a substring replace: `E` occurs inside `entryExists`,
        # and a blind replace once turned it into `entryE2xists` -- a predicate nothing defines,
        # which would have made the two-witness rule vacuously false and `exactly(1, ...)`
        # silently weaker. The repo's own norms call this the targeted-edits lesson.
        second = [re.sub(rf"\b{var}\b", other, l) for l in lits]
        rules.append(self._rule(f"{two}(T)", lits + second + [f"{var} != {other}"]))
        if how == "exactly":
            return [f"{one}({t})", f"not {two}({t})"], rules
        if how == "atMost":
            return [f"not {two}({t})"], rules
        return [f"{one}({t})"], rules

    def _kind_of_var(self, var: str):
        if var in self._create_kinds:
            return self._create_kinds[var]
        for n in self.root.walk():
            m = re.search(rf"\b(?:each|some)\s+(\w+)\s+{var}\b", P.notation_of(n))
            if m:
                return m.group(1)
        return None

    def _modulus(self, of=None) -> str:
        """A pointer's modulus is whatever its own declaration says -- `pointer(depth)` here,
        `pointer(entries)` in some other block. It was hardcoded to `depth` in the first
        version, which is exactly the kind of assumption that makes a compiler work on one
        block and quietly mean something else on the next."""
        if of and of in self.moduli:
            return self.moduli[of]
        mods = set(self.moduli.values())
        if len(mods) == 1:
            return mods.pop()
        if not mods:
            raise EmitError("no pointer window is declared, so there is no modulus")
        raise EmitError(f"several pointer moduli are in play ({sorted(mods)}); say which by "
                        f"writing the relation over a named pointer")

    def _sort(self, e: X.E) -> str:
        """Whether an expression's value is NUMERIC or an OPAQUE token.

        This is the signature's control/data split reaching the compiler, and it decides how a
        comparison lowers. A numeric value compares by value. An opaque token has no value to
        compare -- only the EQUALITY THEORY may say whether two tokens name the same thing, and
        it is the same theory the design's own CAM gates evaluate through, so the contract and
        the hardware are answering one question rather than two. Compared by identity instead,
        two tokens the design rightly judges equal look different to the contract, and the
        contract blames the design for its own model of data. (Found live: the miss queue's
        demandAlwaysHasRoom fired on a correct design for exactly this reason -- the defect the
        entry's CERTIFICATE.md predicted any compiler would hit.)"""
        if e.op in ("num", "arith"):
            return "numeric"
        if e.op == "call":
            if e.text in self.defines and self.defines[e.text][0] is None:
                return "opaque"           # declared value vocabulary holds captured payloads
            return "numeric"              # next/address/params -- the pointer world is numeric
        if e.op == "name":
            n = e.text
            if n in self.ports:
                return "opaque" if self.ports[n].get("role") == "opaque" else "numeric"
            if n in self.windows:
                return "opaque" if self.windows[n][0] == "value" else "numeric"
            if n in self.payload_of:
                iface = self.payload_of[n]
                return "opaque" if any(q.get("interface") == iface and q.get("role") == "opaque"
                                       for q in self.ports.values()) else "numeric"
            return "numeric"
        if e.op == "field":
            var = e.kids[0].text if e.kids[0].op == "name" else None
            iface = self.payload_of.get(var)
            if iface:
                port = iface + e.text[0].upper() + e.text[1:]
                q = self.ports.get(port)
                return "opaque" if q and q.get("role") == "opaque" else "numeric"
            return "opaque"               # a kind's attribute window holds captured payloads
        if e.op == "index":
            base = e.kids[0]
            if base.op == "name" and self.ports.get(base.text, {}).get("elements"):
                return "opaque" if self.ports[base.text].get("role") == "opaque" else "numeric"
            if base.op == "name" and base.text in self.windows:
                return "opaque" if self.windows[base.text][0] == "value" else "numeric"
        return "numeric"

    def _eq_theory(self, a, b, la, lb, want: int) -> tuple:
        """An opaque comparison: declare the question, read the answer. The boundary rule's
        body is exactly the literals that bind the two operands, so the declared pair is the
        pair actually compared."""
        self._used_eq = True
        bnd = self._rule(f"boundary(eq({a}, {b}), 1)", la + lb)
        return la + lb + [f"pval(eq({a}, {b}), {want})"], [bnd]

    def _cmp(self, e: X.E, t: str) -> tuple:
        lhs, rhs = e.kids
        # AN EFFECT HAS A TARGET AND A SOURCE, and they are read at different instants. In
        # `##1 bitIndex = bitIndex + 1` the left is what the window will hold NEXT cycle
        # and the right is what it holds NOW: lowering both at the effect's instant said
        # "next cycle's counter is next cycle's counter plus one", which is unsatisfiable,
        # so the behaviour could never be discharged. The miss queue never shows it
        # because every value it captures arrives as an interface payload, which
        # `_bound_at` already pins to the trigger (found by the second block, 2026-09-01).
        src = self._capture_at if (self._capture and self._capture_at) else t
        a, la, ra = self.value(lhs, t)
        b, lb, rb = self.value(rhs, src)
        opaque = "opaque" in (self._sort(lhs), self._sort(rhs))
        if opaque and getattr(self, "_capture", False):
            # an effect's `=` is CAPTURE: the very token flows into the window, so identity
            # is the meaning -- the equality theory would ask whether two independent tokens
            # happen to name one thing, which is a different question
            return la + lb + [f"{a} = {b}"], ra + rb
        if opaque:
            if e.text not in ("==", "!="):
                raise EmitError(f"`{e.text}` on opaque values -- a token has no order, only "
                                f"equality. Declare the port numeric if its order is meant")
            lits, extra = self._eq_theory(a, b, la, lb, 1 if e.text == "==" else 0)
            return lits, ra + rb + extra
        op = {"==": "=", "!=": "!=", "<": "<", "<=": "<=", ">": ">", ">=": ">="}[e.text]
        if op == "=":
            return la + lb + [f"{a} = {b}"], ra + rb
        return la + lb + [f"{a} {op} {b}"], ra + rb

    def relation(self, e: X.E, t: str) -> tuple:
        """`opposite(P, Q)` -- the one relation on pointers that is not a comparison."""
        if e.op == "call" and e.text == "opposite":
            a, la, ra = self.value(e.kids[0], t)
            b, lb, rb = self.value(e.kids[1], t)
            return la + lb + [f"{b} = ({a} + {self._modulus()}) \\ (2*{self._modulus()})"], ra + rb
        if e.op == "call" and e.text == "$stable":
            v = self.value(e.kids[0], "T")
            a, la, ra = v
            b, lb, rb = self.value(e.kids[0], "T+1")
            return la + lb + [f"{a} = {b}"], ra + rb
        return self.lower(e, t)

    # ------------------------------------------------------------------ whole claims
    def claim(self, node, enclosing=()) -> tuple:
        """One `@property` or `@assume`, as (rules, error-or-None).

        The order below is not arbitrary. The ANTECEDENT is lowered first because it is what
        binds things -- `request.valid(R)` introduces R, and the consequent then speaks about
        it. Lowering the consequent first asks about a variable nothing has introduced.
        """
        self._fresh_rule_scope(node.name)
        # the claim's MAIN holds-atom owns the bare `<name>Holds` spelling: reserve it now,
        # so the fresh-name pool cannot take it for an inner helper -- when it did, two
        # lowerings shared one head and a helper negated itself in its own body
        self._used_names.add(f"{node.name}Holds")
        body = "\n".join(P.notation_of(node).splitlines()[1:])
        guard, rules = "live(T)", []
        try:
            m = re.search(r"enable iff\s*\(([^)]*)\)", body)
            if m:
                # the reset exemption made explicit: this claim is judged exactly where the
                # file's `disable iff` would have silenced it
                body = body.replace(m.group(0), "")
                lits, _ = self.lower(X.parse_expr(m.group(1)), "T")
                guard = ", ".join(lits)

            # a claim may be wrapped in a quantifier -- over an index domain or an object kind
            over_vars, over_lits = [], []
            for kind, var in enclosing:
                self._quantified.add(var)
                over_vars.append(var)
                over_lits.append(self.domain_of(kind, var, "T"))
            binders = re.match(r"\s*((?:each\s+\w+\s+[A-Z]\w*\s*,\s*)*"
                               r"each\s+\w+\s+[A-Z]\w*)\s*(?:where\s+(.*?))?\((.*)\)\s*$",
                               body.strip(), re.S)
            if binders:
                for kind, var in re.findall(r"each\s+(\w+)\s+([A-Z]\w*)", binders.group(1)):
                    self._quantified.add(var)
                    over_vars.append(var)
                    over_lits.append(self.domain_of(kind, var, "T"))
                if binders.group(2):
                    wl, wr = self.lower(X.parse_expr(binders.group(2)), "T")
                    over_lits += wl
                    rules += wr
                body = binders.group(3)

            ant, arrow, cons = X.split_claim(body)
            if arrow is None:
                return [], f"{node.name}: no `|->`, `|=>` or `always`"
            later = arrow == "|=>"

            head_lits = []
            if ant:
                head_lits, arules = self.lower(X.parse_expr(ant), "T")
                rules += arules

            lo, hi, cons = X.strip_delay(cons)
            ranged = lo is not None and lo != hi
            self._open = []
            # the claim's temporal depth feeds the K RECOMMENDATION (the route's rule: when
            # the step fails, raise K toward the deepest reference BEFORE writing an
            # invariant). A symbolic bound like `depth` is kept as its name.
            span = hi if lo is not None else (1 if later else 0)
            self.spans[node.name] = span
            t = "T+K" if ranged else (f"T+{lo}" if lo else ("T+1" if later else "T"))

            if ranged:
                self._open = [f"K = {lo}..{hi}"]
            clits, crules = self.lower(X.parse_expr(cons), t)
            self._open = []
            rules += crules

            name = f"{node.name}Holds"
            args = ", ".join(over_vars + ["T"])
            # every helper needs a POSITIVE literal binding its instant: a consequent that is
            # only a negation leaves T unbound, and clingo refuses the rule as unsafe rather
            # than guessing which instants were meant
            floor = ["gtime(T)"]
            if ranged:
                # `##[a:b] Q` -- Q must hold at SOME instant in the window, so the helper is a
                # witness over it rather than a claim about one instant
                floor += [f"K = {lo}..{hi}", "gtime(T+K)"]
                self._open = [f"K = {lo}..{hi}"]
            elif lo:
                floor.append(f"gtime(T+{lo})")
            elif later:
                floor.append("gtime(T+1)")
            # the helper's body must BIND what its head carries: a consequent that is all
            # negations mentions E without binding it, so the carried variables bring their
            # domain literals along. Adding them cannot change the verdict -- the failure rule
            # only ever asks about objects already inside those domains.
            rules.append(f"{name}({args}) :- {', '.join(floor + over_lits + clits)}.")

            if guard == "live(T)":
                self._exempt(head_lits + clits)
            head = [self._lv()] if guard == "live(T)" else ["gtime(T)", guard]
            if later or lo:
                head.append(self._lv(f"T+{hi if ranged else (lo or 1)}"))
            head += over_lits + head_lits
            # the failure is stamped at the DETERMINATION instant -- where the wrongness
            # appears, not where its trigger fired. For `|=>` that is T+1; for a ranged window
            # it is the instant the last chance was missed, which is the only well-defined
            # choice there. The stamp is the first line of diagnosis, and a report pointing
            # one cycle before its own evidence wastes exactly the person it exists for. This
            # also matches the route's hand-written contracts, so the two kinds read alike.
            if node.kind == "@assume":
                # an assumption is a CONSTRAINT on the world, not a report about it: executions
                # that violate it are excluded, so no property is ever judged on a run the
                # environment promised would not happen. Lowering it as a failType -- which the
                # first version did, unexercised because the FIFO has no assumptions -- made
                # the certificate blame the design for the world's behaviour.
                rules.append(f":- {', '.join(head)}, not {name}({args}).")
            else:
                stamp = f"T+{hi}" if ranged else (f"T+{lo}" if lo else ("T+1" if later else "T"))
                rules.append(f"failType({node.name}, {stamp}) :- {', '.join(head)}, "
                             f"not {name}({args}).")
        except (X.ExprError, EmitError) as e:
            return [], f"{node.name}: {e}"
        return rules, None

    @staticmethod
    def _retime(lits, later: bool) -> list:
        return lits

    def contract_file(self) -> tuple:
        """A complete, runnable contract: the preamble derived from the SIGNATURE, then the
        rules. Nothing here is hand-added -- the `#const` lines come from the parameters'
        defaults and `live` from the reset's own polarity, because a preamble somebody has to
        remember to write is a preamble that will one day disagree with the signature it
        paraphrases."""
        rules, refused = self.contract()
        lines = [f"% GENERATED from {self.root.name} and its signature -- do not edit. The",
                 "% comparison against a hand-written contract is on VERDICTS, never on text."]
        for prm in self.sig.get("parameters") or []:
            if prm.get("default") is not None:
                lines.append(f"#const {prm['name']} = {prm['default']}.")
        if self.reset:
            on = 1 if self.reset.get("polarity") == "active_low" else 0
            lines.append(f"live(T) :- val({self.reset['name']}, {on}, T).")
        else:
            # NO RESET DECLARED: every instant is judged. A pure transition relation is
            # legitimate ("true from any state"), but a contract whose every monitor is
            # guarded by `live(T)` with nothing deriving it certifies ANYTHING -- a false
            # property was reported INDUCTIVE on a reset-less block, and the only symptom was
            # every scenario reporting "no compliant state" (the third block's G26, 2026-09-02).
            lines.append("live(T) :- gtime(T).")
        deepest = 0
        sym = []
        for v in self.spans.values():
            if isinstance(v, int):
                deepest = max(deepest, v)
            else:
                sym.append(v)
        hint = " / ".join([str(deepest)] + sorted(set(sym))) if (deepest or sym) else "0"
        lines += ["",
            f"% deepest temporal reference in the claim set: {hint} cycle(s). If the",
            "% induction step fails, RAISE K TOWARD THIS before writing an invariant -- the",
            "% route's rule, with an incident behind it: an invariant was once added here",
            "% while the real cause was elsewhere, and it survived as cargo until a",
            "% measurement showed the set inductive at K=1 without it."]
        if self._any_input:
            lines += ["",
                "% every scenario's INPUT slot: no constraint beyond the machine being out of",
                "% reset. The runner asserts `:- not holds(Input, 0).`, so an undefined input",
                "% name is an unsatisfiable demand, not a permissive one -- the lesson the",
                "% hand-written contract paid for when all six scenarios reported",
                "% 'no compliant state' over one missing line.",
                "holds(any_input, T) :- live(T)."]
        if self._used_eq:
            lines += ["",
                "% The equality theory's CONCRETE half, carried by the contract itself so it is",
                "% independent of the design's reading. The runner loads the symbolic companion",
                "% only when the design declares data() -- a concrete design never does, and",
                "% without this rule every declared boundary would be an atom nothing derives,",
                "% making each opaque comparison silently unsatisfiable. Concrete operands",
                "% compute; token operands leave this rule silent and take the theory's free",
                "% bits instead. (Found on the FIFO, whose design is concrete while its",
                "% signature rightly calls the payload opaque.)",
                "pval(P, V) :- boundary(P, _), P = eq(A, B), @issym(A) = 0, @issym(B) = 0, "
                "V = @eq(A, B)."]
        if self._used_bit:
            lines += ["",
                "% A BIT OF A PORT, the same way: declared as a boundary and read back, so a",
                "% claim relating a multi-bit port to per-bit state costs one free bit per",
                "% (value, position) instead of enumerating the word. Concrete operands",
                "% compute it here; a token operand leaves this rule silent and takes the",
                "% theory's free bit, exactly as an opaque comparison does.",
                "pval(P, V) :- boundary(P, _), P = bit(A, I), @issym(A) = 0, "
                "V = @slc(A, I, 1)."]
        text = "\n".join(lines) + "\n\n" + "\n".join(rules) + "\n"
        probs = wellformed_problems(text)
        if probs:
            raise EmitError("the generated contract is malformed -- refusing to emit it:\n  "
                            + "\n  ".join(probs))
        return text, refused

    def _fresh_rule_scope(self, decl: str | None = None) -> None:
        """Bindings are PER DECLARATION. `payload_of` leaked across rules once: forwardDemand's
        `as D` made a later scenario's entry variable D look like a forward payload, and
        `D.address` went hunting for a forwardAddress port. A variable means what its own
        declaration binds it to, nothing more. The declaration's NAME comes along so every
        auxiliary atom can carry it -- names are for people."""
        self.payload_of = {}
        self._bound_at = {}
        self._quantified = set()
        self._decl = decl
        self._used_names = set()
        self._port_sample = {}     # (port, instant) -> the ONE sample variable this declaration reads
        self._live = "live"

    def scenario(self, node, enclosing=()) -> tuple:
        """One `@scenario`, in the runner's own shape: a SITUATION the machine is placed in
        (a compliant abstract start -- the properties are assumed, so the state is one the
        design could be in), one cycle, and an EXPECTATION read off the window's instants.
        A `some` wrapper folds into the situation: the solver's job is to find a compliant
        state where such an object exists, which is the existential read."""
        self._fresh_rule_scope(node.name)
        body = "\n".join(P.notation_of(node).splitlines()[1:])
        rules, extra = [], []
        try:
            for kind, var in enclosing:
                self._quantified.add(var)
                extra.append(self.domain_of(kind, var, "T"))
            universal = []          # (var, its domain literal) for each `each` binder
            while True:
                got = self._split_binder(body)
                if got is None:
                    break
                bs, where, inner = got
                for quant, kind, var in bs:
                    self._quantified.add(var)
                    dom = self.domain_of(kind, var, "T")
                    extra.append(dom)
                    if quant == "each":
                        universal.append((var, dom))
                if where:
                    wl, wr = self.lower(X.parse_expr(where), "T")
                    extra += wl
                    rules += wr
                body = inner
            ant, arrow, cons = X.split_claim(body)
            if arrow not in ("|->", "|=>"):
                return [], f"{node.name}: a scenario is `situation |-> expectation` or `|=>`"
            al, ar = self.lower(X.parse_expr(ant), "T")
            rules += ar
            sit = extra + al
            rules.append(self._rule(f"holds({node.name}S, T)", sit))
            at = "1" if arrow == "|=>" else "0"
            a0 = [l.replace(", T)", ", 0)").replace("(T)", "(0)") for l in sit]
            cl, cr = self.lower(X.parse_expr(cons), at)
            rules += cr
            if universal:
                # A UNIVERSAL SCENARIO IS NOT AN EXISTENTIAL ONE, and folding it into the
                # situation the way a `some` folds would say "there is a position where the
                # expectation holds" under a name that promises every position. That is the
                # failure mode this route ranks worst: not a gap but a check that claims more
                # than it tests. So the expectation is discharged per position and the
                # scenario is reached only when NO position violates it.
                for var, _dom in universal:
                    if any(re.search(rf"\b{var}\b", l) for l in al):
                        return [], (f"{node.name}: a universal scenario whose SITUATION "
                                    f"mentions {var} is not lowered -- say the situation "
                                    f"without the position and the expectation with it")
                # the instant is FIXED by the scenario (0 for `|->`, 1 for `|=>`), so the
                # helper carries the position and not a time -- a head with a `T` its body
                # never reads is a rule nobody can check by eye
                vs = ", ".join(v for v, _ in universal)
                doms = [d.replace(", T)", f", {at})") for _v, d in universal]
                ok, bad = f"{node.name}Ok", f"{node.name}Counterex"
                rules.append(f"{ok}({vs}) :- {', '.join([f'gtime({at})'] + doms + cl)}.")
                rules.append(f"{bad} :- "
                             + ", ".join([f"gtime({at})"] + doms + [f"not {ok}({vs})"])
                             + ".")
                keep = [l for l in a0
                        if not any(re.search(rf"\b{v}\b", l) for v, _ in universal)]
                rules.append(f"did({node.name}D) :- {', '.join(keep + ['not ' + bad])}.")
            else:
                rules.append(f"did({node.name}D) :- {', '.join(a0 + cl)}.")
            rules.append(f"scenario({node.name}, {node.name}S, any_input, {node.name}D).")
            self._any_input = True
        except (X.ExprError, EmitError) as e:
            return [], f"{node.name}: {e}"
        return rules, None

    def contract(self) -> tuple:
        """The whole claim half of the contract, plus whatever could not be lowered.

        The walk CARRIES the enclosing quantifier blocks' binders down to each claim. Without
        that, a claim written inside `each entry E:` lowers as though E were nobody's -- its
        helper drops the variable, and the per-entry obligation quietly becomes "some entry",
        which a DIFFERENT entry can discharge. That bug shipped in the first version of this
        function and was caught by reading the miss queue's generated rules, not by any gate:
        the weaker claim still certifies the real design."""
        out, refused = [], []

        def walk(node, enclosing):
            for n in node.children:
                if n.kind == "quantifier":
                    binders = re.findall(r"(?:each|some)\s+(\w+)\s+([A-Z]\w*)", n.header)
                    walk(n, enclosing + binders)
                elif n.kind in ("@property", "@assume"):
                    rules, err = self.claim(n, enclosing)
                    if err:
                        refused.append(err)
                    else:
                        out.extend(rules)
                elif n.kind == "@scenario":
                    rules, err = self.scenario(n, enclosing)
                    if err:
                        refused.append(err)
                    else:
                        out.extend(rules)
                elif n.kind == "@behavior":
                    rules, err = self.behaviour(n, enclosing)
                    if err:
                        refused.append(err)
                    else:
                        out.extend(rules)
                else:
                    walk(n, enclosing)

        walk(self.root, [])
        out += self.frames()
        out += self._single_valued()
        return list(self._defined.values()) + out, refused

    # ================================================================== Stage 3: behaviours
    # A behaviour is a JUDGEMENT ON THE DESIGN, and it lowers to two monitor families
    # (TRANSLATION.md 3.3): the EVENT -- the trigger fired, so the window must show the
    # consequence -- and the FRAME -- nothing that writes this window fired, so it must not
    # have changed. The frame is why behaviours matter: it is the half that catches a slot
    # doing something NOBODY asked for, which no claim states and no event monitor sees.

    _CMD_ACCEPT = re.compile(r"^(accept|refuse)\s+([A-Z]\w*)$")
    _CMD_READY = re.compile(r"^ready on\s+(\w+)$")
    _CMD_HOLD = re.compile(r"^hold\s+(\w+)\s+(high|low)$")
    _CMD_DRIVE = re.compile(r"^drive\s+(\w+)\s+with\s+(.+)$", re.S)
    _CMD_SEND = re.compile(r"^send on\s+(\w+)(?:\s+as\s+([A-Z]\w*))?"
                           r"(?:\s+answering\s+([A-Z]\w*))?\s+with\s+(.+)$", re.S)
    _CMD_CREATE = re.compile(r"^create\s+(\w+)\s+([A-Z]\w*)(?:\s*:\s*(.*))?$", re.S)
    _CMD_DELAY = re.compile(r"^##(\d+)\s+(.+)$", re.S)
    _SCOPED = re.compile(r"^(each|some)\s+(\w+)\s+([A-Z]\w*)\s*"
                         r"(?:where\s+(.*?))?\s*:\s*(.+)$", re.S)

    @staticmethod
    def _split_binder(text: str):
        """`some entry E where P ( body )` split correctly. A regex with a non-greedy
        `where (.*?)` stops at the FIRST parenthesis -- which is `joinable(`'s, inside the
        condition -- and hands back garbage. The scope's paren is the one preceded by
        whitespace at depth zero (parse.py's own rule), so this scans for it."""
        binders = []
        rest = text.strip()
        while True:
            m = re.match(r"\s*(some|each)\s+(\w+)\s+([A-Z]\w*)\s*(.*)$", rest, re.S)
            if not m:
                return None
            binders.append((m.group(1), m.group(2), m.group(3)))
            rest = m.group(4)
            if rest.startswith(","):
                rest = rest[1:]
                continue
            break
        quant, kind, var = binders[-1]
        where = None
        if rest.startswith("where"):
            body = rest[len("where"):]
            depth = 0
            for i, ch in enumerate(body):
                if ch == "(":
                    if depth == 0 and i > 0 and body[i-1].isspace():
                        where = body[:i].strip()
                        inner, tail = Emitter._match_paren(body, i)
                        if inner is None or tail.strip():
                            return None
                        return binders, where, inner
                    depth += 1
                elif ch == ")":
                    depth -= 1
            return None
        if rest.lstrip().startswith("("):
            i = rest.index("(")
            inner, tail = Emitter._match_paren(rest, i)
            if inner is None or tail.strip():
                return None
            return binders, None, inner
        return None

    @staticmethod
    def _match_paren(text: str, at: int):
        depth = 0
        for j in range(at, len(text)):
            if text[j] == "(":
                depth += 1
            elif text[j] == ")":
                depth -= 1
                if depth == 0:
                    return text[at+1:j], text[j+1:]
        return None, ""

    def _ready_port(self, iface: str):
        q = next((q for q in self.ports.values()
                  if q.get("interface") == iface and q.get("role") == "ready"), None)
        if q is None:
            raise EmitError(f"the {iface} interface has no ready port to command")
        return q["name"], (0 if q.get("active", "high") == "low" else 1)

    def _capture_expr(self, text: str, t: str, at: str | None = None) -> tuple:
        """An EFFECT expression: `=` and `==` are CAPTURE -- the very token flows into the
        window -- so both lower by identity, never through the equality theory. A compare in a
        claim asks whether two independent tokens name one thing; a capture in an effect says
        the design copied this one, and identity is exactly that."""
        text = re.sub(r"\bend\s+([A-Z]\w*)", r"!exists(\1)", text)
        text = re.sub(r"(?<![=!<>])=(?!=)", "==", text)
        old, self._capture = self._capture, True
        old_at, self._capture_at = self._capture_at, at
        try:
            return self.lower(X.parse_expr(text), t)
        finally:
            self._capture, self._capture_at = old, old_at

    def behaviour(self, node, enclosing=()) -> tuple:
        """One `@behavior`: the event monitors, plus writer registrations for the frame."""
        self._fresh_rule_scope(node.name)
        body = "\n".join(P.notation_of(node).splitlines()[1:])
        rules, scope_lits = [], []
        try:
            for kind, var in enclosing:
                self._quantified.add(var)
                scope_lits.append(self.domain_of(kind, var, "T"))
            # top-level quantifier wrappers: `some entry E where P ( trigger -> effects )`
            witness = None            # a `some` wrapper's scope: a witness, not a universal
            while True:
                got = self._split_binder(body)
                if got is None:
                    break
                bs, where, inner = got
                quant = bs[-1][0]
                w_lits = []
                for _, kind, var in bs:
                    self._quantified.add(var)
                    w_lits.append(self.domain_of(kind, var, "T"))
                if where:
                    wl, wr = self.lower(X.parse_expr(where), "T")
                    w_lits += wl
                    rules += wr
                if quant == "some":
                    if witness is not None:
                        return [], f"{node.name}: two `some` wrappers -- not lowered"
                    witness = (var, w_lits)
                else:
                    scope_lits += w_lits
                body = inner
            depth = 0
            cut = None
            for i in range(len(body) - 1):
                if body[i] == "(":
                    depth += 1
                elif body[i] == ")":
                    depth -= 1
                elif depth == 0 and body[i:i+2] == "->" and body[i-1] not in "|=<":
                    cut = i
                    break
            if cut is None:
                return [], f"{node.name}: no `->`"
            tl, tr = self.lower(X.parse_expr(body[:cut]), "T")
            rules += tr
            trigger = scope_lits + tl
            # a behaviour that names the reset is judged during the reset, like a claim
            # that names it -- otherwise "reset forces the phase to idle" is a monitor
            # requiring the reset both high and low at one instant
            self._exempt(trigger)
            if witness is not None:
                # `some entry E where P ( trigger -> effect )`: when the trigger holds and
                # SOME scope-satisfying object exists, the design must serve SOME of them --
                # which one is implementation freedom. Folding the scope into the trigger
                # instead demands the effect of EVERY such object at once: askMemory would
                # require every eligible address on one wire in one cycle. The witness shape:
                # any(T) says one exists; sat(T) says one is served; the failure is any
                # without sat.
                var, w_lits = witness
                # the trigger may REFERENCE the witness (`E.address == R.address`), so both
                # `any` and `sat` carry scope AND trigger together; the failure needs only
                # `live` outside them. askMemory's trigger does not mention E and loses
                # nothing; the lift's does, and splitting it left E unbound.
                any_h = self._fresh("anyw_")
                rules.append(self._rule(f"{any_h}(T)", w_lits + tl))
                for item in self._effect_items(body[cut+2:]):
                    item = item.strip()
                    if not item:
                        continue
                    aux, guards, stamp, check = self._effect_core(item)
                    if check is None:
                        return [], (f"{node.name}: effect not lowered under a `some` "
                                    f"wrapper: {item[:50]!r}")
                    self._register_writers(item, w_lits + tl, var)
                    sat = self._fresh("satw_")
                    rules += aux
                    rules.append(self._rule(f"{sat}(T)", w_lits + tl + [check]))
                    rules.append(f"failType({node.name}Wrong, {stamp}) :- {self._lv()}, "
                                 f"{', '.join(guards)+', ' if guards else ''}{any_h}(T), "
                                 f"not {sat}(T).")
                return rules, None
            items = self._effect_items(body[cut+2:])
            create_var, create_caps, delayed_about_create = None, [], []
            for item in items:
                item = item.strip()
                if not item:
                    continue
                m = self._CMD_CREATE.match(item)
                if m:
                    create_var = m.group(2)
                    self._quantified.add(create_var)
                    self._create_kinds[create_var] = m.group(1)
                    if m.group(3):
                        create_caps = [a.strip() for a in m.group(3).split(",")]
                    continue
                m = self._CMD_DELAY.match(item)
                if m and create_var and re.search(rf"\b{create_var}\b", m.group(2)):
                    delayed_about_create.append((int(m.group(1)), m.group(2)))
                    continue
                rules += self._effect(node.name, trigger, item)
            if create_var:
                rules += self._create_monitor(node.name, trigger, create_var,
                                              create_caps, delayed_about_create)
        except (X.ExprError, EmitError) as e:
            return [], f"{node.name}: {e}"
        return rules, None

    def _effect_items(self, text: str) -> list:
        """Effect constructions, one per item. Two holds keep multi-line items whole: open
        PARENTHESES (an `exactly(1, some ... ( ... ))` spans lines, and cutting it per line
        hands the parser fragments), and a COLON scope, which by the language's own rule runs
        to the end of the declaration."""
        out, buf, depth, colon = [], [], 0, False
        for line in text.splitlines():
            if not line.strip() and not buf:
                continue
            buf.append(line)
            if colon:
                continue
            depth += line.count("(") - line.count(")")
            if depth == 0:
                if len(buf) == 1 and re.match(
                        r"^\s*(each|some)\s+\w+\s+[A-Z]\w*.*:", line.strip()):
                    colon = True
                    continue
                out.append("\n".join(buf))
                buf = []
        if buf:
            out.append("\n".join(buf))
        return out

    def _effect_core(self, item) -> tuple:
        """One simple construction as (aux_rules, time_guards, stamp, check): the single
        literal that must HOLD for the effect to have happened. The two composers differ only
        in what they do with the check -- the universal one demands it under the trigger, the
        witness one demands that SOME scope-satisfying object provides it. Scoped and
        `exactly` items compose internally and return check=None."""
        t = "T"
        m = self._CMD_ACCEPT.match(item)
        if m:
            iface = self.payload_of.get(m.group(2))
            if iface is None:
                raise EmitError(f"`{m.group(1)} {m.group(2)}` -- nothing binds {m.group(2)}")
            port, on = self._ready_port(iface)
            want = on if m.group(1) == "accept" else 1 - on
            return [], [], "T", f"val({port}, {want}, T)"
        m = self._CMD_READY.match(item)
        if m:
            port, on = self._ready_port(m.group(1))
            return [], [], "T", f"val({port}, {on}, T)"
        m = self._CMD_HOLD.match(item)
        if m:
            return [], [], "T", f"val({m.group(1)}, {1 if m.group(2) == 'high' else 0}, T)"
        m = self._CMD_DRIVE.match(item)
        if m:
            iface = m.group(1)
            vq = next(q for q in self.ports.values()
                      if q.get("interface") == iface and q.get("role") == "valid")
            data = [q for q in self.ports.values()
                    if q.get("interface") == iface and q.get("role") in ("opaque", "numeric")]
            if len(data) != 1:
                raise EmitError(f"`drive {iface}` needs exactly one payload port")
            v, vl, vr = self.value(X.parse_expr(m.group(2)), t)
            h = self._fresh("did_")
            car = self._carried(vl)
            args = ", ".join(car + ["T"])
            aux = vr + [self._rule(f"{h}({args})",
                                   vl + [f"val({vq['name']}, 1, T)",
                                         f"val({data[0]['name']}, {v}, T)"])]
            return aux, [], "T", f"{h}({args})"
        m = self._CMD_SEND.match(item)
        if m:
            iface, answering, payload = m.group(1), m.group(3), m.group(4)
            vq = next(q for q in self.ports.values()
                      if q.get("interface") == iface and q.get("role") == "valid")
            lits = [f"val({vq['name']}, 1, T)"]
            aux = []
            if answering:
                self.demanded.add("forwarded")
                lits.append(f"forwarded({answering}, T)")
            for part in payload.split(","):
                f, expr = part.split("=", 1)
                port = iface + f.strip()[0].upper() + f.strip()[1:]
                if port not in self.ports:
                    raise EmitError(f"`send on {iface}` -- no port {port!r}")
                v, vl, vr = self.value(X.parse_expr(expr.strip()), t)
                lits += vl + [f"val({port}, {v}, T)"]
                aux += vr
            h = self._fresh("did_")
            car = self._carried(lits)
            args = ", ".join(car + ["T"])
            return aux + [self._rule(f"{h}({args})", lits)], [], "T", f"{h}({args})"
        m = self._CMD_DELAY.match(item)
        if m:
            n, expr = int(m.group(1)), m.group(2)
            cl, cr = self._capture_expr(expr, f"T+{n}", at="T")
            h = self._fresh("did_")
            car = self._carried(cl)
            args = ", ".join(car + ["T"])
            aux = cr + [self._rule(f"{h}({args})", self._domains(car) + cl)]
            return aux, [self._lv(f"T+{n}")], f"T+{n}", f"{h}({args})"
        return None, None, None, None

    def _effect(self, name, trigger, item) -> list:
        """The UNIVERSAL composer: the trigger held, so the check must hold. Scoped items and
        `exactly` compose per-object internally; simple items go through the core."""
        aux, guards, stamp, check = self._effect_core(item)
        if check is not None:
            self._register_writers(item, trigger)
            return aux + [f"failType({name}Wrong, {stamp}) :- {self._lv()}, "
                          f"{', '.join(guards + trigger)}, not {check}."]
        m = self._SCOPED.match(item)
        if m:
            quant, kind, var, where, rest = m.groups()
            self._quantified.add(var)
            scope = [self.domain_of(kind, var, "T")]
            rules = []
            if where:
                wl, wr = self.lower(X.parse_expr(where), "T")
                scope += wl
                rules += wr
            for sub in self._effect_items(rest):
                sub = sub.strip()
                if not sub:
                    continue
                aux, guards, stamp, check = self._effect_core(sub)
                if check is None:
                    raise EmitError(f"effect not lowered inside a scope: {sub[:50]!r}")
                self._register_writers(sub, trigger + scope, var)
                rules += aux + [f"failType({name}Wrong, {stamp}) :- {self._lv()}, "
                                f"{', '.join(guards + trigger + scope)}, not {check}."]
            return rules
        if item.startswith("exactly(1,"):
            inner = item[len("exactly(1,"):].rstrip()
            if inner.endswith(")"):
                inner = inner[:-1]
            got = self._split_binder(inner)
            if got is None:
                raise EmitError("`exactly(1, ...)` in an effect wraps a scoped `some`")
            bs, where, rest = got
            (_, kind, var) = bs[-1]
            self._quantified.add(var)
            scope = [self.domain_of(kind, var, "T")]
            rules = []
            if where:
                wl, wr = self.lower(X.parse_expr(where), "T")
                scope += wl
                rules += wr
            # the MARKER: `answering E` names the served object, and every per-object demand
            # is about the SERVED one, never about all scope-satisfying ones -- the design
            # chooses which to serve, and that freedom is the point of `some`.
            marker = None
            items = [x.strip() for x in self._effect_items(rest) if x.strip()]
            for sub in items:
                sm = self._CMD_SEND.match(sub)
                if sm and sm.group(3):
                    marker = sm.group(3)
            if marker is None:
                raise EmitError("`exactly(1, ...)` needs a `send ... answering X` marker")
            self.demanded.add("forwarded")
            mark = f"forwarded({marker}, T)"
            # existence: the trigger held and something in scope exists, so SOME object is
            # marked and satisfies every sub-item's check
            any_h, sat = self._fresh("anyx_"), self._fresh("satx_")
            rules.append(self._rule(f"{any_h}(T)", scope))
            sat_lits = list(scope) + [mark]
            for sub in items:
                aux, guards, stamp, check = self._effect_core(sub)
                if check is None:
                    raise EmitError(f"effect not lowered inside exactly: {sub[:50]!r}")
                self._register_writers(sub, trigger + [f"entryId({marker})", mark], marker)
                rules += aux
                sat_lits.append(check)
                # per-SERVED correctness: whichever object the design marked must satisfy
                rules.append(f"failType({name}Wrong, {stamp}) :- {self._lv()}, "
                             f"{', '.join(guards + trigger)}, entryId({marker}), {mark}, "
                             f"not {check}.")
            rules.append(self._rule(f"{sat}(T)", sat_lits))
            rules.append(f"failType({name}Wrong, T) :- {self._lv()}, {', '.join(trigger)}, "
                         f"{any_h}(T), not {sat}(T).")
            # exactly ONE: two distinct marked objects is a failure in itself
            rules.append(f"failType({name}Wrong, T) :- {self._lv()}, entryId({marker}), "
                         f"entryId({marker}2), forwarded({marker}, T), "
                         f"forwarded({marker}2, T), {marker} != {marker}2.")
            return rules
        raise EmitError(f"effect not lowered: {item.splitlines()[0][:60]!r}")

    def _register_writers(self, expr_text: str, cause, var=None) -> None:
        """Which windows this effect WRITES, for the frame. A positive mention sets, a negated
        one clears, a capture writes a value. The cause is the trigger-plus-scope that licensed
        the write, recorded so the frame can say `not <some cause>`.

        An entry is `(cause, keys, aux)`. `keys` are the terms the licence is SPECIFIC to and
        `aux` any rules reading them needed. Both are empty on the object path, which names its
        own key `E` directly; an indexed window carries its position, so that a capture at bit
        three licenses a change at bit three and nowhere else.
        """
        expr_text = re.sub(r"\bend\s+([A-Z]\w*)", r"!exists(\1)", expr_text)
        for m in re.finditer(r"(!?)\s*(\w+)\(([A-Z]\w*)\)", expr_text):
            neg, w, v = m.group(1) == "!", m.group(2), m.group(3)
            if w == "exists":
                self._writers.setdefault(("exists", "clear" if neg else "set"),
                                         []).append((cause, [], []))
            elif w in self.defines and self.defines[w][0] is None:
                self._writers.setdefault((w, "clear" if neg else "set"),
                                         []).append((cause, [], []))
        for m in re.finditer(r"([A-Z]\w*)\.(\w+)\s*==?[^=]", expr_text):
            v, field = m.groups()
            kind = self._kind_of_var(v)
            if kind and v not in self.payload_of:
                self._writers.setdefault(
                    (kind + field[0].upper() + field[1:], "write"), []).append((cause, [], []))
        for m in re.finditer(r"(\w+)\(([A-Z]\w*)\)\s*==?[^=]", expr_text):
            f = m.group(1)
            if f in self.defines and self.defines[f][0] is None:
                self._writers.setdefault((f, "write"), []).append((cause, [], []))
        # A WINDOW THE SPECIFICATION DECLARED FOR ITSELF -- a scalar phase, a counter, an
        # array indexed by a declared domain. Every pattern above requires an uppercase
        # OBJECT VARIABLE, so a block whose state is not objects registered no writer at
        # all and therefore got no frame: its contract said what each event does and never
        # said the state holds otherwise, which is a contract that means less than it looks
        # like it means (the second block's G13, 2026-09-02).
        m = re.match(r"\s*(?:##\d+\s+)?(\w+)(?:\[([^\]]+)\])?\s*==?(?!=)\s*\S", expr_text)
        if m and m.group(1) in self.windows:
            w, idx = m.group(1), m.group(2)
            keys, lits, aux = [], [], []
            if idx is not None:
                # THE POSITION IS READ WHERE THE EVENT HAPPENED, exactly as the effect
                # itself reads it -- which position a write lands on is decided by the
                # index now, not by what the index will hold next cycle.
                #
                # Reading it a second time here is BOOKKEEPING, so it must not consume
                # names: a value variable is local to its rule, and letting this call
                # advance the pool renamed the variables in every rule after it. Names are
                # for people, and churn in them is noise in the one artifact a person is
                # asked to read.
                mark, used = self._n, set(self._used_names)
                try:
                    a, la, ra = self.value(X.parse_expr(idx), "T")
                finally:
                    self._n, self._used_names = mark, used
                keys, lits, aux = [a], la, ra
            self._writers.setdefault((w, "write"), []).append(
                (list(cause) + lits, keys, aux))

    def frames(self) -> list:
        """The frame monitors: for every window the specification's behaviours write, a change
        with no licensed cause is a named failure. Windows nobody writes get pure stability.
        The guard `exists at both instants` keeps allocation and death out of every frame --
        they have their own monitors (appeared/vanished)."""
        out = []
        both = ("entryExists(E, T)", "entryExists(E, T+1)")
        bools = [w for w in sorted(self.demanded)
                 if w not in ("entryExists", "forwarded", "corresponds")
                 and not any(k[0] == w and k[1] == "write" for k in self._writers)
                 and w in self.defines and self.defines[w][0] is None
                 and self.defines[w][1]]
        for w in bools:
            for frm, to, mode in ((1, 0, "clear"), (0, 1, "set")):
                may = f"may{w[0].upper()}{w[1:]}{mode.capitalize()}"
                for cause, _keys, _aux in self._writers.get((w, mode), []):
                    out.append(self._rule(f"{may}(E, T)",
                                          ["entryId(E)"] + [c for c in cause]))
                state = f"{w}(E, T)" if frm else f"not {w}(E, T)"
                after = f"not {w}(E, T+1)" if to == 0 else f"{w}(E, T+1)"
                out.append(f"failType({w}Disturbed, T+1) :- live(T), live(T+1), "
                           f"{both[0]}, {both[1]}, {state}, not {may}(E, T), {after}.")
        values = sorted(({k[0] for k in self._writers if k[1] == "write"} - set(self.windows)) |
                        {"entryAddress"} & self.demanded)
        for w in sorted(set(values) | ({"entryAddress"} & self.demanded)):
            may = f"may{w[0].upper()}{w[1:]}Write"
            for cause, _keys, _aux in self._writers.get((w, "write"), []):
                out.append(self._rule(f"{may}(E, T)", ["entryId(E)"] + list(cause)))
            out.append(f"failType({w}Disturbed, T+1) :- live(T), live(T+1), "
                       f"{both[0]}, {both[1]}, {w}(E, V, T), not {may}(E, T), "
                       f"not {w}(E, V, T+1).")
        # THE LIFECYCLE PAIR BELONGS TO BLOCKS THAT HAVE OBJECTS. Emitted unconditionally,
        # they gave a block with no objects at all -- a framing FSM, a counter -- two
        # monitors over `entryExists` and `entryId` that nothing in its design could
        # mount. Inert rather than wrong, since the atoms are never derived, but a
        # contract should not carry promises about a population the specification never
        # mentions (found with the second block's gaps, 2026-09-01).
        out += self._declared_frames()
        if "entryExists" in self.demanded:
            for cause, _keys, _aux in self._writers.get(("exists", "set"), []):
                out.append(self._rule("mayAllocate(T)", list(cause)))
            out.append("failType(entryAppeared, T+1) :- live(T), live(T+1), entryId(E), "
                       "not entryExists(E, T), not mayAllocate(T), entryExists(E, T+1).")
            for cause, _keys, _aux in self._writers.get(("exists", "clear"), []):
                out.append(self._rule("mayVanish(E, T)", ["entryId(E)"] + list(cause)))
            out.append("failType(entryVanished, T+1) :- live(T), live(T+1), "
                       "entryExists(E, T), not mayVanish(E, T), not entryExists(E, T+1).")
        return out

    def _single_valued(self) -> list:
        """A WINDOW HOLDS ONE VALUE AT AN INSTANT, and that is checked rather than assumed.

        Nothing in the machinery made it true. A window is a derived view of the design, and
        every window in the corpus happens to be mounted from exactly one `val/3` atom --
        which the translator's schema makes single-valued per cycle -- so the property came
        for free and was never stated. A linkage that mounts one window from several rules or
        several signals (a one-hot phase, a window defined case by case) has no such
        guarantee, and the failure is the MASKING direction: a claim reads `w(V, T), V = x`,
        which asks whether SOME value is x, so a spurious second value SATISFIES a claim the
        design violates. Measured: with a phase holding both `idle` and `presenting`, "done
        implies presenting" comes back satisfied.

        **A monitor, deliberately, and not an integrity constraint.** A constraint would
        EXCLUDE the multi-valued executions, so a linkage that really is multi-valued would
        make the program unsatisfiable -- and UNSAT reads as "no counterexample", which is
        exactly how two translator defects once hid behind a passing check. As a monitor it
        is reported by name; and because the induction step assumes the property set over its
        window, it doubles as the assumption that stops a free start from inventing
        multi-valued states, which is how the corresponding property discharges structurally.

        The comparison is TERM inequality, not the equality theory, and that is not the usual
        opaque-compare rule being broken: the question here is not whether two values are
        equal but whether the window was mounted twice, and two distinct terms mean two
        distinct `val` facts whatever they denote.

        A window the author declares SET-VALUED is legitimately many-valued and is exempt --
        by its declaration, never by inference.
        """
        out = []
        seen = set()
        for w in sorted(self.windows):
            kind, dom = self.windows[w]
            if kind == "set":
                continue
            keys = ["J"] if dom else []
            guard = []
            if dom:
                ext = self.indexes.get(dom)
                if ext is None:
                    continue
                guard = [f"J = 0..{ext}-1"]
            seen.add(w)
            kh = "".join(k + ", " for k in keys)
            out.append(f"failType({w}NotSingleValued, T) :- live(T), "
                       + "".join(g + ", " for g in guard)
                       + f"{w}({kh}A, T), {w}({kh}B, T), A != B.")
        for w, nkeys in sorted(self.value_windows):
            if w in seen or w in self.windows:
                continue
            keys = [f"K{i}" for i in range(nkeys)]
            kh = "".join(k + ", " for k in keys)
            out.append(f"failType({w}NotSingleValued, T) :- live(T), "
                       f"{w}({kh}A, T), {w}({kh}B, T), A != B.")
        return out

    def _declared_frames(self) -> list:
        """The frame for a window the specification DECLARED ITSELF -- a scalar phase or
        counter, or an array indexed by a declared domain.

        Every rule above this one is keyed by an object and guarded by that object's
        lifetime. These windows have no lifetime: a scalar has no key at all, and an indexed
        one is keyed by its POSITION, whose domain is fixed and always there. So the same
        rule -- a change with no licensed cause is a named failure -- is spelled with the
        key list the declaration gives it.

        Only a window some behaviour WRITES is framed. A window the specification merely
        reads is a derived view of the design: the miss queue's `liveEntries` is the count
        of what exists, and framing it would forbid the design from changing something the
        specification never claimed to control.
        """
        out = []
        for w in sorted(self.windows):
            entries = self._writers.get((w, "write"), [])
            if not entries:
                continue
            dom = self.windows[w][1]
            guard, key = [], []
            if dom:
                ext = self.indexes.get(dom)
                if ext is None:
                    # the domain is undeclared; check.py's `index` rule reports that, and a
                    # frame keyed on a range nobody stated would be a guess
                    continue
                guard, key = [f"J = 0..{ext}-1"], ["J"]
            may = f"may{w[0].upper()}{w[1:]}Write"
            kh = "".join(k + ", " for k in key)
            for cause, keys, aux in entries:
                if len(keys) != len(key):
                    raise EmitError(
                        f"`{w}` is declared with {len(key)} index and written with "
                        f"{len(keys)} -- the frame cannot say which position is licensed")
                out += aux
                out.append(self._rule(f"{may}({''.join(k + ', ' for k in keys)}T)",
                                      list(cause)))
            out.append(f"failType({w}Disturbed, T+1) :- live(T), live(T+1), "
                       + "".join(g + ", " for g in guard)
                       + f"{w}({kh}V, T), not {may}({kh}T), not {w}({kh}V, T+1).")
        return out

    def _create_monitor(self, name, trigger, var, caps, delayed) -> list:
        """`create entry N: caps` plus the `##1 ...` conjuncts about N: some slot not holding
        an entry at T holds one at T+1, carrying the captures, satisfying the conjuncts."""
        self.demanded.add("entryExists")
        self._defined.setdefault("entryId", "entryId(V) :- entryExists(V, T).")
        self._writers.setdefault(("exists", "set"), []).append((trigger, [], []))
        lits = [f"entryId({var})", f"not entryExists({var}, T)",
                f"entryExists({var}, T+1)"]
        rules = []
        for cap in caps:
            cl, cr = self._capture_expr(cap.replace("=", "==", 1)
                                        if "==" not in cap else cap, "T+1")
            lits += cl
            rules += cr
            self._register_writers(cap, trigger, var)
        for n, expr in delayed:
            cl, cr = self._capture_expr(expr, f"T+{n}")
            lits += cl
            rules += cr
            self._register_writers(expr, trigger, var)
        h = self._fresh("new_")
        rules.append(self._rule(f"{h}(T)", lits))
        rules.append(f"failType({name}Wrong, T+1) :- {self._lv()}, {self._lv('T+1')}, "
                     f"{', '.join(trigger)}, not {h}(T).")
        return rules
