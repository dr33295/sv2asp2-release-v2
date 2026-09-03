"""The REFERENCE INTERPRETER and the differential -- TRANSLATION.md Stage 5.

The compiler's correctness bar (TRANSLATION.md §5) forbids "agreement with a hand-written
artifact" and demands two independent semantics with agreement between them. This module is
the second semantics: a direct evaluator that answers, for a specification's PROPERTY
claims and lowered assumptions over a concrete finite trace, exactly which verdicts hold --
written from the methodology's stated meanings (determination instants, quantifier domains,
the payload-binding instant, the reset exemption), never by consulting what emit.py emits.

The differential then runs both semantics on the same random traces: the generated contract
under clingo with the trace pinned as facts, and this evaluator on the same trace. They must
agree on (a) admissibility -- whether the trace violates a lowered assumption, in which case
the ASP side is UNSAT -- and (b) the full set of (monitor, instant) property verdicts. A
deliberate mistranslation planted in the contract must be caught; that sabotage is the
gate's witness that the differential can see anything at all.

SCOPE, stated plainly: property claims and assumptions. Behaviour event/frame monitors and
scenarios are not yet interpreted here -- their failType names are excluded from the
comparison by construction (the comparison keys on the property names this module judged) --
and that gap is recorded in the route worklist as owed.

Trace vocabulary (the same atoms the generated contract reads):
    gtime(T).  val(Signal, V, T).  entryExists(E, T).  <window>(E, T).
    entryAddress(E, V, T).  entryTag(E, V, T).  lineData(E, V, T).
    corresponds(D, E, T).  liveEntries(V, T).  inFlightCount(V, T).
"""
from __future__ import annotations

import dataclasses
import random
import re

from . import parse as _parse
from .expr import parse_expr, split_claim, strip_delay, E


class InterpError(Exception):
    """A construct this interpreter does not cover. Loud, never guessed: an interpreter
    that guesses is a second compiler defect, not a second opinion."""


# ------------------------------------------------------------------ the trace
@dataclasses.dataclass
class Trace:
    H: int                       # instants 0..H inclusive
    entries: list                # entity ids (small ints)
    sig: dict                    # (signal, t) -> int
    winb: dict                   # (window, e, t) -> True       boolean per-entry windows
    winv: dict                   # (window, e, t) -> int        value windows (address/tag/data)
    corr: dict                   # (e, t) -> True               "the forward at t answers e"
    cnt: dict                    # (counter, t) -> int

    def live(self, t: int) -> bool:
        return self.sig.get(("resetN", t)) == 1

    def as_asp(self) -> str:
        out = [f"gtime(0..{self.H})."]
        for (s, t), v in sorted(self.sig.items()):
            out.append(f"val({s}, {v}, {t}).")
        for (w, e, t) in sorted(self.winb):
            out.append(f"{w}({e}, {t}).")
        for (w, e, t), v in sorted(self.winv.items()):
            out.append(f"{w}({e}, {v}, {t}).")
        for (e, t) in sorted(self.corr):
            out.append(f"corresponds(0, {e}, {t}).")
        for (c, t), v in sorted(self.cnt.items()):
            out.append(f"{c}({v}, {t}).")
        return "\n".join(out) + "\n"


BOOL_WINDOWS = ("entryExists", "demanding", "wantsFetch", "inFlight", "filled", "forwarded")
VAL_WINDOWS = ("entryAddress", "entryTag", "lineData")


def random_trace(seed: int, H: int = 5, n_entries: int = 2, n_addr: int = 3,
                 polite: bool = False) -> Trace:
    """A random trace. `polite` biases toward satisfying the missq assumptions (request
    persistence; fills only where an inFlight entry matches) so the SAT branch of the
    differential is exercised, not only the admissibility bit."""
    rng = random.Random(seed)
    tr = Trace(H, list(range(n_entries)), {}, {}, {}, {}, {})
    # a STICKY entry: filled+demanding, never forwarded, for the whole trace -- without
    # this bias the depth-window monitor (answered-within-depth) can essentially never
    # fire, and a monitor the batch never fires is a monitor the differential never checks
    sticky = rng.random() < 0.2
    for t in range(H + 1):
        tr.sig[("resetN", t)] = 1 if rng.random() > 0.1 else 0
        for s in ("requestValid", "requestReady", "memoryRequestValid",
                  "memoryRequestReady", "fillValid", "forwardValid", "redirectValid",
                  "fetchStall"):
            tr.sig[(s, t)] = rng.randint(0, 1)
        tr.sig[("requestIsDemand", t)] = rng.randint(0, 1)
        for s in ("requestAddress", "memoryRequestAddress", "fillAddress"):
            tr.sig[(s, t)] = rng.randrange(n_addr)
        for s in ("requestTag", "forwardTag"):
            tr.sig[(s, t)] = rng.randrange(2)
        for s in ("fillData", "forwardData"):
            tr.sig[(s, t)] = rng.randrange(3)
        live_n = 0
        for e in tr.entries:
            if sticky and e == 0:
                tr.winb[("entryExists", e, t)] = True
                tr.winb[("filled", e, t)] = True
                tr.winb[("demanding", e, t)] = True
                live_n += 1
                tr.winv[("entryAddress", e, t)] = rng.randrange(n_addr)
                tr.winv[("entryTag", e, t)] = rng.randrange(2)
                tr.winv[("lineData", e, t)] = rng.randrange(3)
                continue
            if rng.random() > 0.4:
                tr.winb[("entryExists", e, t)] = True
                live_n += 1
                phase = rng.choice(["wantsFetch", "inFlight", "filled", "none"])
                if phase != "none":
                    tr.winb[(phase, e, t)] = True
                    if rng.random() > 0.85:      # occasionally two phases at once, so the
                        other = rng.choice([p2 for p2 in ("wantsFetch", "inFlight", "filled")
                                            if p2 != phase])
                        tr.winb[(other, e, t)] = True    # overlap monitor can ever fire
                if rng.random() > 0.5:
                    tr.winb[("demanding", e, t)] = True
                if rng.random() > 0.8:
                    tr.winb[("forwarded", e, t)] = True
                    tr.corr[(e, t)] = True
                tr.winv[("entryAddress", e, t)] = rng.randrange(n_addr)
                tr.winv[("entryTag", e, t)] = rng.randrange(2)
                tr.winv[("lineData", e, t)] = rng.randrange(3)
        # the counters are trace values like any other: usually truthful, sometimes not,
        # or the bound monitors (neverOverfilled, fetchLimitHeld) could never fire
        tr.cnt[("liveEntries", t)] = max(0, live_n + rng.choice((0, 0, 0, 1, 3)))
        tr.cnt[("inFlightCount", t)] = max(0, sum(
            1 for e in tr.entries if ("inFlight", e, t) in tr.winb)
            + rng.choice((0, 0, 0, 1, 2)))
    if polite:
        for t in range(H):
            # requestHeldUntilTaken: valid and not accepted => held stable next cycle
            if (tr.sig[("requestValid", t)] == 1
                    and not (tr.sig[("requestReady", t)] == 1)):
                tr.sig[("requestValid", t + 1)] = 1
                for f in ("requestAddress", "requestTag", "requestIsDemand"):
                    tr.sig[(f, t + 1)] = tr.sig[(f, t)]
        for t in range(H + 1):
            # fillsAnswerFetches: a fill only where an inFlight entry matches its address
            targets = [e for e in tr.entries if ("inFlight", e, t) in tr.winb
                       and ("entryExists", e, t) in tr.winb]
            if tr.sig[("fillValid", t)] == 1:
                if targets:
                    tr.sig[("fillAddress", t)] = tr.winv[("entryAddress", targets[0], t)]
                else:
                    tr.sig[("fillValid", t)] = 0
    return tr


# ------------------------------------------------------------------ the evaluator
class Interp:
    """Evaluates a core file's defines, assumptions and property claims over a Trace."""

    def __init__(self, core_path, signature: dict):
        self.params = {p["name"]: p["default"] for p in signature.get("parameters", [])}
        self.ifaces = {}
        for i in signature.get("interfaces", []):
            self.ifaces[i["name"]] = {"protocol": i.get("protocol"), "fields": {}}
        self.levels = set()
        self.resets = {r["name"] for r in signature.get("clocks_and_resets", [])
                       if r.get("type") == "reset" or "reset" in r.get("name", "").lower()}
        for p in signature.get("ports", []):
            i, role = p.get("interface"), p.get("role")
            if role == "level" or i in (None, "-"):
                self.levels.add(p["name"])
                continue
            if role in ("valid", "ready"):
                self.ifaces[i][role] = p["name"]
            else:
                field = p["name"][len(i):]
                field = field[0].lower() + field[1:]
                self.ifaces[i]["fields"][field] = p["name"]

        root = _parse.parse(core_path)
        self.defines, self.assumes, self.props = {}, [], []
        for node in root.children:
            kind = node.kind.lstrip("@")
            if kind == "define":
                m = re.match(r"@define\s+(\w+)(?:\(([^)]*)\))?", node.header)
                body = " ".join(node.body)
                bm = re.match(r"holds when (.*)$", body)
                args = [a.strip() for a in (m.group(2) or "").split(",") if a.strip()]
                self.defines[m.group(1)] = (args, parse_expr(bm.group(1)) if bm else None)
            elif kind == "assume":
                self.assumes.append((node.name, node.text()))
            elif kind == "property":
                self.props.append((node.name, node.text()))

    # ---- expression evaluation. env: var -> ("entity", id) | ("payload", iface, t_bind)
    def _entities_at(self, tr: Trace, t: int) -> list:
        return [e for e in tr.entries if ("entryExists", e, t) in tr.winb]

    def _payload_value(self, tr: Trace, iface: str, t_bind: int):
        fields = self.ifaces[iface]["fields"]
        if len(fields) == 1:
            (sig_name,) = fields.values()
            return tr.sig.get((sig_name, t_bind))
        raise InterpError(f"payload of {iface} used as a bare value with several fields")

    def ev(self, e: E, tr: Trace, t: int, env: dict):
        if t < 0 or t > tr.H:
            raise InterpError("evaluation left the trace")
        op = e.op
        if op == "num":
            return int(e.text)
        if op == "name":
            n = e.text
            if n in env:
                kind = env[n]
                if kind[0] == "payload":
                    return self._payload_value(tr, kind[1], kind[2])
                return kind[1]
            if n in self.params:
                return self.params[n]
            if ("liveEntries" if False else n) in ("liveEntries", "inFlightCount"):
                return tr.cnt.get((n, t), 0)
            if n in self.defines:
                args, body = self.defines[n]
                if args:
                    raise InterpError(f"{n} needs arguments")
                return bool(self.ev(body, tr, t, env))
            if n in self.levels or n in self.resets:
                return tr.sig.get((n, t), 0)
            raise InterpError(f"unknown name {n!r}")
        if op == "and":
            return bool(self.ev(e.kids[0], tr, t, env)) and bool(self.ev(e.kids[1], tr, t, env))
        if op == "or":
            return bool(self.ev(e.kids[0], tr, t, env)) or bool(self.ev(e.kids[1], tr, t, env))
        if op == "not":
            return not bool(self.ev(e.kids[0], tr, t, env))
        if op == "cmp":
            a, b = self.ev(e.kids[0], tr, t, env), self.ev(e.kids[1], tr, t, env)
            return {"==": a == b, "!=": a != b, "<": a < b, "<=": a <= b,
                    ">": a > b, ">=": a >= b}[e.text]
        if op == "arith":
            a, b = self.ev(e.kids[0], tr, t, env), self.ev(e.kids[1], tr, t, env)
            return {"+": a + b, "-": a - b, "*": a * b}[e.text] if e.text != "\\" \
                else a // b
        if op == "field":
            base = e.kids[0]
            if base.op == "name" and base.text in self.ifaces:
                iface = self.ifaces[base.text]
                if e.text == "valid":
                    return tr.sig.get((iface["valid"], t)) == 1
                if e.text == "ready":
                    return tr.sig.get((iface["ready"], t)) == 1
                raise InterpError(f"interface field {e.text!r}")
            if base.op == "name" and base.text in self.levels and e.text == "high":
                return tr.sig.get((base.text, t)) == 1
            if base.op == "name" and base.text in env:
                kind = env[base.text]
                if kind[0] == "payload":
                    sig_name = self.ifaces[kind[1]]["fields"][e.text]
                    return tr.sig.get((sig_name, kind[2]))
                ent = kind[1]
                w = {"address": "entryAddress", "tag": "entryTag"}.get(e.text)
                if w is None:
                    return tr.winv.get((e.text, ent, t))
                return tr.winv.get((w, ent, t))
            raise InterpError(f"field {e.text!r} of {base!r}")
        if op == "ifcall":
            base, args = e.kids[0], e.kids[1:]
            iface = base.text
            meth = e.text
            if meth in ("valid", "arrives"):
                ok = tr.sig.get((self.ifaces[iface]["valid"], t)) == 1
            elif meth == "taken":
                ok = (tr.sig.get((self.ifaces[iface]["valid"], t)) == 1
                      and tr.sig.get((self.ifaces[iface]["ready"], t)) == 1)
            else:
                raise InterpError(f"interface method {meth!r}")
            if ok and args:
                var = args[0].text
                env[var] = ("payload", iface, t)
            return ok
        if op == "call":
            f = e.text
            if f == "exists":
                ent = env[e.kids[0].text][1]
                return ("entryExists", ent, t) in tr.winb
            if f == "accepted":
                kind = env[e.kids[0].text]
                iface = self.ifaces[kind[1]]
                return (tr.sig.get((iface["valid"], t)) == 1
                        and tr.sig.get((iface["ready"], t)) == 1)
            if f == "$stable":
                kind = env[e.kids[0].text]
                iface = kind[1]
                if t == 0:
                    return False
                return all(tr.sig.get((s, t)) == tr.sig.get((s, t - 1))
                           for s in self.ifaces[iface]["fields"].values())
            if f == "exactly":
                want = int(e.kids[0].text)
                q = e.kids[1]
                return self._count_quant(q, tr, t, env) == want
            if f == "corresponds":
                d_var, e_var = e.kids
                ent = env[e_var.text][1]
                return (ent, t) in tr.corr
            if f in self.defines and self.defines[f][1] is not None:
                args, body = self.defines[f]
                sub = dict(env)
                for formal, actual in zip(args, e.kids):
                    sub[formal] = env[actual.text] if actual.text in env else \
                        ("entity", self.ev(actual, tr, t, env))
                return bool(self.ev(body, tr, t, sub))
            if f in VAL_WINDOWS:
                ent = env[e.kids[0].text][1]
                return tr.winv.get((f, ent, t))
            if f in BOOL_WINDOWS:
                ent = env[e.kids[0].text][1]
                return (f, ent, t) in tr.winb
            # an undeclared one-place window over an entity: read it as a boolean window
            if len(e.kids) == 1 and e.kids[0].text in env:
                ent = env[e.kids[0].text][1]
                return (f, ent, t) in tr.winb
            raise InterpError(f"unknown call {f!r}")
        if op == "quant":
            return self._eval_quant(e, tr, t, env)
        if op == "delay":
            raise InterpError("a delay inside an expression position")
        raise InterpError(f"unhandled node {op!r}")

    def _quant_parts(self, q: E):
        quant, kind, var = q.text.split(":")
        where, scope = q.kids
        return quant, var, where, scope

    def _bindings(self, q: E, tr: Trace, t: int, env: dict):
        _, var, where, scope = self._quant_parts(q)
        for ent in self._entities_at(tr, t):
            sub = dict(env)
            sub[var] = ("entity", ent)
            if where is not None and not bool(self.ev(where, tr, t, sub)):
                continue
            yield ent, sub

    def _count_quant(self, q: E, tr: Trace, t: int, env: dict) -> int:
        return sum(1 for _ in self._bindings(q, tr, t, env))

    def _eval_quant(self, q: E, tr: Trace, t: int, env: dict) -> bool:
        quant, var, where, scope = self._quant_parts(q)
        hits = []
        for ent, sub in self._bindings(q, tr, t, env):
            if scope is None:
                hits.append(True)
            else:
                hits.append(bool(self.ev(scope, tr, t, sub)))
        if quant == "some":
            return any(hits)
        return all(hits) if hits else True

    # ---- claims
    def _judged(self, tr: Trace, t: int, reset_exempt: bool) -> bool:
        return (not tr.live(t)) if reset_exempt else tr.live(t)

    def _consequent_obligations(self, cons_text: str):
        """Split a consequent into (lo, hi, expr_text) parts at top-level `&&`,
        reading a leading ##N / ##[lo:hi] on each part. hi may be a parameter name."""
        parts, depth, cur = [], 0, ""
        i, quant_open = 0, False
        while i < len(cons_text):
            c = cons_text[i]
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
            # the grammar's rule, honored here too: a quantifier is the FINAL conjunct and
            # its `where` reaches maximally right, so once one opens at depth 0 nothing to
            # its right is a separate obligation
            if depth == 0 and re.match(r"(?:some|each)\b", cons_text[i:]):
                quant_open = True
            if depth == 0 and not quant_open and cons_text.startswith("&&", i):
                parts.append(cur)
                cur = ""
                i += 2
                continue
            cur += c
            i += 1
        parts.append(cur)
        out = []
        for p in parts:
            lo, hi, rest = strip_delay(p.strip())
            out.append((lo or 0, hi if hi is not None else 0, rest.strip()))
        return out

    def _resolve(self, bound):
        return self.params[bound] if isinstance(bound, str) else bound

    def property_verdicts(self, tr: Trace) -> set:
        out = set()
        for name, text in self.props:
            body = text.split("\n", 1)[1] if "\n" in text else ""
            lines = [l.strip() for l in body.splitlines() if l.strip()]
            exempt = False
            if lines and lines[0].startswith("enable iff"):
                exempt = True
                lines = lines[1:]
            claim = "\n".join(lines)
            binders = []
            m = re.match(r"^((?:each entry \w+,?\s*)+)\(\s*(.*)\)\s*$", claim, re.S)
            if m:
                binders = re.findall(r"each entry (\w+)", m.group(1))
                claim = m.group(2).strip()
            ant, arrow, cons = split_claim(claim)
            shift = 1 if arrow == "|=>" else 0
            for t in range(tr.H + 1):
                if not self._judged(tr, t, exempt):
                    continue
                for env in self._binder_envs(binders, tr):
                    env = dict(env)
                    if arrow == "always":
                        if not bool(self.ev(parse_expr(cons), tr, t, env)):
                            out.add((name, t))
                        continue
                    if ant is not None and not bool(self.ev(parse_expr(ant), tr, t, env)):
                        continue
                    for lo, hi, part in self._consequent_obligations(cons):
                        lo, hi = lo + shift, self._resolve(hi) + shift
                        stamp = t + hi
                        if stamp > tr.H:
                            continue
                        if hi > 0 and not tr.live(stamp):
                            continue
                        if lo == hi:
                            ok = self._eval_part(part, tr, t + lo, env)
                        else:
                            ok = any(self._eval_part(part, tr, t + k, env)
                                     for k in range(lo, hi + 1))
                        if not ok:
                            out.add((name, stamp))
        return out

    def _binder_envs(self, binders: list, tr: Trace):
        if not binders:
            yield {}
            return
        def rec(i, env):
            if i == len(binders):
                yield dict(env)
                return
            for ent in tr.entries:
                env[binders[i]] = ("entity", ent)
                yield from rec(i + 1, env)
        yield from rec(0, {})

    def _eval_part(self, part: str, tr: Trace, t: int, env: dict) -> bool:
        """One consequent part at one instant. An inner `each ... where C: body` is a
        universal over entities existing at the CURRENT instant, its body possibly
        delayed relative to it."""
        m = re.match(r"^each entry (\w+) where (.*?):\s*(.*)$", part, re.S)
        if m:
            var, where, inner = m.group(1), m.group(2), m.group(3)
            for ent in self._entities_at(tr, t):
                sub = dict(env)
                sub[var] = ("entity", ent)
                if not bool(self.ev(parse_expr(where), tr, t, sub)):
                    continue
                lo, hi, rest = strip_delay(inner.strip())
                u = t + (lo or 0)
                if u > tr.H:
                    continue
                if not bool(self.ev(parse_expr(rest), tr, u, sub)):
                    return False
            return True
        try:
            return bool(self.ev(parse_expr(part), tr, t, env))
        except InterpError:
            raise

    def assumption_violations(self, tr: Trace) -> list:
        """The LOWERED assumptions only (an s_eventually obligation is not a rule and is
        skipped exactly as the compiler skips it)."""
        out = []
        for name, text in self.assumes:
            body = "\n".join(text.splitlines()[1:])
            if "s_eventually" in body:
                continue
            ant, arrow, cons = split_claim(body)
            shift = 1 if arrow == "|=>" else 0
            for t in range(tr.H + 1):
                if not tr.live(t):
                    continue
                env = {}
                if ant is not None and not bool(self.ev(parse_expr(ant), tr, t, env)):
                    continue
                ok = True
                for lo, hi, part in self._consequent_obligations(cons):
                    lo, hi = lo + shift, self._resolve(hi) + shift
                    if t + hi > tr.H or (hi > 0 and not tr.live(t + hi)):
                        continue
                    if not self._eval_part(part, tr, t + lo, env):
                        ok = False
                if not ok:
                    out.append((name, t))
        return out

    def property_names(self) -> set:
        return {n for n, _ in self.props}


# ------------------------------------------------------------------ the differential
def clingo_side(contract_text: str, tr: Trace, prop_names: set, workdir) -> tuple:
    """The generated contract under clingo with the trace pinned: ("UNSAT", None) when an
    assumption constraint rejects the trace, else ("SAT", {(name, t)}) filtered to the
    property monitors this interpreter judges."""
    import json
    import pathlib
    import subprocess
    from ..libgen import generated_region
    from ..lint import clingo_bin
    wd = pathlib.Path(workdir)
    (wd / "lib.lp").write_text(generated_region())
    (wd / "contract.lp").write_text(contract_text)
    (wd / "trace.lp").write_text(tr.as_asp())
    r = subprocess.run([clingo_bin(), "--outf=2", "-q0", "--models=1",
                        str(wd / "lib.lp"), str(wd / "contract.lp"), str(wd / "trace.lp")],
                       capture_output=True, text=True)
    out = json.loads(r.stdout)
    if out["Result"].startswith("UNSAT"):
        return "UNSAT", None
    got = set()
    for w in out["Call"][-1]["Witnesses"]:
        for a in w["Value"]:
            m = re.match(r"failType\((\w+),(-?\d+)\)$", a)
            if m and m.group(1) in prop_names:
                got.add((m.group(1), int(m.group(2))))
    return "SAT", got


def differential(core_path, signature: dict, contract_text: str, seeds, workdir,
                 H: int = 5) -> tuple:
    """Run both semantics over random traces. Returns (mismatches, sat_count, fired):
    mismatches = [(seed, kind, detail)], sat_count = traces that reached the SAT branch,
    fired = property names that fired at least once on the agreeing runs -- the caller
    asserts coverage so the differential cannot pass vacuously."""
    it = Interp(core_path, signature)
    names = it.property_names()
    mism, sat_n, fired = [], 0, set()
    for seed in seeds:
        tr = random_trace(seed, H=H, polite=(seed % 2 == 0))
        status, asp = clingo_side(contract_text, tr, names, workdir)
        viol = it.assumption_violations(tr)
        if status == "UNSAT":
            if not viol:
                mism.append((seed, "admissibility",
                             "clingo rejects the trace; the interpreter finds no "
                             "assumption violation"))
            continue
        if viol:
            mism.append((seed, "admissibility",
                         f"the interpreter finds {viol[:3]} violated; clingo accepts"))
            continue
        sat_n += 1
        ref = it.property_verdicts(tr)
        if asp != ref:
            mism.append((seed, "verdicts",
                         f"clingo-only {sorted(asp - ref)[:4]}, "
                         f"interp-only {sorted(ref - asp)[:4]}"))
        else:
            fired |= {n for n, _ in ref}
    return mism, sat_n, fired
