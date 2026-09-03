"""The HUMAN-GATED LADDER -- each artifact of the route is an intermediate step, and no step
begins until a person has read the previous one and approved it.

Why this exists, and why prose was not enough. The route's artifacts are built in order --
the English, the signature, the DSL specification, the contract, the design, the certificate,
the RTL -- and each is derived from the one before it. An agent can produce all seven without
stopping, and what it hands back is then a finished thing nobody watched being assembled. That
is not hypothetical: the first miss-queue contract shipped a contradiction that only the
certificate exposed, because the clauses were laid down together instead of one at a time.
Version 1 answered this with a `flow.yaml` approval ladder; version 2 inherited the CLAIM (the
methodology's carryover chapter said so) but never the machinery, until this file.

NAMING, deliberately: v1's file was `flow.yaml`, but v2 already has a `flow.py` that means
something else entirely -- the VERIFICATION flow, which checks run for an entry, from
`verify.json`. Two unrelated things called "flow" in one tool is how a reader ends up believing
a check ran. This is the LADDER: `ladder.yaml`, `ladder.py`.

THE FIVE STATES, in order:

    pending     the step has not been done
    built       the artifact exists
    explained   its read-back has been written -- what it says, in plain language
    approved    A PERSON HAS READ IT.  Only the user sets this.
    verified    the step's mechanical check has passed (where the step has one)

THE GATE: a step may leave `pending` only when every earlier step is `approved` or better.

WHAT THIS GUARANTEES, AND WHAT IT DOES NOT. It is auditability, not enforcement: nothing here
can stop a misbehaving agent from writing `approved` into the file, and pretending otherwise
would be its own false claim. What it does give is (a) no code path in this tool writes
`approved` -- the agent has to forge it deliberately rather than reach it by running a command,
(b) the state is a committed file, so "did a human see this?" is answerable months later, and
(c) an approval carries the DIGEST of what was approved, so editing the artifact afterwards
makes the approval STALE and re-opens the gate. (c) is the one with real teeth: it catches the
common, innocent version of the failure -- approved, then quietly improved.
"""
from __future__ import annotations

import datetime
import hashlib
import pathlib

import yaml

STATES = ("pending", "built", "explained", "approved", "verified")
_RANK = {s: i for i, s in enumerate(STATES)}

# The route's steps, in order. `check` names the mechanical check that can carry a step to
# `verified`; a step with no check is verified by its approval alone (there is nothing to run).
STEPS = (
    ("specification", "the English in force: resolutions done, every checkable sentence tagged", None),
    ("signature",     "the block's wires, widths, protocols and parameters",                     None),
    ("dsl",           "the machine and its claims, in the specification language",               None),
    ("contract",      "spec.lp -- generated from the two files above, or written by hand today", "lint"),
    ("design",        "the design in the authoring form, and its linkage mounting the windows",  "lint"),
    ("certificate",   "the base, the step at K, the scenarios, the delivery obligations",        "refine"),
    ("rtl",           "the print, and the round trip with a simulator arbitrating",              "roundtrip"),
)
_STEP_NAMES = tuple(n for n, _, _ in STEPS)
_STEP_KEYS = {"name", "artifact", "state", "explained", "approved"}


class LadderError(Exception):
    """A malformed ladder, or an attempt to move a step the gate does not allow."""


def _digest(path: pathlib.Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


class Ladder:
    def __init__(self, path: pathlib.Path, doc: dict):
        self.path, self.doc = path, doc
        self.root = path.parent
        self.steps = {s["name"]: s for s in doc.get("steps", [])}

    # ---------------------------------------------------------------- loading and shape
    @classmethod
    def load(cls, path: pathlib.Path) -> "Ladder":
        doc = yaml.safe_load(path.read_text()) or {}
        if not isinstance(doc, dict):
            raise LadderError(f"{path}: the ladder must be a mapping")
        steps = doc.get("steps")
        if not isinstance(steps, list) or not steps:
            raise LadderError(f"{path}: no steps")
        seen = []
        for s in steps:
            if not isinstance(s, dict):
                raise LadderError(f"{path}: every step must be a mapping")
            unknown = set(s) - _STEP_KEYS
            if unknown:                      # a typo silently ignored is a gate that did not run
                raise LadderError(f"{path}: step {s.get('name')!r} has unknown key(s) "
                                  f"{sorted(unknown)}; known keys are {sorted(_STEP_KEYS)}")
            if s.get("name") not in _STEP_NAMES:
                raise LadderError(f"{path}: unknown step {s.get('name')!r}; "
                                  f"the route's steps are {list(_STEP_NAMES)}")
            if s.get("state", "pending") not in STATES:
                raise LadderError(f"{path}: step {s['name']} has state {s.get('state')!r}; "
                                  f"the states are {list(STATES)}")
            seen.append(s["name"])
        order = [n for n in _STEP_NAMES if n in seen]
        if seen != order:
            raise LadderError(f"{path}: steps are out of route order: {seen} (expected {order})")
        return cls(path, doc)

    @classmethod
    def create(cls, path: pathlib.Path, entry: str, artifacts: dict) -> "Ladder":
        """A fresh ladder: every step pending, each naming the artifact that will fill it."""
        doc = {"entry": entry,
               "steps": [{"name": n, "artifact": artifacts.get(n, ""), "state": "pending"}
                         for n, _, _ in STEPS]}
        path.write_text(yaml.safe_dump(doc, sort_keys=False))
        return cls.load(path)

    def save(self) -> None:
        self.doc["steps"] = [self.steps[n] for n in _STEP_NAMES if n in self.steps]
        self.path.write_text(yaml.safe_dump(self.doc, sort_keys=False))

    # ---------------------------------------------------------------- the state of a step
    def state(self, name: str) -> str:
        """The RECORDED state, corrected for staleness: an approval whose digest no longer
        matches the artifact is not an approval, and this is where that is decided."""
        s = self.steps.get(name)
        if s is None:
            return "pending"
        st = s.get("state", "pending")
        if _RANK[st] >= _RANK["approved"] and self._stale(s):
            return "explained" if s.get("explained") else "built"
        return st

    def _stale(self, s: dict) -> bool:
        ap, art = s.get("approved"), s.get("artifact")
        if not isinstance(ap, dict) or not ap.get("digest") or not art:
            return True                      # approved with no record of WHAT was approved
        p = self.root / art
        return (not p.exists()) or _digest(p) != ap["digest"]

    def stale_note(self, name: str) -> str:
        s = self.steps.get(name) or {}
        if _RANK[s.get("state", "pending")] < _RANK["approved"] or not self._stale(s):
            return ""
        ap, art = s.get("approved"), s.get("artifact")
        if not isinstance(ap, dict) or not ap.get("digest"):
            return "approved, but with no digest -- there is no record of WHAT was approved"
        p = self.root / art
        if not p.exists():
            return f"approved, but {art} no longer exists"
        return f"APPROVAL IS STALE: {art} changed after it was approved"

    # ---------------------------------------------------------------- the gate
    def blocked_by(self, name: str) -> list:
        """The earlier steps that are not yet approved. Non-empty means this step may not start."""
        out = []
        for n in _STEP_NAMES:
            if n == name:
                break
            if n in self.steps and _RANK[self.state(n)] < _RANK["approved"]:
                out.append(n)
        return out

    def advance(self, name: str, to: str, note: str = "") -> None:
        """Move a step to `built` or `explained`. THE TOOL WILL NOT WRITE `approved`: that is
        the user's act, made by editing the file, and this refusal is the point of the ladder."""
        if to == "approved":
            raise LadderError(
                "the tool does not set `approved` -- a person does, by editing the ladder. "
                "Record the artifact's digest beside it:\n"
                f"    approved: {{at: <date>, digest: {self._current_digest(name)}}}")
        if to not in ("built", "explained", "verified"):
            raise LadderError(f"cannot move a step to {to!r}")
        if name not in self.steps:
            raise LadderError(f"no step {name!r} in {self.path}")
        blocked = self.blocked_by(name)
        if blocked:
            raise LadderError(f"step {name!r} is gated: {', '.join(blocked)} "
                              f"{'is' if len(blocked) == 1 else 'are'} not approved yet")
        s = self.steps[name]
        if to == "explained":
            if _RANK[self.state(name)] < _RANK["built"]:
                raise LadderError(f"step {name!r} cannot be explained before it is built")
            if not (note or s.get("explained")):
                raise LadderError(f"step {name!r}: an explanation needs text -- "
                                  "the read-back is the thing a person approves")
            if note:
                s["explained"] = note
        if to == "verified" and _RANK[self.state(name)] < _RANK["approved"]:
            raise LadderError(f"step {name!r} cannot be verified before it is approved")
        s["state"] = to
        self.save()

    def _current_digest(self, name: str) -> str:
        s = self.steps.get(name) or {}
        p = self.root / s.get("artifact", "")
        return _digest(p) if s.get("artifact") and p.exists() else "<artifact missing>"

    # ---------------------------------------------------------------- the report
    def report(self) -> str:
        w = max(len(n) for n in _STEP_NAMES)
        out = [f"ladder: {self.doc.get('entry', self.path.parent.name)}  ({self.path})", ""]
        nxt = None
        for n, gloss, check in STEPS:
            if n not in self.steps:
                continue
            st, s = self.state(n), self.steps[n]
            mark = {"pending": "   ", "built": " . ", "explained": " : ",
                    "approved": " * ", "verified": " ✓ "}[st]
            art = s.get("artifact") or "-"
            out.append(f"{mark} {n.ljust(w)}  {st.ljust(9)}  {art}")
            note = self.stale_note(n)
            if note:
                out.append(f"      !! {note}")
            if nxt is None and _RANK[st] < _RANK["approved"]:
                nxt = (n, st, gloss, check)
        out.append("")
        if nxt is None:
            out.append("every step approved.")
        else:
            n, st, gloss, check = nxt
            out.append(f"NEXT: {n} -- {gloss}")
            out.append({"pending":   "  build the artifact, then: ladder built " + n,
                        "built":     "  write the read-back, then: ladder explained " + n + " --note '...'",
                        "explained": "  WAITING ON THE USER: read it and set `state: approved` with the "
                                     "digest\n           " + self._current_digest(n)}[st])
            if check and st == "explained":
                out.append(f"  (after approval, `{check}` carries this step to verified)")
        return "\n".join(out)


def now() -> str:
    return datetime.datetime.now().strftime("%Y-%m-%d")
