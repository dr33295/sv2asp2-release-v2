"""The auxiliary-atom ROLE names, reachable without importing the emitter.

`schema.py` prints them and a gate checks every generated head is one of them; both would
otherwise pull in `emit`, which pulls in the parser and the signature schema. One function,
reading the emitter's own table, so the printed list cannot drift from the names emitted.
"""
from __future__ import annotations


def roles() -> list[str]:
    from .dsl.emit import Emitter
    return sorted(set(Emitter._ROLES.values()))
