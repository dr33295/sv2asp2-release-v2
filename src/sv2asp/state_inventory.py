"""The design's STATE INVENTORY: every register and every memory, with its definition.

Emitted as `<top>__state.lp`, a companion — never part of the design layer.

Why this exists as its own artifact. The translation is (per the 2026-08-15 decision) the
transition relation and nothing else: it does not say what any state element holds at t=0.
That is the right cut — an init-free design `.lp` IS a transition relation, so a property can
quantify over initial states instead of inheriting one baked-in start. But it only works if
the set of things needing an initial value is *stated somewhere the consumer can read*.
Otherwise a scenario that forgets a flop leaves it dark at every instant and every property
over it passes VACUOUSLY — the failure mode behind F2, F7 and F10.

So this file answers "what state does this design have, and what defines each piece of it":

    state_reg(Spec, Sig, Width, Clk).           a clocked register
    state_mem(Spec, Sig, ElemWidth, Depth, Clk) an addressed family of cells
    state_reset(Spec, Sig, RstSig, Kind, Act).  ... whose value at reset comes from the RTL
    state_unreset(Spec, Sig).                   ... whose power-on value does NOT

`state_unreset` is the operative one: those are exactly the elements an initial-state artifact
must pin, and exactly the ones whose absence must be loud. A register WITH a reset still needs
a power-on value (reset may not be asserted at t=0), but the RTL at least defines where its
value comes from once it is; an unreset element has no such story anywhere in the design.

Facts, not prose, because the intended consumers are machines: the init generator reads this
to know what to pin, and a pins check reads it to know what to demand.
"""

from __future__ import annotations

import re

from .ir.nodes import Design

# A rule head `val(<inst>, <sig>, <value>, T+1)`. The TIME ARGUMENT is what identifies state:
# a signal whose value at T+1 is determined by instant T is a state element, and one derived at
# T is combinational. Nothing here looks at the construct that produced the rule.
def _head_args(line: str) -> list[str] | None:
    """The argument list of a rule head `val(...) :- ...`, split at TOP-LEVEL commas.

    Both compile modes have to be read by one function or the two diverge, which is exactly
    what happened the first time this was written: the pattern assumed the four-argument
    modular head `val(Inst, Sig, V, T+1)` and silently matched nothing in flat mode, where the
    head is `val(Sig, V, T+1)`. The signal is `args[-3]` under BOTH arities, so counting from
    the END is what makes the two modes agree by construction rather than by a second pattern
    kept in step by hand (hard rule 1).
    """
    if not line.startswith("val(") or ":-" not in line:
        return None
    head = line[: line.index(":-")].rstrip()
    if not head.endswith(")"):
        return None
    inner, depth, cur, args = head[4:-1], 0, "", []
    for ch in inner:
        if ch == "," and depth == 0:
            args.append(cur.strip())
            cur = ""
            continue
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        cur += ch
    args.append(cur.strip())
    return args if len(args) >= 3 else None


def state_terms(text: str) -> set[str]:
    """The design's STATE VECTOR as the EMITTED TERMS — `mem(A)`, `u_rf(mem(A))`, `q(I)`, `cnt`.

    `state_signals` is this with each term reduced to its root symbol, which is what an
    inventory row wants. A consumer that has to line these up against named state ELEMENTS
    (the power-on walk does) needs the term itself: under hierarchy flattening the instance
    wraps the signal (`u_rf(mem(A))`), so the root alone collapses every element of one
    instance onto the instance name.
    """
    out: set[str] = set()
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("%"):
            continue
        args = _head_args(line)
        if args is None or args[-1].replace(" ", "") != "T+1":
            continue
        out.add(args[-3].strip())
    return out


def _val_terms_in_body(line: str) -> list[str]:
    """The SIGNAL TERM of every `val(...)` literal in one rule's body -- `q(0)`, `q(I)`, `mem(A)`,
    `cnt`; the modular form `val(Inst, term, V, T)` yields the same term. Balanced-paren scan, so
    a term with nested functors (`u_rf(mem(A))`) is one term."""
    if ":-" not in line:
        return []
    body = line.split(":-", 1)[1]
    out: list[str] = []
    i = 0
    while True:
        j = body.find("val(", i)
        if j < 0:
            break
        # split the literal's top-level arguments
        depth, k, args, start = 0, j + 4, [], j + 4
        while k < len(body):
            ch = body[k]
            if ch == "(":
                depth += 1
            elif ch == ")":
                if depth == 0:
                    args.append(body[start:k].strip())
                    break
                depth -= 1
            elif ch == "," and depth == 0:
                args.append(body[start:k].strip())
                start = k + 1
            k += 1
        if len(args) == 4:                 # modular val/4: (Inst, term, V, T)
            out.append(args[1])
        elif len(args) == 3:               # flat val/3: (term, V, T)
            out.append(args[0])
        i = k + 1
    return out


def family_join(text: str) -> dict[str, int]:
    """For every state FAMILY, the largest number of its atoms ONE emitted rule reads in its
    body -- the JOIN the grounder performs over that family. A per-lane word bridge reads all
    n lanes of `q` in one body (join n); the per-bit assembly reads all w bits; almost every
    other rule reads a family once. It is what the power-on budget must be measured against:
    n independent w-bit choices are n x 2^w atoms but a 2^(n*w) join wherever a rule reads all
    of them at once, and that join, not the atom count, is what hung a 64-bit per-bit register
    and a 4-lane x 8-bit lane register (2026-08-16). Read off the EMITTED RULES, the same way
    `state_terms` reads the state vector: a future rule shape that joins a family shows up here
    without anyone remembering to declare it."""
    join: dict[str, int] = {}
    for raw in text.splitlines():
        line = raw.strip()
        if not line or line.startswith("%"):
            continue
        counts: dict[str, int] = {}
        for term in _val_terms_in_body(line):
            fam = state_family(term)
            counts[fam] = counts.get(fam, 0) + 1
        for fam, c in counts.items():
            if c > join.get(fam, 0):
                join[fam] = c
    return join


def state_family(term: str) -> str:
    """The state FAMILY an emitted term belongs to: `mem(A)` -> `mem`, `u_rf(mem(A))` ->
    `u_rf(mem)`, `u_a(q(I))` -> `u_a(q)`, `mem(0)` -> `mem` — but `u_ctr0(cnt)` -> `u_ctr0(cnt)`.

    Two different things wear the same parentheses. `mem(A)` is a family and an INDEX; under
    hierarchy flattening `u_ctr0(cnt)` is a whole signal NAME, the instance wrapped around the
    signal. Only the innermost argument list is ever an index, and whether it IS one is decided
    by ASP's own naming rule rather than by any convention of ours: a **variable** (leading
    uppercase or `_`) or a **number** is an index, a lowercase identifier is a name.

    Getting this wrong has now cost twice, in both directions:
      * reducing to the ROOT symbol made every hierarchical design report a phantom state
        element named after its instance (`state_other(top, u_ctr0)`), demanding a power-on
        value for something with no atoms anywhere;
      * dropping the innermost list unconditionally put `u_a(q(I))` — a VARIABLE — into a fact,
        which clingo rejects as unsafe and which broke the whole program's grounding.
    """
    i = term.rfind("(")
    if i < 0:
        return term
    j = term.find(")", i)
    if j < 0:
        return term
    args = [a.strip() for a in term[i + 1:j].split(",")]
    if not args or not all(a and (a[0].isupper() or a[0] == "_" or a[0].isdigit()) for a in args):
        return term          # a lowercase identifier: a hierarchy leaf, not an index
    return term[:i] + term[j + 1:]


def state_signals(text: str) -> set[str]:
    """The design's STATE VECTOR, read off the EMITTED RULES.

    This is deliberately NOT an enumeration of construct kinds. Walking kinds
    (`always_ff` registers, memory cells, latches, VFFs, ...) has produced the same bug three
    times in this project: a rule reaching registers but not memory cells, an x-init companion
    covering registers only, and this inventory's first version listing registers and memories
    while silently omitting LATCHES -- measured on the committed `examples/rtl2asp/latch_demo`, whose
    `lq` holds its value across a tick and did not appear. A list maintained by hand is missing
    a kind the day a new stateful construct is added, and nothing goes red.

    So the set is derived from the property that DEFINES state instead. Under the transition
    relation the design denotes, `delta : (state, inputs) -> state'`, a state element is
    precisely a signal whose value at `T+1` is determined by instant `T`. In the emitted
    program that is visible directly: the head's TIME argument is `T+1`. A combinational
    signal's head is at `T`, so it is excluded by the same test rather than by a special case.
    """
    return {t.split("(", 1)[0].strip() for t in state_terms(text)}   # `mem(A)` -> `mem`


def _width(sig) -> int:
    """Bit width of a signal, however the IR type spells it."""
    t = getattr(sig, "irtype", None)
    for attr in ("width", "bits", "w"):
        v = getattr(t, attr, None)
        if isinstance(v, int):
            return v
    return 1


def _mem_elem_width(m) -> int:
    e = getattr(m, "elem", None)
    for attr in ("width", "bits", "w"):
        v = getattr(e, attr, None)
        if isinstance(v, int):
            return v
    return 1


def _loc(x) -> str:
    l = getattr(x, "loc", None)
    return f"{getattr(l, 'file', '?')}:{getattr(l, 'line', '?')}" if l is not None else "?"


def render(design: Design, spec: str | None = None, text: str = "") -> str:
    """The state inventory for one design, as ASP facts with the definitions in comments.

    `text` is the EMITTED program. When given, it decides MEMBERSHIP -- what is state is read
    off the rules (see `state_signals`) -- and the IR supplies each element's metadata (width,
    clock, reset). That split is the point: the set cannot miss a construct kind, and the rows
    still carry the detail a consumer needs.
    """
    s = spec or design.name
    out: list[str] = [
        f"% state inventory for `{s}` -- every register and every memory, with its definition.",
        "% Companion, NOT part of the design layer: the translation carries no initial state,",
        "% so this is the list an init artifact must pin and a pins check must demand.",
        "%",
        "% state_reg(Spec, Sig, Width, Clk).            state_mem(Spec, Sig, ElemW, Depth, Clk).",
        "% state_reset(Spec, Sig, RstSig, Kind, Act).   state_unreset(Spec, Sig).",
        "",
    ]

    # A register may be written by more than one SeqItem (priority arms in separate blocks);
    # first one wins for the clock, and any reset found is recorded.
    reg_clk: dict[str, str] = {}
    reg_rst: dict[str, object] = {}
    reg_loc: dict[str, str] = {}
    for it in design.seq:
        if getattr(it, "combinational", False):
            continue
        reg_clk.setdefault(it.reg, it.clock)
        reg_loc.setdefault(it.reg, _loc(it))
        if it.reset is not None:
            reg_rst.setdefault(it.reg, it.reset)

    out.append(f"% -- registers ({len(reg_clk)}) " + "-" * 40)
    for name in sorted(reg_clk):
        sig = next((x for x in design.signals if x.name == name), None)
        w = _width(sig) if sig is not None else 1
        out.append(f"% {name}: {w}-bit, clocked by {reg_clk[name]}, defined at {reg_loc[name]}")
        out.append(f"state_reg({s}, {name}, {w}, {reg_clk[name]}).")
        r = reg_rst.get(name)
        if r is not None:
            out.append(f"state_reset({s}, {name}, {r.signal}, {r.kind}, {r.active}).")
        else:
            out.append(f"state_unreset({s}, {name}).   % no reset in the RTL -- power-on value"
                       f" must come from outside the translation")
    if not reg_clk:
        out.append("% (none)")
    out.append("")

    # Memories: the clock comes from whatever writes them; a read-only array has none.
    mem_clk: dict[str, str] = {}
    for w_ in design.mem_writes:
        # a COMBINATIONAL array write carries no clock (empty string), and such an array is not
        # sequential state: it is driven at every instant, so it needs no power-on value and
        # must not appear in the list a pins check demands
        if w_.clock:
            mem_clk.setdefault(w_.mem, w_.clock)
    # An array's async reset (`if (rst) for (i...) tab[i] <= C;`), read off the WRITES that carry it
    # -- the same source the emitter forces the cells from. It used to be asserted, in a comment,
    # that "a clocked array is never reset in synthesizable RTL"; that is simply false (F25/F26), and
    # here it was load-bearing: the state vector is a DECLARED INTERFACE, so calling a reset array
    # `state_unreset` tells an init artifact to pin cells the reset already determines and a pins
    # check to demand them -- while the power-on layer, which reads the same writes, correctly opens
    # nothing. Two artifacts of one translation contradicting each other.
    mem_rst: dict[str, tuple] = {}
    for w_ in design.mem_writes:
        if w_.clock and w_.reset is not None:
            mem_rst.setdefault(w_.mem, w_.reset)

    out.append(f"% -- memories ({len(design.mems)}) " + "-" * 40)
    for m in sorted(design.mems, key=lambda x: x.name):
        ew, dims = _mem_elem_width(m), (m.dims or (m.depth,))
        cells = 1
        for d in dims:
            cells *= d
        clk = mem_clk.get(m.name, "none")
        shape = "x".join(str(d) for d in dims)
        out.append(f"% {m.name}: {ew}-bit cells, {shape} = {cells} cell(s), "
                   f"addr {m.addr_width}-bit, "
                   f"{'written by ' + clk if clk != 'none' else 'no clock (combinational or read-only)'}, "
                   f"declared at {_loc(m)}")
        out.append(f"state_mem({s}, {m.name}, {ew}, {cells}, {clk}).")
        if clk == "none":
            out.append(f"% {m.name} is NOT sequential state -- combinational or read-only, so"
                       f" no power-on value is needed and none is demanded")
        elif m.name in mem_rst:
            rsig, rel, rv = mem_rst[m.name]
            out.append(f"state_reset({s}, {m.name}, {rsig}, async, {'low' if rel else 'high'})."
                       f"   % every cell is forced to {rv} while {rsig} is asserted")
        else:
            out.append(f"state_unreset({s}, {m.name}).   % no reset drives this array's cells --"
                       f" every cell's power-on value must come from outside the translation")
    if not design.mems:
        out.append("% (none)")
    out.append("")

    # Anything the EMITTED RULES call state that the two walks above did not cover -- a latch,
    # an inferred latch, a VFF, or a construct added after this file was written. Membership
    # comes from the rules, so a new stateful kind lands here on the day it is added instead of
    # being silently absent. Conservatively unreset: its power-on story is not known here, and
    # under-demanding a pin is what produces a vacuous pass.
    #
    # Matched on the EMITTED TERM, two ways -- whole, and with the innermost index list dropped.
    # Reducing each term to its ROOT SYMBOL (what `state_signals` does, correctly, for an
    # inventory ROW) is wrong for deciding COVERAGE, because a flattened hierarchy wraps the
    # instance around the signal: `u_ctr0(cnt)` reduces to `u_ctr0`, which matches no register,
    # so every hierarchical design reported a phantom `state_other(top, u_ctr0)` /
    # `state_unreset(top, u_ctr0)` -- an INSTANCE NAME listed as a state element with no atoms
    # anywhere. Ten of the committed designs carried one. That is worse than a missing row: a
    # pins check reading this file would demand a power-on value for a thing that cannot have
    # one. `mem(A)` still matches its family `mem` under the second form.
    covered = set(reg_clk) | {m.name for m in design.mems}
    other = sorted({state_family(t) for t in (state_terms(text) if text else ())
                    if t not in covered and state_family(t) not in covered})
    out.append(f"% -- other state ({len(other)}) " + "-" * 40)
    if other:
        out.append("% held across a tick by the emitted rules, but not a plain register or")
        out.append("% array -- a latch, an inferred latch, a VFF, or a newer construct.")
    for name in other:
        sig = next((x for x in design.signals if x.name == name), None)
        w = _width(sig) if sig is not None else 1
        out.append(f"state_other({s}, {name}, {w}).")
        out.append(f"state_unreset({s}, {name}).   % power-on value must come from outside"
                   f" the translation")
    if not other:
        out.append("% (none)")
    out.append("")
    return "\n".join(out) + "\n"
