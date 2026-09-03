"""k-INDUCTION for the refinement loop -- `refine ... --induct K`.

The bounded checks prove a level's invariant set on every trace of length k FROM RESET. Induction
proves the SAME set for ALL time, in two halves:

    BASE  the bounded checks (unchanged), at a horizon of at least K;
    STEP  start from an ARBITRARY state -- every register, latch and memory cell FREE at T=0, the
          spec's / contracts' GHOST state free at T=0, the inputs free at every instant, the level's
          abstract parts free as always -- ASSUME the whole invariant set at T = 0..K-1 and REQUIRE a
          violation at T = K.  UNSAT = the set is inductive: with the base, it holds for all time.

Terminology (the same as the bounded runner's):
    property set    what the level is OBLIGED to prove: the spec's `bad` tags (minus those the
                    level still assumes), its own `viol` guarantees (incl. requirements owed to
                    children), the previous level's dropped assumptions and guarantees.
    environment     the level's `assume` monitors: asserted at EVERY instant of the step, as in
                    the bounded run (an assumption is what the level needs from what it has not
                    built; it is not an obligation here).
    ghost state     the HISTORY predicates a monitor file defines -- a predicate with a head at a
                    later instant than something in its body (`gcnt(C+1, T+1) :- gcnt(C, T), ..`,
                    `fired(T+2) :- .. val(en, 1, T)`). Read off the monitor text by the runner
                    (never enumerated by hand: the F12 lesson) and REQUIRED to have an init.
    ghost init      `<monitor>.ghost.lp` beside the monitor file (`spec.ghost.lp`,
                    `l1.inv.ghost.lp`, `mul4.contract.ghost.lp`): clingo choice rules producing
                    the ghost predicates' values at T=0 -- their whole reachable domain, e.g.
                        { gcnt(C, 0) : C = 0..4 } = 1.
                        { gq(P, V, 0) : V = 0..15 } = 1 :- gcnt(C, 0), P = 0..C-1.
                    A domain too SMALL is UNSOUND (windows dropped from the step); too LARGE only
                    costs completeness (a spurious "not inductive" from a ghost state no past could
                    produce). Err large. The runner checks that every ghost state the base's goal
                    witnesses visit is producible by the init (a sample, not a proof).

Reset in the step: the reset nets (every `arff`'s `rstL`) are held RELEASED throughout. The base
stimulus resets once at T=0, so every window of a reachable trace that starts after T=0 starts
released -- holding it released loses no soundness against that stimulus, and it keeps the ghost
init from colliding with the ghosts' own reset rules at T=0. Every other input is free.

A failed STEP is an INVARIANT REQUEST, not a bug report: the counterexample starts from a state
that satisfies every invariant for K cycles and still violates one at K. Either that start state
is reachable (a real bug the base would find at a longer k) or it is not, and the level owes the
`viol` that excludes it -- the gluing invariant relating the design's state to the ghost
(`fill == gcnt`, `mem[(rd_ptr+P) mod 4] == gq(P)`), or a ranking argument phrased as safety. That
is where the author's (the LLM's) work goes."""
from __future__ import annotations

import pathlib
import re
from dataclasses import dataclass, field

from .load import Design
from .model import CELLS

# The RESERVED name of the runner's own ghost-state projection (`ghost_state(gcnt(3), T)`) -- the
# report's ghost lines, `pin_ghost_state`, and the unique-states constraint all read it. It must be a
# name no author would write, and a spec that writes it anyway is REFUSED (`reserved_collisions`),
# because the two sets of atoms would land in one predicate and corrupt both.
#
# It used to be `gh/2`, and `gh` sat in MONITOR_PREDS so the projection would not be re-detected as a
# ghost. But detection reads the AUTHOR's spec, where the projection never appears -- so the exclusion
# protected nothing and instead BLACKLISTED a natural author name: a spec whose ghost was called `gh`
# (ghost-hours, ghost-head) was reported "no ghost state", got no init requirement and no closure
# check, and every property over that ghost was then VACUOUSLY inductive -- a false proof at exit 0.
# Found on the dataset's count_clock entry, 2026-08-19; witness
# `test_aspfirst_ghost_name_does_not_change_the_proof`.
GHOST_PROJ = "ghost_state"
#: asserts the (guarded) unique-states constraint for a caller that grounds one query at a time
UNIQ_ON = "ind__uniq.\n"
MONITOR_PREDS = {"bad", "failType", "goal", "assume", "viol", "p_assume", "p_viol", "guarantee", "require",
                 "obl", "obl_viol", "obl_owed", "model", "p_model", "cmodel", "pval", "boundary",
                 "val", "time", "gtime", GHOST_PROJ}


def reserved_collisions(text: str) -> list:
    """The RESERVED predicate names a monitor file defines -- author vocabulary colliding with the
    runner's own. A collision is refused rather than worked around: the atoms would be mixed into one
    predicate, and the ghost projection is what the report, the unique-states constraint and
    `pin_ghost_state` read."""
    from clingo import ast
    hit = set()
    for st in _statements(text):
        if st.ast_type != ast.ASTType.Rule or st.head.ast_type != ast.ASTType.Literal:
            continue
        sig = _atom_sig(st.head.atom)
        if sig and sig[0] == GHOST_PROJ:
            hit.add(f"{sig[0]}/{sig[1]}")
    return sorted(hit)
WIDTH_CAP = 20          # a free register / cell above this many bits is refused (2^W choices)


# ---------------------------------------------------------------------------------------------
# reading the ghost state off a monitor file
# ---------------------------------------------------------------------------------------------

def _time_offset(term) -> "tuple | None":
    """(var, offset) if `term` is a time argument -- `T`, `T+2`, `T-1` -- else None."""
    from clingo import ast
    if term.ast_type == ast.ASTType.Variable:
        return (term.name, 0)
    if term.ast_type == ast.ASTType.BinaryOperation:
        l, r = term.left, term.right
        if l.ast_type == ast.ASTType.Variable and r.ast_type == ast.ASTType.SymbolicTerm:
            try:
                n = r.symbol.number
            except Exception:
                return None
            if term.operator_type == ast.BinaryOperator.Plus:
                return (l.name, n)
            if term.operator_type == ast.BinaryOperator.Minus:
                return (l.name, -n)
    return None


def _atom_sig(a):
    """(name, arity, time-offset-or-None) of a symbolic atom's Function term."""
    from clingo import ast
    if a.ast_type != ast.ASTType.SymbolicAtom:
        return None
    f = a.symbol
    if f.ast_type != ast.ASTType.Function or not f.arguments:
        return None
    return (f.name, len(f.arguments), _time_offset(f.arguments[-1]))


def _statements(text: str) -> list:
    from clingo import ast
    out: list = []
    ast.parse_string(text, out.append)
    return out


def ghost_predicates(text: str) -> dict:
    """The HISTORY predicates of a monitor file: name -> arity, for every predicate that some rule
    defines at a later instant than a literal of the same rule's body (head `p(.., T+c)` with a
    body at `T`, or head at `T` with a body at `T-c`). Monitors and the design vocabulary are
    excluded. Read off the text, so a new ghost is caught the day it is written."""
    from clingo import ast
    found: dict = {}
    for st in _statements(text):
        if st.ast_type != ast.ASTType.Rule:
            continue
        head = st.head
        heads = []
        if head.ast_type == ast.ASTType.Literal:
            s = _atom_sig(head.atom)
            if s:
                heads.append(s)
        elif head.ast_type == ast.ASTType.Disjunction:
            for c in head.elements:
                s = _atom_sig(c.literal.atom)
                if s:
                    heads.append(s)
        else:
            continue
        body_offsets: dict = {}
        for lit in st.body:
            if lit.ast_type != ast.ASTType.Literal:
                continue
            s = _atom_sig(lit.atom)
            if s and s[2] is not None:
                var, off = s[2]
                body_offsets[var] = min(body_offsets.get(var, off), off)
        for name, ar, toff in heads:
            if name in MONITOR_PREDS or toff is None:
                continue
            var, off = toff
            if var in body_offsets and off > body_offsets[var]:
                found[name] = ar
    return found


def init_heads(text: str) -> dict:
    """The predicates a ghost-init file gives a value at T=0: name -> arity, read off every
    rule head (choice, disjunction, plain), so the runner can count what the init covers against
    what the monitors need."""
    from clingo import ast
    out: dict = {}

    def take(a):
        s = _atom_sig(a)
        if s:
            out[s[0]] = s[1]

    for st in _statements(text):
        if st.ast_type != ast.ASTType.Rule:
            continue
        h = st.head
        if h.ast_type == ast.ASTType.Literal:
            take(h.atom)
        elif h.ast_type == ast.ASTType.Disjunction:
            for c in h.elements:
                take(c.literal.atom)
        elif h.ast_type == ast.ASTType.Aggregate:
            for e in h.elements:
                take(e.literal.atom)
        elif h.ast_type == ast.ASTType.HeadAggregate:
            for e in h.elements:
                take(e.condition.literal.atom)
    return out


# ---------------------------------------------------------------------------------------------
# the ghost init as a MEMBERSHIP CONDITION (so closure is one query, not an enumeration)
# ---------------------------------------------------------------------------------------------

_MEMB_HEAD = """% generated by sv2asp.aspfirst induct -- the ghost INIT read as a MEMBERSHIP CONDITION on the ghost
% state at instant 1. The init file GENERATES a state (choice rules); to check that a state is IN the
% domain one would otherwise have to generate every state and look, which is an enumeration whose size is
% the ghost's state space -- exactly what induction exists to avoid (a 1000-cycle counter in the ghost
% makes it 160,000). The same rules read as CONSTRAINTS answer membership directly, so closure ("from any
% state in the domain, one step lands in the domain") becomes a single UNSAT query whose cost is the
% design's transition, not the domain's size.
%
% `gh_outside(Why)` holds exactly when the instant-1 ghost state is NOT in the domain:
%   domain(p)   an atom of p that no element condition of the init admits
%   missing(p)  an atom the init requires (a lower bound, or a plain derivation) that the state lacks
%   excluded    a constraint of the init that the state violates
% (at-most-one is NOT here: it is the ghost's own single-valuedness, a separate obligation; here it would
%  be a |domain|^2 pairwise join or an aggregate, and neither is in this grammar)
"""


def init_membership(ghost_text: str, ghosts: dict, symbolic: bool = False) -> tuple:
    """(program, unsupported) -- the ghost-init generator `ghost_text` rewritten as constraints that
    derive `gh_outside(Why)` when the ghost state at instant 1 is outside the declared domain.

    Exact for the shapes the route uses: a choice rule `{ p(A.., 0) : Cond } OP N :- Body.` (any number
    of element sets over ONE predicate), and a plain rule deriving a ghost atom or a helper. Anything
    else is listed in `unsupported` and the caller must not claim closure -- an approximation here would
    make the soundness check itself unsound, which is the one thing it must never be.

    Under the SYMBOLIC reading (`symbolic=True`) the domain closed is the ghost's CONTROL part: a
    condition through a TOKEN HELPER -- a helper of the init whose body reads `data(N)`, the guide's
    `held(X) :- val(N, X, 0), data(N).` convention ("a ghost that carries data draws from the tokens the
    design holds") -- constrains a DATA position, and data positions are free by the reading's premise
    (data-independence: a token is a name, and the step gives every data register a fresh one). The
    enumeration this replaced dropped token-valued ghost atoms from the comparison for the same
    reason; without this, a job's promised result `idiv(a, b)` at instant 1 -- a term no register holds
    yet -- read as "outside the domain" (the ALU dispatcher's closure failed spuriously, 2026-08-19)."""
    from clingo import ast
    stmts = _statements(ghost_text)
    helpers = {st.head.atom.symbol.name for st in stmts
               if st.ast_type == ast.ASTType.Rule and st.head.ast_type == ast.ASTType.Literal
               and getattr(st.head.atom, "symbol", None) is not None
               and st.head.atom.symbol.ast_type == ast.ASTType.Function
               and st.head.atom.symbol.name not in ghosts}
    token_helpers = set()
    if symbolic:
        for st in stmts:
            if (st.ast_type == ast.ASTType.Rule and st.head.ast_type == ast.ASTType.Literal
                    and getattr(st.head.atom, "symbol", None) is not None
                    and st.head.atom.symbol.ast_type == ast.ASTType.Function
                    and st.head.atom.symbol.name in helpers
                    and any(re.search(r"(?<![A-Za-z0-9_])data\(", str(b)) for b in st.body)):
                token_helpers.add(st.head.atom.symbol.name)

    def is_token_cond(c) -> bool:
        a = getattr(getattr(c, "atom", None), "symbol", None)
        return a is not None and getattr(a, "name", None) in token_helpers
    shift = {**{g: a for g, a in ghosts.items()}, "val": 3}       # predicates whose LAST argument is the instant

    class _Rw(ast.Transformer):
        def visit_Function(self, node):
            node = node.update(**self.visit_children(node))
            args = list(node.arguments)
            if node.name in shift and args and str(args[-1]) == "0":
                args[-1] = ast.SymbolicTerm(node.location, _num(1))
                node = ast.Function(node.location, node.name, args, node.external)
            if node.name in helpers:
                node = ast.Function(node.location, node.name + "__m1", list(node.arguments), node.external)
            return node

    rw = _Rw()
    ok_rules, checks, unsupported = [], [], []
    for st in stmts:
        if st.ast_type in (ast.ASTType.Program, ast.ASTType.Comment, ast.ASTType.Definition):
            continue                     # `#program base.`, comments and `#const` carry no init content
        if st.ast_type != ast.ASTType.Rule:
            unsupported.append(str(st))
            continue
        body = ", ".join(str(rw.visit(b)) for b in st.body)
        head = st.head
        if head.ast_type == ast.ASTType.Literal and head.atom.ast_type == ast.ASTType.BooleanConstant:
            # an integrity constraint in the init NARROWS the domain: a state whose body holds is not in it
            checks.append(f"gh_outside(excluded) :- {body}.")
            continue
        if head.ast_type == ast.ASTType.Literal and getattr(head.atom, "symbol", None) is not None \
                and head.atom.symbol.ast_type == ast.ASTType.Function:
            name = head.atom.symbol.name
            h1 = str(rw.visit(head))
            if name in ghosts:                       # a DERIVED ghost atom: it must be there, and nowhere else
                checks.append(f"gh_outside(missing({name})) :- {body}{', ' if body else ''}not {h1}.")
                ok_rules.append(f"{_ok(name, _args(h1))} :- {body}." if body else f"{_ok(name, _args(h1))}.")
            else:                                    # a helper of the init file: derive it at instant 1
                checks.append(f"{h1} :- {body}." if body else f"{h1}.")
            continue
        if head.ast_type != ast.ASTType.Aggregate:
            unsupported.append(str(st))
            continue
        names = {e.literal.atom.symbol.name for e in head.elements}
        if len(names) != 1 or not (names <= set(ghosts)):
            unsupported.append(str(st) + "   (a choice over more than one ghost predicate)")
            continue
        name = names.pop()
        counted = []
        for e in head.elements:
            lit = str(rw.visit(e.literal))
            cond = ", ".join(str(rw.visit(c)) for c in e.condition if not is_token_cond(c))
            pre = ", ".join(x for x in (cond, body) if x)
            # the ok rule is consulted only for an atom that EXISTS at instant 1, so the atom itself may
            # bind the element's variables (a dropped token condition was the binder of its position)
            ok_rules.append(f"{_ok(name, _args(lit))} :- {lit}{', ' + pre if pre else ''}.")
            counted.append((lit, cond))
        g = head.left_guard or head.right_guard
        if g is not None:
            # The guard's LOWER bound (`= 1`, `>= 1`: at least one atom must be present when the body
            # holds) is a MISSING check: no aggregate -- a helper `gh_some_p(..)` per element set, and
            # `gh_outside(missing(p))` when the body holds and no element is present. The UPPER bound
            # (`<= 1`, `= 1`: at most one) is NOT checked here: at-most-one over a wide ghost domain is
            # a |domain|^2 pairwise join or an aggregate, and neither belongs in this grammar -- it is
            # the ghost's own SINGLE-VALUEDNESS, a separate obligation the contract self-checks carry.
            lower = (g.comparison in (ast.ComparisonOperator.Equal, ast.ComparisonOperator.GreaterEqual)
                     and str(g.term) != "0")
            if g.comparison == ast.ComparisonOperator.LessEqual and str(g.term) != "0":
                lower = False                                # `1 >= {..}` is clingo's `{..} <= 1`: no lower bound
            if g.comparison == ast.ComparisonOperator.GreaterEqual:
                lower = True                                 # `1 >= {..}` -- see above; clingo normalises
                # clingo writes `{..} <= 1` as `1 >= {..}` and `{..} >= 1` as `1 <= {..}`: the ROLE of the
                # comparison is decided by which side the count sits on. left_guard means TERM OP COUNT.
                lower = False
            if g.comparison == ast.ComparisonOperator.LessEqual:                    # `1 <= {..}` = at least 1
                lower = str(g.term) != "0"
            if g.comparison == ast.ComparisonOperator.Equal:
                lower = str(g.term) != "0"
            if lower:
                for i, (lit, cond) in enumerate(counted):
                    pre = ", ".join(x for x in (cond, body) if x)
                    checks.append(f"gh_some_{name}_{i} :- {lit}{', ' + pre if pre else ''}.")
                nots = ", ".join(f"not gh_some_{name}_{i}" for i in range(len(counted)))
                checks.append(f"gh_outside(missing({name})) :- {body}{', ' if body else ''}{nots}.")
    for name, ar in sorted(ghosts.items()):
        if not any(r.startswith(f"gh_ok_{name}(") or r.startswith(f"gh_ok_{name} ") or r == f"gh_ok_{name}."
                   for r in ok_rules):
            continue
        vs = ", ".join(f"X{i}" for i in range(ar - 1))
        checks.append(f"gh_outside(domain({name})) :- {name}({vs}{', ' if vs else ''}1), not {_ok(name, vs)}.")
    prog = _MEMB_HEAD + "\n".join(ok_rules + checks) + "\n#defined gh_outside/1.\n"
    for name in ghosts:
        for i in range(8):
            prog += f"#defined gh_some_{name}_{i}/0.\n"
    return prog, unsupported


def _num(i):
    from clingo import Number
    return Number(i)


def _ok(name: str, args: str) -> str:
    """`gh_ok_p(a, b)` -- or the bare `gh_ok_p` when the ghost atom's only argument is the instant."""
    return f"gh_ok_{name}({args})" if args else f"gh_ok_{name}"


def _args(atom_text: str) -> str:
    """The argument list of `p(a, b, 1)` WITHOUT the trailing instant: `a, b`."""
    inner = atom_text[atom_text.index("(") + 1:atom_text.rindex(")")] if "(" in atom_text else ""
    parts, depth, cur = [], 0, []
    for ch in inner:
        if ch == "," and depth == 0:
            parts.append("".join(cur).strip()); cur = []
            continue
        depth += (1 if ch in "([" else 0) - (1 if ch in ")]" else 0)
        cur.append(ch)
    parts.append("".join(cur).strip())
    return ", ".join(parts[:-1])


def _vars(*texts) -> str:
    """The distinct variables of the given texts, in order -- the count tuple of an aggregate element."""
    seen, out = set(), []
    for t in texts:
        for v in re.findall(r"(?<![A-Za-z0-9_])([A-Z][A-Za-z0-9_]*)", t or ""):
            if v not in seen:
                seen.add(v); out.append(v)
    return ", ".join(out) or "1"


# ---------------------------------------------------------------------------------------------
# CASES read off the ghost's own guards -- the border of a counter, the values of a phase
# ---------------------------------------------------------------------------------------------

def ghost_cases(spec_text: str, ghosts: dict, limit: int = 12) -> list:
    """A PARTITION of the ghost state at instant 0 into cases, derived from the ghost rules themselves:
    for a ghost predicate whose transition rules guard a numeric argument (`fc(L, T), L < ticks-1` /
    `fc(ticks-1, T)`), the cases are each guard, the rest, and "no such atom". A proof split this way is
    the border argument made mechanical -- below the border a tick increments, at the border the group
    ends -- and a failure names its case instead of a 160,000-state blur.

    Returns [(label, constraint_text)], the constraint selecting the case at instant 0. One predicate is
    split (the one with the most guards); [] when no ghost has a numeric guard (nothing to split on)."""
    from clingo import ast
    guards: dict = {}                     # (pred, argpos) -> ordered list of (label, selects_text)
    for st in _statements(spec_text):
        if st.ast_type != ast.ASTType.Rule:
            continue
        lits = [b for b in st.body if b.ast_type == ast.ASTType.Literal]
        # variables bound at a numeric position of a ghost predicate in this body, and constant args there
        bound: dict = {}
        for b in lits:
            a = getattr(b, "atom", None)
            if a is None or a.ast_type != ast.ASTType.SymbolicAtom or a.symbol.ast_type != ast.ASTType.Function:
                continue
            f = a.symbol
            if f.name not in ghosts:
                continue
            for i, arg in enumerate(f.arguments[:-1]):          # the last argument is the instant
                if arg.ast_type == ast.ASTType.Variable:
                    bound[str(arg)] = (f.name, i)
                elif arg.ast_type in (ast.ASTType.SymbolicTerm, ast.ASTType.BinaryOperation, ast.ASTType.UnaryOperation):
                    key = (f.name, i)
                    lab = f"{f.name} = {arg}"
                    ent = guards.setdefault(key, [])
                    if lab not in [l for l, _ in ent]:
                        ent.append((lab, f"= {arg}"))
        for b in lits:
            a = getattr(b, "atom", None)
            if a is None or a.ast_type != ast.ASTType.Comparison:
                continue
            terms = [a.term] + [g.term for g in a.guards]
            ops = [g.comparison for g in a.guards]
            if len(terms) != 2 or ops[0] == ast.ComparisonOperator.NotEqual:
                continue
            l, r = terms
            var, other, op = None, None, ops[0]
            if l.ast_type == ast.ASTType.Variable and str(l) in bound:
                var, other = str(l), r
            elif r.ast_type == ast.ASTType.Variable and str(r) in bound:
                var, other = str(r), l
                op = {ast.ComparisonOperator.LessThan: ast.ComparisonOperator.GreaterThan,
                      ast.ComparisonOperator.GreaterThan: ast.ComparisonOperator.LessThan,
                      ast.ComparisonOperator.LessEqual: ast.ComparisonOperator.GreaterEqual,
                      ast.ComparisonOperator.GreaterEqual: ast.ComparisonOperator.LessEqual}.get(op, op)
            if var is None or other.ast_type == ast.ASTType.Variable:
                continue                                 # a comparison against another VARIABLE is not a case
            sym = {ast.ComparisonOperator.LessThan: "<", ast.ComparisonOperator.GreaterThan: ">",
                   ast.ComparisonOperator.LessEqual: "<=", ast.ComparisonOperator.GreaterEqual: ">=",
                   ast.ComparisonOperator.Equal: "="}.get(op)
            if sym is None:
                continue
            key = bound[var]
            lab = f"{key[0]} {sym} {other}"
            ent = guards.setdefault(key, [])
            if lab not in [l for l, _ in ent]:
                ent.append((lab, f"{sym} {other}"))
    if not guards:
        return []
    # prefer a COUNTER (a predicate with ordering guards -- the border argument) over a discrete phase
    def rank(kv):
        gs = kv[1]
        ordered = sum(1 for _, sel in gs if sel[0] in "<>")
        return (ordered, len(gs))
    (pred, pos), gs = max(guards.items(), key=rank)
    ar = ghosts[pred]
    vs = [f"X{i}" for i in range(ar - 1)]
    v = vs[pos]
    atom0 = f"{pred}({', '.join(vs)}, 0)" if vs else f"{pred}(0)"
    cases = [(f"no {pred} at T=0", f":- {atom0}.")]
    negs = []
    for lab, sel in gs:
        # select: an atom exists AND satisfies the guard; exclude every atom that does not
        cases.append((lab, f":- not gh_case.\ngh_case :- {atom0}, {v} {sel}.\n:- {atom0}, not {v} {sel}."))
        negs.append(f"{v} {sel}")
    rest = ", ".join(f"not {n}" for n in negs)
    cases.append((f"{pred} outside every guard", f":- not gh_case.\ngh_case :- {atom0}, {rest}.\n:- {atom0}, not gh_case."))
    return cases[:limit]


def ghost_file_for(monitor_path: pathlib.Path) -> pathlib.Path:
    """`spec.lp` -> `spec.ghost.lp`; `l1.inv.lp` -> `l1.inv.ghost.lp`."""
    return monitor_path.with_name(monitor_path.name[:-3] + ".ghost.lp")


# ---------------------------------------------------------------------------------------------
# the generated companions of the step
# ---------------------------------------------------------------------------------------------

@dataclass
class StepPlan:
    text: str = ""                    # the generated program (state + inputs + time + ghost projection)
    unique: str = ""                  # the unique-states constraint (composed into the step, NOT into the vacuity check)
    regs: list = field(default_factory=list)      # (net, bits) freed at T=0
    mems: list = field(default_factory=list)      # (inst, depth, width)
    inputs: list = field(default_factory=list)    # input ports freed every instant
    resets: list = field(default_factory=list)
    reset_nets: list = field(default_factory=list)   # reset PINS that are not inputs: never pinned, so FREE
    tokens: list = field(default_factory=list)    # data registers / memories freed as TOKENS (symbolic reading)
    ghosts: dict = field(default_factory=dict)    # name -> arity
    pinned: list = field(default_factory=list)    # inputs pinned 1 every instant (obligation under opaque_datapath)
    errors: list = field(default_factory=list)


def _enum_of(w):
    return w[1] if isinstance(w, tuple) and w and w[0] == "enum" else None


def plan_step(d: Design, clocks: set, ghosts: dict, K: int, free_reset: bool = False,
              data: set = frozenset(), free_state: bool = True,
              pin_high: frozenset = frozenset(), skip_state: frozenset = frozenset(),
              extra_resets: frozenset = frozenset()) -> StepPlan:
    """The step's generated program: `#const k`, the time axis, every state element FREE at T=0,
    every input free at every instant (reset nets held released unless `free_reset`), the ghost
    projection `ghost_state/2`, and the unique-states constraint (a window with a repeated full state can
    be shortened, so requiring simple paths loses no soundness and makes the step complete for a
    finite system at some K)."""
    p = StepPlan(ghosts=dict(ghosts))
    L = [f"% generated by sv2asp.aspfirst induct -- the STEP of k-induction, K={K}",
         f"#const k = {K}.",
         "% the time axis"]
    for c in sorted(clocks):
        L.append(f"time({c}, 0..k).")
    # The reset nets a register hangs on -- but only those that are INPUTS are actually held released
    # below (the pin may be a derived net, e.g. `def(arst_n, lnot(areset))`, which nothing pins). The
    # report used to name every reset PIN as "held released" whether or not a rule was emitted for it,
    # which claimed a restriction the step had not applied. It over-states nothing about soundness --
    # an unheld reset is FREE, so the step covers more -- but a reader would draw the wrong conclusion
    # about what was proven, so the two are now distinguished.
    ports = {q.name for q in d.inputs()}
    resets = sorted({i.pins["rstL"] for i in d.cell_insts() if i.cell == "arff" and "rstL" in i.pins}
                    | set(extra_resets))          # reset bindings of ABSTRACT children (compose records
                                                  # them; their arffs never reach this design)
    p.resets = [r for r in resets if r in ports]
    p.reset_nets = [r for r in resets if r not in ports]
    L.append("% every INPUT free at every instant" + (" (reset nets held released)" if resets and not free_reset else ""))
    for port in d.inputs():
        n = port.name
        if n in clocks or n in data:                    # a data input is a token per instant (the companion)
            continue
        if n in resets and not free_reset:
            L.append(f"val({n}, 1, T) :- gtime(T).")
            continue
        if n in pin_high:
            # the delivery obligation under `opaque_datapath`: the enable/isolation input is a
            # FACT, not a choice, so the grounder prunes the idle branches and the datapath
            # stays single-candidate along the value path
            L.append(f"val({n}, 1, T) :- gtime(T).")
            p.pinned.append(n)
            continue
        e = _enum_of(port.width)
        if e:
            L.append(f"{{ val({n}, L, T) : enum_member({e}, L, _) }} = 1 :- gtime(T).")
        else:
            L.append(f"{{ val({n}, V, T) : V = 0..2**{port.width}-1 }} = 1 :- gtime(T).")
        p.inputs.append(n)
    L.append("% every STATE element free at T=0 (the __xinit choice pattern, from the design's cells)"
             if free_state else "% state NOT freed: the design's reset defines it (the ghost-init reset check)")
    for i in (d.cell_insts() if free_state else []):
        if i.cell in ("ff", "arff", "lata"):
            q = i.pins.get("q")
            if q in skip_state:
                continue     # opaque_datapath: the abstract companion owns this net, one token per instant
            w = d.width_of(q)
            e = _enum_of(w)
            if q in data:                                # a data register: a fresh TOKEN, not 2^W choices
                L.append(f"val({q}, init({q}), 0).")
                L.append(f"ind_state({q}).")
                p.tokens.append(q)
                continue
            if e:
                L.append(f"{{ val({q}, L, 0) : enum_member({e}, L, _) }} = 1.")
                p.regs.append((q, e))
            else:
                bits = int(i.iparams.get("width", w if isinstance(w, int) else 0))
                if bits > WIDTH_CAP:
                    p.errors.append(f"register {q} ({i.name}) is {bits} bits: freeing it at T=0 is 2^{bits} choices "
                                    f"(cap 2^{WIDTH_CAP}) -- keep wide datapath state abstract, or narrow it")
                    continue
                L.append(f"{{ val({q}, V, 0) : V = 0..2**{bits}-1 }} = 1.")
                p.regs.append((q, bits))
            L.append(f"ind_state({q}).")
        elif i.cell in ("spram", "farray"):
            depth, width = int(i.iparams["depth"]), int(i.iparams["width"])
            # `farray` reaches here for the same reason `spram` does: its cells ARE state, and the step
            # starts from an arbitrary one. It was missing when the cell was added, and that is not a
            # cost bug -- unfreed cells have no value at T=0, so nothing downstream of the memory can
            # fire and the step goes UNSAT for want of a start state, which the runner would have
            # reported as PROVEN. A vacuous proof, in the one place the whole route's claim lives.
            if i.pins.get("rd") in data or i.pins.get("wd") in data:   # a data memory (spram: declared
                # rd port; farray: readers are mrd EXPRESSIONS, so the content is data iff the write
                # data is -- the same flow rule the symbolic reading applies to the cells): a fresh
                # token per cell
                L.append(f"val(cell({i.name}, A), init(cell({i.name}, A)), 0) :- addr({i.name}, A).")
                L.append(f"ind_state(cell({i.name}, A)) :- addr({i.name}, A).")
                p.tokens.append(f"{i.name}[{depth}]")
                continue
            if width > WIDTH_CAP:
                p.errors.append(f"memory {i.name} is {width} bits wide: freeing its cells at T=0 is 2^{width} "
                                f"choices per cell (cap 2^{WIDTH_CAP})")
                continue
            L.append(f"{{ val(cell({i.name}, A), V, 0) : V = 0..2**{width}-1 }} = 1 :- addr({i.name}, A).")
            L.append(f"ind_state(cell({i.name}, A)) :- addr({i.name}, A).")
            p.mems.append((i.name, depth, width))
    L.append("% the ghost state, projected for the report and the unique-states constraint")
    for name, ar in sorted(ghosts.items()):
        xs = ", ".join(f"X{j}" for j in range(ar - 1))
        term = f"{name}({xs})" if xs else name
        args = f"{xs}, T" if xs else "T"
        L.append(f"{GHOST_PROJ}({term}, T) :- {name}({args}).")
    L.append(f"#show {GHOST_PROJ}/2.")
    L.append(f"#defined ind_state/1.  #defined {GHOST_PROJ}/2.")
    p.text = "\n".join(L) + "\n"
    p.unique = "\n".join([
        "% unique states: no two instants of the window share the full state (registers, cells, ghost).",
        "% A window with a repeated state can be shortened, so requiring simple paths loses no soundness;",
        "% it makes the step complete for a finite system once K exceeds the reachable diameter -- the",
        "% hypothesis then becomes UNSATISFIABLE, which is a proof, not vacuity (the runner tells them apart).",
        "% NEGATION, not an inequality join. `val(Q,V1,T1), val(Q,V2,T2), V1 != V2` is QUADRATIC in the",
        "% state element's value domain -- invisible for a 2- or 4-bit register (16 x 16), and 2^20 per",
        "% instant pair for a 10-bit one, which is what stopped `ve146_serialdata`'s step from",
        "% GROUNDING at all. Every element is single-valued per instant (t34), so \"differs\" is exactly",
        "% \"has a value here it does not have there\", and that is linear. The two ghost rules below",
        "% were already written this way; the register rule was not.",
        "st_diff(T1, T2) :- gtime(T1), gtime(T2), T1 < T2, ind_state(Q), val(Q, V, T1), not val(Q, V, T2).",
        "st_diff(T1, T2) :- gtime(T1), gtime(T2), T1 < T2, {P}(G, T1), not {P}(G, T2).".format(P=GHOST_PROJ),
        "st_diff(T1, T2) :- gtime(T1), gtime(T2), T1 < T2, {P}(G, T2), not {P}(G, T1).".format(P=GHOST_PROJ),
        "% GUARDED by `ind__uniq` so the runner can ground this ONCE and turn it on or off per query",
        "% with an assumption -- the vacuity check needs it OFF, every later query ON. The fallback",
        "% path supplies `UNIQ_ON` to assert it outright.",
        ":- gtime(T1), gtime(T2), T1 < T2, not st_diff(T1, T2), ind__uniq.",
        "#defined ind__uniq/0.", ""])
    return p


def ghost_lines(atoms: list, k: int) -> list:
    """`ghost_state(gcnt(3), 0)` atoms of a witness as per-instant lines for the report."""
    per: dict = {}
    for a in atoms:
        m = re.match(rf"{GHOST_PROJ}\((.+),(\d+)\)$", a)
        if m:
            per.setdefault(int(m.group(2)), []).append(m.group(1))
    out = []
    for t in range(k + 1):
        if t in per:
            out.append(f"  ghost @T={t}: " + ", ".join(sorted(per[t])))
    return out


def ghost_state_at(atoms: list, t: int) -> "frozenset":
    return frozenset(m.group(1) for a in atoms
                     for m in [re.match(rf"{GHOST_PROJ}\((.+),(\d+)\)$", a)] if m and int(m.group(2)) == t)


def pin_ghost_state(state: "frozenset", ghosts: dict, exact: bool = True) -> str:
    """Constraints pinning the ghost state at T=0 to `state` (used to test that an observed ghost
    state is PRODUCIBLE by the init): every observed atom required, and -- when `exact` -- no other
    ghost atom allowed. The symbolic reading passes exact=False: token-valued ghost atoms were
    dropped from `state` (a token from instant 3 cannot exist at T=0), so only the control part
    of the ghost is checked."""
    L = [f":- not {GHOST_PROJ}({g}, 0)." for g in sorted(state)]
    if exact:
        L += [f"obs_gh({g})." for g in sorted(state)]
        L.append(f":- {GHOST_PROJ}(G, 0), not obs_gh(G).")
        L.append("#defined obs_gh/1.")
    return "\n".join(L) + "\n"


# --------------------------------------------------------------------------------------------
# v2 (the linkage doctrine): gating and bounded-only classification
# --------------------------------------------------------------------------------------------

def ghost_gating(text: str) -> dict:
    """v2: for each HISTORY predicate of `text` (per ghost_predicates), whether EVERY rule whose
    head is that predicate carries a positive `refmodel` literal in its body. name -> (arity,
    fully_gated). A gated predicate is inert in the induction step (refmodel is absent there) and
    legal; an ungated one is spec-side ghost STATE, which v2 refuses -- link it to the design's
    flops (a derived view) or gate it under refmodel (METHODOLOGY tenets 2 and 4)."""
    from clingo import ast
    ghosts = ghost_predicates(text)
    gated = {n: True for n in ghosts}
    for st in _statements(text):
        if st.ast_type != ast.ASTType.Rule:
            continue
        heads = []
        h = st.head
        if h.ast_type == ast.ASTType.Literal:
            s = _atom_sig(h.atom)
            if s:
                heads.append(s[0])
        elif h.ast_type == ast.ASTType.Disjunction:
            for c in h.elements:
                s = _atom_sig(c.literal.atom)
                if s:
                    heads.append(s[0])
        if not any(n in ghosts for n in heads):
            continue
        has_refmodel = any(l.ast_type == ast.ASTType.Literal and "refmodel" == str(l.atom)
                           for l in st.body)
        if not has_refmodel:
            for n in heads:
                if n in ghosts:
                    gated[n] = False
    return {n: (ghosts[n], gated[n]) for n in ghosts}


def props_reading(text: str, names: set) -> set:
    """v2: the bad/viol TAGS whose defining rules read any predicate in `names` (directly, one
    level). Used to classify properties as BOUNDED-ONLY: a monitor over a refmodel-gated
    predicate can never fire in the step, so claiming it inductive would be vacuous -- v2 reports
    the split instead (METHODOLOGY tenet 7: the layers are stated, never blurred)."""
    from clingo import ast
    out: set = set()
    if not names:
        return out
    for st in _statements(text):
        if st.ast_type != ast.ASTType.Rule:
            continue
        h = st.head
        if h.ast_type != ast.ASTType.Literal:
            continue
        s = _atom_sig(h.atom)
        if not s or s[0] not in ("bad", "viol", "assume"):
            continue
        body_names = {_atom_sig(l.atom)[0] for l in st.body
                      if l.ast_type == ast.ASTType.Literal and _atom_sig(l.atom)}
        if body_names & names:
            m = re.match(r"(?:bad|viol|assume)\((\w+(?:\([^()]*\))?)\s*,", str(h.atom))
            if m:
                out.add(m.group(1))
    return out
