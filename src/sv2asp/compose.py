"""Composed-level tightness (F1) — the check no PER-SPEC check can make.

`_check_comb_loops` runs per spec, so two modules that are each acyclic can still close a
combinational cycle through the PARENT's port bridges — a loop only the COMPOSED program
shows. Flat mode reports such a loop; modular (the DEFAULT compile) did not, and the
composed program was then non-tight, which means Fages does not apply and every
completion-route argument over it is unsound. That is F1, and it is soundness-critical.

    translate  ->  no loop in the COMPOSED program  =>  tight  =>  Fages
                   =>  completion = stable models

This module builds the SAME-INSTANT positive value-dependency graph over concrete
(instance, signal-term) nodes:

  * a spec rule `val(Inst, s, .., T) :- .., val(Inst, s2, .., T), ..` gives the generic
    edge s2 -> s, instantiated at every `isa` instance of that spec;
  * a manifest bridge `val(child, f, V, T) :- val(parent, a, V, T).` gives the concrete
    cross-instance edge.

A rule whose head is at `T+1` (a register, a hold, a memory write) crosses a time index
and is NOT a same-instant edge — exactly the distinction that makes a sequential design
tight. Negated literals are skipped: tightness is about POSITIVE dependencies, and the
licensed stratified NAF is a separate obligation with its own check.

Ported from the version-4 repository, where it was written against this very defect and
already certifies all 98 committed examples here as tight.
"""

from __future__ import annotations

import pathlib
import re

from .state_inventory import state_family

# companions carry no design rules: the function library, the power-on choices, the
# scenario skeleton, and the single-valuedness guard (F9)
SKIP_SUFFIXES = ("__lib.lp", "__xinit.lp", "__scenario_stub.lp", "__t34.lp")

_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def split_args(s: str) -> list[str]:
    """Split a predicate's argument string on top-level commas (paren-aware)."""
    out, depth, cur = [], 0, []
    for ch in s:
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        if ch == "," and depth == 0:
            out.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    if cur:
        out.append("".join(cur).strip())
    return out


def val_literals(s: str):
    """Every POSITIVE `val(...)` literal in `s`, as its top-level argument list.
    `not val(...)` is excluded -- see the module doc."""
    i = 0
    while True:
        i = s.find("val(", i)
        if i < 0:
            return
        if i > 0 and (s[i - 1].isalnum() or s[i - 1] == "_"):  # word boundary
            i += 4
            continue
        if s[:i].rstrip().endswith("not"):  # negated literal: not a positive dependency
            i += 4
            continue
        depth, j = 0, i + 3
        while j < len(s):
            if s[j] == "(":
                depth += 1
            elif s[j] == ")":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        yield split_args(s[i + 4 : j])
        i = j


def canon(term: str, varmap: dict[str, str]) -> str:
    """Canonicalize a signal term: variables rename to X1, X2, ... in order of first
    appearance within one rule (varmap shared across the rule); constants/fields verbatim."""
    def sub(m: re.Match) -> str:
        t = m.group(0)
        if t[0].isupper() or t[0] == "_":
            if t not in varmap:
                varmap[t] = f"X{len(varmap) + 1}"
            return varmap[t]
        return t
    return _IDENT.sub(sub, term).replace(" ", "")


def term_base(term: str) -> str:
    return term.split("(", 1)[0]


def has_var(term: str) -> bool:
    """A variable in a CANONICALISED term (`canon` renames them X1, X2, ...)."""
    return re.search(r"\bX\d+\b", term) is not None


def has_raw_var(term: str) -> bool:
    """A clingo VARIABLE in a term as WRITTEN in the file: an argument whose identifier
    starts uppercase or `_` (`sum(I)`, `q(V0, V1)`, `mem(A)`).

    Distinct from `has_var` above, which expects `canon`'s renaming -- the dark-read check
    reads terms straight off the emitted text, where a lane producer is still `sum(I)`.
    Conflating the two made every lane-rolled producer look like no producer at all, so the
    check fired on 8 of 21 committed examples: a check that fires on everything is worth
    nothing, which is how the bug was caught."""
    inner = term[term.find("(") + 1:] if "(" in term else term
    return re.search(r"\b[A-Z_][A-Za-z0-9_]*\b", inner) is not None


def load(outdir: pathlib.Path):
    """-> (isa, spec_edges: spec -> {(srcTerm, dstTerm)}, bridge_edges over (inst, term))."""
    isa: dict[str, str] = {}
    spec_edges: dict[str, set[tuple[str, str]]] = {}
    bridge_edges: set[tuple[tuple[str, str], tuple[str, str]]] = set()
    files = [p for p in sorted(outdir.glob("*.lp")) if not p.name.endswith(SKIP_SUFFIXES)]
    manifest = [p for p in files if p.name.endswith("__inst.lp")]
    specs = [p for p in files if p not in manifest]

    for p in manifest:
        text = p.read_text().splitlines()
        for ln in text:
            ln = ln.strip()
            if ln.startswith("isa(") and ln.endswith(")."):
                a = split_args(ln[len("isa(") : -2])
                if len(a) == 2:
                    isa[a[0]] = a[1]
        for ln in text:
            ln = ln.strip()
            if not ln.endswith(".") or ":-" not in ln or not ln.startswith("val("):
                continue
            head, body = ln[:-1].split(":-", 1)
            hv = list(val_literals(head))
            if len(hv) != 1 or len(hv[0]) != 4 or hv[0][3] != "T":
                continue
            vm: dict[str, str] = {}
            hterm = canon(hv[0][1], vm)
            for bv in val_literals(body):
                if len(bv) == 4 and bv[3] == "T":
                    bridge_edges.add(((bv[0], canon(bv[1], vm)), (hv[0][0], hterm)))

    for p in specs:
        spec = p.name[:-3]
        edges = spec_edges.setdefault(spec, set())
        for ln in p.read_text().splitlines():
            ln = ln.strip()
            if not ln.endswith(".") or ":-" not in ln or not ln.startswith("val("):
                continue
            head, body = ln[:-1].split(":-", 1)
            hv = list(val_literals(head))
            # generic 4-ary head val(Inst, sig, V, T) at instant T only
            if len(hv) != 1 or len(hv[0]) != 4 or hv[0][0] != "Inst" or hv[0][3] != "T":
                continue
            vm = {"Inst": "Inst"}  # the instance var is not an index; keep it out of X-numbering
            hterm = canon(hv[0][1], vm)
            for bv in val_literals(body):
                if len(bv) == 4 and bv[0] == "Inst" and bv[3] == "T":
                    edges.add((canon(bv[1], vm), hterm))
    return isa, spec_edges, bridge_edges


def build_graph(isa, spec_edges, bridge_edges):
    adj: dict[tuple[str, str], set[tuple[str, str]]] = {}

    def edge(u, v):
        adj.setdefault(u, set()).add(v)
        adj.setdefault(v, set())

    for inst, spec in isa.items():
        for s2, s in spec_edges.get(spec, ()):  # body -> head
            edge((inst, s2), (inst, s))
    for u, v in bridge_edges:
        edge(u, v)
    # KNOWN UNDER-APPROXIMATION (named, bounded -- version 2's documented stance, kept):
    # a variable-indexed term `s(X1)` and a constant-indexed `s(0)` are DISTINCT nodes, so a
    # cycle that exists only through lane aliasing (a variable read feeding a constant-lane
    # write of the same base) is not reported. Aliasing cannot be modeled as graph edges --
    # a both-ways alias edge is itself a 2-cycle, and one-way loses conservativeness; the
    # sound refinement is TEMPLATE SUBSTITUTION (instantiate each variable edge over the
    # base's observed lane constants, evaluating index arithmetic), which is the named
    # upgrade path if a real design ever exercises this corner. What this build does catch,
    # beyond v2's flat checker: per-lane feedback written with different variable NAMES in
    # its two rules (canonical renaming), and everything cross-instance.
    return adj


def find_cycle(adj):
    WHITE, GREY, BLACK = 0, 1, 2
    color = {n: WHITE for n in adj}
    for root in adj:
        if color[root] != WHITE:
            continue
        stack = [(root, iter(sorted(adj[root])))]
        color[root] = GREY
        path = [root]
        while stack:
            node, it = stack[-1]
            advanced = False
            for nxt in it:
                if color.get(nxt, WHITE) == GREY:
                    return path[path.index(nxt) :] + [nxt]
                if color.get(nxt, WHITE) == WHITE:
                    color[nxt] = GREY
                    stack.append((nxt, iter(sorted(adj.get(nxt, ())))))
                    path.append(nxt)
                    advanced = True
                    break
            if not advanced:
                color[node] = BLACK
                stack.pop()
                path.pop()
    return None


def topo_order(adj):
    indeg = {n: 0 for n in adj}
    for n in adj:
        for m in adj[n]:
            indeg[m] = indeg.get(m, 0) + 1
    ready = sorted(n for n, d in indeg.items() if d == 0)
    order = []
    while ready:
        n = ready.pop(0)
        order.append(n)
        for m in sorted(adj.get(n, ())):
            indeg[m] -= 1
            if indeg[m] == 0:
                ready.append(m)
        ready.sort()
    return order


# ── DARK READS ───────────────────────────────────────────────────────────────────────
#
# The general form of F2, F7 and F10's residue: a rule READS a signal that no rule
# DERIVES. The consumer is emitted, the producer is not, and the signal simply has no
# value at any instant -- so every property over it passes VACUOUSLY while the tool exits
# 0. Each of those findings was a different construct arriving at the same shape, which is
# why this is checked once, generally, over the emitted program rather than per feature:
#
#   F2  `$rose`/`$fell`: modular emitted the consumer and none of the four deriving rules.
#   F7  an unpacked ARRAY through a port: the bridge reads the WORD atom `src`, while the
#       object's atoms are its cells `src(0..3)` -- so both the word and the cells are dark.
#   F10 an unlowerable block: the block's targets got no rules and their consumers did.
#
# An INPUT is legitimately underived -- the scenario supplies it, and that is the boundary
# the whole design layer is a function of. Everything else must have a producer.

def rules_of(path: pathlib.Path):
    """Yield each complete RULE in a file, joined across continuation lines.

    A rule ends at its terminating period, and version 2 writes long ones over several
    lines -- a hand-written functional stub is the usual case. Parsing line-by-line and
    demanding a trailing `.` silently skipped every such rule: the dark-read check then
    reported a stub's own output as underived, when the stub derives it perfectly well and
    the design solves. Found by that false positive.
    """
    buf: list[str] = []
    for raw in path.read_text().splitlines():
        ln = raw.strip()
        if not ln or ln.startswith("%"):
            continue
        buf.append(ln)
        if ln.endswith("."):
            yield " ".join(buf)
            buf = []


def _heads_and_reads(path: pathlib.Path, generic: bool):
    """-> (head terms, read terms) for one file. `generic` = a spec (rules over `Inst`)."""
    heads: set[str] = set()
    reads: set[str] = set()
    for ln in rules_of(path):
        if not ln.startswith("val("):
            continue
        head, _, body = ln[:-1].partition(":-")
        for lit in val_literals(head):
            if len(lit) == 4 and (not generic or lit[0] == "Inst"):
                heads.add(lit[1])
            elif len(lit) == 3 and not generic:
                heads.add(lit[0])
        for lit in val_literals(body):
            if len(lit) == 4 and (not generic or lit[0] == "Inst"):
                reads.add(lit[1])
            elif len(lit) == 3 and not generic:
                reads.add(lit[0])
    return heads, reads


def dark_terms(reads: set[str], derived: set[str], driven: set[str]) -> list[str]:
    """THE DARK-READ DECISION, over plain term sets: which of `reads` nothing derives.

    `derived` is every head term, `driven` every term something outside the design supplies
    (a declared input, or a signal the frontend knows is externally driven).

    **This is deliberately one function used by BOTH compile modes.** The check was written for
    modular and lived only there, so flat -- where a submodule construct that fails to lower
    leaves its consumer reading an atom nothing derives -- had no equivalent at all and reported
    `coverage: OK`, exit 0. That is the two-emitter split (hard rule 1) with flat on the missing
    side for the first time. A second copy of this rule would reproduce the split by
    construction, so the two modes differ only in how they COLLECT the terms, never in what
    counts as dark.

    Two subtleties, both paid for:

      * a head carrying a VARIABLE index (`val(s(I), ..)`) covers every concrete read of that
        base -- that is what makes a lane-rolled producer count as deriving `s(0)`;
      * a base derived as a WORD (arity-0 head) and NEVER with a FUNCTOR means every cell read
        of it is dark, because the atom that exists and the atom being read are different
        atoms. That is F7 -- an unpacked array crossing a PORT, bridged as a scalar -- and it
        has to be tested here rather than by relaxing the variable guard below, which is right
        for `val(X, ..)` (the signal itself is a variable) and would swallow `buf_(V0)`, whose
        base is concrete.
    """
    # INDEXED-ness is decided by `state_family`, not by splitting at the first `(`. Under
    # hierarchy flattening the instance wraps the signal, so `u(buf_(V0))` is one CELL of the
    # family `u(buf_)` -- splitting at the first `(` calls its base `u`, which matches the
    # instance rather than the array and makes every such read look derived. That is the same
    # root-vs-family error that had the state inventory reporting instance names as state, and
    # here it hid F7's own shape in FLAT mode.
    word_derived = {t for t in derived if state_family(t) == t}
    functor_derived = {state_family(t) for t in derived if state_family(t) != t}
    out: list[str] = []
    for t in sorted(reads):
        fam = state_family(t)
        indexed = fam != t
        if indexed and fam in word_derived and fam not in functor_derived:
            out.append(t)                 # word-bridged, read as a cell: F7's shape
            continue
        if t in derived or fam in functor_derived:
            # derived directly, or covered by an INDEXED head of the same family. The second
            # half holds for a BARE read too, and must: the lane<->word bridge derives
            # `val(m(I), ..)` per bit and assembles the word `val(m, ..)` from it, so requiring
            # `indexed` here flags every per-bit signal read as a word (`bitvec_word_form_demo`).
            continue
        if t in driven or fam in driven:
            continue                      # an input / externally driven: the scenario drives it
        if has_raw_var(t):
            # A variable read is bound by the rule, not a signal. This ALSO covers a cell read
            # of a family nothing derives in any form -- an INPUT unpacked array, whose port
            # fact the emitter does not declare (a `Mem` carries no direction), so `driven`
            # cannot know about it. Dropping the guard for indexed terms flags every such
            # array: `src(I)` on a design whose `src` is an input port. The F7 shape does not
            # need it dropped -- that branch fires ABOVE, on the sharper property that the
            # family is word-derived and never functor-derived.
            continue
        out.append(t)
    return out


def split_drivers(text: str) -> list[str]:
    """THE SPLIT-DRIVER DECISION, shared by both compile modes: signals driven BOTH as a whole word and
    per element by INDEPENDENT rules -- two drivers that can disagree, with nothing to arbitrate them.

    The legitimate word/element coexistence is the lane<->word BRIDGE, which is not independent: its
    word rule is assembled FROM the elements (its body reads `y(i)`) and its element rule is decomposed
    FROM the word (its body reads `y`). So a rule is a DRIVER of one form only when its body does not
    read the other form, and two drivers of different granularity for one signal is a defect.

    Written after F22, where `always_comb begin y = a; y[2] = y[2] ^ c; end` emitted a word rule
    (`val(y, V) :- val(a, V)`) beside an element rule (`val(y(2), ..)`) that disagreed with it: a
    consumer reading the word saw the un-updated value, at exit 0 with `coverage: OK`. `t34` cannot see
    it -- `val(y, ..)` and `val(y(2), ..)` are different atoms -- so the guard has to be structural.
    It is deliberately a CHECK rather than a promise about the lowering: the lowering was fixed too,
    but a future construct that splits a signal the same way is caught the day it lands."""
    word: dict[str, bool] = {}       # signal -> has a word rule that does NOT read its elements
    elem: dict[str, bool] = {}       # signal -> has an element rule that does NOT read its word
    for ln in _rules_of_text(text):
        if not ln.startswith("val("):
            continue
        head, _, body = ln[:-1].partition(":-")
        hl = [l for l in val_literals(head) if len(l) == 3]
        if not hl:
            continue
        h = hl[0][0]
        reads = {l[0] for l in val_literals(body) if len(l) == 3}
        base = h.split("(", 1)[0]
        if "(" in h:                                  # an ELEMENT head `y(2)` / `y(I)`
            # A bridge DECOMPOSES over a variable index (`val(y(I), B, T) :- val(y, V, T), I = 0..n-1`),
            # and so does every lane/generate driver -- the head index is a variable in both. A rule that
            # names a CONSTANT element is a driver of that one element. Testing "does the body read the
            # word" instead was wrong and the sabotage control caught it: the F22 rule
            # `val(y(2), ..) :- val(y, V, T), V1 = @slc(V, 2, 1), ..` DOES read the word, so it was
            # misclassified as a bridge and the guard passed on the very defect it was written for.
            args = h[h.index("(") + 1: h.rindex(")")].split(",")
            if all(a.strip().lstrip("-").isdigit() for a in args if a.strip()):
                elem[base] = True
        else:                                         # a WORD head `y`
            if not any(r.split("(", 1)[0] == base and "(" in r for r in reads):
                word[base] = True                     # ...not assembled from the elements
    return sorted(k for k in word if elem.get(k))


def find_dark_reads_flat(text: str, extern: set[str] | None = None) -> list[str]:
    """The FLAT-mode dark read: terms the emitted program reads that nothing in it derives.

    Same decision as the modular check (`dark_terms`), over the single flat namespace -- there
    are no instances, so a term is just a signal. Inputs come from the flat `port(Sig, input,
    Mod)` facts; `extern` carries what only the FRONTEND knows (a struct-typed input port emits
    no `port(..., input)` fact for its FIELDS).

    The gap this closes, witnessed: a submodule whose construct fails to lower leaves the parent
    reading `val(u_x(lq), V, T)` with no rule deriving it, and flat reported `coverage: OK` with
    exit 0. `_check_underivable_reads` did not catch it because that check asks whether a name is
    neither DECLARED nor derived -- and `u_x(lq)` is declared.
    """
    heads: set[str] = set()
    reads: set[str] = set()
    inputs: set[str] = set()
    for ln in _rules_of_text(text):
        if ln.startswith("port(") and ", input," in ln.replace(", input, ", ", input,"):
            a = split_args(ln[len("port("): ln.rindex(")")])
            if len(a) >= 2 and a[1] == "input":
                inputs.add(a[0])
        if ln.startswith("dontcare_at("):
            # a signal the design DECLARES unconstrained (an `x`-valued assignment): the boundary
            # companion supplies its value as a choice, exactly as it does for an unreset register,
            # so it is DRIVEN from outside the design layer -- not a missing producer. Without this
            # every design with an `x` don't-care would be refused as a dark read
            # (notes/design/X_SEMANTICS.md D4).
            inputs.add(ln[len("dontcare_at("):].split(",", 1)[0].strip())
            continue
        if not ln.startswith("val("):
            continue
        head, _, body = ln[:-1].partition(":-")
        for lit in val_literals(head):
            if len(lit) == 3:
                heads.add(lit[0])
        for lit in val_literals(body):
            if len(lit) == 3:
                reads.add(lit[0])
    return dark_terms(reads, heads, inputs | set(extern or ()))


def _rules_of_text(text: str):
    """`rules_of`, over a string rather than a file -- flat mode checks the program it is about
    to write, before any file exists."""
    buf: list[str] = []
    for raw in text.splitlines():
        ln = raw.strip()
        if not ln or ln.startswith("%"):
            continue
        buf.append(ln)
        if ln.endswith("."):
            yield " ".join(buf)
            buf = []


def find_dark_reads(outdir: pathlib.Path,
                    extern: dict[str, set[str]] | None = None) -> list[tuple[str, str]]:
    """Signals a rule reads that nothing derives -> [(instance, term), ...], sorted.

    Collects the terms per instance and defers the decision to `dark_terms`, which flat mode
    uses too -- see there for why that sharing is the point rather than a tidiness.
    """
    files = [p for p in sorted(outdir.glob("*.lp")) if not p.name.endswith(SKIP_SUFFIXES)]
    manifest = [p for p in files if p.name.endswith("__inst.lp")]
    specs = [p for p in files if p not in manifest]

    isa: dict[str, str] = {}
    inputs: set[tuple[str, str]] = set()          # (spec, signal) declared `input`
    for p in specs:
        for ln in p.read_text().splitlines():
            ln = ln.strip()
            if ln.startswith("port(Inst, ") and ", input)" in ln:
                a = split_args(ln[len("port(") : ln.rindex(")")])
                if len(a) >= 2:
                    inputs.add((p.name[:-3], a[1]))
    for p in manifest:
        for ln in p.read_text().splitlines():
            ln = ln.strip()
            if ln.startswith("isa(") and ln.endswith(")."):
                a = split_args(ln[len("isa(") : -2])
                if len(a) == 2:
                    isa[a[0]] = a[1]

    spec_heads: dict[str, set[str]] = {}
    spec_reads: dict[str, set[str]] = {}
    for p in specs:
        h, r = _heads_and_reads(p, generic=True)
        spec_heads[p.name[:-3]] = h
        spec_reads[p.name[:-3]] = r

    # the manifest derives signals too (a bridge's head), and reads them (its body)
    m_heads: set[tuple[str, str]] = set()
    m_reads: set[tuple[str, str]] = set()
    for p in manifest:
        for ln in rules_of(p):
            if not ln.startswith("val("):
                continue
            head, _, body = ln[:-1].partition(":-")
            for lit in val_literals(head):
                if len(lit) == 4:
                    m_heads.add((lit[0], lit[1]))
            for lit in val_literals(body):
                if len(lit) == 4:
                    m_reads.add((lit[0], lit[1]))

    # Collect per INSTANCE, then hand each instance's term sets to the shared decision. The
    # manifest's own heads/reads belong to the instance they name, so they fold in here.
    per_inst_derived: dict[str, set[str]] = {}
    per_inst_reads: dict[str, set[str]] = {}
    for i, t in m_heads:
        per_inst_derived.setdefault(i, set()).add(t)
    for i, t in m_reads:
        per_inst_reads.setdefault(i, set()).add(t)
    for inst, spec in isa.items():
        per_inst_derived.setdefault(inst, set()).update(spec_heads.get(spec, ()))
        per_inst_reads.setdefault(inst, set()).update(spec_reads.get(spec, ()))

    dark: list[tuple[str, str]] = []
    for inst in sorted(set(per_inst_reads) | set(per_inst_derived)):
        spec = isa.get(inst, "")
        # what the design does not have to derive: this spec's declared inputs, plus what only
        # the FRONTEND knows is externally driven (a struct-typed input port emits no
        # `port(..., input)` fact for its FIELDS -- the F6 under-declaration), so the emitted
        # text alone cannot tell that they are driven.
        driven = {sig for sp, sig in inputs if sp == spec} | set((extern or {}).get(spec, ()))
        dark += [(inst, t) for t in dark_terms(per_inst_reads.get(inst, set()),
                                               per_inst_derived.get(inst, set()), driven)]
    return sorted(dark)
