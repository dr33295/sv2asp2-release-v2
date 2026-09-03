"""Clark / HLR program completion of a translated design (Route 2).

A TRANSFORM on the emitted flat `.lp` text (the output of `stages.stage3_emit.emit`) -- not a
re-translation. The completion of a definite program is, per predicate, the biconditional
`p(x̄) ↔ ⋁_rules ∃z̄ (x̄ = head ∧ body)` (local vars existential, inputs/EDB open); for tight programs
its models coincide with the stable models (HLR 2017), so a property can be discharged DEDUCTIVELY.

Two renderers:
  * `completion_asp`  -- the explicit completion in ASP: a witness `der/3` (the *if* disjunction) +
    a DECOUPLED choice `{val} :- der` + the two directions, inputs left open (the faithful §4.1 form).
  * `completion_smt`  -- the classical completion as SMT-LIB QF_BV: each combinational signal a
    bit-vector FUNCTION of the inputs, for all-inputs (incl. wide) proofs in a classical solver.

COMBINATIONAL-FIRST: sequential (`T+1` / register / memory / lane) heads are FLAGGED loud (a `% PROBLEM`
/ `; UNSUPPORTED` line), never silently dropped.
"""
from __future__ import annotations

import re
from itertools import product

COMPLETION_MARK = "% ---- COMPLETION (Clark/HLR"   # ASP form marker (regen tracks it)
SMT_MARK = "; ==== Clark/HLR completion (SMT-LIB QF_BV)"

# @func op name (as emitted, e.g. band/bor/idiv) -> a binary SMT-LIB QF_BV operator, or a special tag.
_BIN_SMT = {"add": "bvadd", "sub": "bvsub", "mul": "bvmul", "band": "bvand", "bor": "bvor",
            "bxor": "bvxor", "shl": "bvshl", "shr": "bvlshr", "ashr": "bvashr"}
_UN_SMT = {"bnot": "bvnot", "neg": "bvneg"}
_CMP_SMT = {"=": "=", "!=": "distinct", "<": "bvult", "<=": "bvule", ">": "bvugt", ">=": "bvuge"}
_SCMP_SMT = {"=": "=", "!=": "distinct", "<": "bvslt", "<=": "bvsle", ">": "bvsgt", ">=": "bvsge"}


def _const_int(tok: str) -> int | None:
    """Fold a body token to an integer if it is a literal or a literal*literal product (a static slice
    index like `I * 8` only folds when I is already ground; a free var -> None -> the op is flagged)."""
    tok = tok.strip().strip('"')                 # wide values are quoted clingo Strings ("8589934592")
    if re.fullmatch(r"-?\d+", tok):
        return int(tok)
    if m := re.fullmatch(r"(-?\d+)\s*\*\s*(-?\d+)", tok):
        return int(m.group(1)) * int(m.group(2))
    return None


def _cmp_int(a: int, op: str, b: int) -> bool:
    return {"=": a == b, "!=": a != b, "<": a < b, "<=": a <= b, ">": a > b, ">=": a >= b}[op]


def _split_top(s: str, sep: str = ",") -> list[str]:
    """Split `s` on `sep` at PAREN DEPTH 0 (so functor args / nested calls stay intact)."""
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if ch == sep and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


class _Lp:
    """A parsed flat `.lp`: schema/script kept verbatim; behavioral rules grouped by head signal.

    `rules` holds EVERY `val(...)` design rule (combinational AND sequential/functor); the renderers
    pick their scope. A rule whose head time is `T+1` introduces SEQUENTIAL STATE (`seq_sigs`): that
    signal has no deriving rule at T=0, so its initial value is an OPEN boundary (like an input). The
    combinational subset (`comb_rules`) -- head time `T`, scalar, non-register -- is what the SMT
    renderer lowers to pure bit-vector functions."""

    def __init__(self, text: str) -> None:
        self.text = text
        self.inputs = set(re.findall(r"port\((\w+), input,", text))
        self.regs = set(re.findall(r"reg\((\w+)\)", text))
        # widths: parse each `type(` line with the paren-aware splitter so FUNCTOR heads are captured too
        # (`type(u_lzd(gcase_0), bit, 1)`), not just scalars (`type(q, bit, 3)`).
        self.widths: dict[str, int] = {}
        self.signed: set[str] = set()
        for ln in text.splitlines():
            s = ln.strip()
            if s.startswith("type(") and s.endswith(")."):
                a = _split_top(s[5:-2])
                if len(a) == 3 and a[1] in ("bit", "signed"):
                    self.widths[a[0]] = int(a[2])
                    if a[1] == "signed":
                        self.signed.add(a[0])
        # index domains for enumeration (Phase 2): lane(owner, lo..hi) and addr(mem, A) :- A = lo..hi
        self.lane_dom: dict[str, range] = {o: range(int(lo), int(hi) + 1)
                                           for o, lo, hi in re.findall(r"lane\((\w+), (\d+)\.\.(\d+)\)", text)}
        self.addr_dom: dict[str, range] = {m: range(int(lo), int(hi) + 1) for m, lo, hi in
                                           re.findall(r"addr\((\w+), \w+\) :- \w+ = (\d+)\.\.(\d+)", text)}
        self.elem_w: dict[str, int] = {m: int(w) for m, e, w in   # memory cell width via element_type
                                       [(m, e, dict(re.findall(r"element_type\((\w+), bit, (\d+)\)", text)).get(e))
                                        for m, e in re.findall(r"array\((\w+), (\w+),", text)] if w}
        # 1-D memory index bit-width: `array(m, _, unpacked, addr_w(W))` (a 2-D array has two addr_w -> no
        # single addr_w entry -> stays per-cell). Used by the SMT Array-theory lowering.
        self.addr_w: dict[str, int] = {m: int(w) for m, w in
                                       re.findall(r"array\((\w+), \w+, unpacked, addr_w\((\d+)\)\)", text)}
        self.enums: dict[str, int] = {lbl: int(v) for _e, lbl, v in   # enum label -> numeric value
                                      re.findall(r"enum_value\((\w+), (\w+), (-?\d+)\)", text)}
        # behavioral rules: a head `val(...)` with a body. (head_sig, head_val, head_time, body_lits)
        self.rules: list[tuple[str, str, str, list[str]]] = []
        self.seq_sigs: list[str] = []            # head sig-terms that appear with a `T+1` time (state)
        for ln in text.splitlines():
            ln = ln.strip()
            if not ln.startswith("val(") or " :- " not in ln:
                continue
            head, body = ln[:-1].split(" :- ", 1)      # drop trailing '.'
            args = _split_top(head[4:-1])              # inside val( ... )
            if len(args) != 3:
                continue
            sig, hv, ht = args
            self.rules.append((sig, hv, ht, _split_top(body)))
            if "+" in ht and sig not in self.seq_sigs:  # T+1 head -> sequential state signal
                self.seq_sigs.append(sig)

    def _is_comb(self, sig: str, ht: str) -> bool:
        """A rule is in COMBINATIONAL SMT scope iff head time is plain `T` and the signal is not a
        register (registers are state, driven by a `T+1` rule). Functor heads (hierarchy / enumerated
        lane / memory cell) ARE in scope -- lowered as flat SMT signals named by `_smt_sym`."""
        return ht == "T" and sig not in self.regs

    def comb_rules(self) -> list[tuple[str, str, str, list[str]]]:
        return [r for r in self.rules if self._is_comb(r[0], r[2])]

    def non_comb_heads(self) -> list[str]:
        """Heads outside combinational scope (T+1 / functor / register) -- flagged by the SMT renderer."""
        return [f"val({s}, {hv}, {ht})" for s, hv, ht, _b in self.rules if not self._is_comb(s, ht)]

    def comb_signals(self) -> list[str]:
        """Combinational head signals in first-appearance order (deterministic)."""
        seen: list[str] = []
        for sig, _hv, _ht, _b in self.comb_rules():
            if sig not in seen:
                seen.append(sig)
        return seen

    def all_signals(self) -> list[str]:
        """Every head signal-term (comb + seq + functor) in first-appearance order."""
        seen: list[str] = []
        for sig, *_ in self.rules:
            if sig not in seen:
                seen.append(sig)
        return seen


def _fo_formulas(lp: _Lp) -> list[str]:
    """The completion as explicit biconditional FORMULAS `p <-> q` (HLR 2017), one per design rule:
    `val(sig, hv, T) <-> exists <locals>: (body conjunction)` -- the locals (body vars not in the head)
    are existentially quantified. The human-readable mathematical object; the ASP choice+constraints and
    the SMT define-funs are operational encodings OF these. (A signal with several rules contributes
    several biconditionals, one per head value -- their disjunction is the predicate's completion.)"""
    out: list[str] = []
    for sig in lp.all_signals():
        for s, hv, ht, body in lp.rules:
            if s != sig:
                continue
            # head-side vars are NOT existential: the value var (if hv is a var) + the time var(s) of ht
            # (`T` for both `T` and `T+1`) + any var inside a functor head term like mem(A).
            headvars = set(re.findall(r"[A-Z]\w*", ht)) | set(re.findall(r"[A-Z]\w*", sig))
            if re.fullmatch(r"[A-Z]\w*", hv):
                headvars.add(hv)
            locs = sorted({v for v in re.findall(r"[A-Z]\w*", " ".join(body)) if v not in headvars})
            q = " & ".join(body)
            ex = f"exists {','.join(locs)}: " if locs else ""
            out.append(f"val({sig}, {hv}, {ht})  <->  {ex}{q}")
    return out


# --------------------------------------------------------------------------
# Renderer A: explicit ASP completion (witness der/3 + decoupled choice + both directions)
# --------------------------------------------------------------------------
def completion_asp(lp_text: str) -> str:
    lp = _Lp(lp_text)
    # rename every design HEAD/FACT `val(...)` -> `der(...)` (the if-disjunction witness). Facts (init /
    # default-memory T=0 atoms) must move too, else the only-if constraint would forbid them.
    body: list[str] = []
    for ln in lp_text.splitlines():
        i = ln.find("val(")
        body.append(ln[:i] + "der(" + ln[i + 4:] if i != -1 and ln.lstrip().startswith("val(") else ln)
    comp = ["", COMPLETION_MARK + "): val(Sig,V,T) <-> der(Sig,V,T); inputs open ----",
            "% the explicit biconditional -- der/3 is the if-disjunction, the choice DECOUPLES val so",
            "% the <-> has classical force; inputs are not derived (left open for a scenario/guess).",
            "% NB: sound only for a TIGHT design (no same-time-index cycle) -- the tightness gate (T2).",
            "%", "% Completion formulas (p <-> q), locals existentially quantified:",
            *(f"%   {f}" for f in _fo_formulas(lp)), "%"]
    # The open boundary is identified by FOUNDEDNESS, not by recognising signal shapes: a `val(Sig,V,T)`
    # is OPEN (free -- an input, or a register/memory cell at its uninitialised T=0) exactly when no rule
    # DERIVES Sig at that time. So `def_at(Sig,T)` marks where Sig is defined, and the only-if direction
    # forbids val<->der disagreement ONLY there. Everything else -- scalar/lane/memory/hierarchy/struct
    # inputs of ANY functor shape, 1-D or N-D, and uninitialised state -- is open with no special case.
    comp += ["{ val(Sig, V, T) } :- der(Sig, V, T).                          % decoupled guess",
             ":- der(Sig, V, T), not val(Sig, V, T).                         % if      : derived => val",
             "def_at(Sig, T) :- der(Sig, V, T).                              % Sig is defined at time T",
             ":- val(Sig, V, T), not der(Sig, V, T), def_at(Sig, T).         % only-if : defined => val=der",
             "% open (free) <=> not def_at: inputs (any shape) and uninitialised T=0 state. No input_sig /",
             "% seq_init / index-domain recovery -- foundedness alone separates the EDB (open) from the IDB."]
    return "\n".join(body).rstrip("\n") + "\n" + "\n".join(comp) + "\n"


# --------------------------------------------------------------------------
# Renderer B: classical SMT-LIB QF_BV (each combinational signal = a bit-vector function of inputs)
# --------------------------------------------------------------------------
def _bvlit(v: int, w: int) -> str:
    return f"(_ bv{v} {w})"


def _smt_sym(term: str, t: int | str | None = None) -> str:
    """A signal term -> an SMT-LIB symbol. A scalar `\\w+` stays bare (and `sig_t` when time-indexed) --
    byte-identical to the original scalar output. A FUNCTOR term (`u_lzd(gcase_0)`, `mem(0)`, `q(1)`)
    becomes a QUOTED symbol `|term|` (and `|term@t|` time-indexed); SMT-LIB allows parens/commas inside
    `|...|` and z3 accepts them."""
    if re.fullmatch(r"\w+", term):
        return term if t is None else f"{term}_{t}"
    return f"|{term}|" if t is None else f"|{term}@{t}|"


class _SmtErr(Exception):
    """An op/shape the SMT renderer can't handle yet -> a loud `; UNSUPPORTED` line, never silent."""


def _smt_resolve(tok: str, subst: dict[str, str], w: int, enums: dict[str, int] | None = None) -> str:
    """Resolve a body token (a bound var, an integer constant, or an enum label) to an SMT-LIB term."""
    if tok in subst:
        return subst[tok]
    if enums and tok in enums:
        return _bvlit(enums[tok] % (1 << w), w)
    if re.fullmatch(r"-?\d+", tok):
        return _bvlit(int(tok) % (1 << w), w)
    if m := re.fullmatch(r'"(-?\d+)"', tok):     # wide value stored as a canonical-decimal clingo String
        return _bvlit(int(m.group(1)) % (1 << w), w)
    raise _SmtErr(f"unresolved term {tok!r}")


_DIVMOD = {"idiv": "bvudiv", "imod": "bvurem", "sidiv": "bvsdiv", "simod": "bvsrem"}


def _smt_func(name: str, args: list[str], w: int) -> str:
    """One value `@func(args)` -> an SMT-LIB QF_BV term. args already resolved; `w` is the op width.
    (Index/width ops -- slc/sext/parity -- and the comparison-shaping ops -- wcmp/signed -- are handled
    in `_smt_rule`, which has the raw integer indices and the relation context they need.)"""
    if name in _BIN_SMT:
        return f"({_BIN_SMT[name]} {args[0]} {args[1]})"
    if name in _UN_SMT:
        return f"({_UN_SMT[name]} {args[0]})"
    if name in _DIVMOD:   # SV divide/modulo by zero -> 0; SMT bv*div/rem are u.b. at 0 -> guard with ite
        op = _DIVMOD[name]
        return f"(ite (= {args[1]} {_bvlit(0, w)}) {_bvlit(0, w)} ({op} {args[0]} {args[1]}))"
    raise _SmtErr(f"@{name} has no QF_BV lowering")


def _cells(base: str, smt_of: dict[str, str]) -> list[tuple[int, str]]:
    """The enumerated ground cells/lanes of `base` -- (index, smt_term) sorted by index."""
    out = []
    for k, term in smt_of.items():
        if m := re.fullmatch(rf"{re.escape(base)}\((\d+)\)", k):
            out.append((int(m.group(1)), term))
    return sorted(out)


def _cell0(sig: str, smt_of: dict[str, str]) -> str:
    cs = _cells(sig[:sig.index("(")], smt_of)
    return f"{sig[:sig.index('(')]}({cs[0][0]})" if cs else sig


def _mem_writes(m: str, rules: list) -> tuple[list, bool]:
    """Recognize memory `m`'s write ports from its `T+1` rules, for the Array-theory lowering. Returns
    (ports, ok): each port = (addr_sig, data_sig, [(guard_sig, guard_val)…]) -- the write `m[addr]<=data`
    enabled when every guard holds. The `mem_hold` hold rule is ignored (store keeps other cells). `ok` is
    False if any `T+1` rule is not the regular write/hold shape -> the caller falls back to per-cell."""
    ports = []
    for s, hv, ht, body in rules:
        if s.split("(", 1)[0] != m or "+" not in ht:
            continue
        if _has_aux(body):                               # the mem_hold-guarded hold rule -> ignored
            continue
        ha = _split_top(s[s.index("(") + 1:-1])
        if len(ha) != 1 or not re.fullmatch(r"[A-Z]\w*", ha[0]) or not re.fullmatch(r"[A-Z]\w*", hv):
            return [], False                             # not a var-indexed, var-data write
        addr_sig = data_sig = None
        guards: list[tuple[str, int, bool]] = []         # (sig, value, is_next-step) -- T+1 guard vs T
        for lit in body:
            if lit.startswith("time(") or re.fullmatch(r"\S+ < k", lit):
                continue
            if mm := re.fullmatch(r"val\((\w+), (\w+), (T(?:\+1)?)\)", lit):
                sig, v, tm = mm.group(1), mm.group(2), mm.group(3)
                if v == ha[0] and tm == "T":
                    addr_sig = sig
                elif v == hv and tm == "T":
                    data_sig = sig
                elif _const_int(v) is not None:
                    guards.append((sig, _const_int(v), tm == "T+1"))
                else:
                    return [], False
            else:
                return [], False                         # @func / relation -> not the simple write shape
        if addr_sig is None or data_sig is None:
            return [], False
        ports.append((addr_sig, data_sig, guards))
    return ports, True


def _array_sort(aw: int, dw: int) -> str:
    return f"(Array (_ BitVec {aw}) (_ BitVec {dw}))"


def _emit_array_mem(out: list[str], base: str, info: dict, cur: dict[str, str],
                    prev: dict[str, str], lp: _Lp, t: int | None) -> None:
    """Emit the Array-theory term for memory `base` at step `t` (or once, `t=None`, for a combinational
    ROM): init = const-zero array (or free for a ROM / uninitialised RAM); transition = nested
    `(ite <enable> (store mem_{t-1} addr_{t-1} data_{t-1}) mem_{t-1})` over the recognized write ports.
    Registers `mem_t` in `cur[base]` so reads lower to `(select mem_t idx)`."""
    aw, dw, sort = info["aw"], info["dw"], _array_sort(info["aw"], info["dw"])
    nm = _smt_sym(base, t)
    if info["rom"] or t in (None, 0) and not info["init"]:
        out.append(f"(declare-fun {nm} () {sort})")              # ROM / uninitialised: free array
    elif t == 0:                                                 # default-init memory: const-zero array
        out.append(f"(define-fun {nm} () {sort} ((as const {sort}) {_bvlit(0, dw)}))")
    else:                                                        # transition: store under each write port
        term = prev[base]
        for addr_sig, data_sig, guards in info["ports"]:
            a = _fit(prev[addr_sig], lp.widths.get(addr_sig, aw), aw)
            d = _fit(prev[data_sig], lp.widths.get(data_sig, dw), dw)
            conds = [f"(= {(cur if nxt else prev)[g]} {_bvlit(v, lp.widths.get(g, 1))})"
                     for g, v, nxt in guards]
            en = conds[0] if len(conds) == 1 else "(and " + " ".join(conds) + ")" if conds else None
            store = f"(store {term} {a} {d})"
            term = f"(ite {en} {store} {term})" if en else store
        out.append(f"(define-fun {nm} () {sort} {term})")
    cur[base] = nm


def _array_mems(lp: _Lp, rules: list) -> dict:
    """Memories lowered via SMT Array theory: each `array(...)` memory with a recognized sequential write
    port (a RAM) or a never-written dynamically-read ROM. Returns {base: {aw, dw, ports, init, rom}}.
    A memory that doesn't qualify (2-D, unrecognized write, combinational per-cell) is absent -> per-cell."""
    heads = {s[:s.index("(")] for s, *_ in rules if "(" in s}
    info: dict = {}
    for m, aw in lp.addr_w.items():
        dw = lp.elem_w.get(m, 1)
        if any(s.split("(", 1)[0] == m and "+" in ht for s, _h, ht, _b in rules):    # sequential RAM
            ports, ok = _mem_writes(m, rules)
            if ok and ports:
                info[m] = {"aw": aw, "dw": dw, "ports": ports, "rom": False,
                           "init": any(s.split("(", 1)[0] == m and ht == "0" for s, _h, ht, _b in rules)}
        elif m not in heads and any(f"{m}(" in lit for _s, _h, _t, b in rules for lit in b):   # ROM
            info[m] = {"aw": aw, "dw": dw, "ports": [], "init": False, "rom": True}
    return info


def _dyn_read(sig: str, subst: dict[str, str], subst_w: dict[str, int],
              smt_of: dict[str, str], widths: dict[str, int]) -> str:
    """A dynamic-index read `mem(V0)` (V0 a runtime value, not an enumerated constant) -> an ite-chain
    SELECT over the enumerated cells: `(ite (= v0 0) |mem(0)| (ite (= v0 1) |mem(1)| …))`."""
    base = sig[:sig.index("(")]
    idx = _split_top(sig[sig.index("(") + 1:-1])
    if len(idx) != 1 or idx[0] not in subst:
        raise _SmtErr(f"dynamic read {sig!r}: multi-index or unbound index")
    cells = _cells(base, smt_of)
    if not cells:
        raise _SmtErr(f"dynamic read {sig!r}: no enumerated cells")
    iw = subst_w.get(idx[0], max(1, (cells[-1][0]).bit_length()))
    term = cells[-1][1]                                  # default = last cell (in-range addresses hit a case)
    for c, ct in reversed(cells[:-1]):
        term = f"(ite (= {subst[idx[0]]} {_bvlit(c, iw)}) {ct} {term})"
    return term


def _smt_rule(hv: str, body: list[str], smt_of: dict[str, str], w: int,
              enums: dict[str, int], widths: dict[str, int],
              cur: dict[str, str] | None = None, arrays: dict[str, int] | None = None,
              ) -> tuple[str | None, str]:
    """(condition, value) for one rule, as SMT-LIB. condition=None if unconditional. `smt_of` maps a
    READ signal to its SMT term (the PREVIOUS step in a transition); `cur` (if given) maps `T+1` reads --
    e.g. a synchronous-reset gate `val(rst_n,1,T+1)` -- to the CURRENT step. `arrays` maps an Array-theory
    memory base to its addr width (a read `mem(idx)` -> `(select <array> idx)`). `w` is the head width."""
    arrays = arrays or {}
    cur = cur if cur is not None else smt_of
    subst: dict[str, str] = {}
    subst_w: dict[str, int] = {}                         # width of each bound read var (for a dynamic index)
    # @wcmp / @signed bound to a temp var keep their COMPARISON shape (3-way sign / signed interp) so the
    # relation that reads them lowers to a signed/unsigned bit-vector compare -- not a value substitution.
    wcmp: dict[str, tuple[str, str, int, bool]] = {}     # dst -> (a, b, width, signed?)
    signed: dict[str, tuple[str, int]] = {}              # dst -> (term, width)
    conds: list[str] = []
    for lit in body:
        if lit.startswith("time(") or re.fullmatch(r"\S+ < k", lit):
            continue                                      # time-domain guard -- the unroll handles time
        if lit.startswith("val("):                       # a read of signal `sig`
            sig, var, _t = _split_top(lit[4:-1])
            mp = cur if _t.replace(" ", "").endswith("+1") else smt_of   # T+1 read -> current step
            base = sig[:sig.index("(")] if "(" in sig else sig
            if base in arrays and "(" in sig:                     # Array-theory read: (select mem idx)
                aw, dw = arrays[base]
                idx = _split_top(sig[sig.index("(") + 1:-1])[0]
                it = _fit(_smt_resolve(idx, subst, aw, enums), subst_w.get(idx, aw), aw)
                subst[var] = f"(select {mp[base]} {it})"
                subst_w[var] = dw
            elif sig in mp:
                if var in enums or _const_int(var) is not None:   # val(s, idle, T): CONDITION sig == const
                    conds.append(f"(= {mp[sig]} {_smt_resolve(var, {}, widths.get(sig, 1), enums)})")
                else:                                             # val(s, V, T): bind read var V to sig
                    subst[var] = mp[sig]
                    subst_w[var] = widths.get(sig, 1)
            elif "(" in sig and any(v in subst for v in re.findall(r"[A-Z]\w*", sig[sig.index("("):])):
                subst[var] = _dyn_read(sig, subst, subst_w, mp, widths)   # mem(V0): ite-chain over cells
                subst_w[var] = widths.get(_cell0(sig, mp), 1)
            else:
                raise _SmtErr(f"read of {sig!r} (not an input/derived signal)")
        elif m := re.fullmatch(r"(\w+) = @(\w+)\((.*)\)", lit):    # Vj = @func(args) -> value binding
            dst, fn, ra = m.group(1), m.group(2), _split_top(m.group(3))
            if fn == "wcmp":
                wcmp[dst] = (_smt_resolve(ra[0], subst, int(ra[2]), enums),
                             _smt_resolve(ra[1], subst, int(ra[2]), enums), int(ra[2]), bool(int(ra[3])))
            elif fn == "signed":
                signed[dst] = (_smt_resolve(ra[0], subst, int(ra[1]), enums), int(ra[1]))
            else:
                subst[dst] = _smt_value(fn, ra, subst, enums, subst_w)
                # result width: slc/sext carry it as ra[2]; parity's RESULT is 1 bit (its
                # width arg is the xor fan-out, Fix 43); everything else = the op width.
                subst_w[dst] = (int(ra[2]) if fn in ("slc", "sext")
                                else 1 if fn == "parity" else int(ra[-1]))
        elif m := re.fullmatch(r"(.+?) (=|!=|<|<=|>|>=) (.+)", lit):  # a native relation -> condition
            conds.append(_smt_cond(m.group(1).strip(), m.group(2), m.group(3).strip(),
                                   subst, subst_w, w, enums, wcmp, signed))
        else:
            raise _SmtErr(f"body literal {lit!r}")
    cond = None if not conds else (conds[0] if len(conds) == 1 else "(and " + " ".join(conds) + ")")
    return cond, _smt_resolve(hv, subst, w, enums)


def _fit(term: str, have: int, want: int) -> str:
    """Coerce an SMT-LIB bit-vector `term` from `have` bits to `want` bits (zero-extend / extract / id) --
    so an operand narrower or wider than the op width matches (e.g. a 6-bit shift amount vs a 64-bit op)."""
    if have == want:
        return term
    if have < want:
        return f"((_ zero_extend {want - have}) {term})"
    return f"((_ extract {want - 1} 0) {term})"


def _smt_value(fn: str, ra: list[str], subst: dict[str, str], enums: dict[str, int],
               subst_w: dict[str, int] | None = None) -> str:
    """A value-producing `@func(args)` -> SMT-LIB term. slc/sext/parity carry integer indices/widths
    (handled here from the RAW args); the rest resolve their operands (fitted to the op width) and go
    through `_smt_func`."""
    sw_map = subst_w or {}
    if fn == "slc":                                      # v[lo +: w] -> static extract (const index only)
        lo, sw = _const_int(ra[1]), int(ra[2])
        if lo is None:
            raise _SmtErr(f"@slc dynamic index {ra[1]!r} (no static bit-vector extract)")
        return f"((_ extract {lo + sw - 1} {lo}) {_smt_resolve(ra[0], subst, lo + sw, enums)})"
    if fn == "sext":                                     # sign-extend fw -> tw bits
        fw, tw = int(ra[1]), int(ra[2])
        return f"((_ sign_extend {tw - fw}) {_smt_resolve(ra[0], subst, fw, enums)})"
    if fn == "parity":                                   # reduction xor of the low `w` bits -> 1 bit
        pw = int(ra[1])
        vt = _smt_resolve(ra[0], subst, pw, enums)
        bits = [f"((_ extract {i} {i}) {vt})" for i in range(pw)]
        return bits[0] if pw == 1 else "(bvxor " + " ".join(bits) + ")"
    if fn == "popcnt":                                   # $countones: sum of the low `w` bits, at width w
        pw = int(ra[1])
        vt = _smt_resolve(ra[0], subst, pw, enums)
        bits = [f"((_ zero_extend {pw - 1}) ((_ extract {i} {i}) {vt}))" for i in range(pw)]
        return bits[0] if pw == 1 else "(bvadd " + " ".join(bits) + ")"
    if fn == "ipow":                                     # a ** n : CONSTANT exponent -> n-fold bvmul
        ow = int(ra[2])
        n = _const_int(ra[1])
        if n is None:
            raise _SmtErr("@pow with a non-constant exponent (no QF_BV term)")
        at = _fit(_smt_resolve(ra[0], subst, ow, enums), sw_map.get(ra[0], ow), ow)
        term = _bvlit(1, ow)                             # a ** 0 = 1
        for _ in range(n):
            term = f"(bvmul {term} {at})"
        return term
    ow = int(ra[-1])                                     # last @func arg is the op width
    args = [_fit(_smt_resolve(a, subst, ow, enums), sw_map.get(a, ow), ow) for a in ra[:-1]]
    return _smt_func(fn, args, ow)


def _smt_cond(lhs: str, op: str, rhs: str, subst: dict[str, str], subst_w: dict[str, int], w: int,
              enums: dict[str, int], wcmp: dict[str, tuple[str, str, int, bool]],
              signed: dict[str, tuple[str, int]]) -> str:
    """A native relation `lhs <op> rhs` -> an SMT-LIB boolean. Operands may be inline @wcmp / @signed
    (so the compare is signed/3-way), a plain term, or an integer/enum constant. An integer constant takes
    the WIDTH of the bit-vector operand it is compared against (not the head width) -- `divisor != 0` is a
    32-bit compare even when the result signal is 1-bit."""
    lo = _operand(lhs, subst, subst_w, w, enums, wcmp, signed)
    ro = _operand(rhs, subst, subst_w, w, enums, wcmp, signed)
    if lo[0] == "wcmp" or ro[0] == "wcmp":               # 3-way sign of (a-b) compared to a constant
        flip = {"<": ">", ">": "<", "<=": ">=", ">=": "<=", "=": "=", "!=": "!="}
        (a, b, _cw, s), k, cop = (lo[1], ro, op) if lo[0] == "wcmp" else (ro[1], lo, flip[op])
        if k[0] != "int":
            raise _SmtErr("@wcmp compared to a non-constant")
        lt, gt = ("bvslt", "bvsgt") if s else ("bvult", "bvugt")
        rel = {-1: f"({lt} {a} {b})", 0: f"(= {a} {b})", 1: f"({gt} {a} {b})"}
        parts = [rel[v] for v in (-1, 0, 1) if _cmp_int(v, cop, k[1])]
        return "false" if not parts else (parts[0] if len(parts) == 1 else "(or " + " ".join(parts) + ")")
    cw = next((o[2] for o in (lo, ro) if o[0] != "int" and o[2]), w)   # compare width = the bv operand's
    if lo[0] == "signed" or ro[0] == "signed":           # signed bit-vector comparison
        a = lo[1][0] if lo[0] == "signed" else _smt_lit(lo, cw)
        b = ro[1][0] if ro[0] == "signed" else _smt_lit(ro, cw)
        return f"({_SCMP_SMT[op]} {a} {b})"
    return f"({_CMP_SMT[op]} {_smt_lit(lo, cw)} {_smt_lit(ro, cw)})"


def _operand(tok: str, subst: dict[str, str], subst_w: dict[str, int], w: int, enums: dict[str, int],
             wcmp: dict[str, tuple[str, str, int, bool]], signed: dict[str, tuple[str, int]]) -> tuple:
    """Tag a relation operand: ('wcmp',(a,b,w,s),cw) | ('signed',(term,w),sw) | ('int',k,None) |
    ('bv',term,width). The width lets an int constant match the bit-vector operand's width."""
    if tok in wcmp:
        return ("wcmp", wcmp[tok], wcmp[tok][2])
    if tok in signed:
        return ("signed", signed[tok], signed[tok][1])
    if tok.startswith("@wcmp("):
        a, b, cw, s = _split_top(tok[6:-1])
        return ("wcmp", (_smt_resolve(a, subst, int(cw), enums),
                         _smt_resolve(b, subst, int(cw), enums), int(cw), bool(int(s))), int(cw))
    if tok.startswith("@signed("):
        v, sw = _split_top(tok[8:-1])
        return ("signed", (_smt_resolve(v, subst, int(sw), enums), int(sw)), int(sw))
    if tok.startswith("@"):
        m = re.fullmatch(r"@(\w+)\((.*)\)", tok)
        ra = _split_top(m.group(2))
        # result width: parity's is 1 bit regardless of its (fan-out) width arg — Fix 43;
        # comparing it against the operand width made the int literal the wrong sort.
        ow = (int(ra[2]) if m.group(1) in ("slc", "sext")
              else 1 if m.group(1) == "parity" else int(ra[-1]))
        return ("bv", _smt_value(m.group(1), ra, subst, enums, subst_w), ow)
    if (k := _const_int(tok)) is not None:
        return ("int", k, None)
    return ("bv", _smt_resolve(tok, subst, w, enums), subst_w.get(tok, w))


def _smt_lit(o: tuple, w: int) -> str:
    """An operand tagged ('bv',term) or ('int',k) as a width-`w` SMT-LIB term."""
    return _bvlit(o[1] % (1 << w), w) if o[0] == "int" else o[1]


def completion_smt(lp_text: str, k: int = 4) -> str:
    """Classical Clark/HLR completion as SMT-LIB QF_BV. A purely combinational design is each signal a
    bit-vector FUNCTION of the free inputs. A sequential design is UNROLLED over time steps 0..k: every
    signal becomes `<sig>_<t>`, registers carry state (reg_{t+1} = next(state_t, in_t)), inputs are fresh
    per step -- a bounded all-inputs/all-traces proof obligation a classical solver discharges."""
    lp = _Lp(lp_text)
    if lp.seq_sigs:
        return _completion_smt_seq(lp, k)
    return _completion_smt_comb(lp)


def _var_domain(lp: _Lp, var: str, headbase: str, body: list[str]) -> range | None:
    """The index range for a head index `var`: a memory cell base in `addr_dom`; else a `lane(owner,var)`
    / `addr(mem,…var…)` domain guard in the body."""
    if headbase in lp.addr_dom:
        return lp.addr_dom[headbase]
    for lit in body:
        if (m := re.fullmatch(rf"lane\((\w+), {re.escape(var)}\)", lit)) and m.group(1) in lp.lane_dom:
            return lp.lane_dom[m.group(1)]
        if (m := re.fullmatch(rf"addr\((\w+),[^)]*\b{re.escape(var)}\b[^)]*\)", lit)) \
                and m.group(1) in lp.addr_dom:
            return lp.addr_dom[m.group(1)]
        if m := re.fullmatch(rf"{re.escape(var)} = (\d+)\.\.(\d+)", lit):   # `I = 0..2` lane decomposition
            return range(int(m.group(1)), int(m.group(2)) + 1)
    return None


def _ground(lp: _Lp, skip: set | None = None) -> list:
    """The rule list with every functor head GROUND. A hierarchy head (`u_lzd(gcase_0)`) is already ground
    -> passes through. A variable-index head (lane `q(I)`, memory cell `mem(A)`) is ENUMERATED over its
    index domain (from `lane(..)`/`addr(..)`/`I=lo..hi` facts -- or inferred from a body functor read whose
    base's domain is known, e.g. a comb lane `y(I)` reading `q(I)`): one ground rule per index tuple, with
    the index vars substituted in head AND body (incl. nested `u_a(q(I))` and reads `val(en(I),..)`) and the
    consumed domain guards dropped. Per-cell widths are registered into `lp.widths`."""
    base_dom: dict[str, range] = {}                            # functor base -> its index domain (pass 1)
    for sig, _hv, _ht, body in lp.rules:
        if "(" in sig and re.search(r"[A-Z]", sig[sig.index("("):]):
            b = sig[:sig.index("(")]
            for v in re.findall(r"[A-Z]\w*", sig[sig.index("("):]):
                if (r := _var_domain(lp, v, b, body)) is not None:
                    base_dom.setdefault(b, r)

    def _dom(v: str, base: str, body: list[str]) -> range | None:
        if (r := _var_domain(lp, v, base, body)) is not None:
            return r
        for lit in body:                                       # infer from a body read with a known base
            if (m := re.fullmatch(r"val\((\w+)\([^)]*\), .+", lit)) and v in re.findall(r"[A-Z]\w*", lit) \
                    and m.group(1) in base_dom:
                return base_dom[m.group(1)]
        return base_dom.get(base)

    skip = skip or set()
    out: list = []
    for sig, hv, ht, body in lp.rules:
        if "(" not in sig or not re.search(r"[A-Z]", sig[sig.index("("):]) \
                or sig[:sig.index("(")] in skip:               # array-mode memory: not enumerated
            out.append((sig, hv, ht, body))                    # scalar / ground functor / array head
            continue
        base = sig[:sig.index("(")]
        ivars = list(dict.fromkeys(re.findall(r"[A-Z]\w*", sig[sig.index("("):])))
        doms = [(v, _dom(v, base, body)) for v in ivars]
        if any(r is None for _v, r in doms):
            out.append((sig, hv, ht, body))                    # can't resolve a domain -> leave as-is
            continue
        rest = [lit for lit in body if not re.fullmatch(r"(lane|addr)\([^)]*\)", lit)
                and not re.fullmatch(r"[A-Z]\w* = \d+\.\.\d+", lit)]   # drop consumed domain guards
        dsize = {v: len(r) for v, r in doms}
        for combo in product(*[list(r) for _v, r in doms]):
            sub = dict(zip([v for v, _ in doms], combo, strict=True))

            def _s(s: str, sub: dict = sub) -> str:
                for v, val in sub.items():
                    s = re.sub(rf"\b{v}\b", str(val), s)
                return s
            gbody = [_s(lit) for lit in rest]
            out.append((_s(sig), _s(hv), ht, gbody))
            for term in re.findall(r"\w+\([^)]*\)", " ".join(rest)):   # est. read-cell widths (lane//N)
                gt, b = _s(term), term[:term.index("(")]
                n = _prod(dsize[v] for v in re.findall(r"[A-Z]\w*", term) if v in dsize) or 1
                if gt not in lp.widths and b in lp.widths and lp.widths[b] % n == 0:
                    lp.widths.setdefault(gt, lp.elem_w[b] if b in lp.elem_w else lp.widths[b] // n)
    for sig, hv, _ht, body in out:       # functor signal width = its head-value producer (self-consistent
        if "(" in sig and sig not in lp.widths and (wd := _infer_width(sig, hv, body, lp)) is not None:
            lp.widths[sig] = wd          # with the define-fun body); elem_w / explicit type win
    return out


def _infer_width(sig: str, hv: str, body: list[str], lp: _Lp) -> int | None:
    """Width of a functor signal lacking an explicit `type(...)`: a memory cell -> `element_type`; else the
    width of its head VALUE -- the `@func` op width or the read it copies -- so the define-fun body and the
    declared sort agree (a lane op may be wider than `type(word)//N`)."""
    base = sig[:sig.index("(")]
    if base in lp.elem_w:
        return lp.elem_w[base]
    if re.fullmatch(r"[A-Z]\w*", hv):
        for lit in body:
            if m := re.fullmatch(rf"{re.escape(hv)} = @(\w+)\((.*)\)", lit):
                ra = _split_top(m.group(2))
                return int(ra[2]) if m.group(1) in ("slc", "sext") else int(ra[-1])
            if lit.startswith("val(") and _split_top(lit[4:-1])[1] == hv:
                return lp.widths.get(_split_top(lit[4:-1])[0])
    return None


def _prod(it) -> int:
    p = 1
    for x in it:
        p *= x
    return p


def _has_aux(body: list[str]) -> bool:
    """True if a body literal is a plain auxiliary-predicate call (e.g. `mem_hold(mem,A,T)`) -- not a
    `val(..)` read, `time(..)` guard, `X = @func(..)` binding, or a native relation. Such a literal marks
    a memory cell's HOLD rule, which the per-cell SMT lowering replaces with a synthesized hold default."""
    for lit in body:
        if (lit.startswith(("val(", "time(")) or " = @" in lit
                or re.fullmatch(r".+ (=|!=|<|<=|>|>=) .+", lit)):
            continue
        if re.fullmatch(r"\w+\(.*\)", lit):
            return True
    return False


def _ordered_heads(rules: list, pred) -> list[str]:
    """Head signal-terms satisfying `pred(sig, ht)`, in first-appearance order (deterministic)."""
    seen: list[str] = []
    for s, _hv, ht, _b in rules:
        if pred(s, ht) and s not in seen:
            seen.append(s)
    return seen


def _declare_functor_inputs(out: list[str], rules: list, smt_of: dict[str, str], lp: _Lp,
                            t: int | None = None, array_bases: set | None = None) -> None:
    """A GROUND functor term read but never produced, whose base predicate is an input port (a lane/cell
    input like `en(0)` after enumeration), is a free SMT constant -- declare it (the SMT route's EDB)."""
    array_bases = array_bases or set()
    produced = {s for s, *_ in rules}
    for _s, _hv, _ht, b in rules:
        for lit in b:
            if not lit.startswith("val("):
                continue
            term = _split_top(lit[4:-1])[0]
            if ("(" not in term or term in produced or term in smt_of or re.search(r"[A-Z]", term)
                    or term[:term.index("(")] not in lp.inputs):
                continue
            nm = _smt_sym(term, t)
            out.append(f"(declare-fun {nm} () (_ BitVec {lp.widths.get(term, 1)}))")
            smt_of[term] = nm
    prod_bases = {s[:s.index("(")] for s in produced if "(" in s}
    for m, dom in lp.addr_dom.items():               # ROM / external memory (read, never written) -> cells free
        if m in prod_bases or m in array_bases or not any(f"{m}(" in lit
                                                          for _s, _h, _t, b in rules for lit in b):
            continue                                 # array-mode ROM is declared as one Array, not cells
        for c in dom:
            term = f"{m}({c})"
            if term in smt_of:
                continue
            lp.widths[term] = lp.elem_w.get(m, lp.widths.get(m, 1))
            smt_of[term] = _smt_sym(term, t)
            out.append(f"(declare-fun {smt_of[term]} () (_ BitVec {lp.widths[term]}))")


def _read_ready(term: str, smt_of: dict[str, str]) -> bool:
    """Is a body read available? A ground term must be in `smt_of`; an Array-theory read `mem(idx)` once
    its array term `mem` is in `smt_of`; a DYNAMIC per-cell read `mem(V0)` once the base's cells exist."""
    if term in smt_of:
        return True
    if "(" in term:
        return term[:term.index("(")] in smt_of or bool(_cells(term[:term.index("(")], smt_of))
    return False


def _emit_comb_defs(out: list[str], rules: list, signals: list[str], smt_of: dict[str, str],
                    lp: _Lp, t: int | None = None, arrays: dict[str, int] | None = None) -> None:
    """Define each combinational signal TERM in `signals` (dependency order) as a define-fun named
    `_smt_sym(sig, t)`. `rules` is the (grounded) rule list; reads resolve through `smt_of` (keyed by the
    signal term, scalar or functor). A signal whose op can't lower / whose read never resolves is declared
    free with a loud `; UNSUPPORTED`."""
    pending = list(signals)
    progress = True
    while pending and progress:
        progress = False
        for sig in list(pending):
            srules = [(hv, b) for s, hv, _ht, b in rules if s == sig]
            reads = {_split_top(lit[4:-1])[0] for _hv, b in srules for lit in b if lit.startswith("val(")}
            if not all(_read_ready(r, smt_of) for r in reads):   # a read not yet available -> defer
                continue
            w = lp.widths.get(sig, 1)
            nm = _smt_sym(sig, t)
            try:
                term = _fold_rules(srules, smt_of, w, lp.enums, lp.widths, arrays=arrays)
            except _SmtErr as e:
                out.append(f"; UNSUPPORTED {nm}: {e}")
                out.append(f"(declare-fun {nm} () (_ BitVec {w}))")
            else:
                out.append(f"(define-fun {nm} () (_ BitVec {w}) {term})")
            smt_of[sig] = nm
            pending.remove(sig)
            progress = True
    for sig in pending:                                  # a cycle / unresolved read -> loud, declare free
        nm = _smt_sym(sig, t)
        out.append(f"; UNSUPPORTED {nm}: combinational cycle / reads a signal with no definition")
        smt_of[sig] = nm
        out.append(f"(declare-fun {nm} () (_ BitVec {lp.widths.get(sig, 1)}))")


def _completion_smt_comb(lp: _Lp) -> str:
    out = [SMT_MARK + " ====", "; each combinational signal is a bit-vector function of the free inputs.",
           "; Completion formulas (p <-> q), locals existentially quantified -- the define-funs below",
           "; are the operational form of these:",
           *(f";   {f}" for f in _fo_formulas(lp)), ";"]
    arr = _array_mems(lp, lp.rules)
    arrays = {m: (i["aw"], i["dw"]) for m, i in arr.items()}
    out.append(f"(set-logic {'QF_ABV' if arr else 'QF_BV'})")   # ABV = arrays + bit-vectors (memory)
    if lp.non_comb_heads():
        out.append(f"; UNSUPPORTED: {len(lp.non_comb_heads())} sequential head(s) (combinational-only)")
    rules = _ground(lp, skip=set(arr))
    smt_of = {i: i for i in sorted(lp.inputs)}            # scalar inputs are free SMT constants
    for i in sorted(lp.inputs):
        out.append(f"(declare-fun {i} () (_ BitVec {lp.widths.get(i, 1)}))")
    for m, info in arr.items():                            # ROMs (read-only memories) -> a free Array
        _emit_array_mem(out, m, info, smt_of, smt_of, lp, None)
    _declare_functor_inputs(out, rules, smt_of, lp, array_bases=set(arr))   # lane/cell inputs -> free
    signals = _ordered_heads(rules, lambda s, ht: lp._is_comb(s, ht))
    _emit_comb_defs(out, rules, signals, smt_of, lp, arrays=arrays)
    return "\n".join(out) + "\n"


def _fold_rules(srules: list[tuple[str, list[str]]], smt_of: dict[str, str], w: int,
                enums: dict[str, int], widths: dict[str, int], default: str | None = None,
                cur: dict[str, str] | None = None, arrays: dict[str, int] | None = None) -> str:
    """Fold a signal's value-rules into one SMT term: unconditional -> the value; conditional -> nested
    ite. With `default` given (e.g. a memory cell's HOLD = its previous value), every rule must be
    conditional and `default` is the final else; without it the LAST rule is the else. `cur` resolves
    `T+1` body reads (current step) vs `smt_of` for `T` reads (previous step)."""
    pairs = [_smt_rule(hv, b, smt_of, w, enums, widths, cur, arrays) for hv, b in srules]
    if default is not None:
        term = default
    elif len(pairs) == 1 and pairs[0][0] is None:
        return pairs[0][1]
    else:
        term, pairs = pairs[-1][1], pairs[:-1]          # else = the last rule's value
    for cond, value in reversed(pairs):
        if cond is None:
            raise _SmtErr("multiple unconditional rules for one signal")
        term = f"(ite {cond} {value} {term})"
    return term


def _completion_smt_seq(lp: _Lp, k: int) -> str:
    """Bounded-unroll completion over time 0..k. Each signal -> `_smt_sym(sig, t)` (scalar `sig_t`, functor
    `|sig@t|`). State (a `T+1` head -- scalar register OR functor cell/lane) carries: `s_t` = its init at
    t=0 (else free/open), and for t>=1 the transition `next(state_{t-1}, in_{t-1})`; an ASYNC-reset rule
    (head time `T`, e.g. `val(reg,0,T):-rst_n=0`) overrides as `ite(reset_t, rval, base)`. Combinational
    signals at t are functions of inputs_t / state_t / earlier comb_t; inputs fresh per step. Functor
    signals are grounded by `_ground` (hierarchy as-is, lane/cell enumerated) -- handled uniformly."""
    arr = _array_mems(lp, lp.rules)                                 # memories lowered via Array theory
    arrays = {m: (i["aw"], i["dw"]) for m, i in arr.items()}
    out = [SMT_MARK + f" (sequential, bounded unroll k={k}) ====",
           "; each signal unrolled over 0..k as <sig>_<t> (|sig@t| for functor terms); state carries",
           "; s_{t+1} = next(state_t, in_t), async reset overrides; inputs fresh per step.",
           "; Completion formulas (p <-> q) of the transition relation:",
           *(f";   {f}" for f in _fo_formulas(lp)), ";",
           f"(set-logic {'QF_ABV' if arr else 'QF_BV'})"]   # ABV = arrays + bit-vectors (memory)
    rules = _ground(lp, skip=set(arr))
    inputs = sorted(lp.inputs)
    regs = [r for r in _ordered_heads(rules, lambda _s, ht: "+" in ht)   # scalar reg + functor cell/lane
            if r.split("(", 1)[0] not in arr]                      # (array memories handled separately)
    state = set(regs)
    comb = [s for s in _ordered_heads(rules, lambda s, ht: lp._is_comb(s, ht)) if s not in state]
    for t in range(k + 1):                                          # fresh scalar input per step
        for i in inputs:
            out.append(f"(declare-fun {_smt_sym(i, t)} () (_ BitVec {lp.widths.get(i, 1)}))")
    prev: dict[str, str] = {}
    for t in range(k + 1):
        smt_of = {i: _smt_sym(i, t) for i in inputs}
        for m, info in arr.items():                                # Array-theory memory at step t
            _emit_array_mem(out, m, info, smt_of, prev, lp, t)
        for r in regs:                                             # state value at step t
            w = lp.widths.get(r, 1)
            nm = _smt_sym(r, t)
            reset = [(hv, b) for s, hv, ht, b in rules if s == r and ht == "T"]   # async reset override
            if t == 0:
                inits = [(hv, b) for s, hv, ht, b in rules if s == r and ht == "0"]
                if inits:
                    base = _fold_rules(inits, smt_of, w, lp.enums, lp.widths)
                elif reset:                                        # open initial state, then reset overrides
                    base = _smt_sym(r, "init")
                    out.append(f"(declare-fun {base} () (_ BitVec {w}))")
                else:
                    out.append(f"(declare-fun {nm} () (_ BitVec {w}))")   # no init / no reset -> free
                    smt_of[r] = nm
                    continue
            else:                                                  # transition from t-1
                allt = [(hv, b) for s, hv, ht, b in rules if s == r and "+" in ht]
                trules = [(hv, b) for hv, b in allt if not _has_aux(b)]   # drop mem_hold-guarded hold rule
                cur = {i: _smt_sym(i, t) for i in inputs}          # T+1 body reads (sync-reset gate) -> step t
                if len(trules) < len(allt):                        # a memory cell: holds when no write fires
                    base = _fold_rules(trules, prev, w, lp.enums, lp.widths,
                                       default=_smt_sym(r, t - 1), cur=cur, arrays=arrays)
                elif trules:
                    base = _fold_rules(trules, prev, w, lp.enums, lp.widths, cur=cur, arrays=arrays)
                else:
                    base = _smt_sym(r, t - 1)
            term = _async_reset(reset, base, smt_of, w, lp, arrays)
            out.append(f"(define-fun {nm} () (_ BitVec {w}) {term})")
            smt_of[r] = nm
        _declare_functor_inputs(out, rules, smt_of, lp, t, array_bases=set(arr))   # lane/cell inputs -> free
        _emit_comb_defs(out, rules, comb, smt_of, lp, t, arrays=arrays)   # combinational signals at step t
        prev = smt_of
    return "\n".join(out) + "\n"


def _async_reset(reset_rules: list, base: str, smt_of: dict[str, str], w: int, lp: _Lp,
                 arrays: dict[str, int] | None = None) -> str:
    """`ite(reset_t, reset_val, base)` for each async-reset rule (head time `T`), in priority order;
    `base` (the transition / init / free value) is the else. No reset rules -> just `base`."""
    term = base
    for hv, body in reversed(reset_rules):
        try:
            cond, value = _smt_rule(hv, body, smt_of, w, lp.enums, lp.widths, arrays=arrays)
        except _SmtErr:
            continue
        term = f"(ite {cond} {value} {term})" if cond else value
    return term
