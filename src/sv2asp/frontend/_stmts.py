from __future__ import annotations



from ..ir.expr import BinOp, BitSel, Cond, Const, Expr, LaneIdx, Ref, Slice, Tag, UnOp
from ..ir.nodes import Branch, CombItem, LatchItem, Loc, MemWrite, Reset, SeqItem, Signal
from ._common import _BINOP, _enum_name


def _coverage(labels: list, universe: list | int) -> tuple[list, set, int]:
    """``(missing, seen, domain)`` for a `case`'s arms over its selector DOMAIN.

    `universe` is the enum's MEMBER LIST, or the domain SIZE for an integral selector. This is
    the whole "do the arms cover the selector" decision with the pyslang type lookup peeled
    away — pure, and therefore checkable: `Sel.covers` mirrors it, and `proofs/gen_sel_lean.py`
    records this function on every case the translator really lowers.

    Getting the DOMAIN wrong is silent-wrong in the dangerous direction: a partial case that
    looks total suppresses the D4 warning, the output stays unbound on the uncovered values,
    and a property over it passes VACUOUSLY there."""
    seen = set(labels)
    if isinstance(universe, int):
        return [x for x in range(universe) if x not in seen], seen, universe
    return [m for m in universe if m not in seen], seen, len(universe)


def _da_eval(shape: tuple, case_total: bool = False) -> set[str]:
    """Definite assignment over the pure shape `_da_shape` builds: the signals assigned on EVERY
    path. This is the algorithm; nothing pyslang reaches it.

    Conservative in the safe direction at each join — a branch whose coverage cannot be
    established contributes nothing, so it under-claims assignment and can only over-report
    latches, never miss one. `case_total` pretends every `case` is total (as if each had a
    `default`), which is what keeps this check from silently overruling the D4 decision.

    Mirrored in Lean as `Paths.da`, checked against THIS function on every always-block the
    translator really lowers (`proofs/gen_paths_lean.py` -> `PathsTable.lean`)."""
    kind = shape[0]
    if kind == "cond":
        _, thn, els = shape
        if els is None:                                   # untaken path drives nothing
            return set()
        return _da_eval(thn, case_total) & _da_eval(els, case_total)
    if kind == "case":
        _, arms, dflt, covered = shape
        arms = list(arms)
        if dflt is not None:
            arms.append(dflt)
        elif not case_total and not covered:
            return set()
        if not arms:
            return set()
        out = _da_eval(arms[0], case_total)
        for a in arms[1:]:
            out &= _da_eval(a, case_total)
        return out
    if kind == "seq":
        parts = shape[1]
        return set().union(*(_da_eval(s, case_total) for s in parts)) if parts else set()
    if kind == "loop":
        return _da_eval(shape[1], case_total)
    return set(shape[1])                                  # leaf


#: A runtime-indexed write to a packed vector decodes into one guarded write per BIT, so the width
#: bounds the emitted program. Above this, refuse loudly rather than emit hundreds of guarded slices.
_MAX_DECODED_BITS = 64


def _has_lane_index(e) -> bool:
    """True if ``e`` mentions a lane index anywhere. Such an expression is only meaningful INSIDE the
    lane rule that binds the index, so it must never be hoisted out of one."""
    if isinstance(e, LaneIdx):
        return True
    if isinstance(e, (list, tuple)):
        return any(_has_lane_index(x) for x in e)
    return any(_has_lane_index(getattr(e, f)) for f in getattr(e, "__dataclass_fields__", ()))


def _has_implicit_lane_ref(e, lane_dims: dict) -> bool:
    """True if ``e`` mentions a signal that is read as a LANE inside a generate.

    A genvar-indexed read `x[i]` lowers to the bare `Ref("x")` on purpose: the emitter adds
    `(I)` because it is emitting inside a lane rule (`_word_body`, `lane_ctx`). The lane-ness is
    therefore CONTEXTUAL -- the same node is the word `x` anywhere else -- and `_has_lane_index`,
    which looks for explicit LaneIdx nodes, cannot see it. Anything that moves an expression out
    of its lane rule has to ask this question as well as the explicit one (F30).
    """
    if isinstance(e, Ref):
        return e.name in lane_dims
    if isinstance(e, (list, tuple)):
        return any(_has_implicit_lane_ref(x, lane_dims) for x in e)
    return any(_has_implicit_lane_ref(getattr(e, f), lane_dims)
               for f in getattr(e, "__dataclass_fields__", ()))


class _StmtMixin:
    """_StmtMixin: stmts methods of PyslangFrontend (split out from the monolith)."""

    def _register_block_locals(self, stmt, signals: dict, loc) -> None:
        """Register a procedural block's local variable declarations (`logic [W-1:0] t;`) as signals
        with their DECLARED width, so a multi-bit BLOCKING intermediate (`t = a & b; y = t | c;`) is a
        WORD and not a phantom 1-bit (defined as val(t,0,..) but read as val(t,V,..) -> no match, no y).
        Branch-path only -- the symbolic executor inlines its own locals (binds them in env). LOOP
        COUNTERS (a for's loopVars) are excluded -- they are not hardware signals."""
        skip: set[str] = set()
        decls: list = []

        def walk(s) -> None:
            if s is None or not hasattr(s, "kind"):
                return
            for lv in getattr(s, "loopVars", []) or []:        # a for-loop owns its counter(s)
                n = getattr(lv, "name", None)
                if n:
                    skip.add(n)
            if _enum_name(s.kind) == "VariableDeclaration":
                sym = getattr(s, "symbol", None)
                if sym is not None and getattr(sym, "name", None):
                    decls.append(sym)
            for attr in ("body", "list", "stmt", "ifTrue", "ifFalse", "defaultCase"):
                c = getattr(s, attr, None)
                if isinstance(c, (list, tuple)):
                    for x in c:
                        walk(x)
                else:
                    walk(c)
            for it in getattr(s, "items", []) or []:
                walk(getattr(it, "stmt", None))

        walk(stmt)
        for sym in decls:                                       # register after all loopVars are known
            if sym.name not in signals and sym.name not in skip:
                signals[sym.name] = Signal(name=sym.name, irtype=self._irtype(sym.type), is_reg=False,
                                           is_port=False, direction=None, initial=None, loc=loc)

    def _latch_enable(self, reg: str, branches: list, loc) -> str | None:
        """The 1-bit "the block DROVE `reg` this instant" signal, for an inferred latch.

        It is the disjunction over the driving branches of their guard conjunction. Built from
        the guards only -- never from `reg` -- so the retention rule `val(reg, V, T+1) :-
        val(en, 0, T+1), val(reg, V, T)` reads the prior instant and closes no combinational
        cycle. Returns None for a branch shape whose guard cannot be read (tag guards, negated
        matches), so those keep the loud refusal rather than getting a guessed enable."""
        def match(sig: str, v: object, eq: bool) -> Expr:
            """`sel == v` / `sel != v` -- a case arm's guard. The value is an enum LABEL or a
            number, which is the same split the `val` atom itself makes."""
            try:
                rhs: Expr = Const(int(str(v).strip('"')), 32)
            except (TypeError, ValueError):
                rhs = Tag(str(v))
            return BinOp("eq" if eq else "ne", Ref(sig), rhs, 1)

        terms: list[Expr] = []
        for b in branches:
            conj: Expr | None = None
            for sig, pol in b.guards:                       # boolean if/else guards
                lit: Expr = Ref(sig) if pol == 1 else UnOp("lnot", Ref(sig), 1)
                conj = lit if conj is None else BinOp("land", conj, lit, 1)
            for sig, v in b.tag_guards:                     # `case (sel) v:` -- an arm
                lit = match(sig, v, True)
                conj = lit if conj is None else BinOp("land", conj, lit, 1)
            for sig, v in b.neg_matches:                    # the `default` arm: differs from all
                lit = match(sig, v, False)
                conj = lit if conj is None else BinOp("land", conj, lit, 1)
            if conj is None:
                return None                  # an UNGUARDED branch drives always -- not a latch
            terms.append(conj)
        if not terms:
            return None
        expr = terms[0]
        for t in terms[1:]:
            expr = BinOp("lor", expr, t, 1)
        if isinstance(expr, Ref):
            return expr.name                 # a single positive guard IS the enable
        return self._hoist_bit(expr, loc).name

    def _lower_always_latch(self, m, flagged) -> None:
        """`always_latch if (en) q <= d;` -> the LatchItem schema (Fix 81).

        Opt-in for the same reason an instantiated latch cell is: a latch is transparent while
        its enable is high, which is a combinational path rather than a register, and is far more
        often an accident than an intent. What was wrong before is that the flag admitted the
        CELL and not this -- the explicit, self-documenting spelling.

        Only the canonical shape is accepted (`if (en) q <= d;`, one signal, no else). Anything
        else is refused rather than guessed at: a latch whose enable or data is a compound
        expression should say so in the RTL by naming the wire."""
        loc = self._loc(m)
        if not getattr(self, "_allow_latches", False):
            flagged.append((loc, (
                "always_latch: level-sensitive latches are OFF by default -- pass "
                "--allow-latches if this design genuinely uses one. A latch is transparent "
                "while its enable is high (zero delay), which is a combinational path, not a "
                "register")))
            return
        body = self._unwrap_block(m.body)
        if _enum_name(body.kind) != "Conditional" or getattr(body, "ifFalse", None) is not None:
            flagged.append((loc, "always_latch: only `if (en) q <= d;` is modelled "
                                 "(one enable, one target, no else)"))
            return
        try:
            en, pol = self._cond_signal(body)
            assign = self._unwrap_block(body.ifTrue)
            expr = assign.expr
            q = self._peel(expr.left).symbol.name
            d = self._peel(expr.right).symbol.name
        except Exception:  # noqa: BLE001 - any shape we cannot read is refused, never guessed
            flagged.append((loc, "always_latch: enable and data must be plain nets "
                                 "(assign a compound expression to a wire first)"))
            return
        if pol != 1:
            flagged.append((loc, "always_latch: an active-low enable (`if (!en)`) is not "
                                 "modelled -- invert it into a named wire"))
            return
        self._latches.append(LatchItem(q=q, d=d, en=en, inst=f"{q}__always_latch", loc=loc))

    # -- procedural block ----------------------------------------------------
    def _lower_block(self, m, comb, seq, writes, reg_names, signals, flagged) -> None:
        self._blk_comb, self._blk_signals = comb, signals  # sinks for hoisted if-conditions
        pk = _enum_name(m.procedureKind)
        if pk == "AlwaysLatch":
            # `always_latch if (en) q <= d;` is the EXPLICIT way to write a latch, and it was
            # refused even with --allow-latches -- which only accepted an instantiated latch
            # CELL, so the cleanest spelling was the one that did not work (Fix 81). It lowers
            # to the same proven schema (LatchItem / Latch.lean): transparent while the enable
            # is high, holding across the boundary when it is low, both guards read at the
            # instant the head is derived so the two are complementary by construction.
            self._lower_always_latch(m, flagged)
            return
        if pk not in ("AlwaysComb", "Always", "AlwaysFF"):
            flagged.append((self._loc(m), f"out-of-scope procedural block: {m.procedureKind}"))
            return
        if pk == "AlwaysComb":
            comb, clock, reset = True, "", None
            self._blk_reset = None
            stmt = self._unwrap_block(m.body)
        else:
            timed = m.body
            if _enum_name(timed.kind) in ("ConcurrentAssertion", "ImmediateAssertion"):
                return  # an assertion in a procedural block is SVA (the property layer), not a gap
            if _enum_name(timed.kind) != "Timed":
                flagged.append((self._loc(m), f"out-of-scope block body: {timed.kind}"))
                return
            clock, reset = self._sensitivity(timed.timing)  # may raise on dual-edge -> flagged
            self._blk_clock = clock          # $rose/$fell sample on THIS block's ticks
            self._blk_reset = reset          # a MEMORY write in this block is gated on it (see _mem_guards)
            comb = clock == ""   # `always @(*)` / `@(a or b)` (no edge) -> combinational
            stmt = self._unwrap_block(timed.stmt)
        reset_values: dict[str, int] = {}
        # Group every assign to a signal into ONE item with branches in priority order. For
        # always_ff: later/else branches carry the negated condition and an if-with-no-else
        # holds the reg -> one register, one value/cycle. For always_comb: same collection, but
        # emitted combinationally at T, and an if-with-no-else is a LATCH (flagged, not held).
        brs: dict[str, list[Branch]] = {}
        locs: dict[str, Loc] = {}
        self._slice_writes = {}
        self._elem_written = set()          # signals this block wrote an ELEMENT of (see the divert)
        blk_flagged: list = []   # branch-path flags -- discarded if the block routes to the executor
        self._hard_flags = []    # soundness refusals -- NEVER discarded (see _lower_loop_body)
        # The branch path below runs UNCONDITIONALLY, as a PROBE: whether the block can be taken
        # straight-line is only known after trying. But its condition-hoists commit as they go --
        # `_hoist_bit`/`_hoist_word`/`_edge_signal` append a CombItem and a Signal to the module's
        # own sinks the moment they run -- so a probe that is later discarded leaves them behind.
        # Snapshot the sinks here and excise that segment if the block diverts (Fix 95): the
        # orphans referenced the PRE-SSA block-local (`cnt`), which only the executor path binds,
        # so the rule read an atom nothing could derive and its companion off-rule then pinned the
        # signal to 0 -- silently, since every emit-time gate passed.
        n_comb, n_edges, n_writes = len(self._blk_comb), len(self._blk_edges), len(writes)
        known = set(signals)
        self._collect_updates(stmt, clock, reset, [], (), (), brs, locs, writes, reset_values,
                              comb, blk_flagged)
        # BEFORE the assembly, which consumes `_slice_writes` and deletes the whole write it uses as a
        # base: a signal written both as a WHOLE and as a PART in one comb block must reach the SSA
        # executor, because the branch path loses their ORDER (see the divert below, F22).
        mixed_writes = {r for r in getattr(self, "_slice_writes", {}) if r in brs}
        mixed_writes |= {r for r in getattr(self, "_elem_written", ()) if r in brs}
        self._assemble_slice_writes(brs, locs, reg_names, comb, blk_flagged, clock, reset,
                                    reset_values)  # clocked slice writes -> module-level RMW
        probe_comb, probe_edges = len(self._blk_comb), len(self._blk_edges)
        probe_sigs = [k for k in signals if k not in known]
        # always_comb that the branch path can't take straight-line: BLOCKING reassignment (an
        # accumulation `s=s+x`, or a default-then-override `y=0; if(c) y=a`), or a `while`/`repeat`
        # loop (which the branch path flagged). Run the symbolic executor (SSA + for/while/repeat
        # unroll + if/else->Cond, shared with functions) over the whole block and emit one
        # combinational assignment per signal. (Pure if/else / lane-rolled `for` stay on the branch
        # path -- no unconditional reassignment, nothing flagged.)
        # INFERRED LATCHES, as a coverage question over the whole block (see _definitely_assigned):
        # a module signal this block writes on SOME path but not on EVERY path retains its value.
        # Computed here, once, so it holds for both lowering routes below -- and restricted to
        # declared module signals, since a block-local temp is SSA'd by the executor and has no
        # atom to be unbound.
        # A signal left undriven ONLY because a `case` has no `default` is the D4 case: translated
        # faithfully and announced on the WARNING channel by _flag_incomplete_case, by decision.
        # Subtracting the case-total run keeps this check from re-classifying that as a refusal.
        latched = [r for r in sorted(self._assigned_regs(stmt)
                                     - self._definitely_assigned(stmt, case_total=True))
                   if r in signals or r.split("(", 1)[0] in signals] if comb else []
        latch_flags = [(self._loc(m),
                        f"always_comb: {r} not assigned on all paths (inferred latch)")
                       for r in latched]
        # --allow-latches: TRANSLATE the inferred latch with latch semantics instead of refusing
        # it (Fix 82). The transparent half is the block's own rules -- `val(y,V,T) :- <guard>,
        # <driver>` IS the driven case -- so all that is missing is the retention, gated on the
        # complement of "the block drove it this instant". That enable is a fresh 1-bit signal
        # built from the driving branches' guards, so it reads only the guards and never `y`:
        # the hold crosses `T -> T+1` and creates no combinational loop, which is exactly why
        # the latch schema is the right shape here (`Latch.lean`).
        if latched and getattr(self, "_allow_latches", False):
            kept = []
            for reg in latched:
                en = self._latch_enable(reg, brs.get(reg, []), self._loc(m))
                if en is None:
                    kept.append(reg)          # shape we cannot read -> keep the loud refusal
                    continue
                self._latches.append(LatchItem(q=reg, d="", en=en, inst=f"{reg}__inferred",
                                               loc=self._loc(m), hold_only=True))
            latch_flags = [(self._loc(m),
                            f"always_comb: {r} not assigned on all paths (inferred latch)")
                           for r in kept]
            self._warns.extend(
                (self._loc(m), f"INFERRED LATCH translated: {r} is not assigned on every path "
                               f"through this always_comb, so it RETAINS its value -- modelled "
                               f"as a level-sensitive latch (--allow-latches). Add a default "
                               f"(`{r} = '0;`) if that was not intended")
                for r in latched if r not in kept)

        def _blocking(bl: list) -> bool:
            return len(bl) > 1 and any(not (b.guards or b.tag_guards or b.neg_matches) for b in bl)
        # A signal written BOTH as a whole and as a PART in one comb block needs the executor too: the
        # branch path collects the two independently and loses their ORDER, so `y[2] = c; y = a;` came
        # out as the read-modify-write `a with bit 2 = c` when SystemVerilog says plain `a` (the whole
        # write is last and wins). `_blocking` cannot see it -- it inspects only `brs`, and part writes
        # live in `_slice_writes` (F22). Ordering is exactly what SSA execution gets right for free.
        if comb and (blk_flagged or mixed_writes or any(_blocking(bl) for bl in brs.values())):
            env = self._try_exec_comb(stmt)   # the executor re-checks genuine latches itself
            if env is not None:
                # The probe is DISCARDED, so its commits are too -- by segment, not by name, so
                # this holds for every helper that hoists (bit, word, case-pattern, edge) rather
                # than only the one the defect was found through. The executor appends its own
                # hoists below, after this point, so the segment is still exactly the probe's.
                # `self._cond_n` is deliberately NOT rewound: a gap in the `cN` numbering is
                # cosmetic, while renumbering would move every executor temp in every diverted
                # block (the divider's `c32..c50`) and break any proof shard that names one.
                del self._blk_comb[n_comb:probe_comb]
                del self._blk_edges[n_edges:probe_edges]
                # ...and the probe's MEMORY/element writes. `writes` was the one sink the rollback
                # missed: an element write (`y[2] = c`) appended during collection survived the divert
                # and was emitted BESIDE the executor's correct whole-signal rule -- the two-driver
                # defect reappearing from the other side, after the executor had got it right (F22).
                del writes[n_writes:]
                for k in probe_sigs:
                    signals.pop(k, None)
                for sig, expr in env.items():
                    # keep only MODULE signals -- block-local temps (a scan accumulator, the loop
                    # var) are not signals and must not be emitted. A signal may appear either
                    # under its FULL functor name (a struct field `p(f)`, which has no root signal
                    # `p`) or under its root (a per-element `arr(k)` of an array signal `arr`).
                    if sig is None:
                        continue
                    if sig not in signals and sig.split("(", 1)[0] not in signals:
                        # A whole-STRUCT write (`p = src`): a struct has no atom of its own -- it
                        # lives as `p(field)` -- so distribute the value across its field
                        # subsignals. Fields the block ALSO wrote individually (`p.f = v`) are in
                        # `env` in their own right and win, which is exactly last-write-wins.
                        # Without this the whole write matched no signal and was dropped SILENTLY,
                        # leaving the struct undriven while coverage reported success (Fix 47).
                        if sig in self._structs:
                            for fn, fw, off in self._structs[sig]:
                                sub = f"{sig}({fn})"
                                if sub in env or sub not in signals:
                                    continue
                                self._blk_comb.append(
                                    CombItem(lhs=sub, rhs=Slice(expr, off + fw - 1, off),
                                             loc=self._loc(m)))
                        continue
                    self._hoist_ctx = sig
                    expr = self._hoist_bit_arms(sig, expr, signals, self._loc(m))
                    self._hoist_ctx = ""
                    self._blk_comb.append(CombItem(lhs=sig, rhs=expr, loc=self._loc(m)))
                flagged.extend(self._hard_flags)   # soundness refusals survive the fallback
                flagged.extend(latch_flags)        # ...and so do genuine latches
                return                        # discard blk_flagged (branch-path false-latch flags)
            # executor couldn't handle it (indexed write, genuine latch, ...) -> the real flags
            flagged.extend(self._hard_flags)
            flagged.extend(latch_flags)
            flagged.extend(blk_flagged or [(self._loc(m), "always_comb: could not lower (blocking/loop)")])
            return
        flagged.extend(self._hard_flags)
        flagged.extend(latch_flags)
        flagged.extend(blk_flagged)
        self._register_block_locals(stmt, signals, self._loc(m))   # multi-bit blocking temps -> words
        if not comb:                       # a flop holds where no branch drives it (always_comb: latch)
            self._complete_holds(brs, locs)
        for reg, branches in brs.items():
            # An UNCONDITIONAL combinational assign of a genuine EXPRESSION (gate / slice / concat /
            # compare -- not a plain copy or tag) is exactly a continuous assign: route it to a
            # CombItem so the capable Group-1 emitter handles it (the seq-comb path only reads
            # Const/Ref/Tag bit values). Copies (Ref/Const/Tag) and any guarded/lane branch stay here.
            if (comb and len(branches) == 1 and reg not in self._lane_dims):
                b = branches[0]
                if (not (b.guards or b.tag_guards or b.neg_matches)
                        and not isinstance(b.value, (Tag, Ref, Const))):
                    self._blk_comb.append(CombItem(lhs=reg, rhs=b.value, loc=locs[reg]))
                    continue
            if not comb:
                reg_names.add(reg)
            rlo, rhi, rstep, roff = self._reg_lane_range.get(reg, (0, None, 1, 0))
            seq.append(SeqItem(reg=reg, clock=clock, reset=reset, branches=tuple(branches),
                               has_hold=False, loc=locs[reg], reset_value=reset_values.get(reg, 0),
                               combinational=comb, lane_lo=rlo, lane_hi=rhi, lane_step=rstep,
                               lane_off=roff))

    def _try_exec_comb(self, stmt) -> dict | None:
        """Symbolically execute an always_comb block's blocking statements (reusing the function
        executor) -> {signal: final value Expr}. None if a construct can't be unrolled (e.g. an
        indexed write), so the caller falls back / flags."""
        env: dict = {}

        def _reads_self(e, name) -> bool:
            if isinstance(e, Ref):
                return e.name == name
            if isinstance(e, (list, tuple)):
                return any(_reads_self(x, name) for x in e)
            return any(_reads_self(getattr(e, f), name)
                       for f in getattr(e, "__dataclass_fields__", ()))

        self._exec_comb = True   # enable Cond-operand hoisting for a scan accumulator (see _lower_expr)
        self._cond_hoist_memo = {}   # id(Cond) -> (the Cond, its tern Ref): repeated reads of one value share a tern; the object is RETAINED (F40)
        try:
            self._exec_func_body(stmt, None, env, {})
        except Exception:  # noqa: BLE001 - any unhandled construct -> fall back, not a crash
            return None
        finally:
            self._exec_comb = False
        # A PART write with no prior write in the block reads the signal's own prior value
        # (`env.get(y, Ref(y))`), which is a LATCH -- correct semantics, but not expressible as a
        # combinational value without a self-reference. If any result still reads its own signal, the
        # executor declines and the caller falls back to the machinery that models latches properly.
        # Without this the latch tests turned into `COMBINATIONAL LOOP: y -> y` (F22).
        if any(_reads_self(v, k) for k, v in env.items() if k):
            return None
        return env

    def _hoist_bit_arms(self, sig: str, expr: Expr, signals: dict, loc) -> Expr:
        """A 1-bit signal driven by a ternary (`y = c ? a&b : 0`, from a default-then-override
        always_comb) -- the bit emitter reads each ARM as a single bit term, which a logic expression
        is not. Hoist a logic-expr arm to a combinational gcond bit so the arm becomes a plain Ref.
        Word signals (the arms go through the @func cascade) and non-ternary values are untouched."""
        s = signals.get(sig)
        if (getattr(getattr(s, "irtype", None), "width", 1) != 1) or not isinstance(expr, Cond):
            return expr
        arm = lambda e: e if isinstance(e, (Const, Ref, Tag)) else self._hoist_bit(e, loc)  # noqa: E731
        return Cond(expr.sel, arm(expr.a), arm(expr.b), expr.width)

    def _sensitivity(self, timing) -> tuple[str, Reset | None]:
        """Classify an always block's sensitivity. No edges -> "" (combinational). Otherwise
        the CLOCK is a posedge (corporate convention), or the lone edge if there is no posedge
        (a falling-edge flop); any OTHER edge is the async reset (negedge=active-low,
        posedge=active-high). Dual-edge use of the SAME clock (half-cycle/DDR) is not modeled."""
        events = getattr(timing, "events", None) or [timing]   # single @(posedge clk) is one event
        edges: list[tuple[str, str]] = []
        for ev in events:
            edge = _enum_name(getattr(ev, "edge", "None_"))
            if edge in ("PosEdge", "NegEdge"):
                sig = ev.expr.symbol.name if hasattr(ev.expr, "symbol") else str(ev.expr).strip()
                edges.append((sig, edge))
        if not edges:
            return "", None  # level-sensitive / @* -> combinational
        by_sig: dict[str, set[str]] = {}
        for s, e in edges:
            by_sig.setdefault(s, set()).add(e)
        dual = [s for s, es in by_sig.items() if len(es) > 1]
        if dual:  # same clock on both edges -> half-cycle phase not representable in the cycle model
            raise NotImplementedError(f"dual-edge clocking on {dual[0]} (half-cycle/DDR) not modeled")
        posedges = [s for s, e in edges if e == "PosEdge"]
        if not posedges:                          # only negedge(s): the (first) one is the clock
            return edges[0][0], None
        clock = posedges[0]
        reset: Reset | None = None
        for s, e in edges:
            if s != clock:                        # the non-clock edge is the async reset
                reset = Reset(signal=s, active="low" if e == "NegEdge" else "high", kind="async")
        return clock, reset

    def _unwrap_block(self, s):
        if _enum_name(s.kind) == "Block":
            return s.body
        return s

    def _is_unit_incr(self, st, var: str) -> bool:
        """True if statement ``st`` is the unit increment of ``var`` (``i++`` or ``i = i + 1``)."""
        return self._incr_const(st, var) == 1

    def _incr_const(self, st, var: str) -> int | None:
        """The constant STRIDE of the loop step ``st`` -- ``i++`` / ``i = i + S`` / ``i += S`` --
        or None if it is not a constant positive increment of ``var``. `i += S` is a compound
        assignment whose right side slang keeps as `i + S` with `i` an `LValueReference`, which
        `_lower_expr` cannot lower; read the shape off the syntax nodes instead."""
        k = _enum_name(st.kind)
        if k == "UnaryOp":
            return 1 if "ncrement" in _enum_name(st.op) else None
        if k != "Assignment":
            return None
        left = self._peel(st.left)
        if _enum_name(left.kind) != "NamedValue" or left.symbol.name != var:
            return None
        rhs = self._peel(st.right)
        if _enum_name(rhs.kind) != "BinaryOp" or _BINOP.get(_enum_name(rhs.op)) != "add":
            return None
        for a, b in ((rhs.left, rhs.right), (rhs.right, rhs.left)):
            pa = self._peel(a)
            is_var = (_enum_name(pa.kind) in ("NamedValue", "LValueReference")
                      and getattr(getattr(pa, "symbol", None), "name", var) == var)
            n = self._const_of(b)
            if is_var and n is not None and n >= 1:
                return n
        return None

    def _for_loop_var(self, stmt) -> str | None:
        """The single loop variable of a ``for``, whether declared in the loop (`for(int i=...)` ->
        ``loopVars``) or pre-declared (`for(i=...)` -> an ``initializers`` assignment). None if not one."""
        lvs = list(getattr(stmt, "loopVars", []))
        if len(lvs) == 1:
            return lvs[0].name
        inits = list(getattr(stmt, "initializers", []))
        if len(inits) == 1 and _enum_name(inits[0].kind) == "Assignment":
            il = self._peel(inits[0].left)
            if _enum_name(il.kind) == "NamedValue":
                return il.symbol.name
        return None

    def _for_init_const(self, stmt, var: str) -> int | None:
        """The constant ``var`` is initialised to (loopVars initializer or an initializers
        assignment), or None if there is none / it is not constant."""
        for lv in getattr(stmt, "loopVars", []):
            if lv.name == var:
                init = getattr(lv, "initializer", None)
                return None if init is None else self._fold(self._lower_expr(init))
        for a in getattr(stmt, "initializers", []):
            if _enum_name(a.kind) == "Assignment":
                il = self._peel(a.left)
                if _enum_name(il.kind) == "NamedValue" and il.symbol.name == var:
                    return self._fold(self._lower_expr(a.right))
        return None

    def _for_init_is_zero(self, stmt, var: str) -> bool:
        """True if ``var`` is initialised to 0 (loopVars initializer or an initializers assignment)."""
        return self._for_init_const(stmt, var) == 0

    def _for_static_range(self, stmt, var: str | None) -> tuple[int, int, int] | None:
        """The (START, EXCLUSIVE upper bound, STEP) of a statically-bounded
        ``for (var = L; var </<= M; var += S)`` (constant L, M, S >= 1) -- the loop var takes
        L, L+S, .. below the bound. None for any other shape (non-constant bound or step); the
        caller flags. The start used to be required to be 0 and the step to be 1; a loop from 1
        is carried as `lane_lo`, a stride as `lane_step`."""
        steps = list(getattr(stmt, "steps", []))
        stop = getattr(stmt, "stopExpr", None)
        if var is None or stop is None or len(steps) != 1:
            return None
        lo = self._for_init_const(stmt, var)
        step = self._incr_const(steps[0], var)
        if lo is None or step is None or step < 1:
            return None
        if _enum_name(stop.kind) != "BinaryOp" or _BINOP.get(_enum_name(stop.op)) not in ("lt", "le"):
            return None
        left = self._peel(stop.left)
        if _enum_name(left.kind) != "NamedValue" or left.symbol.name != var:
            return None
        n = self._const_of(stop.right)
        if n is None:
            return None
        return lo, (n if _BINOP[_enum_name(stop.op)] == "lt" else n + 1), step

    def _loop_writes_mem(self, stmt) -> bool:
        """True if any assignment in ``stmt`` writes ``mem[..]`` (an unpacked array) -- used to decide
        whether a non-constant-bound loop is an (illegal) memory loop to flag vs a packed-vector loop."""
        if _enum_name(stmt.kind) == "ExpressionStatement" and _enum_name(stmt.expr.kind) == "Assignment":
            base = self._peel(self._peel(stmt.expr.left).value) \
                if _enum_name(self._peel(stmt.expr.left).kind) == "ElementSelect" else None
            if base is not None and getattr(getattr(base, "symbol", None), "type", None) is not None \
                    and getattr(base.symbol.type, "isUnpackedArray", False):
                return True
        for attr in ("body", "stmt", "ifTrue", "ifFalse"):
            c = getattr(stmt, attr, None)
            if c is not None and hasattr(c, "kind") and self._loop_writes_mem(c):
                return True
        for attr in ("body", "list"):
            c = getattr(stmt, attr, None)
            if isinstance(c, (list, tuple)) and any(hasattr(x, "kind") and self._loop_writes_mem(x)
                                                    for x in c):
                return True
        return False

    def _count_unit_incr(self, stmt, var: str) -> int:
        """Count the unit increments of ``var`` anywhere in ``stmt`` (a for-shaped while must have 1)."""
        if _enum_name(stmt.kind) == "ExpressionStatement" and self._is_unit_incr(stmt.expr, var):
            return 1
        total = 0
        for attr in ("body", "stmt", "ifTrue", "ifFalse"):
            c = getattr(stmt, attr, None)
            if c is not None and hasattr(c, "kind"):
                total += self._count_unit_incr(c, var)
        for attr in ("body", "list"):
            c = getattr(stmt, attr, None)
            if isinstance(c, (list, tuple)):
                total += sum(self._count_unit_incr(x, var) for x in c if hasattr(x, "kind"))
        return total

    def _while_as_for(self, stmt, prev) -> tuple[str, int] | None:
        """Recognize a statically-bounded for-shaped ``while``: ``prev`` is ``i = 0``, the condition is
        ``i </<= N`` (N constant), and the body has exactly one unit increment of ``i``. Returns
        (loop var, exclusive bound) so it lane-rolls like a ``for``; else None (-> flagged)."""
        cond = getattr(stmt, "cond", None)
        if cond is None or _enum_name(cond.kind) != "BinaryOp":
            return None
        op = _BINOP.get(_enum_name(cond.op))
        left = self._peel(cond.left)
        if op not in ("lt", "le") or _enum_name(left.kind) != "NamedValue":
            return None
        var = left.symbol.name
        n = self._const_of(cond.right)
        if n is None:
            return None
        if prev is None or _enum_name(prev.kind) != "ExpressionStatement" \
                or _enum_name(prev.expr.kind) != "Assignment":
            return None
        pl = self._peel(prev.expr.left)
        if _enum_name(pl.kind) != "NamedValue" or pl.symbol.name != var \
                or self._fold(self._lower_expr(prev.expr.right)) != 0:
            return None
        if self._count_unit_incr(stmt.body, var) != 1:
            return None
        return var, (n if op == "lt" else n + 1)

    def _lower_clocked_while(self, stmt, prev, guards, tag_guards, neg_matches, rec, flagged) -> None:
        """A clocked ``while``: if it is a statically-bounded for-shape, lane-roll it like a ``for``
        (the ``i=i+1`` increment in the body is swallowed as loop control); else flag."""
        shape = self._while_as_for(stmt, prev)
        if shape is None:
            flagged.append((self._loc_expr(stmt), "while in an always block deferred: needs a "
                            "constant-bounded for-shape (i=0; i</<=N; ...; i=i+1), else a runtime "
                            "bound is not synthesizable"))
            return
        var, hi = shape
        self._lower_loop_body({var}, hi, stmt.body, guards, tag_guards, neg_matches, rec, flagged,
                              self._loc_expr(stmt))

    def _flag_incomplete_case(self, stmt, arm_vals) -> None:
        """LOUD MESSAGE for a `case` with no `default` whose arms do not cover the selector.

        The emitted schema is one rule per arm, guarded by `val(sel, v, T)`. With a `default`
        the translator emits a genuine catch-all (selector differs from every explicit label)
        and the schema is TOTAL -- proven unconditionally as `mux_default_total`. With no
        default and uncovered selector values the output is simply UNBOUND on those values:
        not a mistranslation (the RTL defines nothing there either), but every property over
        that signal then passes VACUOUSLY on any trace reaching them. A silent vacuous pass is
        the worst failure mode a verification tool has, so this is reported rather than
        assumed away -- `mux_partial_only_without_default` proves a missing default is the
        ONLY way the mux schema can leave its output unbound.

        The translation itself is unchanged: we never invent a value the RTL does not specify.
        Deliberately conservative -- it flags only when every label is a concrete constant (or
        an enum member) and the selector's domain is known, so casez/casex, computed labels
        and wide selectors are left alone rather than guessed at.

        Reported on the WARNING channel (`_warns` -> `Design.warned`), not as a coverage
        problem: the case IS fully and faithfully translated, so rule 2 -- which is about
        constructs being silently missed -- is not in question. It is also deliberately kept
        off the block's own flag list, since a flag there marks the branch path as unable to
        lower the block and diverts always_comb to the symbolic executor, which would suppress
        the very rules we still want emitted."""
        cov = self._case_coverage(stmt, arm_vals)
        if cov is None:
            return
        missing, seen, domain, what = cov
        if not missing:
            return
        ex = ", ".join(str(x) for x in missing[:3]) + ("..." if len(missing) > 3 else "")
        self._warns.append((self._loc_expr(stmt),
                        f"case without `default` does not cover its {what}: "
                        f"{len(seen)} of {domain} values have an arm; {len(missing)} do not "
                        f"({ex}). The output is UNBOUND there, so a property over it passes "
                        f"VACUOUSLY on any trace reaching those values -- add a `default` arm"))

    def _case_coverage(self, stmt, arm_vals) -> tuple[list, set, int, str] | None:
        """``(missing, seen, domain, what)`` for a `case`'s selector, or None when the domain is
        not knowable. ONE notion of "do the arms cover the selector", shared by the D4 warning
        above and the definite-assignment analysis (`_definitely_assigned`): a case whose arms
        cover every selector value is TOTAL even with no `default`, and both consumers have to
        agree about that or they would contradict each other on the same block."""
        if not arm_vals:
            return None
        t = getattr(stmt.expr, "type", None)
        ct = getattr(t, "canonicalType", t) or t
        if getattr(ct, "isEnum", False):
            try:                                   # enum selector: the domain IS the member set
                # ITERATE the canonical type -- pyslang has no `.members` accessor, so the old
                # spelling raised on every enum and this whole arm was dead (Fix 86). Same
                # spelling as the enum decl walk in `_modules.py`, which is where it was right.
                members = [m.name.lower() for m in ct]
            except Exception:
                return
            if not members or any(v not in members for v in arm_vals):
                return                             # a non-member label -> not a plain enum case
            missing, seen, domain = _coverage(arm_vals, members)
            what = "enum members"
        else:
            w = getattr(t, "bitWidth", None)
            if not w or w > 16:                    # >16 bits: full coverage is never the intent
                return
            vals: list[int] = []
            for v in arm_vals:
                try:
                    vals.append(int(v.strip('"') if isinstance(v, str) else v))
                except (TypeError, ValueError):
                    return                         # non-constant label -> not our business
            missing, seen, domain = _coverage(vals, 1 << w)
            what = f"{w}-bit selector"
        return missing, seen, domain, what

    def _rec_seq(self, items: list, guards, tag_guards, neg_matches, rec, flagged, comb) -> None:
        """Walk a statement sequence, intercepting a for-shaped ``while`` (clocked) WITH its preceding
        ``i=0`` init so the init is consumed (not emitted as a spurious register write)."""
        items = [x for x in items if hasattr(x, "kind")]
        i = 0
        while i < len(items):
            ss = items[i]
            nxt = items[i + 1] if i + 1 < len(items) else None
            if not comb and nxt is not None and _enum_name(nxt.kind) == "WhileLoop" \
                    and self._while_as_for(nxt, ss) is not None:
                self._lower_clocked_while(nxt, ss, guards, tag_guards, neg_matches, rec, flagged)
                i += 2
                continue
            if not comb and _enum_name(ss.kind) == "WhileLoop":
                self._lower_clocked_while(ss, None, guards, tag_guards, neg_matches, rec, flagged)
                i += 1
                continue
            rec(ss, guards, tag_guards, neg_matches)
            i += 1

    def _lower_loop_body(self, lvars: set[str], hi: int | None, body, guards, tag_guards,
                         neg_matches, rec, flagged, loc, lo: int = 0, step: int = 1) -> None:
        """Lane-roll a clocked loop body: bind the loop var(s) as genvars over the progression
        lo, lo+step, .. < hi, push (var, (lo, hi, step)) onto the loop-nest stack (so a nested
        `for(i) for(j)` write reads BOTH bounds per address dimension), and recurse. Flags if the
        body writes a memory more than once."""
        saved_gv, self._genvars = self._genvars, self._genvars | lvars
        saved_order = list(self._genvar_order)
        saved_hi, self._lane_hi = self._lane_hi, (hi if hi is not None else self._lane_hi)
        saved_lo, self._lane_lo = self._lane_lo, (lo if hi is not None else self._lane_lo)
        saved_step, self._lane_step = self._lane_step, (step if hi is not None else self._lane_step)
        for _v in sorted(lvars):
            if _v not in self._genvar_order:
                self._genvar_order.append(_v)
        pushed = [(v, ((lo, hi, step) if hi is not None else None)) for v in lvars]
        self._loop_lane_stack.extend(pushed)
        saved_cnt, self._lane_mem_writes = self._lane_mem_writes, 0
        saved_fold, self._genvar_folded = self._genvar_folded, None
        try:
            rec(body, guards, tag_guards, neg_matches)
            if self._lane_mem_writes > 1:
                flagged.append((loc, f"loop writes a memory {self._lane_mem_writes}x "
                                "(only one lane-rolled write per loop is modeled)"))
            # A fold that swallowed a loop variable somewhere the LaneIdx lowering could not
            # reach (a slice BOUND, which must be a literal offset) -- refuse rather than bake
            # iteration 0 into every lane.
            if self._genvar_folded is not None:
                self._hard_flags.append((loc, (
                    f"procedural loop body uses the loop variable as a VALUE "
                    f"({self._genvar_folded}), not only as a select index -- the body is "
                    f"lane-rolled (lowered once, index fanned by the grounder), so the variable "
                    f"is not a readable signal and the rule would never fire. Rewrite the "
                    f"index-dependent value as a select, or unroll explicitly.")))
        finally:
            self._genvars = saved_gv
            self._genvar_order = saved_order
            self._lane_hi = saved_hi
            self._lane_lo = saved_lo
            self._lane_step = saved_step
            del self._loop_lane_stack[len(self._loop_lane_stack) - len(pushed):]
            self._lane_mem_writes = saved_cnt
            self._genvar_folded = saved_fold

    def _collect_updates(self, stmt, clock, reset, guards, tag_guards, neg_matches,
                         brs, locs, writes, rvals, comb=False, flagged=None) -> None:
        rec = lambda s, g, tg, nm: self._collect_updates(  # noqa: E731
            s, clock, reset, g, tg, nm, brs, locs, writes, rvals, comb, flagged)
        kind = _enum_name(stmt.kind)
        if kind == "Conditional":
            cond_sig, pol = self._cond_signal(stmt)
            # async-reset branch (the reset signal is in the sensitivity list): ifTrue is the
            # reset action (capture reg -> reset value), ifFalse is the clocked body.
            if reset and cond_sig == reset.signal:
                self._collect_reset_values(stmt.ifTrue, rvals)
                if stmt.ifFalse is not None:
                    rec(stmt.ifFalse, guards, tag_guards, neg_matches)
                return
            # priority if/else: ifTrue gets the condition, ifFalse gets its NEGATION
            rec(stmt.ifTrue, [*guards, (cond_sig, pol)], tag_guards, neg_matches)
            if stmt.ifFalse is not None:
                rec(stmt.ifFalse, [*guards, (cond_sig, 1 - pol)], tag_guards, neg_matches)
            elif comb:
                pass    # combinational path coverage is a WHOLE-BLOCK question -- see
                        # _definitely_assigned, called once per always_comb block. Flagging here
                        # (the old shape test) both missed the other ways to leave a path
                        # undriven and mis-flagged `y = 0; if (s) y = a;`, where the earlier
                        # unconditional write already covers every path.
            else:
                # sequential: every reg assigned in ifTrue HOLDS when the condition is false
                for reg in self._assigned_regs(stmt.ifTrue):
                    brs.setdefault(reg, []).append(
                        Branch(guards=(*guards, (cond_sig, 1 - pol)), value=Ref(reg),
                               tag_guards=tuple(tag_guards), neg_matches=tuple(neg_matches),
                               loc=self._loc_expr(stmt)))
                    locs.setdefault(reg, self._loc_expr(stmt))
        elif kind == "Case" and _enum_name(stmt.condition) in ("WildcardJustZ", "WildcardXOrZ"):
            # casez/casex: arms are a PRIORITY chain of masked equalities. Each arm hoists a
            # gcond bit `(sel & care_mask) == pattern`; a later arm fires only if all earlier
            # gconds are false (first-match-wins). default fires when none matched.
            sel_expr = self._lower_expr(stmt.expr)
            width = getattr(getattr(stmt.expr, "type", None), "bitWidth", 1) or 1
            prior: list[tuple[str, int]] = []
            for item in stmt.items:
                mask, pat = (None, None)
                if len(item.expressions) == 1:
                    mask, pat = self._wildcard_mask(item.expressions[0], width)
                if mask is None:  # multi-label arm or non-binary wildcard literal -> flag
                    flagged.append((self._loc_expr(item.stmt),
                                    "casez/casex: multi-label or non-binary wildcard arm (deferred)"))
                    continue
                g = self._hoist_masked_eq(sel_expr, mask, pat, width, self._loc_expr(item.stmt))
                rec(item.stmt, [*guards, *prior, (g, 1)], tag_guards, neg_matches)
                prior.append((g, 0))
            if getattr(stmt, "defaultCase", None) is not None:
                rec(stmt.defaultCase, [*guards, *prior], tag_guards, neg_matches)
        elif kind == "Case":
            sel = self._ref_name(stmt.expr)
            arm_vals = [self._match_value(lab) for it in stmt.items for lab in it.expressions]
            for item in stmt.items:
                for label in item.expressions:
                    rec(item.stmt, guards, (*tag_guards, (sel, self._match_value(label))), neg_matches)
            if getattr(stmt, "defaultCase", None) is not None:
                # default arm = selector differs from EVERY explicit arm value
                rec(stmt.defaultCase, guards, tag_guards, (*neg_matches, *[(sel, v) for v in arm_vals]))
            else:
                self._flag_incomplete_case(stmt, arm_vals)
        elif kind == "ForLoop":
            # procedural for: roll the loop var as a lane index (like a genvar), lower body once.
            # A memory write q[i]<=.. additionally lane-rolls over addr(mem,I) with the static bound;
            # a non-constant-bounded for over a MEMORY is not synthesizable -> flag.
            var = self._for_loop_var(stmt)
            lvs = {v.name for v in getattr(stmt, "loopVars", [])} | ({var} if var else set())
            rng = self._for_static_range(stmt, var)
            if rng is None:
                # The body is lowered ONCE with the loop var fanned by the grounder over the
                # lane domain 0..N-1 (`I` bound by the body's lane reads, or by an explicit
                # range). That is the loop's index set ONLY for the canonical shape; a
                # `for (i = 1; ...)`, `i += 2`, or a runtime bound `i < n` used to roll over
                # EVERY lane -- `y[0]` driven by the loop that starts at 1 as well as by its
                # own assignment (multi-valued), or `n` ignored outright -- silently, in both
                # modes. Until a partial index set is modelled, refuse. This was only ever
                # refused when the loop wrote a MEMORY; a packed vector was silently over-driven.
                what = "a memory" if self._loop_writes_mem(stmt.body) else "a lane"
                flagged.append((self._loc_expr(stmt), (
                    f"for over {what} with a non-constant bound / non-unit step / non-constant "
                    f"init: lane-rolling needs a constant unit-step range `for (i = L; i < N; "
                    f"i++)` (deferred -- unroll explicitly)")))
                return
            lo, hi, step = rng
            self._lower_loop_body(lvs, hi, stmt.body, guards, tag_guards, neg_matches, rec, flagged,
                                  self._loc_expr(stmt), lo=lo, step=step)
        elif kind == "RepeatLoop":   # repeat (N) body -> N copies (N constant)
            n = self._fold(self._lower_expr(stmt.count))
            if n is None or n < 0 or n > self._UNROLL_CAP:
                flagged.append((self._loc_expr(stmt), "repeat with a non-constant / huge count (deferred)"))
            else:
                for _ in range(n):
                    rec(stmt.body, guards, tag_guards, neg_matches)
        elif kind == "WhileLoop":
            # Reached for a comb while (-> the executor unrolls it) or a non-for-shaped clocked while
            # (a for-shaped clocked while is intercepted with its init in _rec_seq). FLAG either way.
            self._lower_clocked_while(stmt, None, guards, tag_guards, neg_matches, rec, flagged) \
                if not comb else flagged.append((self._loc_expr(stmt),
                                                 "WhileLoop in an always block deferred"))
        elif kind in ("DoWhileLoop", "ForeverLoop", "ForeachLoop"):
            # need in-body loop control or are unbounded -- not modeled. FLAG (never a silent miss).
            flagged.append((self._loc_expr(stmt),
                            f"{kind} in an always block deferred (use a constant-bounded for)"))
        elif kind == "Block":
            body = stmt.body if hasattr(stmt.body, "__iter__") else [stmt.body]
            self._rec_seq(list(body), guards, tag_guards, neg_matches, rec, flagged, comb)
        elif kind == "List":
            self._rec_seq(list(stmt.list), guards, tag_guards, neg_matches, rec, flagged, comb)
        elif kind == "ExpressionStatement":
            self._lower_nb_assign(stmt.expr, guards, tag_guards, neg_matches, brs, locs, writes, clock)

    def _complement(self, guard_list: list) -> list | None:
        """CNF complement: the conjunctions (a DNF) where NONE of the given (sig,pol)-conjunction guards
        hold = AND over guards of (NOT guard). An unconditional [] guard -> [] (always driven, no
        complement). Returns None on a runaway CNF->DNF blowup (rare; caller leaves the reg as-is)."""
        terms: list[list[tuple[str, int]]] = [[]]
        for g in guard_list:
            if not g:
                return []
            neg = [(s, 1 - p) for s, p in g]                # OR of the negated literals of this guard
            nxt: list[list[tuple[str, int]]] = []
            for t in terms:
                for s, p in neg:
                    if any(s2 == s and p2 != p for s2, p2 in t):
                        continue                            # contradiction (s already forced the other way)
                    nxt.append(t if (s, p) in t else [*t, (s, p)])
            terms = nxt
            if len(terms) > 64:
                return None
        seen: set = set()
        out = []
        for t in terms:
            k = tuple(sorted(t))
            if k not in seen:
                seen.add(k)
                out.append(t)
        return out

    @staticmethod
    def _excl(g1, g2) -> bool:
        """Do two (sig,pol) conjunctions CONFLICT (share a signal with opposite polarity)? Then they
        cannot both fire -- a later one never overrides an earlier one (within-chain priority branches)."""
        return any(s1 == s2 and p1 != p2 for s1, p1 in g1 for s2, p2 in g2)

    @staticmethod
    def _merge_lits(base, extra):
        """``base`` ∪ ``extra`` as one conjunction (dedup), or None if contradictory."""
        out = list(base)
        for s, p in extra:
            if any(s2 == s and p2 != p for s2, p2 in out):
                return None
            if (s, p) not in out:
                out.append((s, p))
        return out

    def _complete_holds(self, brs: dict, locs: dict) -> None:
        """SV write resolution per sequential reg: LAST-WRITE-WINS + a joint hold. Order the reg's assign
        branches by source; an assign is suppressed where a LATER OVERLAPPING assign also fires (a later
        separate `if` to the same reg overrides an earlier one -- SV nonblocking last-write-wins); the reg
        HOLDS where no assign fires (the complement). For within-chain (mutually-exclusive) branches the
        suppression is skipped (``_excl``) and the complement is just the else paths -- so existing output
        is unchanged (zero churn). Fixes a reg written in only some branches losing state (B1) and a reg
        written by overlapping separate statements double-valuing (B2). A reg with case-arm (tag/neg)
        guards keeps the within-chain handling and only completes its hold."""
        for reg, bl in brs.items():
            if any(b.tag_guards or b.neg_matches for b in bl):     # case reg
                # A LATER untagged assign overrides a case that already covers every path:
                #     case (state) ... default: ... endcase
                #     if (reset) state <= S0;
                # The `if` has no else, so collection added a hold `(reset, 0) -> state` -- right for a
                # standalone `if`, wrong here, because the CASE already assigned on that path. Emitted
                # as-is the register took TWO values whenever the case fired with reset low, so every
                # interesting trace was UNSATISFIABLE -- and UNSAT reads as "no counterexample", with
                # `VERDICT: OK`. Last-write-wins is the fix: the arms fire only where the later assign
                # does not, and its implicit hold goes away. Applied ONLY when the arms cover every
                # path (a default/neg-match branch exists), so a partial case keeps its hold and every
                # existing design's output is byte-identical. (F24, on VerilogEval's fsm_hdlc
                # reference, 2026-08-20; the shape `case … endcase; if (reset) …` is ordinary RTL.)
                bl = self._override_case_by_later_assign(reg, bl)
                # last-write-wins WITHIN each case arm: a default (unconditional) assign suppressed
                # where a later guarded assign to the SAME reg in the SAME arm fires -- e.g.
                # `case(state) IDLE: begin err<=0; if(c) err<=1; end`.
                bl = self._resolve_case_arms(reg, bl)
                self._complete_case_holds(reg, bl)
                brs[reg] = bl
                continue
            assigns = [b for b in bl if not (isinstance(b.value, Ref) and b.value.name == reg)]
            new = self._suppress(assigns)                          # last-write-wins over the assigns
            if new is None:
                continue
            hold = self._complement([b.guards for b in assigns])   # reg holds where no assign fires
            if hold:
                have = {tuple(sorted(t.guards)) for t in new}
                for t in hold:
                    if tuple(sorted(t)) not in have:
                        have.add(tuple(sorted(t)))
                        new.append(Branch(guards=tuple(t), value=Ref(reg), tag_guards=(), neg_matches=()))
            brs[reg] = new

    def _suppress(self, assigns: list) -> list | None:
        """Last-write-wins over a list of assign branches (in source order): each branch is restricted
        to where NO later OVERLAPPING assign (by ``guards``) also fires -- so a later separate/nested
        write to the same reg overrides an earlier one (SV nonblocking). Returns the restricted branches
        (tag/neg guards preserved), or None on a complement blow-up (caller leaves the reg as-is)."""
        new: list = []
        for i, b in enumerate(assigns):
            overlap = [lb for lb in assigns[i + 1:] if not self._excl(b.guards, lb.guards)]
            if not overlap:                                        # no later assign can co-fire -> as-is
                new.append(b)
                continue
            supp = self._complement([lb.guards for lb in overlap])  # no later overlapping assign fires
            if supp is None:
                return None
            for st in supp:                                        # G_i AND (no later overlap fires)
                m = self._merge_lits(b.guards, st)
                if m is not None:
                    new.append(Branch(guards=tuple(m), value=b.value,
                                      tag_guards=b.tag_guards, neg_matches=b.neg_matches, loc=b.loc))
        return new

    def _override_case_by_later_assign(self, reg: str, bl: list) -> list:
        """`case … endcase` followed by `if (c) reg <= v;` -- the later assign WINS where it fires.

        Returns the branch list with (a) the later untagged assign's guards negated onto every case
        arm, and (b) the implicit hold that `if` contributed dropped. Only when the arms cover every
        path (some branch carries neg_matches, i.e. the case has a default), because only then is the
        hold provably unreachable; otherwise the list is returned unchanged, so nothing that works
        today moves."""
        tagged = [b for b in bl if b.tag_guards or b.neg_matches]
        if not any(b.neg_matches for b in tagged):
            return bl                                   # a partial case still needs its hold
        untagged = [b for b in bl if not (b.tag_guards or b.neg_matches)]
        assigns = [b for b in untagged if not (isinstance(b.value, Ref) and b.value.name == reg)]
        holds = [b for b in untagged if isinstance(b.value, Ref) and b.value.name == reg]
        if not assigns or not holds:
            return bl
        # every guard the later assigns fire under, negated, conjoined onto each arm
        blocked = self._complement([b.guards for b in assigns])
        if not blocked:
            return bl
        out: list = []
        for b in tagged:
            for extra in blocked:
                merged = self._and_guards(b.guards, extra)
                if merged is not None:
                    out.append(Branch(guards=merged, value=b.value, tag_guards=b.tag_guards,
                                      neg_matches=b.neg_matches, loc=b.loc))
        out.extend(assigns)                             # ...and the later assign itself, unguarded by us
        return out

    def _complete_case_holds(self, reg: str, bl: list) -> None:
        """Complete the HOLD for a case-assigned register -- it keeps its value wherever no assign fires.
        Two gaps the per-statement collection misses for an FSM register:
          * WITHIN-ARM -- the selector matches an arm but that arm's guards fail (a reg assigned in
            `MULTIPLY_N` only `if (mult_done)` must hold the rest of the arm). Add, per arm, the
            complement of the arm's assign guards under the arm's tag/neg.
          * CROSS-ARM -- the selector matches NONE of the arms the reg is assigned in (a reg assigned
            only in IDLE/MULTIPLY_N/MULTIPLY_D must hold in NORMALIZE/ITERATE/CHECK/DONE). Add one hold
            whose neg-matches are all the assigned arm values. Skipped if the reg is assigned in the
            DEFAULT arm (a neg-match branch already drives the non-explicit selector values).
        Holds are appended (de-duplicated); existing assigns / collected holds are untouched."""
        assigns = [b for b in bl if not (isinstance(b.value, Ref) and b.value.name == reg)]
        seen = {(tuple(sorted(b.guards)), b.tag_guards, b.neg_matches) for b in bl}

        def add(guards, tg, nm) -> None:
            key = (tuple(sorted(guards)), tg, nm)
            if key not in seen:
                seen.add(key)
                bl.append(Branch(guards=tuple(guards), value=Ref(reg), tag_guards=tg, neg_matches=nm))

        by_arm: dict = {}
        for b in assigns:
            by_arm.setdefault((b.tag_guards, b.neg_matches), []).append(b)
        # An UNTAGGED assign (`if (rst) state <= IDLE; else case (state) ...`) fires whatever the
        # selector is, so it is not an "arm" and its complement is not a hold on its own -- under
        # `rst=0` the case arms drive. Completing it in isolation claimed a hold everywhere the arms
        # were driving, which double-valued the register on every transition (Fix 93: `fsm_demo`
        # derived BOTH `idle` and `run` at the same tick). Every hold must therefore ALSO require
        # that no untagged assign fires; `base` is that condition, and `[()]` (no constraint) when
        # there are none -- so a design without an untagged assign is bit-for-bit unchanged.
        untagged = by_arm.pop(((), ()), [])
        base = self._complement([b.guards for b in untagged]) if untagged else [()]
        if base is None:
            return
        for (tg, nm), arm in by_arm.items():                   # WITHIN-ARM: hold where the arm's guards fail
            for t in (self._complement([b.guards for b in arm]) or []):
                for u in base:
                    merged = self._and_guards(t, u)
                    if merged is not None:
                        add(merged, tg, nm)
        tagset = tuple(sorted({tv for b in assigns for tv in b.tag_guards}))
        if tagset and not any(b.neg_matches for b in assigns):  # CROSS-ARM: selector none of the arms
            for u in base:
                add(u, (), tagset)

    @staticmethod
    def _and_guards(a, b) -> tuple | None:
        """Conjoin two (sig, pol) guard conjunctions, preserving `a`'s order and de-duplicating.
        None when they contradict (one signal forced both ways), which drops the term."""
        out = list(a)
        for s, p in b:
            if any(s2 == s and p2 != p for s2, p2 in out):
                return None
            if (s, p) not in out:
                out.append((s, p))
        return tuple(out)

    def _resolve_case_arms(self, reg: str, bl: list) -> list:
        """Apply last-write-wins WITHIN each case arm (branches sharing the same tag/neg guards). An arm
        with an unconditional default AND a guarded override (`err<=0; if(c) err<=1;`) is resolved by
        ``_suppress`` and its now-redundant explicit holds dropped (the default drives the arm). Arms
        without that pattern -- pure case arms -- pass through unchanged (zero churn)."""
        by_arm: dict = {}
        for b in bl:
            by_arm.setdefault((b.tag_guards, b.neg_matches), []).append(b)
        out: list = []
        for arm in by_arm.values():
            assigns = [b for b in arm if not (isinstance(b.value, Ref) and b.value.name == reg)]
            if any(not b.guards for b in assigns) and any(b.guards for b in assigns):
                s = self._suppress(assigns)                        # default + override in this arm
                if s is not None:
                    out.extend(s)                                  # drop the arm's Ref-holds
                    continue
            out.extend(arm)                                        # pure case arm -> unchanged
        return out

    def _definitely_assigned(self, stmt, case_total: bool = False) -> set[str]:
        """Signals assigned on EVERY path through ``stmt`` — the standard definite-assignment
        analysis, and the combinational counterpart of `_assigned_regs` (which is "on SOME path").

        In `always_comb` the difference between the two IS the set of inferred latches: a signal
        the block sometimes writes and sometimes does not retains its old value, which is a
        level-sensitive latch and almost never what the RTL author meant.

        This replaces a SHAPE test — "a Conditional with no else" — that missed every other way
        to leave a path undriven, and silently:

            if (s) y = a; else z = b;      // BOTH y and z latch; there IS an else
            case (sel) 2'd0: begin y=a; z=b; end  default: y = b; endcase   // z latches

        Both translated cleanly, exit 0, with the undriven signal simply UNBOUND — so every
        property over it passed vacuously. Same lesson as the slice-write coverage (Fix 68):
        the question is whether the paths COVER the signal, never what the statement looks like.

        Conservative in the safe direction at each join: a branch whose coverage cannot be
        established contributes nothing, so the analysis under-claims assignment and can only
        over-report latches, never miss one.

        ``case_total`` pretends every `case` is total (as if each had a `default`). The two runs
        differ exactly on the signals whose only gap is a MISSING DEFAULT — which is the D4 case,
        already reported on its own WARNING channel and deliberately still translated. Splitting
        it out here is what keeps this check from silently overruling that decision."""
        return _da_eval(self._da_shape(stmt), case_total)

    def _da_shape(self, stmt) -> tuple:
        """The pyslang statement tree reduced to the PURE SHAPE definite assignment reasons about
        — the only part of it the analysis reads. Everything pyslang-specific stops here.

        Node forms (see `_da_eval`, which is the algorithm, and `Paths.Stmt` in Lean, which is
        the model checked against it):

            ("cond", then, else_or_None)
            ("case", [arms], default_or_None, arms_cover_the_domain)
            ("seq",  [parts])                  -- Block / List: paths run in sequence
            ("loop", body)                     -- constant non-zero trip count, so the body runs
            ("leaf", frozenset(names))         -- an assignment, or nothing
        """
        k = _enum_name(stmt.kind)
        if k == "Conditional":
            return ("cond", self._da_shape(stmt.ifTrue),
                    None if stmt.ifFalse is None else self._da_shape(stmt.ifFalse))
        if k == "Case":
            dflt = getattr(stmt, "defaultCase", None)
            # No default: total only if the arms cover the selector's whole domain. Wildcard
            # (casez/casex) labels and computed labels make that unknowable -> not total.
            wildcard = _enum_name(stmt.condition) in ("WildcardJustZ", "WildcardXOrZ")
            # A WILDCARD case's labels are PATTERNS, not values -- evaluating them as values
            # would trip the x/z-literal refusal (Fix 87), which is about x in VALUE position.
            # So the labels are only read when the coverage question is actually asked.
            cov = None if wildcard else self._case_coverage(
                stmt, [self._match_value(lab) for it in stmt.items for lab in it.expressions])
            return ("case", [self._da_shape(it.stmt) for it in stmt.items],
                    None if dflt is None else self._da_shape(dflt),
                    cov is not None and not cov[0])
        if k == "Block":
            body = stmt.body if hasattr(stmt.body, "__iter__") else [stmt.body]
            return ("seq", [self._da_shape(s) for s in body])
        if k == "List":
            return ("seq", [self._da_shape(s) for s in stmt.list])
        if k in ("ForLoop", "ForeachLoop"):
            # A synthesizable for/foreach has a constant, non-zero trip count (a non-constant one
            # is refused elsewhere), so its body definitely runs.
            return ("loop", self._da_shape(stmt.body))
        return ("leaf", frozenset(self._assigned_regs(stmt)))

    def _assigned_regs(self, stmt) -> set[str]:
        """Register names assigned (nonblocking, plain LHS) anywhere in ``stmt`` -- used to
        synthesize the implicit hold for a Conditional with no else."""
        out: set[str] = set()

        def walk(s) -> None:
            k = _enum_name(s.kind)
            if k == "Conditional":
                walk(s.ifTrue)
                if s.ifFalse is not None:
                    walk(s.ifFalse)
            elif k == "Case":
                for it in s.items:
                    walk(it.stmt)
                if getattr(s, "defaultCase", None) is not None:
                    walk(s.defaultCase)
            elif k == "Block":
                for ss in s.body if hasattr(s.body, "__iter__") else [s.body]:
                    walk(ss)
            elif k == "List":
                for ss in s.list:
                    walk(ss)
            elif k == "ExpressionStatement" and _enum_name(s.expr.kind) == "Assignment":
                left = s.expr.left
                lk = _enum_name(left.kind)
                # A GENVAR-indexed ElementSelect (q[gv] inside a generate) is a per-lane REGISTER --
                # it needs the normal implicit hold (q[e] <= q[e]) like a scalar reg, so add its base.
                if lk == "ElementSelect":
                    gs = self._genvar_select_dims(left)
                    # F16 (2026-08-18): a genvar-indexed write to an UNPACKED ARRAY (`q[i] <= ..` with
                    # `logic [7:0] q [4]`) is a MEMORY write, lowered per cell by the memory path -- adding
                    # its base here made a phantom WORD register `q` (hold + reset) that nothing read,
                    # while the array's reset arm never reached the cells (they only held under reset).
                    if gs is not None and gs[0] not in getattr(self, "_mem_dims", {}):
                        out.add(gs[0])
                    return   # a runtime-indexed memory write self-holds via its own RMW assembly
                # RangeSelect/MemberAccess (slice/field) writes self-hold via their own RMW assembly --
                # exclude them so no spurious whole-reg hold branch.
                if lk in ("RangeSelect", "MemberAccess"):
                    return
                if lk == "Concatenation":
                    # every operand of a concatenation target is a register this block writes, so
                    # each needs its own implicit hold branch
                    for nm_, regw_, toff_, w_, _s, dyn_ in (self._concat_targets(left) or []):
                        if dyn_ is None and toff_ == 0 and w_ == regw_:   # a part/dynamic write
                            out.add(nm_)                                  # self-holds via its RMW
                    return
                name = self._peel(left).symbol.name
                if lk == "NamedValue" and name in self._structs:
                    # a whole-struct write holds each field subsignal (no own atom for the struct)
                    out.update(f"{name}({fn})" for fn, _w, _o in self._structs[name])
                else:
                    out.add(name)

        walk(stmt)
        return out

    def _reset_loop_target(self, body) -> str | None:
        """The unpacked ARRAY a reset loop's body writes (`tab[i] <= C;`), or None if the body is not
        that shape. Used only to decide whether the loop covers the array."""
        s = body
        while s is not None and _enum_name(getattr(s, "kind", "")) in ("Block", "List"):
            items = list(s.body if hasattr(getattr(s, "body", None), "__iter__")
                         else ([s.body] if getattr(s, "body", None) is not None else getattr(s, "list", [])))
            if len(items) != 1:
                return None
            s = items[0]
        if s is None or _enum_name(getattr(s, "kind", "")) != "ExpressionStatement":
            return None
        e = s.expr
        if _enum_name(e.kind) != "Assignment" or _enum_name(e.left.kind) != "ElementSelect":
            return None
        root = self._peel(e.left.value)
        nm = getattr(getattr(root, "symbol", None), "name", None)
        return nm if nm in getattr(self, "_mem_dims", {}) else None

    def _collect_reset_values(self, stmt, rvals: dict[str, int]) -> None:
        """Walk a reset-branch statement, recording reg -> constant reset value."""
        kind = _enum_name(stmt.kind)
        if kind in ("Block",):
            for ss in stmt.body if hasattr(stmt.body, "__iter__") else [stmt.body]:
                self._collect_reset_values(ss, rvals)
        elif kind == "List":
            for ss in stmt.list:
                self._collect_reset_values(ss, rvals)
        elif kind in ("ForLoop", "ForeachLoop"):
            # `if (!rst) for (int i = 0; i < N; i++) tab[i] <= C;` -- an unpacked array cleared cell by
            # cell, which is how an array of REGISTERS is reset (VerilogEval's gshare does exactly this
            # to its PHT). This walk did not descend into a loop, so the reset was recorded NOWHERE:
            # the emitter produced a write rule, hold rules, and NO reset -- with `mem_hold` telling
            # every cell to HOLD under reset, the exact opposite of the RTL. `--strict-coverage` exited
            # 0 with no problem and no warning: a SILENT WRONG (F25, 2026-08-20). F16 fixed the
            # GENERATE form of the same thing; this plain-`for` form was never covered.
            #
            # A loop that does NOT cover the whole address range is not a whole-array reset, so it is
            # refused loudly rather than recorded as one.
            var = self._for_loop_var(stmt) if kind == "ForLoop" else None
            rng = self._for_static_range(stmt, var) if var else None
            body = getattr(stmt, "body", None)
            tgt = self._reset_loop_target(body)
            if tgt is not None and kind == "ForLoop":
                depth = getattr(self, "_mem_dims", {}).get(tgt, (0,))[0]
                if rng is None or rng != (0, depth, 1):
                    self._hard_flags.append((self._loc_expr(stmt), (
                        f"{tgt}: the reset loop does not cover the whole array "
                        f"({'non-constant bounds' if rng is None else f'{rng[0]}..{rng[1] - 1} step {rng[2]}'} "
                        f"of 0..{depth - 1}) -- a PARTIAL reset of an array is not modelled; the cells "
                        f"outside it keep their power-on value (deferred)")))
                    return
            if body is not None and hasattr(body, "kind"):
                self._collect_reset_values(body, rvals)
        elif kind == "ExpressionStatement" and _enum_name(stmt.expr.kind) == "Assignment":
            left = stmt.expr.left
            if _enum_name(left.kind) == "ElementSelect":
                # F16: `q[i] <= C` in the reset branch of a MEMORY (an unpacked array): every cell resets
                # to C -- recorded for the memory-write emitter (a per-cell level force), not as a word
                root = self._peel(left.value if hasattr(left, "value") else left)
                rn = getattr(getattr(root, "symbol", None), "name", None)
                if rn is not None and rn in getattr(self, "_mem_dims", {}):
                    cv = self._const_of(stmt.expr.right)
                    if cv is not None:
                        self._mem_resets = getattr(self, "_mem_resets", {})
                        self._mem_resets[rn] = cv
                return
            if _enum_name(left.kind) == "Concatenation":
                # `{pm, hh, mm, ss} <= 25'h0120000` in a reset branch: each target resets to its OWN
                # slice of the constant (the count_clock reference resets its whole clock this way)
                tg_ = self._concat_targets(left)
                cv = self._const_of(stmt.expr.right)
                if tg_ is not None and cv is not None:
                    for nm_, regw_, toff_, w_, soff_, dyn_ in tg_:
                        if dyn_ is None and toff_ == 0 and w_ == regw_:   # a part/dynamic reset rides
                            rvals[nm_] = (cv >> soff_) & ((1 << w_) - 1)  # its own slice RMW
                return
            if _enum_name(left.kind) == "NamedValue":
                # An ENUM register resets to a TAG, not to the member's number: the reset rule
                # `val(state, idle, T) :- val(rst_n, 0, T)` must speak the tag the transition
                # rules match on. Folding `IDLE` to 0 made the reset value a number no arm
                # matched -- with a `default` arm the FSM recovered one cycle late (and read
                # `busy` wrong during reset), without one it was dark forever after reset.
                rhs = self._peel(stmt.expr.right)
                if (_enum_name(rhs.kind) == "NamedValue"
                        and getattr(getattr(rhs, "symbol", None), "name", None) in self._enum_members):
                    rvals[left.symbol.name] = rhs.symbol.name.lower()
                    return
                cv = self._const_of(stmt.expr.right)
                if cv is None:
                    # A non-constant reset value used to become 0 SILENTLY. It is not a
                    # power-on constant, so refuse rather than invent one.
                    self._hard_flags.append((self._loc_expr(stmt.expr), (
                        f"{left.symbol.name}: reset branch assigns a non-constant value "
                        f"(`{str(getattr(stmt.expr, 'syntax', '')).strip()}`) -- a reset value must "
                        f"be a constant or an enum member (deferred)")))
                    cv = 0
                rvals[left.symbol.name] = cv

    def _mem_guards(self, guards: tuple) -> tuple:
        """The guards of a clocked MEMORY write, plus the block's ASYNC reset deasserted at T.
        The reset branch of `always_ff @(posedge clk or negedge rst_n) if (!rst_n) .. else ..`
        is stripped from the guards (registers carry it as `SeqItem.reset` and the emitter gates
        their update on it), but a memory write in the `else` has no such carrier -- it was
        emitted with its own guards only, so `mem[wp] <= din` WROTE while reset was asserted,
        which the LRM's reset branch (executing at that edge) forbids. Found by the random
        sweep on a FIFO whose reset was pulsed mid-run."""
        r = getattr(self, "_blk_reset", None)
        if r is None or any(g == r.signal for g, _p in guards):
            return tuple(guards)
        return (*guards, (r.signal, 1 if r.active == "low" else 0))

    def _decode_bit_write(self, name: str, vw: int, idx: Expr, iw: int, val: Expr,
                          gt: tuple, tag_guards, neg_matches, loc: Loc) -> None:
        """`name[idx] <= val` with a RUNTIME idx, as one GUARDED single-bit write per position --
        `name[k] <= (idx == k) ? val : name[k]`. The slice-write RMW composes the (disjoint) bits, so
        the target stays an ordinary register: word reads, the implicit hold and the power-on policy
        all follow with no special case downstream. Shared by the bare `q[i] <= b` statement and by a
        concatenation target with a runtime-indexed operand (`{q[i], r} <= v`)."""
        iref = idx if isinstance(idx, (Ref, Const)) else self._hoist_word(idx, iw, loc)
        bit = val if isinstance(val, (Ref, Const)) else self._hoist_bit(val, loc)
        for k in range(vw):
            g = self._hoist_bit(BinOp("eq", iref, Const(k, iw), 1), loc)
            self._record_slice(name, vw, k, 1, bit, (*gt, (g.name, 1)), tag_guards, neg_matches, loc)

    def _concat_targets(self, left) -> list | None:
        """`{a, b, c}` as an assignment TARGET -> [(name, regwidth, target_offset, width, source_offset)],
        or None if an operand is not a signal or a CONSTANT part-select of one.

        SystemVerilog fills a concatenation MSB-first: the leftmost operand takes the high bits, so
        `{pm, hh, mm, ss} <= v` means pm <= v[24], hh <= v[23:16], mm <= v[15:8], ss <= v[7:0]. Each
        target is then an ordinary register write of a SLICE of the source -- the same distribution a
        whole-struct write makes across its fields, which is why both emitters need no change.

        An operand may be a whole signal or a constant part-select of one (`{q[3:0], r, q[7:4]} <= v`,
        legal synthesizable SV that Icarus and Verilator both accept): a whole signal becomes an
        ordinary register write, a part-select becomes a SLICE write, and the existing RMW machinery
        assembles them. A runtime index or a non-signal operand returns None so the caller refuses by
        NAME rather than lowering half of it. (Before this existed, a concatenation target reached
        `.symbol` on a ConcatenationExpression and the whole always-block failed with a leaked
        AttributeError -- loud, but naming a Python error instead of the construct. Found on
        VerilogEval's count_clock reference, `{pm,hh,mm,ss} <= 25'h0120000`, 2026-08-19.)"""
        if _enum_name(left.kind) != "Concatenation":
            return None
        parts = []
        for op in left.operands:
            w = getattr(getattr(op, "type", None), "bitWidth", 1) or 1
            k = _enum_name(op.kind)
            if k == "RangeSelect":                       # `{q[3:0], r} <= v` -- a PART of a target
                base = self._peel(op.value)
                bounds = self._range_bounds(op)
                if _enum_name(base.kind) != "NamedValue" or bounds is None:
                    return None
                hi, lo = bounds
                regw = getattr(getattr(op.value, "type", None), "bitWidth", hi + 1) or (hi + 1)
                parts.append((base.symbol.name, regw, lo, hi - lo + 1, None))
                continue
            if k == "ElementSelect":                     # `{q[3], r} <= v` -- one bit of a target
                base = self._peel(op.value)
                if _enum_name(base.kind) != "NamedValue":
                    return None
                idx = self._const_of(op.selector)
                regw = getattr(getattr(op.value, "type", None), "bitWidth", None)
                if idx is not None:
                    parts.append((base.symbol.name, regw or (idx + 1), idx, 1, None))
                    continue
                # a RUNTIME index: the SOURCE split is still static (every operand of a concatenation
                # has a fixed width), only WHERE the bit lands is dynamic -- so it decodes exactly like
                # a bare `q[i] <= b` (_decode_bit_write). Refused as "no fixed bit position" until
                # 2026-08-19, which confused the source offset with the target offset.
                if regw is None or regw > _MAX_DECODED_BITS:
                    return None
                iw = getattr(getattr(op.selector, "type", None), "bitWidth", None) or 32
                parts.append((base.symbol.name, regw, None, 1, (self._lower_expr(op.selector), iw)))
                continue
            po = self._peel(op)
            if _enum_name(po.kind) != "NamedValue":
                return None
            parts.append((po.symbol.name, w, 0, w, None))   # a whole signal: the part IS the register
        src = sum(w for _n, _rw, _to, w, _d in parts)
        out = []
        for name, regw, tgt_off, w, dyn in parts:        # leftmost = most significant
            src -= w
            out.append((name, regw, tgt_off, w, src, dyn))
        return out

    def _lower_nb_assign(self, expr, guards, tag_guards, neg_matches, brs, locs, writes, clock) -> None:
        if _enum_name(expr.kind) != "Assignment":
            return
        left = expr.left
        # the target, for a COMPOUND assignment's `LValueReference` on the right (see _lower_expr)
        saved_lv, self._lvalue_node = getattr(self, "_lvalue_node", None), left
        try:
            self._lower_nb_assign_body(expr, left, guards, tag_guards, neg_matches, brs, locs, writes, clock)
        finally:
            self._lvalue_node = saved_lv

    def _lower_nb_assign_body(self, expr, left, guards, tag_guards, neg_matches, brs, locs, writes, clock) -> None:
        # A loop control increment (`i = i + 1`) writes the genvar itself -- it is loop control, not
        # state. Lane-rolling fans `i` over the address domain, so swallow the increment (no write).
        lp = self._peel(left)
        if _enum_name(lp.kind) == "NamedValue" and lp.symbol.name in self._genvars:
            return
        gt = tuple(guards)
        loc = self._loc_expr(expr)
        if self._lhs_index_uses_genvar_arith(left):
            self._hard_flags.append((loc, (
                f"write target index uses the loop variable arithmetically "
                f"(`{str(getattr(left, 'syntax', '')).strip()}`): only a bare `sig[i]` lane-rolls; "
                f"an arithmetic index would fold to one iteration (deferred -- shift the range and "
                f"index with the bare variable, or unroll explicitly)")))
            return
        gs = self._genvar_select_dims(left)  # y[i]...[i] in a procedural for -> indexed lane write
        lane_w, lane_off = None, 0
        if gs is None:                       # y[i*W +: W] -> the same, with W-bit lanes
            ls = self._genvar_lane_slice(left)
            if ls is not None:
                gs, lane_w = (ls[0], 1), ls[1]
        if gs is None:                       # y[i+1] <= .. -> head lane I+1
            os_ = self._genvar_offset_select(left)
            if os_ is not None:
                gs, lane_off = (os_[0], 1), os_[1]
        # The RHS is lowered AFTER the lane target is registered (see below), so a lane write
        # lowers it inside its branch; every other LHS shape lowers it here.
        val = None if gs is not None else self._lower_expr(expr.right)
        if gs is not None:
            base, dims = gs
            if lane_w is None and lane_off == 0:
                self._check_genvar_index_order(left, gs)
            root = self._select_root(left)   # `q` for q[i][j] (peel(left.value).symbol is None there)
            if root is not None and getattr(getattr(root, "type", None), "isUnpackedArray", False):
                # q[i] / q[i][j] <= .. in a loop -> lane-roll the MEMORY over addr(mem, I[, J]).
                self._check_array_rank(root.name, dims)
                adims = self._mem_dims.get(root.name, (1,))
                vs = self._genvar_select_vars(left)             # loop vars, outer (leftmost) first
                bounds = self._mem_lane_bounds(vs, dims, adims, loc)   # per-dim (bound, start)
                if bounds is None:
                    return
                hi, lo = bounds
                val = self._lower_expr(expr.right)
                self._lane_mem_writes += 1
                r = getattr(self, "_blk_reset", None)
                mres = getattr(self, "_mem_resets", {}).get(root.name)
                writes.append(MemWrite(mem=root.name, addrs=tuple(LaneIdx(p) for p in range(dims)),
                                       data=val, guards=self._mem_guards(gt), clock=clock, loc=loc,
                                       lane_rolled=True, lane_hi=tuple(hi), lane_lo=tuple(lo),
                                       reset=(r.signal, 1 if r.active == "low" else 0, mres) if (r is not None and mres is not None) else None))
                return
            # mark as INDEXED only when the index is actually needed.  Three conditions that mean
            # the signal IS per-lane: (a) the RHS expression references the genvar, (b) there are
            # guards (even without the genvar in the RHS, guards may be per-lane — e.g. `if setb[e]`),
            # or (c) there are tag_guards. Only a completely guard-free, index-free RHS is a broadcast.
            # Registered BEFORE the RHS is lowered so a neighbouring-lane read of the target
            # (`q[i] <= q[i-1]`, a shift chain) lowers as a lane read, not a word bit-select.
            is_broadcast = (not guards and not tag_guards
                            and not self._expr_uses_genvar(expr.right))
            if not is_broadcast:
                self._lane_dims[base] = max(self._lane_dims.get(base, 0), dims)
                self._note_lane_elem_w(base, lane_w or getattr(getattr(left, "type", None),
                                                               "bitWidth", 1) or 1)
                # The loop's index range travels with the register: the SeqItem takes the domain
                # literal `I = lo..hi-1` from it. Two loops writing one lane register over
                # DIFFERENT ranges would need per-branch domains -- refuse rather than pick one.
                rng = (self._lane_lo, self._lane_hi, self._lane_step, lane_off)
                prev = self._reg_lane_range.get(base)
                if prev is not None and prev != rng:
                    self._hard_flags.append((loc, (
                        f"{base}: lane-written by two loops over different index sets "
                        f"({prev} and {rng} as (start, bound, step, head offset)) -- one index "
                        f"set per lane register is modelled (deferred)")))
                    return
                self._reg_lane_range[base] = rng
            reg = base
            val = self._lower_expr(expr.right)
        elif _enum_name(left.kind) == "RangeSelect":   # q[hi:lo] <= v -> clocked slice write (RMW)
            base = self._peel(left.value)
            bounds = self._range_bounds(left)
            if bounds is None:
                raise NotImplementedError("clocked write to a dynamic part-select (runtime base)")
            hi, lo = bounds
            regw = getattr(getattr(left.value, "type", None), "bitWidth", hi + 1) or (hi + 1)
            self._record_slice(base.symbol.name, regw, lo, hi - lo + 1, val, gt, tag_guards, neg_matches, loc)
            return
        elif _enum_name(left.kind) == "MemberAccess":
            uv = self._union_view(left)
            if uv is not None:
                # A PACKED UNION member write. A union's members all overlap the SAME bits (the
                # LRM requires packed-union members to be the same size), so writing a member
                # drives the union's packed WORD -- not a struct-style field subsignal. The READ
                # side already did this via `_union_view`; the write side did not, so
                # `u.word = w` drove `u(word)` while `u.bytes.hi` read `u`. Different atoms:
                # the union was never driven and every reader was silently UNBOUND, with
                # coverage reporting OK.
                uroot, uoff, uw = uv
                if uoff == 0 and uw == self._unions[uroot]:
                    reg = uroot                                   # whole-width member -> the word
                else:
                    self._record_slice(uroot, self._unions[uroot], uoff, uw, val, gt,
                                       tag_guards, neg_matches, loc)
                    return
            else:
                inner = self._peel(left.value)
                if (_enum_name(inner.kind) == "ElementSelect"          # arr[i].field <= v (cell RMW)
                        and _enum_name(self._peel(inner.value).kind) == "NamedValue"
                        and self._peel(inner.value).symbol.name in self._struct_mems):
                    if clock == "":
                        # COMBINATIONAL `arr[i].field = v` has no cell-RMW path: the clocked
                        # form splices the field into the cell word against its PREVIOUS value,
                        # which a combinational cell does not have. Emitting the whole-cell copy
                        # the fall-through produced dropped the field offset entirely, so two
                        # field writes both drove the whole cell and it went MULTI-VALUED with
                        # `coverage: OK` (Fix 77). Refuse until the comb form is built.
                        self._hard_flags.append((loc, (
                            f"combinational write to `{self._peel(inner.value).symbol.name}"
                            f"[..].{left.member.name}`: a field of an unpacked array-of-struct "
                            f"element. Only the CLOCKED form is modelled (the cell RMW needs a "
                            f"previous value); use always_ff, or drive the whole element")))
                        return
                    self._record_cell_field_write(left, val, self._mem_guards(gt), clock, loc, writes)
                    return
                if _enum_name(inner.kind) == "MemberAccess":           # q.a.x <= v (nested field, RMW)
                    root, members = self._member_chain(left)
                    target = f"{root}({members[0].name})"
                    regw = next(w for fn, w, _o in self._structs[root] if fn == members[0].name)
                    off = sum(m.bitOffset for m in members[1:])
                    w = getattr(getattr(left, "type", None), "bitWidth", 1) or 1
                    self._record_slice(target, regw, off, w, val, gt, tag_guards, neg_matches, loc)
                    return
                reg = self._member_name(left)                          # q.field <= v -> whole subsignal write
        elif (_enum_name(left.kind) == "ElementSelect"
              and _enum_name(self._peel(left.value).kind) == "MemberAccess"):
            # s.arr[i] <= v, where `arr` is a PACKED array member of a struct. The field lives
            # as ONE packed subsignal `s(arr)`, so this is a SLICE write at index*elemWidth --
            # the exact mirror of the read side, which already emits
            #   val(o0, V1, T) :- val(s(arr), V0, T), V1 = @slc(V0, 0, 8).
            # Before this it fell into the memory-write branch below, where `_select_root` has
            # no `.name` for a MemberAccess base and raised AttributeError.
            base = self._peel(left.value)
            root, members = self._member_chain(base)
            field = members[0].name
            target = f"{root}({field})"
            fld = next((w for fn, w, _o in self._structs.get(root, ()) if fn == field), None)
            idx = self._const_of(left.selector)
            ew = getattr(getattr(left, "type", None), "bitWidth", None)
            if fld is None or idx is None or not ew:
                raise NotImplementedError(
                    f"write to struct array member {target}[…] needs a constant index and a "
                    f"packed field (got index={idx!r}, field_width={fld!r}, elem_width={ew!r})")
            self._record_slice(target, fld, idx * ew, ew, val, gt, tag_guards, neg_matches, loc)
            return
        elif _enum_name(left.kind) == "ElementSelect":  # mem[a] / mem[a][b] <= data (dynamic address)
            root = self._select_root(left)
            idxs = self._select_indices(left)
            if (len(idxs) == 1 and root.name not in getattr(self, "_mem_dims", {})
                    and self._const_of(left.selector) is None):
                # `q[i] <= b` with a RUNTIME index on a PACKED VECTOR -- legal synthesizable SV (it
                # A CONSTANT index (`y[0] <= a[0]`) is NOT this: it names one fixed lane, and the path
                # below emits exactly that lane's rule -- which is how a lane signal written partly by a
                # generate and partly by a bare statement composes. Decoding it would replace one lane
                # rule with a whole-width guarded decoder and collide with the generate's lanes
                # (`test_lane_roll_over_a_partial_index_set[gs1]` caught this).
                # becomes a decoder driving per-bit enables). It used to take the memory path below,
                # which emits addressed cells `val(q(A), ..)` and `mem_hold(q, A, T)` for a signal that
                # is NOT an array: `addr(q, A)` was never emitted, so the hold could not fire and the
                # cells had no power-on -- caught loudly by the power-on walk ("STATE WITH NO POWER-ON
                # POLICY"), so the construct simply did not translate (2026-08-19).
                #
                # Lowered as what the hardware is: one GUARDED single-bit write per position,
                # `q[k] <= (i == k) ? b : q[k]`. The existing slice-write RMW composes them (the
                # regions are disjoint), so `q` stays an ordinary register -- word reads, the implicit
                # hold and the power-on policy all follow with no special case anywhere downstream.
                vw = getattr(getattr(left.value, "type", None), "bitWidth", None)
                iw = getattr(getattr(left.selector, "type", None), "bitWidth", None) or 32
                if vw is None:
                    self._hard_flags.append((loc, f"{root.name}: runtime-indexed write to a vector of "
                                                  f"unknown width (deferred)"))
                    return
                if vw > _MAX_DECODED_BITS:
                    self._hard_flags.append((loc, (
                        f"{root.name}[{str(getattr(left.selector, 'syntax', '')).strip()}] <= ..: a "
                        f"runtime-indexed write decodes into one guarded write per bit, and {vw} bits "
                        f"exceeds the {_MAX_DECODED_BITS}-bit budget (deferred -- index a memory, or "
                        f"write the bits explicitly)")))
                    return
                self._decode_bit_write(root.name, vw, idxs[0], iw, val, gt, tag_guards, neg_matches, loc)
                return
            self._check_array_rank(root.name, len(idxs))
            # note the element write for the mixed-write divert (F22). Deciding the LOWERING ROAD here
            # would be source-order dependent -- `y[0] <= a[0]` written ABOVE a generate that makes `y`
            # a lane signal is processed before `_lane_dims` knows about it, and a constant bit write
            # routed to the slice path on that basis broke four lane tests. The decision belongs where
            # the information is complete, so record the fact and decide after the block is collected.
            self._elem_written = getattr(self, "_elem_written", set())
            self._elem_written.add(root.name)
            r = getattr(self, "_blk_reset", None)
            mres = getattr(self, "_mem_resets", {}).get(root.name)
            writes.append(
                MemWrite(mem=root.name, addrs=tuple(idxs), data=val, guards=self._mem_guards(gt),
                         clock=clock, loc=loc,
                         reset=(r.signal, 1 if r.active == "low" else 0, mres) if (r is not None and mres is not None) else None)
            )
            return
        elif _enum_name(left.kind) == "Concatenation":
            tg_ = self._concat_targets(left)
            if tg_ is None:
                self._hard_flags.append((loc, (
                    "concatenation assignment target with an operand that is neither a signal nor a "
                    f"CONSTANT part-select of one (`{str(getattr(left, 'syntax', '')).strip()}`): a "
                    "runtime index has no fixed bit position to distribute into (deferred -- write the "
                    "parts as separate assignments)")))
                return
            # compute the source ONCE when it is not already a simple term, then slice it per target
            src = val
            if not isinstance(val, (Const, Ref, Tag)):
                src = self._hoist_word(val, sum(w_ for _n, _rw, _to, w_, _so, _d in tg_), loc)
            for nm_, regw_, toff_, w_, soff_, dyn_ in tg_:
                piece = Slice(src, soff_ + w_ - 1, soff_)
                if dyn_ is not None:                           # a RUNTIME-indexed bit of a target
                    self._decode_bit_write(nm_, regw_, dyn_[0], dyn_[1], piece, gt,
                                           tag_guards, neg_matches, loc)
                elif toff_ == 0 and w_ == regw_:               # a WHOLE target: an ordinary write
                    brs.setdefault(nm_, []).append(
                        Branch(guards=gt, value=piece, tag_guards=tuple(tag_guards),
                               neg_matches=tuple(neg_matches), loc=loc))
                    locs.setdefault(nm_, loc)
                else:                                          # a PART of a target: a slice write
                    self._record_slice(nm_, regw_, toff_, w_, piece, gt, tag_guards, neg_matches, loc)
            return
        elif _enum_name(left.kind) == "NamedValue" and left.symbol.name in self._structs:
            # whole-struct clocked write `reg <= src`: distribute the source across the field
            # subsignals (a struct has no own atom -- packed or unpacked, it lives as p(field)).
            # The matching implicit hold is per-subsignal too (see _assigned_regs).
            for fn, w, off in self._structs[left.symbol.name]:
                sub = f"{left.symbol.name}({fn})"
                brs.setdefault(sub, []).append(
                    Branch(guards=gt, value=Slice(val, off + w - 1, off),
                           tag_guards=tuple(tag_guards), neg_matches=tuple(neg_matches), loc=loc))
                locs.setdefault(sub, loc)
            return
        else:
            reg = self._peel(left).symbol.name
        # A 1-bit reg whose GUARDED branch value is a logic EXPRESSION (`if(c) y=a&b;`) can't be read
        # as a single bit term by the seq emitter (it needs on-set/off-set). Hoist the expression to a
        # combinational gcond bit -- then the branch value is a plain Ref the emitter reads directly.
        # Only GUARDED branches: an unconditional 1-bit assign routes to a clean CombItem upstream
        # (no gcond indirection), so leave it alone.
        lwidth = getattr(getattr(expr.left, "type", None), "bitWidth", 1) or 1
        if (gt or tag_guards or neg_matches) and lwidth == 1 and not isinstance(val, (Const, Ref, Tag)):
            self._hoist_ctx = reg
            val = self._hoist_bit(val, loc)
            self._hoist_ctx = ""
        elif (clock and lwidth == 1 and not isinstance(val, (Const, Ref, Tag, Slice, BitSel))
              and not _has_lane_index(val)):
            # An UNGUARDED 1-bit register whose D-input is an EXPRESSION (`q <= ~a;`, `c <= a&b|a&c|b&c;`,
            # `out <= in ^ out;`) -- the comment above assumed these route to a clean CombItem upstream,
            # but they reach the seq emitter, whose `_bit_read` handles only Const/Ref/Slice/BitSel and
            # raised `inline 1-bit register d-expression deferred (use a named wire)`. Hoisting is what
            # the guarded branch already does; the exclusion list is narrower here (Slice/BitSel are
            # bit-readable) so every design that already worked keeps its output byte-for-byte.
            # NEVER when the value carries a LANE INDEX (`q[i] <= q[i-1]` in a generate): hoisting
            # lifts the expression OUT of the lane rule, where `I` is no longer bound -- the emitted
            # rule was unsafe and clingo could not ground it (caught by the gsh shift-chain case).
            # CLOCKED blocks only (`clock` non-empty): in an always_comb an unguarded 1-bit assign
            # already routes to a clean CombItem downstream, and hoisting there put a gcond in front of
            # five corpus designs' output (caught by `regen --check`).
            # Five VerilogEval references were blocked on this alone (2026-08-20).
            self._hoist_ctx = reg
            val = self._hoist_bit(val, loc)
            self._hoist_ctx = ""
        brs.setdefault(reg, []).append(
            Branch(guards=gt, value=val, tag_guards=tuple(tag_guards), neg_matches=tuple(neg_matches),
                   loc=loc))
        locs.setdefault(reg, loc)

