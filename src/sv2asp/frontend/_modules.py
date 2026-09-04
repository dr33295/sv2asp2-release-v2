from __future__ import annotations

import dataclasses
from dataclasses import dataclass, field



from .. import primitives
from ..ir.expr import (BinOp, BitSel, Concat, Cond, Const, Expr, LaneIdx, MemRef, Ref, Slice,
                       UnOp)
from ..ir.internal_clocks import classify_internal_clocks
from ..ir.enumval import _with_x_check, enum_reads_as_numbers
from ..ir.nodes import (
    Branch, CellInfo, Clock, CombItem, DerivedClock, Design, Enum, InferredLatch, LatchItem,
    Loc, Mem, MemRead,
    MemWrite, MuxItem, Param, Reset, SeqItem, Signal, VffItem,
)
from ..ir.types import ElementType, IRType, Kind
from ._common import _BINOP, _enum_name


@dataclass
class LowerCtx:
    """The accumulators every module-lowering function writes into.

    These used to be threaded POSITIONALLY through eight functions. Adding one IR node
    (`latches`) meant editing eight signatures and eight call sites, and produced five
    signature mismatches in a row -- each caught by the suite, but only because the suite is
    thorough. Passing one object makes adding the next node a one-line change, and makes an
    arity mismatch impossible rather than merely detectable."""

    comb: list = field(default_factory=list)
    seq: list = field(default_factory=list)
    muxes: list = field(default_factory=list)
    latches: list = field(default_factory=list)
    vffs: list = field(default_factory=list)
    signals: dict = field(default_factory=dict)
    mems: list = field(default_factory=list)
    writes: list = field(default_factory=list)
    reg_names: set = field(default_factory=set)
    cells: list = field(default_factory=list)
    enums: dict = field(default_factory=dict)
    flagged: list = field(default_factory=list)


class _NotAffine(Exception):
    """A slice bound that is not an affine expression over the lane index."""


class _ModuleMixin:
    """_ModuleMixin: modules methods of PyslangFrontend (split out from the monolith)."""

    def _lower_module(self, top: object) -> Design:
        return self._norm_design(self._lower_body(top.body, top.name))

    # -- clingo-identifier normalization -------------------------------------
    # clingo reads an UPPERCASE- (or underscore-) leading identifier as a VARIABLE; SV allows such
    # names (N_reg, MyBus, _tmp). Emitting them bare makes a constant into a variable (unsafe-variable
    # grounding errors / silent capture). A post-pass over the built IR lowercases the leading char of
    # every identifier COMPONENT of every name -- so a functor/hierarchy term like u_M(Field) becomes
    # u_M(field) with its structure intact. Run on the FINAL IR, before the emitter adds the real clingo
    # variables (V/T/I/A), so it never touches an intended variable. Idempotent.
    def _lower_body(self, body: object, modname: str) -> Design:
        self._scope = body
        self._eval_scope = body  # scope for constant evaluation (switched during inlining)
        saved_mod, self._current_module = getattr(self, "_current_module", ""), modname  # parent of top-level instances
        saved_lanes, self._lane_dims = self._lane_dims, {}
        saved_elemw, self._lane_elem_w = self._lane_elem_w, {}
        saved_gl, self._gen_locals = self._gen_locals, {}                 # per module (the F15 lesson)
        saved_lf, self._lane_fields = self._lane_fields, {}                # lane fields, per module too
        saved_rlr, self._reg_lane_range = self._reg_lane_range, {}   # per module (the F15 lesson)
        saved_ifp, self._iface_ports = self._iface_ports, set()
        saved_domains, self._lane_domains = self._lane_domains, {}
        saved_em, self._enum_members = self._enum_members, set()
        saved_eto, self._enum_type_of = self._enum_type_of, {}
        saved_st, self._structs = self._structs, {}
        saved_un, self._unions = self._unions, {}
        saved_if, self._interfaces = self._interfaces, {}
        saved_sm, self._struct_mems = self._struct_mems, {}
        saved_sfm, self._struct_field_mems = self._struct_field_mems, {}
        saved_pw, self._partials = self._partials, {}
        saved_pfs, self._prim_flop_slices = self._prim_flop_slices, {}
        saved_cs, self._clocked_slices = self._clocked_slices, {}   # clocked slice writes, ACROSS blocks
        params: list[Param] = []
        signals: dict[str, Signal] = {}
        enums: dict[str, Enum] = {}
        mems: list[Mem] = []
        comb: list[CombItem] = []
        seq: list[SeqItem] = []
        muxes: list[MuxItem] = []
        latches: list[LatchItem] = []
        #: the SAME list, reachable from the statement mixin -- `always_latch` lowers to a
        #: LatchItem from `_lower_block`, which does not receive the module's accumulators
        self._latches = latches
        self._inferred_latches: list[InferredLatch] = []   # per-module accumulator
        self._blk_edges = []                              # $rose/$fell, per-module accumulator
        vffs: list[VffItem] = []
        cells: list[CellInfo] = []
        packed: dict[str, tuple[int, ...]] = {}  # packed multi-D signal -> declared per-dim widths
        writes: list[MemWrite] = []
        reads: list[MemRead] = []  # noqa: F841 (combinational reads modeled as CombItem)
        flagged: list[tuple[Loc, str]] = []
        # gated/derived clocks from ICG primitives (accumulates over THIS module). Saved/restored
        # because _lower_body recurses for submodule flattening -- a sub's local derived clocks must
        # not leak into the parent's list (the parent re-adds them instance-qualified via sub.derived_clocks).
        saved_derived, self._derived = getattr(self, "_derived", []), []
        saved_stub_rules, self._stub_rules = getattr(self, "_stub_rules", []), []
        port_dir: dict[str, str] = {}
        reg_names: set[str] = set()
        # One object carrying every accumulator, so adding an IR node is a one-line change here
        # instead of eight signatures and eight call sites. The lists/dicts are SHARED with the
        # locals above -- the ctx wraps them, it does not copy them.
        ctx = LowerCtx(comb=comb, seq=seq, muxes=muxes, latches=latches, vffs=vffs,
                       signals=signals, mems=mems, writes=writes, reg_names=reg_names,
                       cells=cells, enums=enums, flagged=flagged)
        # sinks for hoisted sub-expressions (nested ternaries, compound if-conditions) so they
        # are available for continuous assigns too, not only procedural blocks. Saved/restored
        # because _lower_body recurses for submodule flattening.
        saved_bc, saved_bs = self._blk_comb, self._blk_signals
        self._blk_comb, self._blk_signals = comb, signals

        # First pass: ports give direction; collect declarations.
        dir_map = {"In": "input", "Out": "output", "InOut": "inout", "Ref": "ref"}
        for m in body:
            k = _enum_name(m.kind)
            if k == "Port":
                port_dir[m.name] = dir_map.get(_enum_name(m.direction), _enum_name(m.direction).lower())
            elif k == "InterfacePort" and self._modular:
                self._iface_ports.add(m.name)          # `b.sig` through THIS port is a modport access,
                # not a reach into a child (see `_hier_ref`'s modular hierarchical-read recording)
                # MODULAR only: a module lowered STANDALONE must declare its interface-port signals
                # b(sig) with the type from the modport, so shape analysis sizes them right (flat
                # instead aliases them onto the connected interface instance during flattening). The
                # modport member's internalSymbol is the interface variable carrying the width.
                conn = getattr(m, "connection", None)
                mp = conn[1] if conn and len(conn) >= 2 else getattr(m, "modport", None)
                for x in (mp or ()):
                    isym = getattr(x, "internalSymbol", None)
                    sn = f"{m.name}({x.name})"
                    if isym is not None and sn not in signals:
                        signals[sn] = Signal(name=sn, irtype=self._irtype(isym.type), is_reg=False,
                                             is_port=False, direction=None, initial=None, loc=self._loc(m))

        def _dispatch(m) -> None:
            k = _enum_name(m.kind)
            if k == "Parameter":
                self._param_names_seen.add(m.name)     # for the unapplied-override check
                params.append(Param(name=m.name.lower(), value=self._cv_int(m.value), expr=None, loc=self._loc(m)))
            elif k in ("Net", "Variable"):
                t = m.type
                if getattr(t, "isUnpackedArray", False):
                    cur, dims = t, []                       # walk the nested unpacked dimensions
                    while getattr(cur, "isUnpackedArray", False):
                        cur = cur.canonicalType             # resolve typedef aliases (TypeAliasType has no .range)
                        rng = cur.range  # ConstantRange e.g. [3:0]
                        dims.append(abs(rng.left - rng.right) + 1)
                        cur = cur.elementType
                    cur = cur.canonicalType                 # innermost cell: resolve an aliased element type too
                    dims = tuple(dims)                       # cur is now the innermost cell type
                    self._mem_depth[m.name] = dims[0]
                    self._mem_dims[m.name] = dims
                    is_struct = getattr(cur, "isStruct", False)
                    if len(dims) > 2:
                        flagged.append((self._loc(m),
                                        f"{m.name}: {len(dims)}-D unpacked array (>=3 dims) deferred"))
                        return
                    if len(dims) > 1 and is_struct:
                        flagged.append((self._loc(m),
                                        f"{m.name}: 2-D array of structs deferred (1-D cell layout only)"))
                        return
                    mems.append(
                        Mem(
                            name=m.name,
                            elem=ElementType(f"{m.name}_elem", self._kind(cur), cur.bitWidth,
                                             four_state=bool(getattr(cur, "isFourState", False))),
                            addr_width=max(1, (dims[0] - 1).bit_length()),
                            depth=dims[0],
                            loc=self._loc(m),
                            dims=dims,
                        )
                    )
                    if is_struct:   # array of structs: a word cell; arr[i].field is a slice of the cell
                        self._struct_mems[m.name] = [
                            (f.name, f.type.bitWidth, f.bitOffset) for f in cur.canonicalType]
                elif _enum_name(t.canonicalType.kind) == "PackedUnionType" and m.name not in self._unions:
                    # packed union -> ONE WORD signal; member accesses are slice/views of it (all
                    # members overlay the same bits). Reinterpretation, not disjoint subsignals.
                    self._unions[m.name] = t.bitWidth
                    if m.name not in signals:
                        signals[m.name] = Signal(name=m.name, irtype=IRType(Kind.BIT, t.bitWidth,
                                                 sv_base=self._decl_base(t),
                                                 four_state=bool(getattr(t, "isFourState", False))),
                                                 is_reg=False, is_port=m.name in port_dir,
                                                 direction=port_dir.get(m.name), initial=None,
                                                 loc=self._loc(m))
                elif getattr(t, "isStruct", False) and m.name not in self._structs:
                    # packed struct -> decompose into per-field subsignals p(field); the whole
                    # struct relates to its fields by concat (read) / slice (write) via bit_offset.
                    layout: list[tuple[str, int, int]] = []
                    for f in t.canonicalType:
                        if getattr(f.type, "isUnpackedArray", False):
                            # a struct field that is an unpacked array -> a struct-field MEMORY s(arr)
                            # (its own addr domain + functor cells val(s(arr(A)), V, T)); not a packed slice.
                            self._make_struct_field_mem(m.name, f, mems, flagged, self._loc(m))
                            continue
                        fname = f"{m.name}({f.name})"
                        layout.append((f.name, f.type.bitWidth, f.bitOffset))
                        if fname not in signals:
                            # A struct PORT's fields are ports: the boundary crosses them, and
                            # they are what the design actually reads and drives (a struct has
                            # no atom under its bare name). They carried `is_port=False,
                            # direction=None`, so no `port(...)` fact was declared for them in
                            # EITHER mode -- the under-declaration `compose.find_dark_reads`
                            # names, which is why it needed an `extern` side-channel fed by a
                            # loc-text heuristic to avoid reporting an input struct's fields as
                            # dark. Inheriting the parent's direction states it instead.
                            _pd = port_dir.get(m.name)
                            signals[fname] = Signal(name=fname,
                                                    irtype=self._irtype(f.type),
                                                    is_reg=False, is_port=_pd is not None,
                                                    direction=_pd,
                                                    initial=None, loc=self._loc(m))
                    self._structs[m.name] = layout
                elif m.name not in signals:  # dedup Net/Variable for same name
                    enum_type = None
                    if getattr(t, "isEnum", False):
                        # LOWERCASED: a clingo constant starts lowercase; `typedef enum {...} States` emitted
                        # verbatim made `enum_value(States, s, 0)` -- `States` a VARIABLE, 18 unsafe rules (loud;
                        # found on VerilogEval's fancytimer reference, 2026-08-19). Members were already lowered;
                        # the cast path (`_decl_base`) already lowered the type; this declaration walk did not.
                        enum_type = (getattr(t, "name", None) or f"{m.name}_enum").lower()
                        self._enum_type_of.setdefault(str(getattr(t, "canonicalType", t)), enum_type)
                        if enum_type not in enums:
                            members = tuple((mem.name.lower(), self._cv_int(mem.value))
                                            for mem in t.canonicalType)
                            enums[enum_type] = Enum(name=enum_type, members=members)
                            self._enum_members |= {mem.name for mem in t.canonicalType}
                    signals[m.name] = Signal(
                        name=m.name,
                        irtype=self._irtype(t),
                        is_reg=False,
                        is_port=m.name in port_dir,
                        direction=port_dir.get(m.name),
                        initial=None,
                        loc=self._loc(m),
                        enum_type=enum_type,
                    )
                    pd = self._packed_dims(t)            # packed multi-D: record the declared shape
                    if len(pd) >= 2:                     # (>=2 dims; type/3 keeps the flattened width)
                        packed[m.name] = pd
                    init = getattr(m, "initializer", None)
                    if init is not None:
                        # `wire x = expr;` carries its driver as the net's initializer (pyslang emits NO
                        # separate ContinuousAssign for it) -- it is a CONTINUOUS assignment, lower it at T.
                        # A VARIABLE initializer is instead a power-on value (`logic x = 5;`) -- an
                        # `initial`-style construct, OUTSIDE the supported RTL convention -> flag, never drop.
                        if k == "Net":
                            self._try_lower(
                                lambda m=m, init=init: comb.append(CombItem(
                                    lhs=m.name, rhs=self._lower_expr(init, top=True), loc=self._loc(m))),
                                m, "net declaration initializer (continuous assign)", flagged)
                        else:
                            flagged.append((self._loc(m), f"{m.name}: variable declaration initializer "
                                            "(power-on value) -- `initial`-style init is out of scope; "
                                            "drive it from reset"))
            elif k == "ContinuousAssign":
                self._try_lower(lambda m=m: comb.extend(self._lower_assign(m, writes)),
                                m, "continuous assign", flagged)
            elif k == "ProceduralBlock":
                self._try_lower(lambda m=m: self._lower_block(m, comb, seq, writes, reg_names, signals, flagged),
                                m, "procedural block", flagged)
            elif k == "Instance":
                self._try_lower(lambda m=m: self._lower_instance(
                    m, ctx),
                    m, "instance", flagged)
            elif k == "InstanceArray":  # sub u[N](...) -> ONE lane-rolled rule-set (the array index is the lane)
                self._try_lower(lambda m=m: self._lower_instance_array(
                    m, ctx),
                    m, "instance array", flagged)
            elif k == "GenerateBlockArray":  # for-generate over a vector -> rolled lane rules
                gv = self._generate_instances_genvar(m)
                nested = self._nested_instance_generate(m) if gv is None else None
                if gv is not None:           # `for(i) sub u(.x(d[i]))` -> lane-roll like sub u[N]
                    self._try_lower(lambda m=m, gv=gv: self._lower_generate_instances(
                        m, gv, ctx), m, "generate instances", flagged)
                elif nested is not None:     # `for(i) for(j) sub u(.x(a[i][j]))` -> 2-D lane-roll
                    self._try_lower(lambda m=m, nz=nested: self._lower_nested_generate_instances(
                        m, *nz, ctx), m, "nested generate instances", flagged)
                else:
                    self._try_lower(lambda m=m: self._lower_generate(m, _dispatch, flagged),
                                    m, "generate", flagged)
            elif k == "GenerateBlock" and not getattr(m, "isUninstantiated", False):
                for sub in m:        # if/case-generate: inline only the TAKEN branch (elaborated)
                    _dispatch(sub)
            elif k == "UninstantiatedDef":   # a cell with NO module definition -- but it may be a
                cell = getattr(m, "definitionName", None) or "?"   # library PRIMITIVE (ACME_FF, VCMUX,
                spec = primitives.lookup(cell)                     # ...) -> lower via the schema, §2.10
                if spec is not None:
                    self._try_lower(lambda m=m, spec=spec: self._lower_uninst_primitive(
                        m, spec, ctx),
                        m, "primitive (uninstantiated def)", flagged)
                else:                                              # a real missing module -> fail loud
                    flagged.append((self._loc(m), f"undefined instance {getattr(m, 'name', '?')} of "
                                    f"'{cell}' (no module definition or primitive stub in scope)"))
            # Property/Sequence (SVA) are the verification layer -- classified `property` by the
            # span (not a gap), so no explicit handling here.

        for m in body:
            _dispatch(m)
        # flop-slice coalescing runs FIRST: a reg driven by both a flop and a comb constant tie folds
        # the comb bits into the flop RMW (and removes them from _partials), so the comb assembler
        # below sees only the purely-combinational partials.
        self._assemble_clocked_slices(seq, reg_names, flagged)    # RMW slice writes, merged across blocks
        self._assemble_prim_flop_slices(seq, reg_names, flagged)  # coalesce per-bit primitive flops
        self._assemble_partials(comb, flagged)   # reconstruct words written via slice-writes
        self._assemble_lane_fields(comb, flagged)  # one lane definition per word stitched from affine fields

        # mark registers
        signals = {
            n: (Signal(**{**s.__dict__, "is_reg": True}) if n in reg_names else s)
            for n, s in signals.items()
        }
        # A GENERATE-LOCAL declaration (`for (genvar i ..) begin : g  logic t; assign t = ..; end`) is
        # PER-ITERATION in SV: `t` inside `g[i]` is a different net for every i. In the lane model it is
        # a lane signal of the loop's extent -- `val(t(I), V, T)` -- whose WORD is N copies of the
        # declared width. It used to be one module-level net: absorbed into a lane group only when
        # its body happened to read a lane by a bare `x[i]` (the closure), and otherwise a single
        # WORD `t` given one value per iteration -- multi-valued, i.e. UNSAT with `t34`, "no
        # counterexample" -- as `logic gnt__e0; assign gnt__e0 = !any[i-1];` was (found by the
        # spec2rtl lane print, with F17). Per-iteration scope DEFINES the lane; the width follows.
        for n, ext in self._gen_locals.items():
            s = signals.get(n)
            if s is None or n in self._structs or "(" in n:
                continue
            w = s.irtype.width if isinstance(s.irtype.width, int) else 1
            signals[n] = Signal(**{**s.__dict__, "irtype": IRType(s.irtype.kind, ext * w, sv_base=s.irtype.sv_base,
                                                                  four_state=s.irtype.four_state)})
        lane_dims_local, self._lane_dims = self._lane_dims, saved_lanes
        lane_elemw_local, self._lane_elem_w = self._lane_elem_w, saved_elemw
        self._gen_locals = saved_gl
        self._lane_fields = saved_lf
        self._reg_lane_range = saved_rlr
        self._iface_ports = saved_ifp
        lane_domains_local, self._lane_domains = self._lane_domains, saved_domains
        self._enum_members = saved_em
        self._enum_type_of = saved_eto
        self._structs = saved_st
        self._unions = saved_un
        self._interfaces = saved_if
        self._struct_mems = saved_sm
        self._struct_field_mems = saved_sfm
        self._partials = saved_pw
        self._prim_flop_slices = saved_pfs
        self._clocked_slices = saved_cs
        self._blk_comb, self._blk_signals = saved_bc, saved_bs
        self._current_module = saved_mod
        derived_local, self._derived = self._derived, saved_derived   # restore parent's accumulator
        stub_rules_local, self._stub_rules = self._stub_rules, saved_stub_rules  # restore parent's accumulator
        # collect the full clock structure up front: free (input) clocks + gated/derived clocks (ICG).
        derived_names = {dc.name for dc in derived_local}
        base_clocks = {it.clock for it in seq if not it.combinational and it.clock
                       and it.clock not in derived_names}
        base_clocks |= {w.clock for w in writes if w.clock and w.clock not in derived_names}
        base_clocks |= {dc.base for dc in derived_local}
        clocks = (*[Clock(c) for c in sorted(base_clocks)],
                  *[Clock(dc.name, derived=True, base=dc.base, gate=dc.gate) for dc in derived_local])
        # every enum read in a NUMERIC position becomes EnumVal -- once, for every consumer (ir/enumval.py);
        # an `x` used where a VALUE is required is refused here; and an INTERNAL-SIGNAL clock is
        # classified into an edge-derived clock domain here (F27) -- so BOTH emitters see all three
        return classify_internal_clocks(_with_x_check(enum_reads_as_numbers(Design(
            name=modname,
            params=tuple(params),
            signals=tuple(signals.values()),
            mems=tuple(mems),
            clocks=clocks,
            resets=(),
            comb=tuple(comb),
            edges=tuple(self._blk_edges),
            seq=tuple(seq),
            mem_writes=tuple(writes),
            mem_reads=(),
            muxes=tuple(muxes),
            latches=tuple(latches),
            inferred_latches=tuple(self._inferred_latches),
            vffs=tuple(vffs),
            lane_signals=tuple(sorted(lane_dims_local)),
            lane_dims=dict(lane_dims_local),
            lane_elem_w=dict(lane_elemw_local),
            lane_domains=dict(lane_domains_local),
            enums=tuple(enums.values()),
            cells=tuple(cells),
            packed_dims=dict(packed),
            flagged=tuple([*flagged, *self._unbound_stub_problems(),
                           *self._unapplied_override_problems(),
                           *self._unused_intake_problems(getattr(self, "_compiled_files", []))]),
            warned=tuple(getattr(self, '_warns', []) or []),
            derived_clocks=tuple(derived_local),
            stub_rules=tuple(stub_rules_local),
        ))))

    # -- continuous assign ---------------------------------------------------
    def _lower_assign(self, m: object, writes: list) -> list[CombItem]:
        a = m.assignment
        left = a.left
        loc = self._loc(m)
        if _enum_name(left.kind) == "Concatenation":
            # a CONCAT LHS `{a, b[hi:lo], ...} = rhs`: split the rhs across the targets, MSB-first.
            # Hoist rhs to a temp word so each target reads a plain slice; then lower each operand
            # assignment through the normal LHS machinery (plain net / part-select / member).
            total = getattr(getattr(a.right, "type", None), "bitWidth", None)
            if total is None:
                raise NotImplementedError("concat-LHS assign with non-constant total width")
            rhs = self._lower_expr(a.right, top=True)
            if not isinstance(rhs, (Ref, Const)):
                rhs = self._hoist_word(rhs, total, loc)
            out: list[CombItem] = []
            off = total
            for op in left.operands:              # operands are MSB-first
                w = getattr(getattr(op, "type", None), "bitWidth", 1) or 1
                off -= w
                out.extend(self._assign_lhs_operand(op, Slice(rhs, off + w - 1, off), w, loc))
            return out
        return self._lower_assign_one(a, left, loc, writes)

    def _assign_lhs_operand(self, op, val: Expr, w: int, loc: Loc) -> list[CombItem]:
        """Assign an already-lowered value ``val`` (w-bit) to a single LHS operand ``op`` of a concat
        LHS. Handles a plain net, a plain-vector part-select, and a struct field (the concat-LHS cases
        in real RTL). An unrecognized operand shape flags loud (never silently dropped)."""
        k = _enum_name(op.kind)
        if k == "NamedValue":
            return [CombItem(lhs=op.symbol.name, rhs=val, loc=loc)]
        if k == "MemberAccess":
            return [CombItem(lhs=self._member_name(op), rhs=val, loc=loc)]
        pw = self._partselect_lhs(op)
        if pw is not None:
            target, tw, poff, pw_ = pw
            self._record_partial_expr(target, tw, poff, pw_, val, loc)
            return []
        raise NotImplementedError(f"concat-LHS operand {k} (unsupported target shape)")

    def _mem_lane_bounds(self, vs: list, dims: int, adims: tuple, loc) -> tuple[list, list] | None:
        """Per-dimension (EXCLUSIVE bound, START) of a lane-rolled MEMORY write `q[i][j] <= ..`,
        from the active loop nest: `hi` None = the loop covers that whole dimension; `lo` 0 = the
        canonical start. Shared by the generate and procedural paths; `_mem_partition` turns
        both ends into the write condition and the complementary holds (`Mem.lean`)."""
        stack = dict(self._loop_lane_stack)
        his, los = [], []
        for p in range(dims):
            b = stack.get(vs[p]) if p < len(vs) else None
            lo, hi, step = b if b is not None else (0, None, 1)
            if step != 1:
                # The memory write/hold partition (`_mem_partition`, `Mem.lean`) knows a window,
                # not a stride; a strided memory loop is refused rather than rolled over the
                # cells in between.
                self._hard_flags.append((loc, (
                    f"loop over a memory with stride {step} (`{vs[p]} += {step}`): a memory "
                    f"lane-roll models a contiguous window only (deferred -- unroll explicitly)")))
                return None
            his.append(None if (hi is not None and p < len(adims) and hi >= adims[p]) else hi)
            los.append(lo)
        return his, los

    # ------------------------------------------------------------------ lane FIELDS
    # A generate write whose target is a FIELD of a lane's word at a position that may move
    # with the genvar -- `pp[i][((i-1)*2)+2 +: 65]`, the way every Booth partial-product array
    # is stitched (a field report, 2026-09-03) -- and, the same machinery, a constant field
    # `y[i][3:0]`. Each field is recorded; at the module epilogue the fields of one word are
    # checked DISJOINT and COVERING over the loop's own range (a numeric check: the range is
    # elaboration-constant) and composed into ONE lane definition, the word being the OR of
    # every field masked and shifted to its position, the position an expression over the
    # lane index the emitter renders as the rule's own `I`. A field whose WIDTH moves with
    # the genvar is accepted in one form only: a single bit replicated to exactly fill it
    # (`{(61-((i-1)*2)){s[i]}}`, the sign extension), which is the bit gating a fill mask.

    def _lane_field_target(self, left):
        """`(base, lo_ir, hi_ir, w, wtot)` if `left` is `base[gv][<range>]` on a packed 2-D
        signal with both bounds affine in the in-scope genvar (constants included); `w` is the
        field width when it is the same for every iteration, else None. None if not this shape."""
        lk = _enum_name(getattr(left, "kind", None) or "")
        if not self._genvars or lk not in ("RangeSelect", "ElementSelect"):
            return None
        # the lane roller's own shapes come first: a pure genvar-select chain (`match[i][j]`, a
        # two-level lane write), the byte-lane idiom and the neighbouring-lane offset are not
        # fields -- a bare genvar is affine, and without this the field parser stole the
        # corpus's 2-D CAM (the regen gate, 2026-09-04)
        if (self._genvar_select_dims(left) is not None or self._genvar_lane_slice(left) is not None
                or self._genvar_offset_select(left) is not None):
            return None
        inner = self._peel(left.value)
        if _enum_name(inner.kind) != "ElementSelect":
            return None
        gs = self._genvar_select_dims(inner)
        if gs is None or gs[1] != 1:
            return None
        if lk == "ElementSelect":
            # `pp[i][127] = s`: a ONE-bit field at a constant or affine position (2026-09-04)
            base = self._select_root(inner)
            if base is None or getattr(getattr(base, "type", None), "isUnpackedArray", False):
                return None
            wtot = getattr(getattr(inner, "type", None), "bitWidth", None)
            if not wtot:
                return None
            try:
                lo = self._affine_ir(left.selector)
            except _NotAffine:
                return None
            return gs[0], lo, lo, 1, wtot
        base = self._select_root(inner)
        if base is None or getattr(getattr(base, "type", None), "isUnpackedArray", False):
            return None
        wtot = getattr(getattr(inner, "type", None), "bitWidth", None)
        if not wtot:
            return None
        sk = getattr(getattr(left, "selectionKind", None), "name", "Simple")
        try:
            if sk == "IndexedUp":
                w = self._const_of(left.right)
                if w is None:
                    return None
                lo = self._affine_ir(left.left)
                hi = BinOp("add", lo, Const(w - 1, 32), 32)
            elif sk == "IndexedDown":
                w = self._const_of(left.right)
                if w is None:
                    return None
                hi = self._affine_ir(left.left)
                lo = BinOp("sub", hi, Const(w - 1, 32), 32)
            else:
                hi, lo = self._affine_ir(left.left), self._affine_ir(left.right)
                ws = {self._eval_affine(hi, i) - self._eval_affine(lo, i) + 1 for i in self._lane_range()}
                w = ws.pop() if len(ws) == 1 else None
        except _NotAffine:
            return None
        return gs[0], lo, hi, w, wtot

    def _affine_ir(self, e):
        """The bound `e` as IR over the lane index: Const, LaneIdx, and add/sub/mul of those.
        Anything else raises _NotAffine (the caller then leaves the target to the refusal)."""
        cv = self._const_of(e)
        if cv is not None and not self._expr_uses_genvar(e):
            return Const(cv, 32)
        p = self._peel(e)
        k = _enum_name(p.kind)
        if k == "NamedValue" and p.symbol.name in self._genvars and p.symbol.name in self._genvar_order:
            return LaneIdx(self._genvar_order.index(p.symbol.name))
        if k == "BinaryOp" and _BINOP.get(_enum_name(p.op)) in ("add", "sub", "mul"):
            return BinOp(_BINOP[_enum_name(p.op)], self._affine_ir(p.left), self._affine_ir(p.right), 32)
        raise _NotAffine(str(getattr(p, "syntax", "")))

    @staticmethod
    def _eval_affine(ir, i: int) -> int:
        if isinstance(ir, Const):
            return ir.value
        if isinstance(ir, LaneIdx):
            return i
        if isinstance(ir, BinOp):
            a, b = _ModuleMixin._eval_affine(ir.left, i), _ModuleMixin._eval_affine(ir.right, i)
            return {"add": a + b, "sub": a - b, "mul": a * b}[ir.op]
        raise _NotAffine(repr(ir))

    def _lane_range(self):
        return range(self._lane_lo, self._lane_hi, self._lane_step or 1)

    def _record_lane_field(self, lf, right, loc) -> None:
        base, lo, hi, w, wtot = lf
        if w is not None:
            val = self._lower_expr(right, top=True)
            field = BinOp("shl", BinOp("and", val, Const((1 << w) - 1, wtot), wtot), lo, wtot)
        else:
            # a width that moves with the genvar: a CONSTANT fill (`'0`, `'1`) or ONE bit
            # replicated to exactly fill [hi:lo] (the sign extension)
            r = self._peel(right)
            unit = None
            cv = self._const_of(r) if not self._expr_uses_genvar(r) else None
            if cv is not None:
                one = Const(1, wtot)
                fill = BinOp("sub", BinOp("shl", one, BinOp("add", hi, Const(1, 32), 32), wtot),
                             BinOp("shl", one, lo, wtot), wtot)
                if cv == 0:
                    field = Const(0, wtot)
                elif cv == (1 << (getattr(getattr(r, "type", None), "bitWidth", 0) or 0)) - 1:
                    field = fill
                else:
                    raise NotImplementedError(
                        f"lane field `{base}[i][hi:lo]` whose WIDTH moves with the genvar holds the constant "
                        f"{cv}: only all-zeros or all-ones fills a moving width")
                rec = (lo, hi, w, field, loc, (self._lane_lo, self._lane_hi, self._lane_step or 1), wtot)
                self._lane_fields.setdefault(base, []).append(rec)
                return
            if _enum_name(r.kind) == "Replication":
                u = r.concat
                if _enum_name(u.kind) == "Concatenation" and len(list(u.operands)) == 1:
                    u = list(u.operands)[0]
                u = self._peel(u)
                if (getattr(getattr(u, "type", None), "bitWidth", None) or 0) == 1:
                    try:
                        cnt = self._affine_ir(r.count)
                        if all(self._eval_affine(cnt, i) == self._eval_affine(hi, i) - self._eval_affine(lo, i) + 1
                               for i in self._lane_range()):
                            unit = self._lower_expr(u, top=True)
                    except _NotAffine:
                        unit = None
            if unit is None:
                raise NotImplementedError(
                    f"lane field `{base}[i][hi:lo]` whose WIDTH moves with the genvar: only a single bit "
                    f"replicated to exactly fill the field is lowered (the sign-extension shape); this "
                    f"value is not that")
            one = Const(1, wtot)
            fill = BinOp("sub", BinOp("shl", one, BinOp("add", hi, Const(1, 32), 32), wtot),
                         BinOp("shl", one, lo, wtot), wtot)
            # the fill GATED by the bit: fill * bit (the bit is 0 or 1), which the word cascade
            # computes exactly at the word width -- a Cond inside arithmetic is what it refuses
            field = BinOp("mul", fill, unit, wtot)
        rec = (lo, hi, w, field, loc, (self._lane_lo, self._lane_hi, self._lane_step or 1), wtot)
        self._lane_fields.setdefault(base, []).append(rec)

    def _assemble_lane_fields(self, comb, flagged) -> None:
        """One lane definition per RUN of lanes that share a field set. A word's fields may come
        from several generate ranges -- a conditional generate inside the loop is partitioned
        into runs, and a first-lane special case is written by its own block -- so the fields
        are grouped PER LANE by which ranges contain it, checked disjoint and covering per lane,
        and emitted once per maximal run of consecutive lanes with the same field set (a field
        report, 2026-09-04: `lane fields written from generates with different ranges`)."""
        for base, recs in self._lane_fields.items():
            wtots = {r[6] for r in recs}
            loc = recs[0][4]
            if len(wtots) != 1:
                flagged.append((loc, f"{base}: lane fields of different word widths"))
                continue
            wtot = wtots.pop()
            lanes = sorted({i for r in recs for i in range(r[5][0], r[5][1], r[5][2])})
            per_lane: dict = {}
            bad = None
            for i in lanes:
                fs = tuple(k for k, r in enumerate(recs) if i in range(r[5][0], r[5][1], r[5][2]))
                covered = [0] * wtot
                for k in fs:
                    lo, hi = recs[k][0], recs[k][1]
                    a, b = self._eval_affine(lo, i), self._eval_affine(hi, i)
                    if a < 0 or b >= wtot or b < a:
                        bad = f"lane {i}: field [{b}:{a}] is outside the {wtot}-bit word"
                        break
                    for q in range(a, b + 1):
                        if covered[q]:
                            bad = f"lane {i}: bit {q} is written by two fields"
                            break
                        covered[q] = 1
                    if bad:
                        break
                if bad:
                    break
                if not all(covered):
                    bad = f"lane {i}: bit(s) {[q for q, c in enumerate(covered) if not c][:6]} are written by no field"
                    break
                per_lane[i] = fs
            if bad:
                flagged.append((loc, f"{base}: the lane fields must be disjoint and cover the word -- {bad}"))
                continue
            self._lane_dims[base] = max(self._lane_dims.get(base, 0), 1)
            self._note_lane_elem_w(base, wtot)
            # runs of consecutive lanes (step 1) with the same field set -> one definition each
            run_start, run_fs = None, None
            def emit(lo_i, hi_i, fs):
                rhs = recs[fs[0]][3]
                for k in fs[1:]:
                    rhs = BinOp("or", rhs, recs[k][3], wtot)
                comb.append(CombItem(lhs=base, rhs=rhs, loc=recs[fs[0]][4], lane_hi=hi_i + 1, lane_lo=lo_i, lane_step=1))
            prev = None
            for i in lanes:
                fs = per_lane[i]
                if run_start is not None and (fs != run_fs or i != prev + 1):
                    emit(run_start, prev, run_fs)
                    run_start = None
                if run_start is None:
                    run_start, run_fs = i, fs
                prev = i
            if run_start is not None:
                emit(run_start, prev, run_fs)
        self._lane_fields = {}

    def _lower_assign_one(self, a, left, loc, writes):
        lf = self._lane_field_target(left)
        if lf is not None:
            # a FIELD of a lane's word at a position that may move with the genvar
            # (`pp[i][((i-1)*2)+2 +: 65]`): recorded now, composed into ONE lane definition per
            # word at the module epilogue (`_assemble_lane_fields`)
            self._record_lane_field(lf, a.right, loc)
            return []
        if self._lhs_index_uses_genvar_arith(left):
            raise NotImplementedError(
                f"write target index uses the genvar arithmetically, in a form that is not lowered "
                f"(`{str(getattr(left, 'syntax', '')).strip()}`): a bare `sig[i]` lane-rolls, and a "
                f"field of a lane's word at an AFFINE position (`sig[i][a*i+b +: W]`, `[hi:lo]` with "
                f"both bounds affine, or constants) composes; anything else would fold to one "
                f"iteration (deferred -- index with the bare genvar, or unroll explicitly)")
        # a per-lane write y[gv]...[gv] inside a generate nest: drop the indices, record # of dims.
        # `y[i*W +: W]` (the byte-lane idiom) is the same write with W-bit lanes.
        gs = self._genvar_select_dims(left)
        lane_w, lane_off = None, 0
        if gs is None:
            ls = self._genvar_lane_slice(left)
            if ls is not None:
                gs, lane_w = (ls[0], 1), ls[1]
        if gs is None:                       # y[i+1] = .. -> head lane I+1 (the carry-chain shape)
            os_ = self._genvar_offset_select(left)
            if os_ is not None:
                gs, lane_off = (os_[0], 1), os_[1]
        if gs is not None:
            base, dims = gs
            if lane_w is None and lane_off == 0:
                self._check_genvar_index_order(left, gs)
            root = self._select_root(left)
            if root is not None and getattr(getattr(root, "type", None), "isUnpackedArray", False):
                # assign mem[i]...[i] in a generate -> a COMBINATIONAL memory write (clock="") lane-rolled
                # over addr(mem, I[, J]). A memory is ADDRESSED (runtime address domain), NOT a compile-time
                # lane functor: the genvar rides addr(mem, I), broadcast operands stay whole words. Mirrors
                # the clocked path. _check_array_rank rejects a packed bit-select indexed by a genvar
                # (mem[i][bit] on a 1-D memory: index rank != array rank) -> a loud flag, not a silent miss.
                self._check_array_rank(root.name, dims)
                # Per-dimension iteration bound, exactly as the procedural `for` path computes it:
                # the generate may cover only PART of the array's address domain, and the cells it
                # does not write must stay undriven (`None` = covers the whole dimension).
                adims = self._mem_dims.get(root.name, (1,))
                vs = self._genvar_select_vars(left)          # genvars, outer (leftmost) first
                bounds = self._mem_lane_bounds(vs, dims, adims, loc)
                if bounds is None:
                    return []
                ghi, glo = bounds
                self._lane_mem_writes += 1
                writes.append(MemWrite(mem=root.name, addrs=tuple(LaneIdx(p) for p in range(dims)),
                                       data=self._lower_expr(a.right, top=True), guards=(), clock="",
                                       loc=loc, lane_rolled=True, lane_hi=tuple(ghi),
                                       lane_lo=tuple(glo)))
                return []
            # only mark as INDEXED if the RHS actually depends on the genvar index;
            # a broadcast (ppSgn_M1[i] = same_for_all_i) stays a plain word signal
            # to avoid an unbound lane variable I in the emitted rule head.
            # Registered BEFORE the RHS is lowered: a chain `c[i] = c[i-1] & p[i]` reads its own
            # target at a neighbouring lane, and `_lower_expr` decides lane-read (`ElemSel`)
            # versus word bit-select by whether the base is a lane signal YET -- lowering the
            # RHS first made `c[i-1]` a bit-select of the WORD read through the LANE atom.
            if self._expr_uses_genvar(a.right):
                self._lane_dims[base] = max(self._lane_dims.get(base, 0), dims)
                self._note_lane_elem_w(base, lane_w or getattr(getattr(left, "type", None),
                                                               "bitWidth", 1) or 1)
            rhs_expr = self._lower_expr(a.right, top=True)
            return [CombItem(lhs=base, rhs=rhs_expr, loc=loc, lane_hi=self._lane_hi,
                             lane_lo=self._lane_lo, lane_step=self._lane_step, lane_off=lane_off)]
        sfm = self._struct_field_mem_select(left)
        if sfm is not None:    # assign s.arr[idx] = v -> a combinational memory cell write on s(arr)
            mem, sel = sfm
            writes.append(MemWrite(mem=mem, addrs=(self._lower_expr(sel),),
                                   data=self._lower_expr(a.right, top=True), guards=(), clock="", loc=loc))
            return []
        if _enum_name(left.kind) == "NamedValue" and left.symbol.name in self._structs:
            # whole-struct write: distribute the source across the field slices
            src = self._lower_expr(a.right, top=True)
            return [CombItem(lhs=f"{left.symbol.name}({fn})", rhs=Slice(src, off + w - 1, off), loc=loc)
                    for fn, w, off in self._structs[left.symbol.name]]
        if _enum_name(left.kind) == "HierarchicalValue":
            # writing an interface signal through a MODPORT is legitimate (a shared net); reaching DOWN
            # into a submodule's own signal (`top.u.cnt = d`) is a backdoor driver that bypasses the
            # port list -- it double-drives a reg the submodule already owns. Reject it (fail-loud).
            if _enum_name(getattr(left, "symbol", left).kind) != "ModportPort":
                raise NotImplementedError(
                    f"hierarchical WRITE across a module boundary "
                    f"({str(getattr(left, 'syntax', '')).strip()}) -- a backdoor driver bypassing the "
                    "port list (double-drives a reg the submodule owns); drive it through a port")
            return [CombItem(lhs=self._hier_name(left), rhs=self._lower_expr(a.right, top=True), loc=loc)]
        if _enum_name(left.kind) == "MemberAccess":
            uv = self._union_view(left)
            if uv is not None:                          # write THROUGH a union member view
                root, off, w = uv
                if off == 0 and w == self._unions[root]:
                    self._hoist_ctx = root
                    rhs = self._lower_expr(a.right, top=True)
                    self._hoist_ctx = ""
                    return [CombItem(lhs=root, rhs=rhs, loc=loc)]
                self._record_partial(root, self._unions[root], off, w, a.right, loc)  # u.f.hi = ...
                return []
            if _enum_name(self._peel(left.value).kind) == "MemberAccess":   # p.a.x = ... (nested)
                root, members = self._member_chain(left)
                target = f"{root}({members[0].name})"
                tw = next(w for fn, w, _o in self._structs[root] if fn == members[0].name)
                off = sum(m.bitOffset for m in members[1:])
                w = getattr(getattr(left, "type", None), "bitWidth", 1) or 1
                self._record_partial(target, tw, off, w, a.right, loc)
                return []
            lhs_name = self._member_name(left)
            self._hoist_ctx = lhs_name
            rhs = self._lower_expr(a.right, top=True)
            if isinstance(rhs, Cond) and (getattr(getattr(left, "type", None), "bitWidth", 0) == 1):
                rhs = self._hoist_bool_arms(rhs, loc)           # G27a: boolean arms are named bits
            self._hoist_ctx = ""
            return [CombItem(lhs=lhs_name, rhs=rhs, loc=loc, lane_hi=self._lane_hi,
                             lane_lo=self._lane_lo, lane_step=self._lane_step)]
        # a plain-vector PART-SELECT LHS: `assign x[hi:lo] = ...` (or a single-bit `x[i] = ...`).
        # Route it through the slice-write / partial machinery so the disjoint slices reassemble the
        # whole word (untouched bits flagged if uncovered). A struct/union/array select was handled above.
        pw = self._partselect_lhs(left)
        if pw is not None:
            target, tw, off, w = pw
            # hoist the RHS to a temp so the reassembled word (a Concat of parts) always sees a plain
            # Ref -- a top-level ternary/compound word expr can't sit as a raw Concat part.
            self._hoist_ctx = target
            rhs = self._lower_expr(a.right, top=True)
            if not isinstance(rhs, (Ref, Const, Slice, BitSel)):
                rhs = self._hoist_word(rhs, w, loc)
            self._hoist_ctx = ""
            self._record_partial_expr(target, tw, off, w, rhs, loc)
            return []
        lhs_name = left.symbol.name
        self._hoist_ctx = lhs_name
        rhs = self._lower_expr(a.right, top=True)
        if isinstance(rhs, Cond) and (getattr(getattr(left, "type", None), "bitWidth", 0) == 1):
            rhs = self._hoist_bool_arms(rhs, loc)               # G27a: boolean arms are named bits
        self._hoist_ctx = ""
        return [CombItem(lhs=lhs_name, rhs=rhs, loc=loc, lane_hi=self._lane_hi,
                         lane_lo=self._lane_lo, lane_step=self._lane_step)]

    def _partselect_lhs(self, left):
        """If ``left`` is a plain-vector part-select ``x[hi:lo]`` / bit-select ``x[i]`` over a NamedValue
        root, return (root_name, root_width, lo, width); else None. Non-constant bounds -> None (flag
        falls through to the generic path). Struct/union/array-cell selects are handled by the caller."""
        k = _enum_name(left.kind)
        if k == "RangeSelect":
            base = self._peel(left.value)
            if _enum_name(base.kind) != "NamedValue":
                return None
            bnds = self._range_bounds(left)
            if bnds is None or bnds[0] is None:
                return None
            hi, lo = bnds
            rw = getattr(getattr(base, "type", None), "bitWidth", hi + 1) or (hi + 1)
            return (base.symbol.name, rw, lo, hi - lo + 1)
        if k == "ElementSelect":
            base = self._peel(left.value)
            if _enum_name(base.kind) == "MemberAccess":
                # `s.arr[i]` -- a PACKED array member of a struct. The field lives as ONE packed
                # subsignal `s(arr)`, which is itself a signal in the model, so the write is a
                # slice of THAT: offset i*elemWidth, width elemWidth. This mirrors the read side,
                # which already emits `val(o0,V1,T) :- val(s(arr),V0,T), V1 = @slc(V0,0,8).`
                # Without this the base fell through as a non-NamedValue and the caller raised
                # AttributeError ('ElementSelectExpression' has no attribute 'symbol').
                root, members = self._member_chain(base)
                field = members[0].name
                fw = next((w for fn, w, _o in self._structs.get(root, ()) if fn == field), None)
                idx = self._const_of(left.selector)
                ew = getattr(getattr(left, "type", None), "bitWidth", None)
                if fw is None or idx is None or not ew:
                    return None            # dynamic index / unpacked field -> generic path flags
                return (f"{root}({field})", fw, idx * ew, ew)
            if _enum_name(base.kind) != "NamedValue":
                return None
            # a memory / unpacked-array cell write is handled elsewhere (isUnpackedArray); only a
            # packed-vector bit-select `x[i]` reaches here.
            if getattr(getattr(base, "type", None), "isUnpackedArray", False):
                return None
            idx = self._const_of(left.selector)
            if idx is None:
                return None
            rw = getattr(getattr(base, "type", None), "bitWidth", idx + 1) or (idx + 1)
            # the ELEMENT width: 1 for a plain vector, W for a packed multi-dimensional
            # `logic [N-1:0][W-1:0] y` -- `y[0]` is bits [W-1:0], not bit 0. It was taken as 1
            # bit, which turned `assign y[0] = b0` on a packed 2-D into a one-bit slice write.
            ew = getattr(getattr(left, "type", None), "bitWidth", 1) or 1
            return (base.symbol.name, rw, idx * ew, ew)
        return None

    def _make_struct_field_mem(self, struct: str, f, mems, flagged, loc) -> None:
        """A struct field that is an unpacked array -> a struct-field MEMORY named `s(arr)`: a normal
        Mem with its own addr domain, addressed exactly like a top-level memory (the emit leaf-injects
        the address into the functor: val(s(arr(A)), V, T)). 1-D scalar-cell arrays only; else flag."""
        memname = f"{struct}({f.name})"
        cur, dims = f.type, []
        while getattr(cur, "isUnpackedArray", False):
            cur = cur.canonicalType
            rng = cur.range
            dims.append(abs(rng.left - rng.right) + 1)
            cur = cur.elementType
        cur = cur.canonicalType
        if len(dims) != 1 or getattr(cur, "isStruct", False):
            flagged.append((loc, f"{memname}: struct field array (only 1-D scalar-cell arrays supported)"))
            return
        self._mem_depth[memname] = dims[0]
        self._mem_dims[memname] = (dims[0],)
        self._struct_field_mems.setdefault(struct, {})[f.name] = memname
        mems.append(Mem(name=memname, depth=dims[0], dims=(dims[0],), loc=loc,
                        addr_width=max(1, (dims[0] - 1).bit_length()),
                        elem=ElementType(f"{struct}_{f.name}_elem", self._kind(cur), cur.bitWidth,
                                         four_state=bool(getattr(cur, "isFourState", False)))))

    def _struct_field_mem_select(self, e):
        """If ``e`` is `s.arr[idx]` where `s.arr` is a struct-field memory, return (mem_name, idx_expr);
        else None. The select is ElementSelect(MemberAccess(NamedValue(s), arr), idx)."""
        if _enum_name(e.kind) != "ElementSelect":
            return None
        base = self._peel(e.value)
        if _enum_name(base.kind) != "MemberAccess":
            return None
        root = self._peel(base.value)
        if _enum_name(root.kind) != "NamedValue":
            return None
        mem = self._struct_field_mems.get(root.symbol.name, {}).get(base.member.name)
        return (mem, e.selector) if mem is not None else None

    def _record_partial(self, target: str, width: int, off: int, w: int, val_e, loc: Loc) -> None:
        """Record a slice-write ``target[off+w-1:off] = val`` (a union member or nested struct field).
        Collected per target; `_assemble_partials` reconstructs the whole word from the slices."""
        self._partials.setdefault(target, (width, []))[1].append(
            (off, w, self._lower_expr(val_e, top=True), loc))

    def _record_partial_expr(self, target: str, width: int, off: int, w: int, val: Expr, loc: Loc) -> None:
        """Like ``_record_partial`` but the value is an ALREADY-lowered IR Expr (a plain-vector
        part-select LHS whose RHS was hoisted upstream)."""
        self._partials.setdefault(target, (width, []))[1].append((off, w, val, loc))

    def _assemble_prim_flop_slices(self, seq: list, reg_names: set, flagged: list) -> None:
        """Coalesce part-select PRIMITIVE flop writes into ONE SeqItem per register. Several cells each
        drive a sub-range of the same reg (`clkenDup_D4[0]`, `[1]`, ...); emitting one SeqItem each would
        multi-drive the whole reg. Merge all slices into a single read-modify-write value (each slice's
        enable self-holds via ``_build_rmw``); untouched bits retain the prior reg value.

        A reg driven PARTLY by a flop (clocked, e.g. `Fi1_D4[9:0]`) and partly by a combinational
        constant assign (`Fi1_D4[39:10]='0'`) shows up in BOTH this collector and ``_partials``. The
        constant bits never change, so they are correctly modeled as HELD register bits: fold the
        matching ``_partials`` slices into this RMW (unguarded), and drop them from ``_partials`` so
        the comb assembler doesn't also emit (and mis-flag) them."""
        for reg, (regw, clk, reset, reset_value, parts) in self._prim_flop_slices.items():
            loc0 = parts[0][4]
            slices = [(off, w, d, ()) if not guards else (off, w, d, guards)
                      for off, w, d, guards, _l in parts]
            if reg in self._partials:                      # fold in the comb constant/other bits
                _cw, cparts = self._partials.pop(reg)
                slices += [(off, w, v, ()) for off, w, v, _l in cparts]
            value = self._build_rmw(Ref(reg), regw, slices, loc0, flagged)
            if value is None:
                continue
            reg_names.add(reg)
            seq.append(SeqItem(reg=reg, clock=clk, reset=reset,
                               branches=(Branch(guards=(), value=value),),
                               has_hold=False, loc=loc0, reset_value=reset_value))

    def _assemble_partials(self, comb: list, flagged: list) -> None:
        """Reconstruct each partially-written word from its slice-writes. Slices that tile the word
        disjointly emit ``target = {parts}`` (a Concat -> OR-of-shifts). UNCOVERED bit ranges are
        TIED TO 0 (over-width scratch nets / explicit ``[hi:lo]='0`` ties are common in real RTL) and
        the auto-tied ranges are recorded in the rule's provenance comment -- clean grounding, never
        silent. A genuine OVERLAP (two writers to one bit) is a real multi-driver bug -> flagged."""
        for target, (width, parts) in self._partials.items():
            ordered = sorted(parts, key=lambda p: p[0])   # by offset ascending
            loc = parts[-1][3]
            # A LANE signal (genvar-indexed somewhere in the module) written at CONSTANT lanes
            # beside its lane-rolled writes -- the base case of a chain, `assign c[0] = cin;`
            # next to `for (i = 1; ...) c[i] = c[i-1] & p[i]` -- is a partial lane loop of extent
            # one per part: `val(c(I), V, T) :- I = 0..0, ...`, not a word reassembled from
            # slices (which would have tied the loop's lanes to 0 and been refused as a per-lane
            # non-copy). Each part must be exactly one element wide at an element boundary; any
            # other slice of a lane signal keeps the word path (and its refusal).
            ew = self._lane_elem_w.get(target, 1) or 1
            if target in self._lane_dims:
                if self._lane_dims[target] == 1 and all(
                        w == ew and off % ew == 0 for off, w, _v, _l in ordered):
                    for off, w, v, pl in ordered:
                        comb.append(CombItem(lhs=target, rhs=v, loc=pl,
                                             lane_lo=off // ew, lane_hi=off // ew + 1))
                    continue
                # Any other slice of a LANE signal has no per-lane reading: the word assembly
                # below would be emitted as a per-lane rule (the value of the whole word in
                # every lane) -- refuse rather than that.
                flagged.append((loc, f"partial write to lane signal {target}: a slice that is not "
                                     f"a whole lane at a lane boundary (deferred)"))
                continue
            # detect overlap (a real error) while walking; fill gaps with Const(0, gapw).
            overlap = False
            filled: list[tuple[int, int, Expr]] = []      # (off, w, value)
            tied: list[str] = []
            pos = 0
            for off, w, v, _l in ordered:
                if off < pos:
                    overlap = True
                    break
                if off > pos:                              # a gap [pos, off) -> tie to 0
                    filled.append((pos, off - pos, Const(0, off - pos)))
                    tied.append(f"[{off - 1}:{pos}]")
                filled.append((off, w, v))
                pos = off + w
            if overlap:
                flagged.append((loc, f"partial write to {target}: overlapping slices "
                                     "(multi-driver, not modeled)"))
                continue
            if pos < width:                                # top gap [pos, width) -> tie to 0
                filled.append((pos, width - pos, Const(0, width - pos)))
                tied.append(f"[{width - 1}:{pos}]")
            # Concat is MSB-first: highest offset first
            cparts = tuple((v, w) for off, w, v in sorted(filled, key=lambda p: -p[0]))
            tie_note = f"  [auto-tied to 0: {', '.join(tied)}]" if tied else ""
            tloc = Loc(file=loc.file, line=loc.line, text=(loc.text or target) + tie_note)
            comb.append(CombItem(lhs=target, rhs=Concat(cparts), loc=tloc))

    # -- clocked partial (slice) writes -> read-modify-write (untouched bits retain) -----
    def _range_bounds(self, e) -> tuple[int, int] | None:
        """(hi, lo) constant bit bounds of a RangeSelect, handling `+:`/`-:`; None if non-constant."""
        sk = getattr(getattr(e, "selectionKind", None), "name", "Simple")
        if sk == "Simple":
            hi, lo = self._const_of(e.left), self._const_of(e.right)
            return (hi, lo) if hi is not None and lo is not None else None
        b, w = self._const_of(e.left), self._const_of(e.right)
        if b is None or w is None:
            return None
        return (b + w - 1, b) if sk == "IndexedUp" else (b, b - w + 1)

    def _record_slice(self, reg: str, regw: int, off: int, w: int, val, g, tg, nm, loc: Loc) -> None:
        """Record a clocked slice write ``reg[off+w-1:off] <= val`` (a register part-select or a
        nested struct field). Merged per register into one read-modify-write branch."""
        self._slice_writes.setdefault(reg, (regw, []))[1].append((off, w, val, tuple(g), tg, nm, loc))

    def _guard_cond(self, guards: tuple) -> Expr | None:
        """A 1-bit Expr true iff every ``(sig, pol)`` guard holds (None = unconditional)."""
        e: Expr | None = None
        for sig, pol in guards:
            lit = Ref(sig) if pol == 1 else UnOp("not", Ref(sig), 1)
            e = lit if e is None else BinOp("and", e, lit, 1)
        return e

    #: Guarded slices per inferred latch beyond which the guard-combination split is refused.
    #: Each guarded slice doubles the rule count, so this bounds the emitted program; three is
    #: already well past anything real RTL writes, and exceeding it is announced, not silent.
    _LATCH_GUARD_CAP = 3

    def _latch_slice_variants(self, reg: str, width: int, parts: list, loc: Loc,
                              flagged: list) -> tuple | None:
        """One (guard-literals, value) VARIANT per combination of the guarded slices firing.

        This is the guarded-slice inferred latch (Fix 83). The obvious lowering --
        `guard ? val : reg[region]` -- has to be hoisted into a temp, and that temp reads `reg`
        at the SAME instant as the head, which is a genuine combinational loop (the T2 detector
        catches it, which is how the shape was found). Splitting the RULE on the guard instead
        removes the conditional entirely:

            val(y, Vn, T+1) :- T<k, val(s,1,T+1), <a at T+1>, .., Vn = ..a..      -- s fires
            val(y, Vn, T+1) :- T<k, val(s,0,T+1), val(y,Vo,T), .., Vn = ..Vo[3:0].. -- s holds

        Both guards are read at `T+1`, the instant the head is derived, so exactly one variant
        applies and the schema is single-valued by DESTINATION-GATING -- the same argument that
        makes the async-reset flop and the latch cell single-valued (`Latch.lean`). The held
        region reads `reg` at `T`, so nothing depends on `reg` within one time index.

        Returns None when the shape cannot be split (too many guarded slices, or a guard that is
        not a plain boolean), leaving the caller's loud refusal in place."""
        guarded = [(i, p) for i, p in enumerate(parts) if p[3] or p[4] or p[5]]
        if not guarded or len(guarded) > self._LATCH_GUARD_CAP:
            return None
        for _i, p in guarded:
            if p[4] or p[5] or not p[3]:      # tag guards / negated matches -> not a boolean split
                return None
        variants = []
        for mask in range(1 << len(guarded)):
            lits: list[tuple[str, int]] = []
            slices: list = []
            ok = True
            for pos, (idx, p) in enumerate(guarded):
                fires = bool(mask >> pos & 1)
                for sig, pol in p[3]:
                    lits.append((sig, pol if fires else 1 - pol))
            if not ok:
                return None
            for i, (off, w, val, g, _tg, _nm, _l) in enumerate(parts):
                gi = next((pos for pos, (idx, _p) in enumerate(guarded) if idx == i), None)
                if gi is None:
                    slices.append((off, w, val, ()))          # unconditional: always driven
                elif mask >> gi & 1:
                    slices.append((off, w, val, ()))          # this variant: the slice fires
                else:
                    # ...else the region HOLDS: read it out of the target's PRIOR value. The
                    # emitter retimes reads of the target itself to `T`, so this is the previous
                    # instant and closes no combinational cycle.
                    slices.append((off, w, Slice(Ref(reg), off + w - 1, off), ()))
            v = self._build_rmw(Ref(reg), width, slices, loc, flagged)
            if v is None:
                return None
            variants.append((tuple(lits), v))
        return tuple(variants)

    def _priority_chain(self, writes: list, width: int, fallback: Expr, loc: Loc) -> Expr:
        """Compose guarded writes to ONE target into a value: the LAST write whose guard holds wins,
        an unguarded write replaces everything below it, and when no guard holds the target keeps
        ``fallback`` (its prior value, or the bits of the RMW base). ``writes`` is [(value, guards)]
        in SOURCE order -- nonblocking semantics: the last assignment executed is the one that lands.

        A `Cond` cannot sit inside a word expression as a value term, so every intermediate is hoisted
        to its own combinational net (the frontend does the same for a nested ternary), and a composed
        guard -- an AND of gcond bits -- is hoisted to a single bit, since a Cond selector is one bit."""
        chain: Expr | None = None
        for v, g in writes:
            c = self._guard_cond(g)
            if c is not None and not isinstance(c, Ref):
                c = self._hoist_bit(c, loc)
            if c is None:
                chain = v
                continue
            els = chain if chain is not None else fallback
            if isinstance(els, Cond):
                els = self._hoist_word(els, width, loc)
            chain = Cond(c, v, els, width)
        return chain if chain is not None else fallback

    def _ordered_rmw(self, base: Expr, width: int, writes: list, loc: Loc) -> Expr:
        """The GENERAL read-modify-write: fold every write to the register in SOURCE order, each step
        "replace this region if the guard holds, else keep what we have". This is the LRM's nonblocking
        semantics literally -- the last assignment executed is the one that lands -- so it is correct
        for writes to OVERLAPPING regions, which no per-region composition can express.

        The reference case (VerilogEval count_clock, synthesizable, accepted by Icarus and Verilator):

            if (enable[4] && hh[3:0] == 4'h9) hh[3:0] <= 0;
            else if (enable[4])               hh[3:0] <= hh[3:0] + 1;
            if (enable[4] && hh[7:0] == 8'h12) hh[7:0] <= 8'h1;      // overlaps BOTH of the above
            else if (enable[5])                hh[7:4] <= hh[7:4] + 1;

        Order is what decides: at 0x12 the earlier `hh[3:0]` write is overwritten by the later whole
        `hh[7:0]` one, and the answer is 0x01. Treating the wide write as an RMW *base* would put it
        UNDER the narrow one and give 0x03 -- which is why the disjoint-region form cannot be reused
        here by reordering.

        `_build_rmw` stays the path for DISJOINT regions: it emits the same value in one mask/or
        expression instead of a fold of per-step terms, and keeping it leaves every existing design's
        output byte-identical."""
        cur = base
        for off, w, val, guards, _tg, _nm, _l in writes:
            mask = ((1 << w) - 1) << off
            keep = ((1 << width) - 1) & ~mask
            placed: Expr = val if w == width and off == 0 else BinOp(
                "or",
                BinOp("and", cur, Const(keep, width), width),
                BinOp("shl", val, Const(off, width), width) if off else val,
                width)
            cond = self._guard_cond(guards)
            if cond is not None and not isinstance(cond, Ref):
                cond = self._hoist_bit(cond, loc)
            if cond is None:
                cur = placed
                continue
            self._hoist_ctx = base.name if isinstance(base, Ref) else ""
            # both arms of the Cond must be value TERMS, and `cur` must stay one for the next step
            cur = self._hoist_word(Cond(cond, self._hoist_word(placed, width, loc), cur, width), width, loc)
            self._hoist_ctx = ""
        return cur

    def _build_rmw(self, base: Expr, width: int, slices: list, loc: Loc, flagged: list) -> Expr | None:
        """new = (base & keepmask) | region_1 | ... where each region is `(val << off)`, and a
        CONDITIONAL slice contributes `(guard ? val : base[region]) << off` (so it self-holds when the
        guard is false). ``base`` is the prior reg value (Ref) or a whole-write value. Untouched bits
        keep ``base``; full coverage drops the keep term. Overlap/out-of-range -> flag (None)."""
        fullmask, smask, shifted = (1 << width) - 1, 0, []
        for off, w, val, guards in slices:
            lm = ((1 << w) - 1) << off
            if lm & smask or lm & ~fullmask:
                flagged.append((loc, "slice write: overlapping or out-of-range slices (not modeled)"))
                return None
            smask |= lm
            cond = self._guard_cond(guards)
            # A slice written under SEVERAL guards (`if (!rst && en) q[3:0] <= d`) composes to an AND
            # of bits, which is not a Cond selector -- hoist it, as the chain builder does. Reachable
            # only since a guarded whole write stopped being refused (2026-08-19): before that this
            # combination never got here, and the Cond was emitted as
            # `% UNSUPPORTED (ternary with unsupported selector)` -- loud, and dark downstream.
            if cond is not None and not isinstance(cond, Ref):
                cond = self._hoist_bit(cond, loc)
            # a conditional slice self-holds: hoist `guard ? val : base[region]` to a comb signal so
            # the Cond sits in the word RMW as a plain Ref (like a nested ternary).
            if cond is not None:
                self._hoist_ctx = base.name if isinstance(base, Ref) else ""
            region = val if cond is None else self._hoist_word(
                Cond(cond, val, Slice(base, off + w - 1, off), w), w, loc)
            if cond is not None:
                self._hoist_ctx = ""
            shifted.append(BinOp("shl", region, Const(off, width), width) if off else region)
        ins = shifted[0]
        for s in shifted[1:]:
            ins = BinOp("or", ins, s, width)
        keep = fullmask & ~smask
        if keep:   # partial -> OR in the retained base bits
            return BinOp("or", BinOp("and", base, Const(keep, width), width), ins, width)
        return ins

    def _assemble_slice_writes(self, brs: dict, locs: dict, reg_names: set, comb: bool,
                               flagged: list, clock: str = "", reset=None,
                               reset_values: dict | None = None) -> None:
        """Merge clocked slice writes per register into ONE read-modify-write branch. Each slice is a
        per-region update over a base = the unconditional whole-write value (if any) else the prior reg;
        a conditional slice self-holds (`guard ? val : base[region]`). Combinational slice writes, an
        enum-conditioned slice, or a conditional/multiple whole-write alongside slices -> flag."""
        reset_values = reset_values or {}
        self._slice_blk = getattr(self, "_slice_blk", 0) + 1     # one id per always block
        blk_id = self._slice_blk
        for reg, (regw, parts) in self._slice_writes.items():
            loc0 = parts[0][6]
            if comb:
                # COMBINATIONAL slice writes (`always_comb begin y = '0; y[3:0] = a; … end`) are
                # ordinary RTL, not an error. What decides legality is whether every bit of the
                # target is driven on every path -- exactly the latch question -- NOT the mere
                # presence of a slice write, which is what this used to reject.
                #
                #   * an unconditional whole write in the same block is the BASE, and the slices
                #     override it (`y = '0;` then `y[3:0] = a;`);
                #   * with no base, the slices must COVER every bit;
                #   * anything left uncovered, or a slice written under a guard, genuinely
                #     retains its value -- that is an inferred LATCH, and stays a loud problem.
                fullmask = (1 << regw) - 1
                smask = 0
                for _o, _w, _v, _g, _tg, _nm, _l in parts:
                    smask |= ((1 << _w) - 1) << _o
                whole = brs.get(reg)
                has_base = (whole is not None and len(whole) == 1
                            and not (whole[0].guards or whole[0].tag_guards or whole[0].neg_matches))
                # A GUARDED slice is only a latch when there is no base: with `y = '0;` present
                # the base drives every bit and the slice conditionally overrides it, which is
                # `guard ? val : base[region]` -- exactly what _build_rmw constructs.
                guarded = any(g or tg or nm for _o, _w, _v, g, tg, nm, _l in parts)
                if not has_base and guarded and getattr(self, "_allow_latches", False):
                    # A CONDITIONALLY-written slice with no default is a latch on PART of the
                    # word: the guarded region holds when its guard is low, while the rest is
                    # still driven at the same instant. Lowered by splitting the RULE on the
                    # guard (Fix 83) rather than embedding `guard ? val : y[region]`, whose
                    # hoisted temp read `y` at the head's own instant -- a combinational loop.
                    vs = self._latch_slice_variants(reg, regw, parts, loc0, flagged)
                    if vs is not None:
                        miss_g = fullmask & ~smask
                        self._inferred_latches.append(InferredLatch(
                            lhs=reg, width=regw, keep=miss_g, bits="conditionally-written",
                            value=vs[0][1], variants=vs, loc=loc0))
                        self._warns.append((loc0, (
                            f"INFERRED LATCH translated: {reg} has a conditionally-written slice "
                            f"with no default, so those bits RETAIN their value when the guard is "
                            f"low -- modelled as a level-sensitive latch (--allow-latches). Add a "
                            f"default (`{reg} = '0;`) if that was not intended")))
                        continue
                if not has_base and guarded:
                    flagged.append((loc0, (
                        f"{reg}: conditionally-written SLICE in always_comb with no default -- "
                        f"an inferred LATCH on part of the word. This is the one latch shape "
                        f"--allow-latches does NOT cover: a whole-signal inferred latch holds "
                        f"the signal (one retention rule), but here only SOME bits hold while "
                        f"the rest must still be driven at the same instant, and the "
                        f"self-hold `guard ? val : {reg}[region]` is hoisted into a temp that "
                        f"reads {reg} at that instant -- a combinational loop, which the T2 "
                        f"detector catches. Add a default (`{reg} = '0;`) to make the block "
                        f"fully driven, or write the intent as an explicit `always_latch`")))
                    continue
                if not has_base and (smask & fullmask) != fullmask:
                    # A GENUINE INFERRED LATCH: some bit is not driven on every path, so it
                    # retains its value. TRANSLATE it with the latch semantics proven in
                    # Latch.lean rather than refusing -- same policy as the incomplete selector
                    # (D4) and the combinational loop (T2) -- and report it LOUDLY.
                    miss = fullmask & ~smask if not guarded else fullmask & ~smask
                    bits_l = [i for i in range(regw) if miss >> i & 1]
                    rngs, st = [], None
                    for i in range(regw + 1):
                        if i in bits_l and st is None:
                            st = i
                        elif i not in bits_l and st is not None:
                            rngs.append(f"{i - 1}:{st}" if i - 1 > st else f"{st}")
                            st = None
                    desc = ", ".join(rngs) if rngs else "conditionally-written"
                    slices_l = [(off, w, val, g) for off, w, val, g, _tg, _nm, _l in parts]
                    # base = the signal's PRIOR value: `(prior & keep) | driven regions`, and a
                    # guarded slice self-holds as `guard ? val : prior[region]`.
                    v_l = self._build_rmw(Ref(reg), regw, slices_l, loc0, flagged)
                    if v_l is None:
                        continue
                    self._inferred_latches.append(InferredLatch(lhs=reg, width=regw, keep=miss, bits=desc,
                                                     value=v_l, loc=loc0))
                    flagged.append((loc0, f"{reg}: INFERRED LATCH -- bit(s) [{desc}] are not "
                                          f"assigned on every path through this always_comb, so "
                                          f"they RETAIN their value. Translated with latch "
                                          f"semantics (see the `% INFERRED LATCH` comment in the "
                                          f".lp); add a default (`{reg} = '0;`) if a latch was "
                                          f"not intended"))
                    reg_names.discard(reg)
                    continue
                base_c: Expr = whole[0].value if has_base else Const(0, regw)
                if has_base:
                    del brs[reg]
                slices_c = [(off, w, val, g) for off, w, val, g, _tg, _nm, _l in parts]
                value_c = self._build_rmw(base_c, regw, slices_c, loc0, flagged)
                if value_c is None:
                    continue
                self._blk_comb.append(CombItem(lhs=reg, rhs=value_c, loc=loc0))
                continue
            if any(tg or nm for _o, _w, _v, _g, tg, nm, _l in parts):
                flagged.append((loc0, f"{reg}: enum/case-conditioned slice write (deferred)"))
                continue
            # CLOCKED slice writes are assembled at MODULE end (`_assemble_clocked_slices`), so
            # slices of one register written from SEVERAL always blocks -- `q[3:0] <= a` in one,
            # `q[7:4] <= b` in another, ordinary RTL -- compose into ONE read-modify-write. Per
            # block, each produced its own whole-word RMW (its slice plus the OTHER bits held), two
            # next values for one register: multi-valued, UNSAT under any scenario, which a
            # property check reads as "no counterexample" -- with exit 0 and `coverage: OK`.
            base = None
            if reg in brs:   # a whole write to reg in the same block -> it is the RMW base (override it)
                whole = brs[reg]
                if any(b.tag_guards or b.neg_matches for b in whole):
                    flagged.append((loc0, f"{reg}: case-conditioned whole write beside slice writes (deferred)"))
                    continue
                # A GUARDED whole write is the RMW base composed as a priority chain, not a refusal:
                # `if (reset) {pm,hh,mm,ss} <= C; else if (ena) ss[3:0] <= ..` writes the WHOLE register
                # under reset and SLICES of it otherwise. Each guarded whole write self-holds against
                # what precedes it -- the same `guard ? value : prior` shape a conditional SLICE already
                # gets in _build_rmw -- and a later assignment overrides an earlier one (nonblocking:
                # the last one executed wins). An UNCONDITIONAL whole write replaces the chain below it.
                # Refused as "mixed slice + conditional/multiple whole write" until 2026-08-19, met on
                # VerilogEval's count_clock reference, which resets its clock through a concatenation
                # target and then counts the digits by part-select.
                base = self._priority_chain([(b.value, b.guards) for b in whole], regw, Ref(reg), loc0)
                if isinstance(base, Cond):
                    # a Cond cannot sit inside the word RMW as a value term -- hoist it to a comb net
                    base = self._hoist_word(base, regw, loc0)
                del brs[reg]
            entry = self._clocked_slices.setdefault(reg, {
                "regw": regw, "clock": clock, "reset": reset, "reset_value": reset_values.get(reg, 0),
                "base": None, "parts": [], "loc": loc0})
            if entry["clock"] != clock or entry["reset"] != reset:
                flagged.append((loc0, (
                    f"{reg}: slice-written from two always blocks with different clock/reset "
                    f"(one register, one clock domain -- deferred)")))
                continue
            if base is not None:
                if entry["base"] is not None:
                    flagged.append((loc0, f"{reg}: whole-written in two always blocks beside slice "
                                          f"writes (multi-driver)"))
                    continue
                entry["base"] = base
            entry["parts"].extend(parts)
            # which always block each part came from: order is defined WITHIN a block (the LRM's
            # nonblocking semantics -- last assignment wins) and NOT between blocks, so overlapping
            # writes may be folded in source order only when they share one block
            entry.setdefault("blocks", []).extend([blk_id] * len(parts))
            reg_names.add(reg)

    def _assemble_clocked_slices(self, seq: list, reg_names: set, flagged: list) -> None:
        """ONE read-modify-write SeqItem per slice-written register, over the slices recorded from
        EVERY always block of the module (`_assemble_slice_writes`). Overlapping slices from two
        blocks are a genuine multi-driver -> flagged; disjoint ones compose, exactly as nonblocking
        writes to disjoint slices compose under the LRM."""
        for reg, e in self._clocked_slices.items():
            parts, regw, loc0 = e["parts"], e["regw"], e["loc"]
            # SEVERAL guarded writes to the SAME region are a PRIORITY CHAIN, not an overlap:
            # `if (c) ss[3:0] <= 0; else ss[3:0] <= ss[3:0] + 1;` is one region written twice under
            # complementary guards -- ordinary RTL, and the shape every BCD counter is written in.
            # Group by region first, compose each group, and check overlap between DISTINCT regions
            # only. (Grouping was absent until 2026-08-19: the same region twice was reported
            # "overlapping clocked slice writes (multi-driver, not modeled)" -- loud, but a refusal of
            # correct RTL. Met on VerilogEval's count_clock reference.)
            by_region: dict = {}
            order: list = []
            for off, w, v, g, _tg, _nm, _l in parts:
                if (off, w) not in by_region:
                    by_region[(off, w)] = []
                    order.append((off, w))
                by_region[(off, w)].append((v, g))
            covered = 0
            overlap = False
            for off, w in order:
                m = ((1 << w) - 1) << off
                if covered & m:
                    overlap = True
                covered |= m
            base: Expr = e["base"] if e["base"] is not None else Ref(reg)
            if overlap and len(set(e.get("blocks", []))) > 1:
                # overlapping writes from TWO always blocks: the LRM defines no order between blocks,
                # so this is a genuine multi-driver -- a race, not a priority chain. Still refused.
                flagged.append((loc0, f"{reg}: overlapping clocked slice writes from DIFFERENT always "
                                      f"blocks (multi-driver: the LRM orders writes within a block, "
                                      f"not between them)"))
                continue
            if overlap:
                # OVERLAPPING regions in ONE block: order decides, so fold every write in source order
                # instead of composing per region (see _ordered_rmw). Refused until 2026-08-19.
                value = self._ordered_rmw(base, regw, parts, loc0)
                seq.append(SeqItem(reg=reg, clock=e["clock"], reset=e["reset"],
                                   branches=(Branch(guards=(), value=value, loc=loc0),),
                                   has_hold=False, loc=loc0, reset_value=e["reset_value"]))
                reg_names.add(reg)
                continue
            slices = []
            for off, w in order:
                grp = by_region[(off, w)]
                if len(grp) == 1:
                    slices.append((off, w, grp[0][0], grp[0][1]))
                    continue
                # later assignment wins; an unconditional one replaces the chain below it; when no
                # guard fires the region self-holds (falls back to the base's bits)
                self._hoist_ctx = reg
                chain = self._priority_chain(grp, w, Slice(base, off + w - 1, off), loc0)
                if isinstance(chain, Cond):
                    chain = self._hoist_word(chain, w, loc0)
                self._hoist_ctx = ""
                slices.append((off, w, chain, ()))    # the chain carries its own guards now
            value = self._build_rmw(base, regw, slices, loc0, flagged)
            if value is None:
                continue
            seq.append(SeqItem(reg=reg, clock=e["clock"], reset=e["reset"],
                               branches=(Branch(guards=(), value=value, loc=loc0),),
                               has_hold=False, loc=loc0, reset_value=e["reset_value"]))

    def _record_cell_field_write(self, left, val, guards, clock, loc, writes: list) -> None:
        """arr[i].field <= v -> a clocked read-modify-write of the memory CELL (untouched fields
        retain). Emitted as a MemWrite carrying the written slice(s); the emitter splices the cell.

        Several fields of the SAME cell under the same guard merge into ONE MemWrite (Fix 77).
        Each write preserves the bits it does not touch, so emitting one rule per field gave the
        cell TWO next-state values -- each carrying its own field's new value beside the other
        field's OLD one -- and `arr[0].tag <= t0; arr[0].val_ <= v0;` in one always_ff left the
        cell multi-valued with `coverage: OK`. The emitter already splices any number of slices
        into a single rule; only the frontend was splitting them."""
        inner = self._peel(left.value)                      # the ElementSelect arr[i]
        arr = self._peel(inner.value).symbol.name
        idx = self._lower_expr(inner.selector)
        layout = self._struct_mems[arr]
        w, off = next((fw, fo) for fn, fw, fo in layout if fn == left.member.name)
        cellw = max(o + fw for _fn, fw, o in layout)
        for i, prev in enumerate(writes):
            if (prev.mem == arr and prev.addrs == (idx,) and prev.clock == clock
                    and prev.guards == guards and prev.rmw_slices):
                if any(o == off for o, _sw, _v in prev.rmw_slices):
                    break                       # same field written twice -> last-write-wins path
                writes[i] = dataclasses.replace(
                    prev, rmw_slices=(*prev.rmw_slices, (off, w, val)))
                return
        writes.append(MemWrite(mem=arr, addrs=(idx,), data=val, guards=guards, clock=clock, loc=loc,
                               rmw_slices=((off, w, val),), cell_width=cellw))

    def _register_interface(self, inst, signals: dict) -> None:
        """An interface instance is a bundle of SHARED wires. Flatten each interface signal to a
        qualified net ``inst(sig)`` (no copying -- producer and consumer reference the same net).
        Records the instance in ``self._interfaces`` so hierarchical refs ``inst.sig`` resolve."""
        sigs: set[str] = set()
        for m in inst.body:
            if _enum_name(m.kind) in ("Variable", "Net"):
                qn = f"{inst.name}({m.name})"
                sigs.add(m.name)
                if qn not in signals:
                    t = m.type
                    signals[qn] = Signal(name=qn, irtype=self._irtype(t),
                                         is_reg=False, is_port=False, direction=None,
                                         initial=None, loc=self._loc(m))
        self._interfaces[inst.name] = sigs

    def _lower_generate(self, arr: object, dispatch, flagged: list) -> None:
        """A generate block (for / if / case, possibly nested). pyslang has already resolved every
        condition and unrolled the for; we lower the FIRST elaborated entry's members through the SAME
        module-body ``dispatch`` -- so a generate body supports the full construct set (assigns,
        always blocks, instances, nested + conditional generates) -- with the for-loop genvar (if any)
        in scope as the lane variable, so ``sig[genvar]`` rolls to one indexed rule (the grounder fans
        the lane). A genvar-free entry is a conditional/region with no lane -- just inline it."""
        entries = list(getattr(arr, "entries", []))
        if not entries:
            return
        # The genvar's VALUE per entry (a Parameter symbol; None when the block has no genvar --
        # a lone conditional/region, lowered once with no lane).
        gvals: list[int | None] = []
        for e in entries:
            p = next((x for x in e if _enum_name(x.kind) == "Parameter"), None)
            cv = getattr(p, "value", None) if p is not None else None   # a ConstantValue
            try:
                gvals.append(int(str(cv)) if cv is not None else None)
            except ValueError:
                gvals.append(None)
        genvar = next((p.name for p in entries[0] if _enum_name(p.kind) == "Parameter"), None)
        has_lane = genvar is not None and all(v is not None for v in gvals)

        def _ap(vals: list[int]) -> tuple[int, int, int] | None:
            """(lo, exclusive hi, step) if ``vals`` is an ascending arithmetic progression."""
            if not vals:
                return None
            step = (vals[1] - vals[0]) if len(vals) > 1 else 1
            if step < 1 or vals != [vals[0] + step * k for k in range(len(vals))]:
                return None
            return vals[0], vals[-1] + 1, step

        # Lane-rolling lowers ONE representative entry and fans the index over the loop's index
        # set as a domain literal `I = lo..hi-1[, (I - lo) \ step = 0]` -- an ARITHMETIC
        # PROGRESSION. Anything else (a genvar stepping irregularly) is refused rather than rolled
        # over every lane.
        if has_lane and _ap(gvals) is None:
            flagged.append((self._loc(arr), (
                f"for-generate over genvar values {gvals}: only an arithmetic progression "
                f"(constant step) is lane-rolled (deferred -- unroll explicitly)")))
            return
        # UNIFORMITY. Lane-rolling one entry over a range is correct only when every entry in
        # that range has the SAME structure. A genvar-DEPENDENT conditional generate
        # (`for(i) if (i == 0) … else …`) makes the entries differ, so the entries are
        # PARTITIONED into classes of equal signature, each class lowered from its own first
        # entry over its own index set: `{0}` from `first`, `{1..N-1}` from `rest`; `{0,2}` /
        # `{1,3}` from `if (i % 2 == 0)`'s two arms. A class must be an arithmetic progression
        # (`if (i == 0 || i == 3)` is not) -- refused.
        #
        # The signature must see WHICH arm each entry instantiates. pyslang keeps BOTH arms of
        # a conditional generate in every entry, the untaken one marked `isUninstantiated`, so
        # `(kind, name)` alone is identical across entries whenever the arms are NAMED
        # (`begin : first … begin : rest`) -- exactly how real RTL, and every lint rule, writes
        # them. The witness this check was born with used UNNAMED arms, which pyslang auto-names
        # `genblk1` on the taken side only, so the names differed by accident and the check
        # passed for a reason that did not generalise: with named arms it was blind, entry[0]'s
        # arm was rolled over every lane and the other arm silently dropped.
        def _sig(e):
            return tuple((_enum_name(x.kind), getattr(x, "name", ""),
                          bool(getattr(x, "isUninstantiated", False)))
                         for x in e if _enum_name(x.kind) != "Parameter")
        classes: dict[tuple, list[int]] = {}          # signature -> entry indices (in order)
        reps: dict[tuple, object] = {}
        for k, e in enumerate(entries):
            sg = _sig(e)
            classes.setdefault(sg, []).append(k)
            reps.setdefault(sg, e)
        if not has_lane and len(classes) > 1:
            flagged.append((self._loc(arr), "for-generate with a genvar-dependent conditional/case "
                            "(non-uniform iterations) -- not uniformly lane-rollable"))
            return
        plan = []
        for sg, ks in classes.items():
            if not has_lane:
                plan.append((reps[sg], 0, 1, 1))
                continue
            ap = _ap([gvals[k] for k in ks])
            if ap is None:
                flagged.append((self._loc(arr), (
                    f"for-generate with a genvar-dependent conditional/case whose arm is taken "
                    f"at genvar values {[gvals[k] for k in ks]} -- not an arithmetic progression, "
                    f"so no one domain literal covers it (deferred -- unroll explicitly)")))
                return
            plan.append((reps[sg], *ap))
        for e0, lo, hi, step in plan:
            self._lower_generate_run(arr, e0, genvar if has_lane else None, lo, hi, step,
                                     dispatch, flagged)

    def _lower_generate_run(self, arr, e0, genvar: str | None, lo: int, hi: int, step: int,
                            dispatch, flagged: list) -> None:
        """Lower ONE representative generate entry ``e0`` with ``genvar`` in scope as the lane
        variable ranging over the arithmetic progression ``lo, lo+step, .. < hi`` (a class of
        `_lower_generate`'s partition; the whole loop when it is uniform)."""
        saved, self._genvars = self._genvars, self._genvars | ({genvar} if genvar else set())
        saved_order = list(self._genvar_order)
        saved_hi, self._lane_hi = self._lane_hi, (hi if genvar else self._lane_hi)
        saved_lo, self._lane_lo = self._lane_lo, (lo if genvar else self._lane_lo)
        saved_step, self._lane_step = self._lane_step, (step if genvar else self._lane_step)
        # Push (genvar, (start, exclusive bound, step)) so a lane-rolled write inside the
        # generate can guard its index the same way the procedural `for` does. In SYNTHESIZABLE
        # SV the iteration range is always elaboration-time constant, so these are literals in
        # the emitted rule -- never a runtime read.
        pushed_lane = bool(genvar)
        if pushed_lane:
            self._loop_lane_stack.append((genvar, (lo, hi, step)))
        if genvar and genvar not in self._genvar_order:
            self._genvar_order.append(genvar)
        saved_fold, self._genvar_folded = self._genvar_folded, None
        try:
            for mm in e0:
                if _enum_name(mm.kind) != "Parameter":  # skip the genvar itself
                    dispatch(mm)
                    # a net/variable DECLARED in this generate body is per-iteration: a LANE of the
                    # loop's extent by construction (see the module epilogue for the width)
                    if genvar and _enum_name(mm.kind) in ("Variable", "Net"):
                        t = getattr(mm, "type", None)
                        if (getattr(t, "isUnpackedArray", False) or getattr(t, "isStruct", False)
                                or getattr(t, "isUnion", False) or getattr(t, "isEnum", False)):
                            flagged.append((self._loc(mm), f"{mm.name}: an array/struct/union/enum declared "
                                            f"inside a for-generate body (deferred -- declare it at module "
                                            f"level, indexed by the genvar)"))
                        elif len(self._genvars) > 1:
                            flagged.append((self._loc(mm), f"{mm.name}: a declaration inside a NESTED "
                                            f"for-generate body (deferred -- declare it at module level)"))
                        else:
                            self._lane_dims[mm.name] = max(self._lane_dims.get(mm.name, 0), 1)
                            self._note_lane_elem_w(mm.name, getattr(t, "bitWidth", 1) or 1)
                            self._gen_locals[mm.name] = max(self._gen_locals.get(mm.name, 0), hi)
            # VALUE-USE of the genvar (defect D1). Lane-rolling lowers one entry and fans the index,
            # which is only sound when the body is index-INVARIANT apart from the indices it selects
            # with. A genvar used as a VALUE (`a + i`, `a[i*8 +: 8]`, `(i == 0) ? …`) is a Parameter
            # and so constant-folds to that entry's value, which would then be baked into EVERY lane
            # -- e.g. `y[i] = a + i` gave every lane `a + 0`. Nothing downstream can detect it (the
            # genvar is gone by then), so refuse here rather than emit a silently wrong model.
            if genvar and self._genvar_folded is not None and hi - lo > step:
                flagged.append((self._loc(arr), (
                    f"for-generate body uses genvar {genvar!r} as a VALUE "
                    f"({self._genvar_folded.strip()!r}), not only as a select index -- it constant-"
                    f"folds to one iteration and lane-rolling would apply that to every lane. Rewrite "
                    f"the index-dependent value as a select (`sig[{genvar}]`), or unroll explicitly.")))
        finally:
            self._genvars = saved
            self._genvar_order = saved_order
            self._lane_hi = saved_hi
            self._lane_lo = saved_lo
            self._lane_step = saved_step
            if pushed_lane:
                self._loop_lane_stack.pop()
            self._genvar_folded = saved_fold

    # -- primitive instances (catalog §2.10 generalized; see primitives.py) ---
    def _lower_uninst_primitive(self, node, spec, ctx: LowerCtx) -> None:
        """Lower a library PRIMITIVE that pyslang left as an ``UninstantiatedDefSymbol`` (no module
        definition in scope -- e.g. ``ACME_FF``/``ACME_VCMUX``). The node shape differs from a normal
        Instance: pins come from ``portNames`` (parallel to ``portConnections``, each an AssertionExpr
        with ``.expr``); params are NOT elaborable (InvalidExpression), so sizes are read from the port
        widths. We resolve the same flop / vcmux / clz / comb / wire semantics as ``_lower_instance``."""
        comb, seq, muxes, latches = ctx.comb, ctx.seq, ctx.muxes, ctx.latches
        reg_names, cells, flagged = ctx.reg_names, ctx.cells, ctx.flagged
        loc = self._loc(node)
        mod = node.definitionName
        names = list(node.portNames)
        conns = list(node.portConnections)
        pin_expr: dict[str, object] = {}     # pin name -> pyslang expression (from .expr)
        pin_w: dict[str, int] = {}           # pin name -> actual bit width
        for nm, c in zip(names, conns, strict=False):
            e = getattr(c, "expr", None)
            if e is None:
                continue
            pin_expr[nm] = e
            pin_w[nm] = getattr(getattr(e, "type", None), "bitWidth", 1) or 1

        def add_cell(*outs: str) -> None:
            cells.append(CellInfo(inst=node.name, cell_type=mod.lower(),
                                  outs=tuple(outs), parent=self._current_module))

        def pin_name(pin: str, role: str = "input") -> str:
            """The NET a pin is connected to. A compound INPUT connection -- a concatenation
            of select bits, a replication, an expression -- is hoisted into a named temp
            (`<inst>__tN`) and the temp's name returned, which is what the refusal used to
            tell a person to do by hand. An output, clock or reset pin must be a net, and
            anything else there is a refusal that NAMES the pin -- never a Python
            AttributeError (a field report, 2026-09-04: a vectored mux with no definition in
            scope, `.sel({s3, s2, s1, s0})`, crashed here after F41 had fixed the
            instantiated path only)."""
            e = pin_expr[pin]
            p = self._peel(e)
            if hasattr(p, "symbol"):
                return p.symbol.name
            if role != "input":
                raise NotImplementedError(
                    f"{spec.category} {node.name}: pin {pin} ({role}) is connected to a "
                    f"{_enum_name(p.kind)} (`{str(getattr(p, 'syntax', '')).strip()}`), not a plain "
                    f"net -- assign it to a wire first and connect the wire")
            saved_ctx, self._hoist_ctx = self._hoist_ctx, node.name
            try:
                ref = self._hoist_word(self._lower_expr(e), pin_w.get(pin, 1), loc)
            finally:
                self._hoist_ctx = saved_ctx
            return ref.name

        if spec.category == "latch":
            # opt-in only; see the instantiated path for the reasoning
            if not getattr(self, "_allow_latches", False):
                flagged.append((loc, f"latch {mod} {node.name}: level-sensitive latches are OFF "
                                     f"by default -- pass --allow-latches if this design "
                                     f"genuinely uses one. A latch is transparent while its "
                                     f"enable is high (zero delay), which is a combinational "
                                     f"path, not a register"))
                return
            need = [spec.pins[k] for k in ("q", "d", "en")]
            if any(n not in pin_expr for n in need):
                flagged.append((loc, f"latch {mod} {node.name}: needs en/d/q connected"))
                return
            nm = lambda pin: pin_name(pin, "output" if pin == spec.pins["q"] else "input")  # noqa: E731
            latches.append(LatchItem(q=nm(spec.pins["q"]), d=nm(spec.pins["d"]),
                                     en=nm(spec.pins["en"]), inst=node.name, loc=loc))
            add_cell(nm(spec.pins["q"]))
            return
        if spec.category == "flop":
            qpin, dpin = spec.pins["q"], spec.pins["d"]
            if qpin not in pin_expr or dpin not in pin_expr or spec.pins["clk"] not in pin_expr:
                flagged.append((loc, f"primitive {mod} {node.name}: flop needs clk/d/q connected"))
                return
            q_e = pin_expr[qpin]
            qk = _enum_name(q_e.kind)
            ps = self._partselect_lhs(q_e) if qk in ("RangeSelect", "ElementSelect") else None
            if qk == "NamedValue":
                q = pin_name(qpin, "output")
            elif ps is not None:
                q = ps[0]                                  # (root, root_width, lo, w)
            else:
                flagged.append((loc, f"primitive {mod} {node.name}: q output is not a net/part-select"))
                return
            clk = pin_name(spec.pins["clk"], "clock")
            d = self._lower_expr(pin_expr[dpin])
            dw = pin_w.get(dpin, 1)
            # the flop's D must be a clean value-term (catalog §2.10 "no computation in D"): hoist a
            # compound D to a named comb wire so the register reads a plain Ref (also lets a 1-bit reg
            # avoid the inline-d-expression limit).
            if not isinstance(d, (Ref, Const)):
                self._hoist_ctx = q
                d = self._hoist_word(d, dw, loc)
                self._hoist_ctx = ""
            # enable: a constant 1 -> unconditional; a signal/expr -> guard (hoist a compound enable)
            guards: tuple[tuple[str, int], ...] = ()
            enpin = spec.pins.get("en")
            if enpin is not None and enpin in pin_expr:
                en_e = self._lower_expr(pin_expr[enpin])
                if not (isinstance(en_e, Const) and en_e.value == 1):
                    self._hoist_ctx = q
                    en_ref = en_e if isinstance(en_e, Ref) else self._hoist_bit(en_e, loc)
                    self._hoist_ctx = ""
                    guards = ((en_ref.name, 1),)
            reset = None
            reset_value = 0
            if spec.reset and spec.pins.get("rstL") in pin_expr:
                reset = Reset(signal=pin_name(spec.pins["rstL"], "reset"),
                              active=spec.reset, kind="async")
            if ps is not None:
                # a part-select q[off+w-1:off] <= d: RECORD it; multiple per-bit/per-slice flops on the
                # same reg (e.g. clkenDup_D4[0..3]) are COALESCED into ONE SeqItem after dispatch (else
                # N SeqItems would each drive the whole reg = multi-driver). Untouched bits self-hold.
                _root, regw, lo, w = ps
                self._prim_flop_slices.setdefault(q, (regw, clk, reset, reset_value, []))[4].append(
                    (lo, w, d, guards, loc))
                reg_names.add(q)
                add_cell(q)
                return
            reg_names.add(q)
            seq.append(SeqItem(reg=q, clock=clk, reset=reset,
                               branches=(Branch(guards=guards, value=d),),
                               has_hold=bool(guards), loc=loc, reset_value=reset_value))
            add_cell(q)
            return
        if spec.category == "vcmux":
            opin, spin, ipin = spec.out, spec.pins["sel"], spec.pins["in"]
            if opin not in pin_expr or spin not in pin_expr or ipin not in pin_expr:
                flagged.append((loc, f"primitive {mod} {node.name}: vcmux needs in/sel/out connected"))
                return
            out = pin_name(opin, "output")
            w, n = pin_w[opin], pin_w[spin]
            in_e = self._lower_expr(pin_expr[ipin])
            # Same FLAT one-hot lowering as the instantiated path (see there): one rule per
            # one-hot code plus an all-zero default, exactly as docs/reference/SV_PRIMITIVE_LIBRARY.md documents.
            muxes.append(MuxItem(out=out, sel=pin_name(spin),          # a concat of select bits hoists
                                 arms=tuple(Slice(in_e, i * w + w - 1, i * w) for i in range(n)),
                                 loc=loc, onehot=True))
            add_cell(out)
            return
        if spec.category == "clock_gate":
            # ICG with NO definition in scope -- the ordinary case for a vendor cell, and the
            # whole reason the registry exists. It used to be refused here while the same cell
            # WITH a definition lowered fine, so whether a design translated depended on having
            # a cell library beside it (Fix 80). `gclk` is a DERIVED CLOCK DOMAIN (§6.7), not a
            # flop enable: it ticks only on the base clock's edges where the gate holds, and the
            # master-tick machinery gives flops on it their hold between those edges.
            cpin, epin, gpin = spec.pins["clk"], spec.pins["en"], spec.pins["gclk"]
            missing = [p for p in (cpin, epin, gpin) if p not in pin_expr]
            if missing:
                flagged.append((loc, f"primitive {mod} {node.name}: clock gate needs "
                                     f"{', '.join(missing)} connected"))
                return
            en_expr = self._lower_expr(pin_expr[epin])
            if not isinstance(en_expr, Ref):
                flagged.append((loc, f"clock-gate {node.name}: enable must be a net (assign the "
                                     "gate condition to a wire first), got a compound expression"))
                return
            gclk = pin_name(gpin, "output")
            base = pin_name(cpin, "clock")
            self._derived.append(DerivedClock(name=gclk, base=base, gate=en_expr.name, loc=loc))
            add_cell(gclk)
            return
        if spec.category in ("comb", "wire"):
            # Generic combinational cell with NO definition in scope -- the site-plugin
            # path (config.py): the spec's ``build`` may compose any IR expression over
            # the pin actuals, including FuncCall to a plugin-registered @func. Every
            # pin except ``out`` is an input (direction info is unavailable on an
            # uninstantiated def). Output connect mirrors the clz case: concat-aware.
            if spec.out is None or spec.out not in pin_expr:
                flagged.append((loc, f"primitive {mod} {node.name}: output pin "
                                     f"{spec.out!r} not connected"))
                return
            pinmap = {nm: self._lower_expr(e) for nm, e in pin_expr.items() if nm != spec.out}
            ow = pin_w.get(spec.out, 1)
            if spec.category == "wire":
                if len(pinmap) != 1:
                    flagged.append((loc, f"primitive {mod} {node.name}: wire needs exactly one input"))
                    return
                rhs = next(iter(pinmap.values()))
            else:
                rhs = spec.build(pinmap)
            out_e = pin_expr[spec.out]
            if _enum_name(out_e.kind) == "Concatenation":
                self._hoist_ctx = node.name
                ref = self._hoist_word(rhs, ow, loc)
                self._hoist_ctx = ""
                off = ow
                for op in out_e.operands:     # MSB-first
                    w = getattr(getattr(op, "type", None), "bitWidth", 1) or 1
                    off -= w
                    comb.extend(self._assign_lhs_operand(op, Slice(ref, off + w - 1, off), w, loc))
                add_cell(node.name)
            else:
                root_name = pin_name(spec.out, "output")
                comb.append(CombItem(lhs=root_name, rhs=rhs, loc=loc))
                add_cell(root_name)
            return
        if spec.category == "clz":  # count-leading-zeros / count-leading-sign-bits
            d_pin   = spec.pins.get("clzD",   "clzD_E1")
            s_pin   = spec.pins.get("clzS",   "clzS_E1")
            in_pin  = spec.pins.get("cntIn",  "cntIn_E1")
            sgn_pin = spec.pins.get("cntSgn", "cntSgn_E1")
            if d_pin not in pin_expr or in_pin not in pin_expr or sgn_pin not in pin_expr:
                flagged.append((loc, f"primitive {mod} {node.name}: clz needs cntIn/cntSgn/clzD"))
                return
            # @clz has a HARDWIRED 64-bit window (emit/lib.py; proven contract in
            # proofs/lean — le_fClz_iff is stated over v < 2^64): a wider input would be
            # silently masked to its low 64 bits. Fail loud instead (finding F4).
            iw = pin_w.get(in_pin, 0)
            if iw > 64:
                flagged.append((loc, f"primitive {mod} {node.name}: clz input is {iw} bits but "
                                     "@clz has a hardwired 64-bit window"))
                return
            in_e  = self._lower_expr(pin_expr[in_pin])
            sgn_e = self._lower_expr(pin_expr[sgn_pin])
            # BinOp("clz", cntIn, cntSgn, 7) -> @clz(cntIn, cntSgn, 7) via _WORD_OPS in the emitter
            self._hoist_ctx = node.name      # name after instance (e.g. aluClzA)
            clz_ref = self._hoist_word(BinOp("clz", in_e, sgn_e, 7), 7, loc)
            self._hoist_ctx = ""
            # clzD_E1: may be a concat ({alz, aLeadingZeroes_D1[5:0]}) or a plain net
            d_e = pin_expr[d_pin]
            if _enum_name(d_e.kind) == "Concatenation":
                off = pin_w[d_pin]
                for op in d_e.operands:       # MSB-first
                    w = getattr(getattr(op, "type", None), "bitWidth", 1) or 1
                    off -= w
                    comb.extend(self._assign_lhs_operand(op, Slice(clz_ref, off + w - 1, off), w, loc))
            else:
                root_name = pin_name(d_pin, "output")
                comb.append(CombItem(lhs=root_name, rhs=clz_ref, loc=loc))
                add_cell(root_name)
            # clzS_E1 (SIMD half-word CLZ): structurally unused downstream; tie to 0 + document
            if s_pin in pin_expr:
                s_root = pin_name(s_pin, "output")
                sw = pin_w[s_pin]
                tie_loc = Loc(file=loc.file, line=loc.line,
                              text=(loc.text or "") + f"  [auto-tied to 0: clzS_E1 ({sw} bits) unused]")
                comb.append(CombItem(lhs=s_root, rhs=Const(0, sw), loc=tie_loc))
            return
        flagged.append((loc, f"primitive {mod} {node.name}: category {spec.category!r} "
                             "not supported as an uninstantiated def"))

    def _port_width(self, conn) -> int:
        """Bit width of a port connection's actual expression (from its pyslang type)."""
        e = conn.expression
        if _enum_name(e.kind) == "Assignment":   # output ports wrap the net in an lvalue
            e = e.left
        return getattr(getattr(e, "type", None), "bitWidth", 1) or 1

    def _unused_intake_problems(self, files: list[str]) -> list:
        """`-D` defines and `-I` include dirs that could not have had any effect.

        The third instance of ONE pattern (see `_unbound_stub_problems`,
        `_unapplied_override_problems`): compare what was DECLARED against what the compile
        actually consumed, and report the difference.

        For a DEFINE the criterion is textual and deliberately so: if the macro name occurs
        nowhere in the sources actually compiled, then defining it provably changed nothing.
        That is sound -- nested references (`` `define A `B ``) still put the name in the text --
        and it catches the dangerous case, which is a typo'd config select. `+define+USE_AND`
        misspelt does not fail; it silently takes the `` `else `` branch, so a DIFFERENT DESIGN
        is translated and proven than the one asked for.

        For an INCLUDE DIR the criterion is existence: a path that is not a directory cannot
        contribute a header, so naming it is a mistake."""
        import os
        import re as _re
        probs: list = []
        text = []
        for f in files:
            try:
                with open(f, errors="ignore") as fh:
                    text.append(fh.read())
            except OSError:
                continue
        blob = "\n".join(text)
        for name in sorted(self._defines):
            if not _re.search(rf"(?<![A-Za-z0-9_]){_re.escape(name)}(?![A-Za-z0-9_])", blob):
                probs.append((Loc(f"<define:{name}>", 0),
                              f"`define '{name}' was passed but appears NOWHERE in the compiled "
                              f"sources, so it had no effect. A misspelt config select does not "
                              f"fail -- it silently takes the other branch, translating a "
                              f"DIFFERENT design than the one requested"))
        for d in self._incdirs:
            if not os.path.isdir(d):
                probs.append((Loc(f"<incdir:{d}>", 0),
                              f"include directory '{d}' does not exist, so no header can "
                              f"resolve through it"))
        return probs

    def _unapplied_override_problems(self) -> list:
        """A `-p NAME=V` / manifest parameter override that names no parameter is a LOUD problem.

        Overrides are handed to slang as `compilation.paramOverrides`. A name matching nothing
        -- a typo, a parameter that was renamed or removed, the wrong case -- is simply dropped:
        elaboration proceeds with the DEFAULT, translation succeeds, and coverage reports OK.

        The consequence is the same shape as the unbound-stub defect, and worse in one respect:
        the user believes they configured the design (`-p W=64`) and every downstream artefact
        -- widths, lane counts, the modular spec key, the property proven -- silently belongs to
        a DIFFERENT configuration than the one they asked for. A proof then holds of a design
        nobody requested.

        Compared against the parameter names elaboration actually produced, so it also catches
        an override aimed at a module that was never instantiated."""
        seen = {n.lower() for n in getattr(self, "_param_names_seen", set())}
        missing = sorted(k for k in self._overrides if k.lower() not in seen)
        return [(Loc(f"<param:{k}>", 0),
                 f"parameter override '{k}={self._overrides[k]}' was NOT applied: no parameter "
                 f"of that name exists in the elaborated design, so the DEFAULT value was used. "
                 f"Check the name against the RTL (case-sensitive) -- every width, lane count "
                 f"and spec key downstream belongs to the unconfigured design")
                for k in missing]

    def _unbound_stub_problems(self) -> list:
        """A declared stub that never bound to any instance is a LOUD problem.

        `sources.json` `stubs` maps a MODULE NAME to a functional-stub `.lp`. The dispatch is
        `if mod in self._stubs`, so a name that matches nothing -- a typo, a renamed module, a
        wrong-case entry -- simply never fires, and the module is translated in FULL instead.
        Nothing else notices: coverage is happy, because every line really was translated.

        That is the worst shape a defect can take here. The user asked for the block to be
        SEALED behind a functional spec (a Booth multiplier reduced to `@mul`), and instead got
        its entire implementation, silently -- so any proof then runs against the very thing the
        stub was meant to abstract away. Declaring a stub is an explicit instruction; failing to
        apply it must never be quiet."""
        missing = sorted(set(self._stubs) - set(getattr(self, "_stubs_used", set())))
        return [(Loc(f"<stub:{m}>", 0),
                 f"stub declared for module '{m}' in sources.json never bound: no instance of "
                 f"that module was found, so it was NOT stubbed. Check the name against the "
                 f"RTL (case-sensitive); the module is otherwise translated in full")
                for m in missing]

    def _lower_stubbed_instance(self, inst, mod, comb, cells, signals, flagged) -> None:
        """Project-local FUNCTIONAL STUB (sources.json `stubs`): replace a submodule's
        implementation with a hand-written ASP model, keyed by module name. The submodule body is
        NOT translated. We (1) bridge every port to the instance-qualified functor `inst(port)`, and
        (2) emit the stub text with `@INST@` substituted by the instance name -- so the stub, written
        in terms of `@INST@(port)`, references the same `inst(port)` signals the bridges drive/read.

        This is how a datapath block whose *implementation* is out of scope (or irrelevant to the
        property under test) is sealed behind its functional spec -- e.g. a Booth multiplier stubbed
        to `@mul`. Only modules explicitly listed in `stubs` are stubbed; nothing is auto-subbed."""
        loc = self._loc(inst)
        name = inst.name
        out_nets: list[str] = []
        for c in inst.portConnections:
            if _enum_name(getattr(c.port, "kind", "")) == "InterfacePort":
                flagged.append((loc, f"stub {mod} {name}: interface ports not supported in a stub"))
                continue
            if c.expression is None:      # unconnected port -> no bridge
                continue
            formal = c.port.name
            direction = _enum_name(c.port.direction)
            # register the stub's port signal with its declared width so stage-2 analysis gives it
            # the right (word/bit) shape -- the submodule body is NOT translated, so nothing else
            # declares these signals.  A 1-bit port stays bit; a wider port is a word.
            ptype = getattr(c.port, "type", None)
            pw = getattr(ptype, "bitWidth", 1) or 1
            sig_name = f"{name}({formal})"
            signals[sig_name] = Signal(name=sig_name, irtype=IRType(self._kind(ptype) if ptype else Kind.BIT, pw),
                                       is_reg=False, is_port=False, direction=None, initial=None, loc=loc)
            if direction == "In":         # inst(formal) <- parent actual (may be slice/concat/expr)
                comb.append(CombItem(lhs=f"{name}({formal})",
                                     rhs=self._lower_expr(c.expression), loc=loc))
            elif direction == "Out":      # parent actual <- inst(formal)
                e = c.expression
                if _enum_name(e.kind) == "Assignment":
                    e = e.left
                if _enum_name(e.kind) == "NamedValue":
                    net = self._peel(e).symbol.name
                    comb.append(CombItem(lhs=net, rhs=Ref(f"{name}({formal})"), loc=loc))
                    out_nets.append(net)
                elif _enum_name(e.kind) == "Concatenation":
                    # {hi, lo[..]} <- inst(formal): split the output value MSB-first across targets
                    src = Ref(f"{name}({formal})")
                    total = getattr(getattr(e, "type", None), "bitWidth", None)
                    if total is None:
                        flagged.append((loc, f"stub {mod} {name}: output concat {formal} has no width"))
                    else:
                        off = total
                        for op in e.operands:
                            w = getattr(getattr(op, "type", None), "bitWidth", 1) or 1
                            off -= w
                            comb.extend(self._assign_lhs_operand(op, Slice(src, off + w - 1, off), w, loc))
                            r = self._select_root(op) if _enum_name(op.kind) == "ElementSelect" else None
                            tgt = (r.name if r is not None else
                                   self._peel(op).symbol.name if _enum_name(op.kind) == "NamedValue" else None)
                            if tgt is not None:
                                out_nets.append(tgt)
                else:
                    # slice/part-select output actual: reuse the partial machinery (as _flatten does)
                    pw = self._partselect_lhs(e)
                    if pw is not None:
                        target, tw, off, w = pw
                        self._record_partial_expr(target, tw, off, w, Ref(f"{name}({formal})"), loc)
                        out_nets.append(target)
                    else:
                        flagged.append((loc, f"stub {mod} {name}: output port {formal} actual shape "
                                             "unsupported (expected net, part-select, or concat)"))
            else:
                flagged.append((loc, f"stub {mod} {name}: inout/ref port {formal} not supported"))
        # emit the stub text with @INST@ -> the instance name (so @INST@(port) == name(port))
        self._stubs_used.add(mod)          # for the declared-but-never-bound check
        stub_text = self._stubs[mod].replace("@INST@", name)
        self._stub_rules.append(f"% functional stub: {mod} {name} ({self._current_module})")
        self._stub_rules.append(stub_text.rstrip())
        cells.append(CellInfo(inst=name, cell_type=mod.lower(),
                              outs=tuple(out_nets), parent=self._current_module))

    def _modular_port_actuals(self, inst, ctx: LowerCtx) -> None:
        """MODULAR mode, one child instance: for every data port whose actual is NOT a plain
        signal, give the parent spec a signal `<inst>__<formal>` that the manifest bridges to,
        and wire the actual to it in the parent -- an INPUT's expression becomes a comb rule
        driving that signal; an OUTPUT's slice/concat target is reassembled from it (partials),
        exactly as the flat path does in `_flatten_user_instance`. Recorded in
        `self._modular_actuals[(parent module, instance, formal)]` for `parse_modular`'s tree
        walk. Struct and array ports with a non-simple actual are refused (their manifest bridge
        is per field / per cell and needs a name on both sides)."""
        comb, signals, flagged = ctx.comb, ctx.signals, ctx.flagged
        name, loc, parent = inst.name, self._loc(inst), self._current_module
        for c in inst.portConnections:
            if _enum_name(c.port.kind) == "InterfacePort" or c.expression is None:
                continue
            e = c.expression
            if _enum_name(e.kind) == "Assignment":
                e = e.left
            pe = self._peel(e)
            if _enum_name(pe.kind) == "NamedValue" and getattr(pe, "symbol", None) is not None:
                continue                                  # a plain signal: the manifest bridges by name
            formal = c.port.name
            direction = _enum_name(c.port.direction)
            if direction not in ("In", "Out"):
                continue
            ptype = getattr(c.port, "type", None)
            w = getattr(ptype, "bitWidth", None) or 1
            if (ptype is not None and (_enum_name(ptype.canonicalType.kind) == "PackedStructType"
                                       or getattr(ptype, "isUnpackedArray", False))):
                flagged.append((loc, f"instance {name}: {direction.lower()}put port {formal} is a "
                                     f"struct/array connected to an EXPRESSION actual "
                                     f"(`{str(getattr(e, 'syntax', '')).strip()}`) -- the modular "
                                     f"bridge is per part and needs a plain signal on both sides "
                                     f"(deferred)"))
                continue
            hname = f"{name}__{formal}"
            if hname not in signals:
                signals[hname] = Signal(name=hname, irtype=IRType(Kind.BIT, w), is_reg=False,
                                        is_port=False, direction=None, initial=None, loc=loc)
            self._modular_actuals[(parent, name, formal)] = hname
            if direction == "In":
                comb.append(CombItem(lhs=hname, rhs=self._lower_expr(c.expression), loc=loc))
                continue
            src = Ref(hname)
            ek = _enum_name(e.kind)
            if ek == "Concatenation":                     # {a, b[..]} <- child output: split MSB-first
                total = getattr(getattr(e, "type", None), "bitWidth", None)
                off = total
                for op in e.operands:
                    ow = getattr(getattr(op, "type", None), "bitWidth", 1) or 1
                    off -= ow
                    self._modular_out_target(op, Slice(src, off + ow - 1, off), name, loc, comb, flagged)
            else:                                         # x[hi:lo] <- child output (reassembled)
                self._modular_out_target(e, src, name, loc, comb, flagged)

    def _modular_out_target(self, op, val: Expr, name: str, loc, comb: list, flagged: list) -> None:
        """One output-side target of a modular child: a plain net -> a comb copy; a part-select ->
        a partial (reassembled by `_assemble_partials`); else flag."""
        k = _enum_name(op.kind)
        if k == "NamedValue":
            comb.append(CombItem(lhs=op.symbol.name, rhs=val, loc=loc))
            return
        pw = self._partselect_lhs(op)
        if pw is not None:
            target, tw, poff, pw_ = pw
            self._record_partial_expr(target, tw, poff, pw_, val, loc)
            return
        flagged.append((loc, f"submodule output target {k} on {name} (unsupported shape)"))

    def _lower_instance(self, inst, ctx: LowerCtx) -> None:
        comb, seq, muxes, latches, vffs = ctx.comb, ctx.seq, ctx.muxes, ctx.latches, ctx.vffs
        signals, mems, writes = ctx.signals, ctx.mems, ctx.writes
        reg_names, cells, enums, flagged = ctx.reg_names, ctx.cells, ctx.enums, ctx.flagged
        defn = getattr(inst, "definition", None)
        mod = defn.name if defn else "?"
        loc = self._loc(inst)
        if defn is not None and _enum_name(getattr(defn, "definitionKind", None)) == "Interface":
            self._register_interface(inst, signals)   # a bundle of shared wires, qualified inst(sig)
            return
        if mod in self._stubs:   # project-local FUNCTIONAL STUB: model the block, don't translate its body
            self._lower_stubbed_instance(inst, mod, comb, cells, signals, flagged)
            return
        spec = primitives.lookup(mod)
        if spec is None:
            # not a known primitive -> a user-defined submodule.
            if self._modular and getattr(inst, "body", None) is not None:
                # modular mode: the child is a SEPARATE spec linked by the instance manifest, NOT
                # flattened here; its ports become this module's boundary signals. A port whose
                # ACTUAL is an expression (`~t`, `{2'b11, d}`, `x[3:0]`, `{hi, lo}` on an output)
                # is hoisted to a parent-side signal HERE, so the manifest can bridge to a name --
                # it used to collapse every actual to its ROOT signal, silently: `.d(~t)` on a
                # child of a module that also had a port `d` bridged the child to the PARENT's `d`.
                self._modular_port_actuals(inst, ctx)
                return
            # flat mode: flatten it hierarchically, qualifying every internal name by the instance.
            if getattr(inst, "body", None) is not None:
                self._flatten_user_instance(inst, ctx)
            else:
                flagged.append((loc, f"unsupported module instance: {mod} {inst.name}"))
            return

        def add_cell(*outs: str) -> None:   # record the structural instance (cell/3, §4.1)
            cells.append(CellInfo(inst=inst.name, cell_type=mod.lower(),
                                  outs=tuple(outs), parent=self._current_module))
        conns = {c.port.name: c for c in inst.portConnections}
        params = {p.name: self._cv_int(p.value) for p in inst.body
                  if _enum_name(p.kind) == "Parameter"}

        def actual_name(pin: str, role: str = "strict") -> str:
            # an output-port connection wraps the external net in an Assignment lvalue
            e = conns[pin].expression
            if _enum_name(e.kind) == "Assignment":
                e = e.left
            p = self._peel(e)
            if hasattr(p, "symbol"):
                return p.symbol.name
            if role == "input":
                # a compound INPUT connection (a concatenation of select bits, an expression) is
                # hoisted into a named temp (`<inst>__tN`) -- what the refusal below tells a
                # person to do by hand (a field report, 2026-09-04: the vectored mux's `sel`)
                saved_ctx, self._hoist_ctx = self._hoist_ctx, inst.name
                try:
                    ref = self._hoist_word(self._lower_expr(e), self._port_width(conns[pin]), loc)
                finally:
                    self._hoist_ctx = saved_ctx
                return ref.name
            # a connection that is not a plain net on a pin that must be one (an output, a
            # clock, a reset, a lane pin). Named, so it is a refusal a person can act on and
            # not a Python AttributeError leaking out of the guard (a field report,
            # 2026-09-03: a vectored flop's `.En({4{opvld}})` crashed instead of refusing)
            raise NotImplementedError(
                f"{spec.category} {inst.name}: pin {pin} is connected to a {_enum_name(p.kind)} "
                f"(`{str(getattr(p, 'syntax', '')).strip()}`), not a plain net -- assign the "
                f"expression to a wire first and connect the wire")

        def broadcast_enable(pin: str, lanes: int) -> "str | None":
            """`.En({N{x}})` with N the lane count and x a 1-bit net: ONE enable for every lane.
            Returns x's name, or None when the connection is anything else."""
            e = conns[pin].expression
            if _enum_name(e.kind) != "Replication":
                return None
            if (self._const_of(e.count) or 0) != lanes:
                return None
            unit = e.concat                      # pyslang wraps the replicated operand(s) in a Concatenation
            if _enum_name(unit.kind) == "Concatenation":
                ops = list(unit.operands)
                if len(ops) != 1:
                    return None
                unit = ops[0]
            unit = self._peel(unit)
            if not hasattr(unit, "symbol") or (getattr(getattr(unit, "type", None), "bitWidth", None) or 0) != 1:
                return None
            return unit.symbol.name

        def actual_expr(pin: str) -> Expr:
            return self._lower_expr(conns[pin].expression)

        if spec.category == "wire":  # buffer / DV force-release mux collapse: out = in
            in_pin = next(c.port.name for c in inst.portConnections
                          if _enum_name(c.port.direction) == "In")
            out = actual_name(spec.out)
            comb.append(CombItem(lhs=out, rhs=actual_expr(in_pin), loc=loc))
            add_cell(out)
            return
        if spec.category == "comb":  # logic gate / 2-way mux
            pinmap = {c.port.name: self._lower_expr(c.expression)
                      for c in inst.portConnections if _enum_name(c.port.direction) == "In"}
            out = actual_name(spec.out)
            comb.append(CombItem(lhs=out, rhs=spec.build(pinmap), loc=loc))
            add_cell(out)
            return
        if spec.category == "mux":  # encoded select: out = arms[sel]
            out = actual_name(spec.out)
            muxes.append(MuxItem(out=out, sel=actual_name(spec.pins["sel"], "input"),
                                 arms=tuple(actual_expr(pin) for pin in spec.inputs), loc=loc))
            add_cell(out)
            return
        if spec.category == "vcmux":  # one-hot VECTOR mux: out = sel-selected W-bit slice of `in`
            out = actual_name(spec.out)
            w = self._port_width(conns[spec.out])                 # W = output width
            n = self._port_width(conns[spec.pins["sel"]])         # N = sel width = # inputs (one-hot)
            in_e = self._lower_expr(conns[spec.pins["in"]].expression)
            # The documented lowering is FLAT -- one rule per one-hot code, plus an all-zero
            # default -- not a nested Cond chain. Emitting it as a one-hot MuxItem matches
            # docs/reference/SV_PRIMITIVE_LIBRARY.md, keeps arm selection single-valued for the same reason a
            # binary mux is (the guards are distinct selector VALUES), and avoids a nested
            # ternary the word emitter cannot read.
            muxes.append(MuxItem(out=out, sel=actual_name(spec.pins["sel"], "input"),   # a concat of select bits hoists
                                 arms=tuple(Slice(in_e, i * w + w - 1, i * w) for i in range(n)),
                                 loc=loc, onehot=True))
            add_cell(out)
            return
        if spec.category == "clock_gate":  # ICG: gclk is a DERIVED clock domain (§6.7), NOT a flop enable
            en_expr = self._lower_expr(conns[spec.pins["en"]].expression)
            if not isinstance(en_expr, Ref):   # a real ICG enable is a clean net; assign a complex gate to a wire
                flagged.append((loc, f"clock-gate {inst.name}: enable must be a net (assign the gate "
                                     "condition to a wire first), got a compound expression"))
                return
            gclk, base = actual_name(spec.pins["gclk"]), actual_name(spec.pins["clk"])
            self._derived.append(DerivedClock(name=gclk, base=base, gate=en_expr.name, loc=loc))
            add_cell(gclk)
            return
        if spec.category == "vff":  # vectored flop: per-lane independent flops (§4.6)
            lanes = params.get(spec.lanes_param, 1) or 1
            width = (params.get(spec.width_param, 1) if spec.width_param else 1) or 1
            q = actual_name(spec.pins["q"])
            d = actual_name(spec.pins["d"])
            en_bc = broadcast_enable(spec.pins["en"], lanes)      # `.En({N{x}})`: one net for all lanes
            en = en_bc if en_bc is not None else actual_name(spec.pins["en"])
            reg_names.add(q)
            # functor lane: ONE lane axis q(I) regardless of width -- the per-lane value keeps its
            # own shape (a bit at width 1, the whole W-bit WORD at width>1), so word arithmetic on a
            # lane works. The enable is per-lane too -- unless it is a broadcast, which is the
            # scalar it names. width is carried for the lane_shape marker.
            self._lane_dims[q] = self._lane_dims[d] = 1
            if en_bc is None:
                self._lane_dims.setdefault(en, 1)
                self._lane_elem_w.setdefault(en, 1)
            self._lane_elem_w[q] = self._lane_elem_w[d] = width   # per-lane bit width (for the word bridge)
            vffs.append(VffItem(q=q, d=d, en=en, clock=actual_name(spec.pins["clk"]),
                                lanes=lanes, inst=inst.name, loc=loc, width=width,
                                en_lane=en_bc is None))
            add_cell(q)
            return
        if spec.category == "latch":
            # LEVEL-SENSITIVE. Opt-in only: latches are rare, discouraged, and easy to use by
            # accident, so instantiating one is a LOUD problem unless --allow-latches says the
            # designer meant it. (Inferring a latch remains refused outright, always.)
            if not getattr(self, "_allow_latches", False):
                flagged.append((loc, f"latch {mod} {inst.name}: level-sensitive latches are "
                                     f"OFF by default -- pass --allow-latches if this design "
                                     f"genuinely uses one. A latch is transparent while its "
                                     f"enable is high (zero delay), which is a combinational "
                                     f"path, not a register"))
                return
            latches.append(LatchItem(q=actual_name(spec.pins["q"]),
                                     d=actual_name(spec.pins["d"]),
                                     en=actual_name(spec.pins["en"]),
                                     inst=inst.name, loc=loc))
            add_cell(actual_name(spec.pins["q"]))
            return
        if spec.category == "flop":
            q = actual_name(spec.pins["q"])
            clk = actual_name(spec.pins["clk"])
            d = actual_expr(spec.pins["d"])
            reset = None
            reset_value = 0
            if spec.reset:
                reset = Reset(signal=actual_name(spec.pins["rstL"]), active=spec.reset, kind="async")
                if spec.reset_value_param:
                    reset_value = params.get(spec.reset_value_param, 0) or 0
            # enable: a constant 1 -> unconditional; a signal -> guard
            guards: tuple[tuple[str, int], ...] = ()
            en = spec.pins.get("en")
            if en is not None:
                en_expr = self._lower_expr(conns[en].expression)
                if not (isinstance(en_expr, Const) and en_expr.value == 1):
                    guards = ((actual_name(en), 1),)
            reg_names.add(q)
            seq.append(SeqItem(reg=q, clock=clk, reset=reset,
                               branches=(Branch(guards=guards, value=d),),
                               has_hold=bool(guards), loc=loc, reset_value=reset_value))
            add_cell(q)
            return
        flagged.append((loc, f"unsupported primitive category {spec.category}: {mod}"))

    # -- hierarchical flattening (catalog Group 4) ---------------------------
    # A user submodule is flattened into the parent: every internal name is qualified by the
    # INSTANCE name as a structured term, val(u_inst(sig), ...), so multiple instances of the
    # same module never collide. Clock/reset ports are SUBSTITUTED to the parent actual (they
    # name a shared time domain, not per-instance state); data ports are bridged.
    def _flatten_user_instance(self, inst, ctx: LowerCtx) -> None:
        comb, seq, muxes, latches, vffs = ctx.comb, ctx.seq, ctx.muxes, ctx.latches, ctx.vffs
        signals, mems, writes = ctx.signals, ctx.mems, ctx.writes
        reg_names, cells, enums, flagged = ctx.reg_names, ctx.cells, ctx.enums, ctx.flagged
        loc = self._loc(inst)
        name = inst.name
        conns = list(inst.portConnections)
        out_nets: list[str] = []   # parent nets this submodule instance drives (for cell/3)

        # lower the submodule body (recursing into ITS instances -> already-qualified names)
        #
        # F15: THREE per-module accumulators live on `self` and are RESET by `_lower_body`, so
        # the recursive call below silently took them over from the parent. Everything the child
        # lowered landed in the parent's Design under the CHILD's unqualified names -- an
        # inferred latch or a `$rose` inside a submodule derived `il` / `s__rose` in the parent
        # namespace while the parent's own consumers read `u(il)` / `u(s__rose)`, so the real
        # signal was dark AND a same-named parent signal would have been silently collided with.
        # Explicit latches fared differently and worse: the parent builds its Design from a LOCAL
        # `latches` list, so the child's were simply dropped.
        #
        # Saving and restoring them here is the same discipline `_scope`/`_eval_scope` already
        # get, and the lifts further down are what actually carries the child's constructs across
        # -- qualified, like every other family.
        saved, saved_eval = self._scope, self._eval_scope
        saved_il, saved_ed, saved_la = self._inferred_latches, self._blk_edges, self._latches
        try:
            sub = self._lower_body(inst.body, inst.definition.name)
        finally:
            self._scope, self._eval_scope = saved, saved_eval
            self._inferred_latches, self._blk_edges = saved_il, saved_ed
            self._latches = saved_la

        # clock/reset formals name a shared time domain -> substitute the parent actual.
        # Must scan EVERY clocked construct: seq regs, memory writes, vectored flops, AND the BASE clock
        # of any gated (ICG) clock -- a cross-domain ICG whose base clock is NOT also a flop clock would
        # otherwise be wrapped u(base) instead of substituted to the parent's clock net (the gated clock
        # rule `time(u(gclk)):-time(<base>),..` then never fires because the scenario drives time(base)).
        clock_formals = ({it.clock for it in sub.seq}
                         | {w.clock for w in sub.mem_writes}
                         | {it.clock for it in sub.vffs}
                         | {dc.base for dc in sub.derived_clocks})
        reset_formals = {it.reset.signal for it in sub.seq if it.reset is not None}
        special = clock_formals | reset_formals

        def actual_name_of(c) -> str:
            e = c.expression
            if _enum_name(e.kind) == "Assignment":  # output port wraps the net in an lvalue
                e = e.left
            pe = self._peel(e)
            if _enum_name(pe.kind) != "NamedValue" or getattr(pe, "symbol", None) is None:
                # a struct / array / clock / reset port needs a NAMED actual (its bridge is per
                # part, or a domain substitution); an expression here used to surface as a raw
                # AttributeError -- loud, but not a reason
                raise NotImplementedError(
                    f"instance {name}: port {c.port.name} is a struct/array/clock/reset port "
                    f"connected to an EXPRESSION actual (`{str(getattr(e, 'syntax', '')).strip()}`) "
                    f"-- its bridge needs a plain signal on both sides (deferred)")
            return pe.symbol.name

        def _bridge_out_operand(op, val: Expr, w: int, loc, bridges, out_nets, flagged) -> None:
            """Drive one output-side target ``op`` from the submodule output value ``val``. A plain
            net -> direct bridge; a plain-vector part-select -> a partial (reassembled into the whole
            net by ``_assemble_partials``); else flag loud."""
            k = _enum_name(op.kind)
            if k == "NamedValue":
                bridges.append(CombItem(lhs=op.symbol.name, rhs=val, loc=loc))
                out_nets.append(op.symbol.name)
                return
            pw = self._partselect_lhs(op)
            if pw is not None:
                target, tw, poff, pw_ = pw
                self._record_partial_expr(target, tw, poff, pw_, val, loc)
                out_nets.append(target)
                return
            flagged.append((loc, f"submodule output target {k} on {name} (unsupported shape)"))

        subst: dict[str, str] = {}
        bridges: list[CombItem] = []
        # the child's own arrays, by FORMAL name. Taken from the SUB design rather than from
        # `mems`: the qualified copies (`u_inst(buf_)`) are appended further down, AFTER this
        # loop runs, so reading `mems` here finds nothing at all.
        child_arrays = {m.name: m for m in sub.mems}
        for c in conns:
            if _enum_name(c.port.kind) == "InterfacePort":
                continue   # interface ports carry no direction; aliased below (shared wires)
            if c.expression is None:
                # UNCONNECTED PORT. The two directions are not symmetric:
                #   * an unconnected OUTPUT is simply unobserved by the parent -- common,
                #     legitimate, and harmless. No bridge, no complaint.
                #   * an unconnected INPUT is a real design defect, and modelling it silently is
                #     WORSE than dropping it. The formal gets no driver, so every rule reading it
                #     fails to fire, and the 1-bit excluded-middle rule
                #     (`val(x,0,T) :- …, not val(x,1,T)`) then turns "undriven" into a definite
                #     CONSTANT 0. The design behaves as if the floating input were tied low, with
                #     no warning -- and a property over the affected outputs is "proved" against a
                #     model the hardware does not implement.
                if _enum_name(c.port.direction) == "In":
                    flagged.append((loc, f"instance {name}: input port '{c.port.name}' is "
                                         f"UNCONNECTED. It gets no driver, so every rule reading "
                                         f"it fails and the 1-bit fallback makes it a constant 0 "
                                         f"-- the design would silently behave as if it were tied "
                                         f"low. Connect it, or tie it off explicitly in the RTL"))
                continue
            formal = c.port.name
            direction = _enum_name(c.port.direction)
            ptype = getattr(c.port, "type", None)
            port_struct = ptype is not None and _enum_name(ptype.canonicalType.kind) == "PackedStructType"
            if formal in special:
                subst[formal] = actual_name_of(c)
            elif port_struct:
                # a STRUCT port: both sides use one-level field subsignals X(field). Bridge per
                # field -- u_inst(p(f)) <-> actual(f) -- not the whole struct (which would leave
                # the submodule's p(f) subsignals undriven, a silent miss).
                actual = actual_name_of(c)
                if actual not in self._structs:
                    flagged.append((loc, f"struct port {formal} on {name}: actual {actual!r} is not a "
                                         "decomposed struct"))
                    return
                for f in ptype.canonicalType:
                    sub_f, act_f = f"{name}({formal}({f.name}))", f"{actual}({f.name})"
                    if direction == "In":
                        bridges.append(CombItem(lhs=sub_f, rhs=Ref(act_f), loc=loc))
                    else:
                        bridges.append(CombItem(lhs=act_f, rhs=Ref(sub_f), loc=loc))
                        out_nets.append(act_f)
            elif formal in child_arrays:
                # F7-flat: an unpacked ARRAY port bridges PER CELL. Falling through to the
                # generic word bridge below produced `u_inst(buf_) = arr` -- and since a Mem has
                # no entry in `signals` for the emitter to take a width from, that rendered as a
                # ONE-BIT excluded-middle pair, while the consumer read a CELL
                # (`val(u_inst(buf_(V0)), ..)`). Both the word atom and the cells were dark.
                #
                # Modelled on the STRUCT port case above -- same problem, same answer: bridge the
                # parts, not the aggregate. The difference is that a struct's parts are a fixed
                # field list while an array's are an address DOMAIN, so this is one lane-rolled
                # combinational write over `addr(mem, I[, J])` rather than one item per part.
                _cm = child_arrays[formal]
                _nd = len(_cm.dims or (_cm.depth,))
                _act = actual_name_of(c)
                if _act not in self._mem_dims:
                    flagged.append((loc, f"array port {formal} on {name}: actual {_act!r} is "
                                         f"not an unpacked array, so there are no cells to "
                                         f"bridge (a whole-array actual is required)"))
                    return
                _ix = tuple(LaneIdx(p) for p in range(_nd))
                _child, _parent = f"{name}({formal})", _act
                _dst, _src = ((_child, _parent) if direction == "In" else (_parent, _child))
                writes.append(MemWrite(mem=_dst, addrs=_ix, data=MemRef(_src, _ix),
                                       guards=(), clock="", loc=loc, lane_rolled=True,
                                       lane_hi=(None,) * _nd))
                if direction != "In":
                    out_nets.append(_parent)
            elif direction == "In":   # data input: u_inst(formal) <- parent actual (may be slice/concat)
                bridges.append(CombItem(lhs=f"{name}({formal})",
                                        rhs=self._lower_expr(c.expression), loc=loc))
            elif direction == "Out":  # data output: parent actual <- u_inst(formal); the actual may be
                src = Ref(f"{name}({formal})")                 # a plain net, a part-select, or a concat
                e = c.expression
                if _enum_name(e.kind) == "Assignment":
                    e = e.left
                ek = _enum_name(e.kind)
                if ek == "NamedValue":
                    out = e.symbol.name
                    bridges.append(CombItem(lhs=out, rhs=src, loc=loc))
                    out_nets.append(out)
                elif ek == "Concatenation":     # {a, b[..]} <- submodule output: split MSB-first
                    total = getattr(getattr(e, "type", None), "bitWidth", None)
                    off = total
                    for op in e.operands:
                        w = getattr(getattr(op, "type", None), "bitWidth", 1) or 1
                        off -= w
                        _bridge_out_operand(op, Slice(src, off + w - 1, off), w, loc,
                                            bridges, out_nets, flagged)
                else:                            # a part-select x[hi:lo] <- submodule output (RMW)
                    _bridge_out_operand(e, src, getattr(getattr(e, "type", None), "bitWidth", 1) or 1,
                                        loc, bridges, out_nets, flagged)
            else:
                flagged.append((loc, f"inout/ref port {formal} on {name} not supported"))

        # interface ports: the submodule's interface signals port(sig) ARE the connected parent
        # interface instance's nets actual(sig) (shared wires) -> alias by substitution, no copy.
        for sm in inst.body:
            if _enum_name(sm.kind) != "InterfacePort":
                continue
            conn = getattr(sm, "connection", None)
            actual = conn[0].name if conn and len(conn) >= 1 and hasattr(conn[0], "name") else None
            if actual is None or actual not in self._interfaces:
                flagged.append((loc, f"interface port {sm.name} on {name}: connected instance "
                                     f"{actual!r} not registered (declare the interface before the instance)"))
                return
            for sig in self._interfaces[actual]:
                subst[f"{sm.name}({sig})"] = f"{actual}({sig})"

        def w(n: str) -> str:
            return self._wrap_name(n, name, subst)

        # merge submodule signals (clock/reset port signals ARE the parent's -> skip)
        for s in sub.signals:
            if s.name in special:
                continue
            wn = w(s.name)
            if wn not in signals:
                signals[wn] = Signal(name=wn, irtype=s.irtype, is_reg=s.is_reg,
                                     is_port=False, direction=None, initial=None, loc=s.loc)
        for it in sub.comb:
            # `dataclasses.replace` so a field neither renamed nor wrapped (`lane_lo`, `lane_hi`)
            # rides through: listing the fields DROPPED `lane_hi` here for every partial loop
            # inside a flattened submodule (the same trap `_norm_design` records).
            comb.append(dataclasses.replace(it, lhs=w(it.lhs),
                                            rhs=self._wrap_expr(it.rhs, name, subst)))
        for it in sub.seq:
            reg_names.add(w(it.reg))
            reset = it.reset
            if reset is not None:
                reset = Reset(signal=w(reset.signal), active=reset.active, kind=reset.kind)
            branches = tuple(
                Branch(guards=tuple((w(g), p) for g, p in b.guards),
                       value=self._wrap_expr(b.value, name, subst),
                       tag_guards=tuple((w(s), tag) for s, tag in b.tag_guards),
                       neg_matches=tuple((w(s), v) for s, v in b.neg_matches), loc=b.loc)
                for b in it.branches)
            # a COMBINATIONAL seq item (always_comb) has clock "" -> keep it "" (wrapping "" would
            # make a phantom clock u_inst()); preserve the combinational flag + the lane domain too.
            seq.append(dataclasses.replace(
                it, reg=w(it.reg), clock=(w(it.clock) if it.clock else ""), reset=reset,
                branches=branches, lane_domain=(w(it.lane_domain) if it.lane_domain else None)))
        for it in sub.muxes:
            muxes.append(MuxItem(out=w(it.out), sel=w(it.sel),
                                 arms=tuple(self._wrap_expr(a, name, subst) for a in it.arms),
                                 loc=it.loc))
        for it in sub.vffs:
            vffs.append(VffItem(q=w(it.q), d=w(it.d), en=w(it.en), clock=w(it.clock),
                                lanes=it.lanes, inst=w(it.inst), loc=it.loc))
        # F15: the three families the flattening never carried. `dataclasses.replace` rather
        # than a positional rebuild, deliberately -- each of these nodes has grown optional
        # fields (`hold_only`, `variants`) since it was written, and a positional copy silently
        # drops the ones it does not mention, which is the failure this whole entry is about.
        for it in sub.latches:
            latches.append(dataclasses.replace(
                it, q=w(it.q), d=w(it.d), en=w(it.en), inst=w(it.inst)))
        for il in sub.inferred_latches:
            self._inferred_latches.append(dataclasses.replace(
                il, lhs=w(il.lhs), value=self._wrap_expr(il.value, name, subst),
                variants=tuple((tuple((w(g), p) for g, p in gs),
                                self._wrap_expr(v, name, subst)) for gs, v in il.variants)))
        for ed in sub.edges:
            # the clock is a FORMAL of the child: `w` routes it through `subst`, so it resolves
            # to the parent's actual clock net rather than a phantom `u_inst(clk)`.
            self._blk_edges.append(dataclasses.replace(
                ed, lhs=w(ed.lhs), sig=w(ed.sig), clock=(w(ed.clock) if ed.clock else ed.clock)))
        # submodule DERIVED (gated) clocks: instance-qualify them so two instances of the same unit get
        # distinct per-instance gated clocks. The base clock is a shared domain (subst maps it to the
        # parent actual); the gate is a per-instance data signal (wrapped to u_inst(en), driven by its
        # bridge). So `clkgate` inside gated_unit u0/u1 -> time(u0(gclk)):-time(clk),val(u0(en),1) and
        # time(u1(gclk)):-time(clk),val(u1(en),1) -- each gated by THAT instance's enable.
        for dc in sub.derived_clocks:
            self._derived.append(DerivedClock(name=w(dc.name), base=w(dc.base),
                                              gate=w(dc.gate), loc=dc.loc, kind=dc.kind))
        for n in sub.lane_signals:  # genvar-indexed signals (wrapped), preserving dim count
            self._lane_dims[w(n)] = sub.lane_dims.get(n, 1)
        # merge submodule MEMORIES (instance-qualified): the array decl + its writes. Reads inside the
        # sub are MemRefs in comb/seq exprs, already wrapped above. Clock formals subst to the parent.
        for m in sub.mems:
            wn = w(m.name)
            # wrap the element-type NAME as a functor too (w("mem_elem") -> u_inst(mem_elem)); a
            # suffix form "u_inst(mem)_elem" would be malformed clingo.
            mems.append(Mem(name=wn, elem=ElementType(w(m.elem.name), m.elem.kind, m.elem.width,
                                                      four_state=m.elem.four_state),
                            addr_width=m.addr_width, depth=m.depth, loc=m.loc, dims=m.dims))
            self._mem_depth[wn] = m.depth
            self._mem_dims[wn] = m.dims or (m.depth,)
        for mw in sub.mem_writes:
            writes.append(MemWrite(
                mem=w(mw.mem),
                addrs=tuple(self._wrap_expr(a, name, subst) for a in mw.addrs),
                data=self._wrap_expr(mw.data, name, subst),
                guards=tuple((w(g), p) for g, p in mw.guards),
                clock=(w(mw.clock) if mw.clock else ""), loc=mw.loc,
                rmw_slices=tuple((off, sw, self._wrap_expr(v, name, subst))
                                 for off, sw, v in mw.rmw_slices),
                cell_width=mw.cell_width, lane_rolled=mw.lane_rolled, lane_hi=mw.lane_hi,
                lane_lo=mw.lane_lo))
        comb.extend(bridges)
        # structural manifest: the submodule instance itself + its own (re-qualified) nested cells.
        # A sub's direct child carried parent == the sub's module name -> re-parent to this instance;
        # deeper paths are wrapped. (cell_type already lowercased in the sub -- don't re-lower.)
        cells.append(CellInfo(inst=name, cell_type=inst.definition.name.lower(),
                              outs=tuple(out_nets), parent=self._current_module))
        for c in sub.cells:
            cells.append(CellInfo(inst=w(c.inst), cell_type=c.cell_type,
                                  outs=tuple(w(o) for o in c.outs),
                                  parent=(name if c.parent == inst.definition.name else w(c.parent))))
        # enum TYPES are package-global -> surface a submodule's enums in the flat schema (dedup by
        # name); and propagate the sub's flags so a nested failure stays LOUD, never a silent miss.
        for en in sub.enums:
            enums.setdefault(en.name, en)
        flagged.extend(sub.flagged)

    # -- arrays of instances (catalog §4.7) ----------------------------------
    # `sub u[N] (.a(a), .b(b), .y(y))` is a generate-for of instances: element i wires to the
    # index-i slice of each shared bus. We lower the submodule body ONCE and lift it to the
    # INDEXED (lane) shape -- the array index is the lane I. Sliced ports SUBSTITUTE to the
    # parent net (the slice index IS the lane), broadcast scalar ports (clk/rst) substitute as a
    # shared scalar, and internal signals are wrapped `u(sig)` and lane-indexed. Non-uniform
    # arrays (per-element params, non-index wiring) are flagged, never mistranslated.
    def _lower_instance_array(self, arr, ctx: LowerCtx) -> None:
        comb, seq, muxes, latches, vffs = ctx.comb, ctx.seq, ctx.muxes, ctx.latches, ctx.vffs
        signals, mems, writes = ctx.signals, ctx.mems, ctx.writes
        reg_names, cells, enums, flagged = ctx.reg_names, ctx.cells, ctx.enums, ctx.flagged
        elements = list(getattr(arr, "elements", []))
        name = getattr(arr, "arrayName", None) or "arr"
        loc = self._loc(arr)
        n = len(elements)
        if n == 0:
            return
        e0 = elements[0]
        mod = e0.definition.name if getattr(e0, "definition", None) else "?"
        prim = primitives.lookup(mod)
        if prim is None and getattr(e0, "body", None) is None:
            flagged.append((loc, f"unsupported instance array: {mod} {name}"))
            return

        def actual(c):  # the connected expression; an output wraps the lvalue in an Assignment
            e = c.expression
            e = e.left if _enum_name(e.kind) == "Assignment" else e
            return self._peel(e)   # strip any width Conversion wrapper

        # classify each formal: broadcast scalar (same whole net for all elements) or per-lane
        # slice (net[i] with i == the element position). Anything else -> non-uniform -> flag.
        subst: dict[str, str] = {}
        lane_ports: set[str] = set()
        for pc0 in e0.portConnections:
            formal = pc0.port.name
            kinds: list[str] = []
            nets: list[str] = []
            idxs: list[int | None] = []
            for el in elements:
                c = next((p for p in el.portConnections if p.port.name == formal), None)
                e = actual(c) if c is not None else None
                ek = _enum_name(e.kind) if e is not None else "?"
                if ek == "NamedValue":
                    kinds.append("scalar")
                    nets.append(self._peel(e).symbol.name)
                    idxs.append(None)
                elif ek == "ElementSelect" and _enum_name(self._peel(e.value).kind) == "NamedValue":
                    kinds.append("lane")
                    nets.append(self._peel(e.value).symbol.name)
                    idxs.append(self._const_of(self._peel(e.selector)))  # peel: selector may be wrapped
                else:
                    kinds.append("?")
                    nets.append("")
                    idxs.append(None)
            if any(k == "?" for k in kinds) or len(set(nets)) != 1:
                flagged.append((loc, f"non-uniform array port {formal} on {name}[{n}] "
                                     "(lane-rolling needs an index slice or a broadcast scalar)"))
                return
            net = nets[0]
            # A rolled rule reads val(net, I, ...) over lane I = the bit index, so each element
            # must slice a DISTINCT bit and the slices must cover exactly {0..n-1} (order-free:
            # ascending [n] and descending [n-1:0] both qualify; pyslang slices every port of an
            # element to the SAME bit, so cross-port lane alignment is guaranteed by construction).
            if all(k == "scalar" for k in kinds):
                subst[formal] = net                       # broadcast (clock/reset): shared scalar
            elif all(k == "lane" for k in kinds) and sorted(i for i in idxs if i is not None) == list(range(n)):
                subst[formal] = net          # per-lane slice covering bits 0..n-1
                lane_ports.add(net)
                # the lane ELEMENT width: `q[i]` of a packed 2-D `[N-1:0][W-1:0] q` is W bits, and
                # the lane<->word bridge must split the word at I*W. It defaulted to 1: the lane
                # rules produced N W-bit lanes while the bridge waited for N*W one-bit ones -- the
                # port was dark (found by the hierarchical sweep, modular).
                self._note_lane_elem_w(net, getattr(getattr(e, "type", None), "bitWidth", 1) or 1)
            else:
                flagged.append((loc, f"non-uniform array port {formal} on {name}[{n}] "
                                     "(slices must cover bits 0..n-1, one distinct bit per element)"))
                return

        def params_of(el) -> tuple:
            return tuple(sorted((p.name, self._cv_int(p.value))
                                for p in el.body if _enum_name(p.kind) == "Parameter"))
        if any(params_of(el) != params_of(e0) for el in elements):
            flagged.append((loc, f"non-uniform parameters across {name}[{n}] (lane-rolling needs uniform)"))
            return

        # an array of PRIMITIVE cells -> lane-roll the primitive over the array index (= the lane),
        # reusing the same port classification (subst/lane_ports) + lane machinery as a submodule array.
        if prim is not None:
            self._lower_primitive_array(prim, name, n, subst, lane_ports, mod,
                                        comb, seq, vffs, signals, reg_names, cells, flagged, loc)
            return

        # lower the submodule body once (scalar), then lift to the lane shape
        self._lift_instance_lanes(e0.body, mod, name, subst, lane_ports, (n,), loc,
                                  comb, seq, signals, reg_names, cells, enums, flagged)

    def _lift_instance_lanes(self, e0_body: object, mod: str, name: str, subst: dict, lane_ports: set,
                             dims: tuple, loc: object, comb: list, seq: list, signals: dict,
                             reg_names: set, cells: list, enums: dict, flagged: list) -> None:
        """Lower a submodule body ONCE (scalar) and lift it to the lane shape over array index/indices:
        internal signals wrap to ``name(sig)`` and are INDEXED (one index per ``dims`` entry), port nets
        are substituted (per-lane slice -> INDEXED parent net; broadcast -> shared scalar), every rule fans
        over ``lane(name, 0..n1-1[, 0..n2-1])``. Shared by the instance-array (`sub u[N]`, 1-D), the
        generate-for-of-instances (`for(i) sub u(.x(d[i]))`, 1-D), and the NESTED generate-of-instances
        (`for(i) for(j) sub u(.x(a[i][j]))`, 2-D) paths -- each classifies ports into (subst, lane_ports)
        with the right per-dim shape, then calls this identical lift with ``dims = (n,)`` or ``(ni, nj)``."""
        nd = len(dims)
        saved, saved_eval = self._scope, self._eval_scope
        try:
            sub = self._lower_body(e0_body, mod)
        finally:
            self._scope, self._eval_scope = saved, saved_eval
        if sub.mems or sub.vffs or sub.muxes:
            flagged.append((loc, f"array submodule {name} ({mod}) has memory/vff/mux (deferred)"))
            return

        def w(nm: str) -> str:
            return self._wrap_name(nm, name, subst)

        for net in lane_ports:          # shared bus nets are read/written per-lane -> INDEXED (nd indices)
            self._lane_dims[net] = nd
        for s in sub.signals:           # internal (non-port) signals -> wrapped, lane-indexed
            if s.name in subst:
                continue
            wn = w(s.name)
            if wn not in signals:
                signals[wn] = Signal(name=wn, irtype=s.irtype, is_reg=s.is_reg, is_port=False,
                                     direction=None, initial=None, loc=s.loc)
            self._lane_dims[wn] = nd
        self._lane_domains[name] = dims  # lane(name, 0..n1-1[, 0..n2-1]) -- binds the index(es)

        for it in sub.comb:
            # `dataclasses.replace` so a field neither renamed nor wrapped (`lane_lo`, `lane_hi`)
            # rides through: listing the fields DROPPED `lane_hi` here for every partial loop
            # inside a flattened submodule (the same trap `_norm_design` records).
            comb.append(dataclasses.replace(it, lhs=w(it.lhs),
                                            rhs=self._wrap_expr(it.rhs, name, subst)))
        for it in sub.seq:
            reg = w(it.reg)
            reg_names.add(reg)
            reset = it.reset
            if reset is not None:
                reset = Reset(signal=w(reset.signal), active=reset.active, kind=reset.kind)
            branches = tuple(
                Branch(guards=tuple((w(g), p) for g, p in b.guards),
                       value=self._wrap_expr(b.value, name, subst),
                       tag_guards=tuple((w(s), tag) for s, tag in b.tag_guards),
                       neg_matches=tuple((w(s), v) for s, v in b.neg_matches), loc=b.loc)
                for b in it.branches)
            seq.append(dataclasses.replace(
                it, reg=reg, clock=(w(it.clock) if it.clock else ""), reset=reset,
                branches=branches, lane_domain=name))
        # structural manifest: the array as one lane-rolled cell (lane-ness shown by lane(name,0..n-1))
        # + its own nested cells, re-qualified through the array instance name.
        cells.append(CellInfo(inst=name, cell_type=mod.lower(), outs=(), parent=self._current_module))
        for c in sub.cells:
            cells.append(CellInfo(inst=w(c.inst), cell_type=c.cell_type,
                                  outs=tuple(w(o) for o in c.outs),
                                  parent=(name if c.parent == mod else w(c.parent))))
        for en in sub.enums:           # package-global enum types surface in the flat schema (dedup)
            enums.setdefault(en.name, en)
        flagged.extend(sub.flagged)    # nested flags stay loud

    def _generate_instances_genvar(self, arr) -> str | None:
        """If a for-generate stamps ONE instance per iteration (`for(i) sub u(...)`) and nothing else,
        return the genvar name; else None (-> the normal generate dispatch). Detected so it can lane-roll
        like the `sub u[N]` instance array instead of crashing in the per-instance flatten."""
        entries = list(getattr(arr, "entries", []))
        if not entries:
            return None
        genvar = None
        for e in entries:
            members = list(e)
            insts = [x for x in members if _enum_name(x.kind) == "Instance"]
            params = [x for x in members if _enum_name(x.kind) == "Parameter"]
            others = [x for x in members if _enum_name(x.kind) not in ("Instance", "Parameter")]
            if len(insts) != 1 or others:    # purely a one-instance-per-iteration generate, nothing mixed in
                return None
            if params:
                genvar = params[0].name
        return genvar

    def _lower_generate_instances(self, arr, genvar: str, ctx: LowerCtx) -> None:
        """`for(i) sub u(.a(d[i]), .y(o[i]))` -> ONE lane-rolled rule-set, exactly like the `sub u[N]`
        instance array. Classify each port across the entries: `NamedValue(net)` = broadcast scalar,
        `net[genvar]` = per-lane slice (lane = the entry's genvar value, 0..n-1); then reuse the shared
        lane lift. Non-uniform / mixed / non-genvar-indexed -> flag (sound)."""
        comb, seq, muxes, latches, vffs = ctx.comb, ctx.seq, ctx.muxes, ctx.latches, ctx.vffs
        signals, mems, writes = ctx.signals, ctx.mems, ctx.writes
        reg_names, cells, enums, flagged = ctx.reg_names, ctx.cells, ctx.enums, ctx.flagged
        entries = list(getattr(arr, "entries", []))
        n = len(entries)
        name = getattr(arr, "arrayName", None) or "g"
        loc = self._loc(arr)
        insts = [next((x for x in e if _enum_name(x.kind) == "Instance"), None) for e in entries]
        e0 = insts[0]
        mod = e0.definition.name if getattr(e0, "definition", None) else "?"

        def gval(e) -> int | None:
            p = next((x for x in e if _enum_name(x.kind) == "Parameter" and x.name == genvar), None)
            return self._cv_int(p.value) if p is not None else None

        def actual(c):
            ex = c.expression
            ex = ex.left if _enum_name(ex.kind) == "Assignment" else ex
            return self._peel(ex)

        subst: dict[str, str] = {}
        lane_ports: set[str] = set()
        for pc0 in e0.portConnections:
            formal = pc0.port.name
            kinds, nets, idxs = [], [], []
            for inst, ent in zip(insts, entries, strict=True):
                c = next((p for p in inst.portConnections if p.port.name == formal), None)
                e = actual(c) if c is not None and c.expression is not None else None
                ek = _enum_name(e.kind) if e is not None else "?"
                sel = self._peel(e.selector) if ek == "ElementSelect" else None
                if ek == "NamedValue":
                    kinds.append("scalar")
                    nets.append(self._peel(e).symbol.name)
                    idxs.append(None)
                elif (ek == "ElementSelect" and _enum_name(self._peel(e.value).kind) == "NamedValue"
                      and _enum_name(sel.kind) == "NamedValue" and sel.symbol.name == genvar):
                    kinds.append("lane")
                    nets.append(self._peel(e.value).symbol.name)
                    idxs.append(gval(ent))
                else:
                    kinds.append("?")
                    nets.append("")
                    idxs.append(None)
            if any(k == "?" for k in kinds) or len(set(nets)) != 1:
                flagged.append((loc, f"non-uniform generate-instance port {formal} on {name}[{n}] "
                                     "(needs a `net[genvar]` slice or a broadcast scalar)"))
                return
            net = nets[0]
            if all(k == "scalar" for k in kinds):
                subst[formal] = net
            elif all(k == "lane" for k in kinds) and sorted(i for i in idxs if i is not None) == list(range(n)):
                subst[formal] = net
                lane_ports.add(net)
                self._note_lane_elem_w(net, getattr(getattr(e, "type", None), "bitWidth", 1) or 1)
            else:
                flagged.append((loc, f"non-uniform generate-instance port {formal} on {name}[{n}]"))
                return

        prim = primitives.lookup(mod)
        if prim is not None:
            self._lower_primitive_array(prim, name, n, subst, lane_ports, mod,
                                        comb, seq, vffs, signals, reg_names, cells, flagged, loc)
            return
        if getattr(e0, "body", None) is None:
            flagged.append((loc, f"unsupported generate instance: {mod} {name}"))
            return
        self._lift_instance_lanes(e0.body, mod, name, subst, lane_ports, (n,), loc,
                                  comb, seq, signals, reg_names, cells, enums, flagged)

    def _nested_instance_generate(self, arr) -> tuple | None:
        """If `arr` is a 2-LEVEL `for(i) for(j) sub u(...)` -- an outer for-generate whose EVERY block holds
        exactly ONE inner instance-generate (and the genvar param) -- return
        (outer_gv, inner_gv, instances, ni, nj) with `instances` the flat i-major list of leaf instances;
        else None. Only 2 levels (a deeper nest falls through to the normal generate dispatch -> flags)."""
        entries = list(getattr(arr, "entries", []))
        if not entries:
            return None
        outer_gv, inners = None, []
        for e in entries:
            members = list(e)
            gbas = [x for x in members if _enum_name(x.kind) == "GenerateBlockArray"]
            params = [x for x in members if _enum_name(x.kind) == "Parameter"]
            others = [x for x in members if _enum_name(x.kind) not in ("GenerateBlockArray", "Parameter")]
            if len(gbas) != 1 or others:        # not purely one nested generate per outer block
                return None
            if params:
                outer_gv = params[0].name
            inners.append(gbas[0])
        inner_gv = self._generate_instances_genvar(inners[0])
        if inner_gv is None or any(self._generate_instances_genvar(ia) != inner_gv for ia in inners):
            return None                          # inner blocks aren't a uniform single-instance generate
        njs = {len(list(getattr(ia, "entries", []))) for ia in inners}
        if len(njs) != 1:
            return None                          # ragged inner dimension -> not a rectangular grid
        instances = [next((x for x in je if _enum_name(x.kind) == "Instance"), None)
                     for ia in inners for je in ia.entries]
        return (outer_gv, inner_gv, instances, len(inners), njs.pop())

    def _lower_nested_generate_instances(self, arr, outer_gv: str, inner_gv: str, instances: list,
                                         ni: int, nj: int, ctx: LowerCtx) -> None:
        """`for(i) for(j) sub u(.x(a[i][j]))` -> ONE 2-D lane-rolled rule-set (lane indices = the two
        genvars). Each port is either a 2-D slice `net[i][j]` (-> per-lane INDEXED parent net) or a bare
        net (broadcast scalar); then the shared lift rolls the submodule body over lane(name, 0..ni-1,
        0..nj-1). Non-slice / partial-slice ports flag (sound)."""
        comb, seq, muxes, latches, vffs = ctx.comb, ctx.seq, ctx.muxes, ctx.latches, ctx.vffs
        signals, mems, writes = ctx.signals, ctx.mems, ctx.writes
        reg_names, cells, enums, flagged = ctx.reg_names, ctx.cells, ctx.enums, ctx.flagged
        name = getattr(arr, "arrayName", None) or instances[0].name
        loc = self._loc(arr)
        e0 = instances[0]
        mod = e0.definition.name if getattr(e0, "definition", None) else "?"

        def lane_net(c) -> str | None:           # net[outer_gv][inner_gv] -> base net name, else None
            ex = c.expression
            ex = ex.left if _enum_name(ex.kind) == "Assignment" else ex
            e = self._peel(ex)
            if _enum_name(e.kind) != "ElementSelect":
                return None
            s_in = self._peel(e.selector)        # innermost index -> inner genvar
            e1 = self._peel(e.value)
            if (_enum_name(s_in.kind) != "NamedValue" or s_in.symbol.name != inner_gv
                    or _enum_name(e1.kind) != "ElementSelect"):
                return None
            s_out = self._peel(e1.selector)      # outer index -> outer genvar
            base = self._peel(e1.value)
            if (_enum_name(s_out.kind) != "NamedValue" or s_out.symbol.name != outer_gv
                    or _enum_name(base.kind) != "NamedValue"):
                return None
            return base.symbol.name

        subst: dict[str, str] = {}
        lane_ports: set[str] = set()
        for c in e0.portConnections:             # the body is one instance template -> classify on e0
            if _enum_name(c.port.kind) == "InterfacePort" or c.expression is None:
                continue
            formal = c.port.name
            ex = c.expression.left if _enum_name(c.expression.kind) == "Assignment" else c.expression
            if _enum_name(self._peel(ex).kind) == "NamedValue":
                subst[formal] = self._peel(ex).symbol.name      # broadcast scalar
                continue
            net = lane_net(c)
            if net is None:
                flagged.append((loc, f"nested generate-instance port {formal} on {name} needs a "
                                     f"`net[{outer_gv}][{inner_gv}]` 2-D slice or a broadcast scalar"))
                return
            subst[formal] = net
            lane_ports.add(net)

        if primitives.lookup(mod) is not None:
            flagged.append((loc, f"nested generate of PRIMITIVE cells ({name}) not yet supported"))
            return
        if getattr(e0, "body", None) is None:
            flagged.append((loc, f"unsupported nested generate instance: {mod} {name}"))
            return
        self._lift_instance_lanes(e0.body, mod, name, subst, lane_ports, (ni, nj), loc,
                                  comb, seq, signals, reg_names, cells, enums, flagged)

    def _lower_primitive_array(self, prim, name: str, n: int, subst: dict, lane_ports: set, mod: str,
                               comb, seq, vffs, signals, reg_names, cells, flagged, loc) -> None:
        """An array of N PRIMITIVE cells (1-bit elements) lane-rolled over the array index (= lane I):
        a flop array -> a lane register (broadcast/no enable) or a VFF (per-lane enable); a gate/buf
        array -> a lane comb rule. Sliced ports are lane-indexed (val(net, I, ..)); broadcast ports
        (clk, a shared enable) stay scalar. ``subst`` maps each pin to its parent net (from the shared
        port classification); ``lane_ports`` are the sliced nets. mux and other categories defer."""
        self._lane_domains[name] = (n,)        # lane(name, 0..n-1) -- binds I where no operand does
        for net in lane_ports:                # the sliced nets are lane signals (INDEXED)
            self._lane_dims[net] = 1
        cells.append(CellInfo(inst=name, cell_type=mod.lower(), outs=(), parent=self._current_module))
        pins = prim.pins

        if prim.category in ("comb", "wire"):     # logic gate / buffer -> a per-lane comb rule
            out = subst.get(prim.out)
            if out is None:
                flagged.append((loc, f"primitive array {mod} {name}[{n}]: output {prim.out!r} unconnected"))
                return
            if prim.category == "wire":
                ins = [subst[p] for p in subst if p != prim.out]
                if len(ins) != 1:
                    flagged.append((loc, f"primitive array {mod} {name}[{n}]: buffer needs one input"))
                    return
                comb.append(CombItem(lhs=out, rhs=Ref(ins[0]), loc=loc))
            else:
                pinmap = {p: Ref(subst[p]) for p in subst if p != prim.out}
                comb.append(CombItem(lhs=out, rhs=prim.build(pinmap), loc=loc))
            return

        if prim.category == "flop":
            q, d, clk = subst.get(pins.get("q")), subst.get(pins.get("d")), subst.get(pins.get("clk"))
            if q is None or d is None or clk is None:
                flagged.append((loc, f"primitive array {mod} {name}[{n}]: flop needs clk/d/q connected"))
                return
            reg_names.add(q)
            en_pin = pins.get("en")
            en = subst.get(en_pin) if en_pin else None
            if en is not None and en in lane_ports:       # per-lane enable -> a VFF (per-lane capture)
                self._lane_dims[q] = self._lane_dims[d] = 1
                vffs.append(VffItem(q=q, d=d, en=en, clock=clk, lanes=n, inst=name, loc=loc, width=1))
            else:                                         # broadcast / no enable -> a lane register
                guards = ((en, 1),) if en is not None else ()
                seq.append(SeqItem(reg=q, clock=clk, reset=None,
                                   branches=(Branch(guards=guards, value=Ref(d)),),
                                   has_hold=bool(guards), loc=loc, lane_domain=name))
            return

        flagged.append((loc, f"primitive array {mod} {name}[{n}]: category {prim.category!r} deferred"))

