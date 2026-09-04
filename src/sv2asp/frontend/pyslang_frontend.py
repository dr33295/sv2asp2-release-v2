from __future__ import annotations

import os

import dataclasses
import pyslang

# --- pyslang >=11 compat shim -------------------------------------------------
# pyslang 11.0.0 moved several names that used to live at the top level (the
# version this project pins to, pyslang==10.0.0) into submodules. This is a
# no-op against the pinned version (the names are already present at top
# level there); it only activates when running against a newer pyslang.
for _name, _submod in (
    ("ASTContext", "ast"), ("Compilation", "ast"), ("CompilationOptions", "ast"),
    ("EvalContext", "ast"), ("LookupLocation", "ast"),
    ("PreprocessorOptions", "parsing"), ("Token", "parsing"), ("TokenKind", "parsing"),
    ("SyntaxTree", "syntax"),
):
    if not hasattr(pyslang, _name):
        setattr(pyslang, _name, getattr(getattr(pyslang, _submod), _name))
# ------------------------------------------------------------------------------

from .. import primitives
from ..ir.nodes import Clock as _IrClock, DerivedClock as _IrDerivedClock, Loc
from .base import FrontendResult, Span
from ._common import _DECL_KINDS, _DESIGN_KINDS, _PROPERTY_KINDS, _enum_name


from ._exprs import _ExprMixin
from ._modules import _ModuleMixin
from ._stmts import _StmtMixin
from ._types import _TypesMixin


class SvSourceError(Exception):
    """The SOURCE does not compile: slang reported an error-severity diagnostic.

    This is not a coverage problem, it is a refusal. slang recovers from errors and hands back
    a syntax tree anyway, so translation would proceed happily over a design that is not the
    one in the file -- `assign y = {2{a}, b};` (illegal: a replication is already braced)
    recovers to `assign y = {2{a}};` and silently drops `b`, and a missing `;` recovers to
    something that may or may not be what was meant. There is nothing to report per-construct
    because the construct the tool sees never existed. See Fix 73."""


class PyslangFrontend(_TypesMixin, _ExprMixin, _StmtMixin, _ModuleMixin):
    """Frontend implementation backed by pyslang (see module docstring)."""

    def __init__(self, param_overrides: dict[str, int] | None = None,
                 top: str | None = None, incdirs: list[str] | None = None,
                 defines: dict[str, str] | None = None,
                 stubs: dict[str, str] | None = None) -> None:
        self._overrides = param_overrides or {}
        self._top = top
        self._modular = False                  # modular mode: record child user-submodule instances
        self._incdirs = incdirs or []
        self._defines = defines or {}
        self._stubs = stubs or {}              # module name -> functional-stub .lp TEXT (project-local)
        self._src_cache: dict[str, list[str]] = {}
        self._genvars: set[str] = set()       # genvar names in scope (inside a generate nest)
        #: The SAME genvars in NEST ORDER (outer first). A genvar used as a VALUE lowers to the
        #: lane variable at its nest position (`LaneIdx`), which is exactly what the rule head
        #: binds — `val(y(I), …) :- addr(y,I), …, V = @add(V0, I, 32)`. Order is what maps
        #: `for(i) for(j)` to `I`, `J`.
        self._genvar_order: list[str] = []
        #: Exclusive iteration bound of the innermost enclosing generate/loop, or None. Attached
        #: to lane-rolled CombItems so the emitted rule can guard `I < bound` (see CombItem).
        self._lane_hi: int | None = None
        self._lane_lo: int = 0                 # start of the enclosing loop/generate range (inclusive)
        self._lane_step: int = 1               # stride of the enclosing loop/generate (`i += 2` -> 2)
        self._reg_lane_range: dict[str, tuple[int, int | None, int, int]] = {}  # lane reg -> (lo, hi, step, off)
        # Set when a constant fold collapsed a subtree that REFERENCED an in-scope genvar (see
        # `_lower_expr`). Lane-rolling lowers one entry and fans the index, so such a fold bakes
        # THAT entry's index value into every lane -- silently wrong. `_lower_generate` checks the
        # flag and refuses instead (defect D1).
        self._genvar_folded: str | None = None
        #: Flags that must SURVIVE the always_comb executor fallback. `_lower_block` discards
        #: branch-path flags when the symbolic executor succeeds (they are false-latch noise),
        #: but a soundness refusal recorded during that pass must not be lost with them (D5).
        self._hard_flags: list = []
        self._loop_lane_stack: list[tuple[str, tuple[int, int | None, int] | None]] = []  # loop nest: (var, (lo, excl hi, step))
        self._lane_mem_writes = 0             # # lane-rolled mem writes in the current loop body (>1=flag)
        self._lane_dims: dict[str, int] = {}  # sig accessed as sig[gv]...[gv] -> # of lane indices
        self._lane_fields: dict = {}          # base -> fields of its lane word (affine positions), per module
        self._gen_locals: dict[str, int] = {}  # a net/variable DECLARED inside a for-generate -> the loop's extent (per module)
        self._lane_elem_w: dict[str, int] = {}   # lane sig -> per-lane element bit width (1 = bit-vector)
        self._lane_domains: dict[str, tuple] = {}  # array-instance lane owner -> per-dim lane counts (ni[,nj])
        self._param_names_seen: set[str] = set()   # every parameter name elaboration
                                            # produced (see _unapplied_override_problems)
        self._stubs_used: set[str] = set()   # stub module names that actually bound (see
                                            # _unbound_stub_problems: a declared stub that
                                            # never binds is a LOUD problem, not a no-op)
        self._modular_flags: list = []   # instance-level problems found while walking
        self._modular_actuals: dict = {}  # (parent module, instance, formal) -> hoisted parent-side signal
        self._modular_hier_reads: dict = {}  # module -> {(functor name, path parts)} read into a child
        self._iface_ports: set = set()      # the current module's interface PORT names (modular)
        self._blk_reset = None              # the async reset of the always block being lowered
                                         # the modular tree (see parse_modular)
        self._warns: list = []   # loud advisories that are NOT coverage problems (Design.warned)
        self._enum_members: set[str] = set()  # all enum member labels (orig case) -> lowered to Tag
        self._enum_type_of: dict[str, str] = {}  # str(canonical enum type) -> its enum_type name (a hoisted enum-valued temp inherits it)
        self._cond_n = 0                       # counter for hoisted if-condition signals
        self._hoist_ctx: str = ""              # current LHS target for intermediate naming (set around RHS lowering)
        self._blk_comb: list = []              # comb sink for the block currently being lowered
        self._blk_signals: dict = {}           # signals dict for hoisted condition signals
        self._blk_edges: list = []             # $rose/$fell sink for the block being lowered
        self._blk_clock: str = ""              # the enclosing clocked block's clock, if any
        self._structs: dict[str, list] = {}    # struct var -> [(field, width, bit_offset), ...]
        self._mem_depth: dict[str, int] = {}   # memory name -> outer-dim # cells (full vs partial loop)
        self._mem_dims: dict[str, tuple[int, ...]] = {}  # memory name -> per-dim cell counts (outer-first)
        self._unions: dict[str, int] = {}      # packed-union var -> total bit width (one WORD signal)
        self._interfaces: dict[str, set[str]] = {}  # interface instance -> its signal names (shared wires)
        self._struct_mems: dict[str, list] = {}  # unpacked array-of-struct -> element field layout
        self._struct_field_mems: dict[str, dict[str, str]] = {}  # struct var -> {array field -> mem name s(arr)}
        self._partials: dict[str, tuple] = {}  # word target -> (width, [(off, w, val, loc)]) slice writes
        self._slice_writes: dict = {}  # clocked slice writes per reg (scoped to one always block)
        self._clocked_slices: dict = {}  # clocked slice writes per reg ACROSS blocks (per module)
        self._prim_flop_slices: dict = {}  # part-select PRIMITIVE flop writes per reg -> coalesced 1 SeqItem

    def _bag(self) -> object:
        """Compilation + preprocessor options: param overrides, `include dirs, +defines.

        Include dirs let `` `include "params.svh" `` resolve so parameter DEFAULTS defined
        in a header are used when an instance/module gives no explicit value.
        """
        co = pyslang.CompilationOptions()
        co.paramOverrides = [f"{k}={v}" for k, v in self._overrides.items()]
        po = pyslang.PreprocessorOptions()
        po.additionalIncludePaths = list(self._incdirs)
        po.predefines = [f"{k}={v}" for k, v in self._defines.items()]
        bag = pyslang.Bag()
        bag.compilationOptions = co
        bag.preprocessorOptions = po
        return bag

    def _tree(self, f: str, sm: object, bag: object) -> object:
        return pyslang.SyntaxTree.fromFile(f, sm, bag)

    # -- entry ---------------------------------------------------------------
    def parse_all(self, files: list[str], defn_files: list[str] | None = None) -> list[FrontendResult]:
        """Translate EVERY top module defined in ``files`` (one result each).

        ``defn_files`` (packages/params) are compiled for resolution but never translated.
        Modules whose definition lives in a defn file are skipped. Results are sorted by
        module name for determinism.
        """
        bag = self._bag()
        sm = pyslang.SourceManager()
        #: every file this compile consumes -- the basis for the declared-vs-consumed check on
        #: `-D` defines (see _unused_intake_problems)
        self._compiled_files = [*(defn_files or []), *files]
        self._bagref, self._smref = bag, sm
        comp = pyslang.Compilation(bag)
        # definition/dependency files first (packages, param/config files), so the
        # design's names + parameters resolve. These are NOT translated or covered.
        for f in defn_files or []:
            comp.addSyntaxTree(self._tree(f, sm, bag))
        for f in files:
            comp.addSyntaxTree(self._tree(f, sm, bag))
        self._sm = sm
        root = comp.getRoot()
        self._check_source_errors(comp, sm)

        source_set = {os.path.realpath(f) for f in files}
        trees = {f: self._tree(f, sm, bag) for f in files}
        spans_by_file = {f: tuple(self._collect_spans(trees[f])) for f in files}
        live_by_file = {os.path.realpath(f): self._live_lines(trees[f]) for f in files}

        results: list[FrontendResult] = []
        for top in sorted(root.topInstances, key=lambda t: t.name):
            def_file = self._sm.getFileName(top.location)
            if os.path.realpath(def_file) not in source_set:
                continue  # module defined in a package/param file -> not translated
            design = self._lower_module(top)
            # per-design coverage: the spans of the file the module is defined in
            real = os.path.realpath(def_file)
            src_file = next((f for f in files if os.path.realpath(f) == real), def_file)
            results.append(FrontendResult(
                design=design, source_files=(src_file,), spans=spans_by_file.get(src_file, ()),
                live_lines={real: live_by_file.get(real, frozenset())}))
        return results

    def param_table(self, files: list[str], defn_files: list[str] | None = None) -> dict:
        """Phase-1 parameter extraction: resolve EVERY parameter across all files (packages,
        `include'd .svh headers via incdirs, module defaults + overrides) to a concrete value.

        Returns {"packages": {pkg: {P: v}}, "modules": {mod: {P: v}}}. Defaults come from the
        definitions; explicit overrides (``-p``/instance) win. Lets translation use these
        resolved values directly and lets the user inspect what every parameter resolved to.
        """
        bag = self._bag()
        sm = pyslang.SourceManager()
        comp = pyslang.Compilation(bag)
        for f in (defn_files or []):
            comp.addSyntaxTree(self._tree(f, sm, bag))
        for f in files:
            comp.addSyntaxTree(self._tree(f, sm, bag))
        root = comp.getRoot()
        self._check_source_errors(comp, sm)

        def params_of(scope) -> dict[str, int]:
            out: dict[str, int] = {}
            for m in scope:
                if _enum_name(m.kind) == "Parameter":
                    v = self._cv_int(m.value)
                    if v is not None:
                        out[m.name] = v
            return out

        table: dict = {"packages": {}, "modules": {}}
        for pkg in comp.getPackages():
            if pkg.name in ("std",):
                continue
            ps = params_of(pkg)
            if ps:
                table["packages"][pkg.name] = ps
        for top in root.topInstances:
            ps = params_of(top.body)
            if ps:
                table["modules"][top.name] = ps
        return table

    def parse(self, files: list[str], defn_files: list[str] | None = None) -> FrontendResult:
        """Translate a single module (``--top`` if set, else the first by name)."""
        results = self.parse_all(files, defn_files)
        if not results:
            raise ValueError("no top module found in the source files")
        if self._top is not None:
            want = self._cid(self._top)   # design names are normalized to valid clingo constants
            matches = [r for r in results if r.design.name == want]
            if not matches:
                names = ", ".join(r.design.name for r in results)
                raise ValueError(f"top module {self._top!r} not found; modules: {names}")
            return matches[0]
        return results[0]

    def parse_modular(self, files: list[str], defn_files: list[str] | None = None) -> dict:
        """MODULAR translation: lower each distinct (module, param-tuple) ONCE (its own body, child
        user-submodules NOT flattened), and walk the elaborated instance tree. Returns
        {specs: {spec_key: Design}, tree: [instance dicts], top: name, topclk: name|None}. The caller
        (emit_modular) renders instance-parameterized rules + an instance manifest that links them."""
        bag = self._bag()
        sm = pyslang.SourceManager()
        comp = pyslang.Compilation(bag)
        for f in defn_files or []:
            comp.addSyntaxTree(self._tree(f, sm, bag))
        for f in files:
            comp.addSyntaxTree(self._tree(f, sm, bag))
        self._sm = sm
        root = comp.getRoot()
        self._check_source_errors(comp, sm)
        tops = sorted(root.topInstances, key=lambda t: t.name)
        if self._top is not None:
            tops = [t for t in tops if t.name == self._top] or tops
        if not tops:
            raise ValueError("no top module found")
        # F8 -- SEVERAL TOPS AND NO `top` NAMED. Taking the first translated ONE design and
        # dropped the other with no message: nothing about the emitted program was wrong,
        # but a design the manifest named simply vanished, which this repository's own
        # fail-loud rule forbids. Refuse and NAME them, so the fix is one word (`top:`)
        # rather than a missing file the user has to notice.
        if self._top is None and len(tops) > 1:
            names = ", ".join(t.name for t in tops)
            raise ValueError(
                f"the sources contain {len(tops)} top-level modules ({names}) and the "
                f"manifest names no `top`. Translating one and dropping the rest would be "
                f"silent -- name the one you want with `top`, or run once per design")
        top = tops[0]

        self._modular = True
        specs: dict[str, object] = {}        # spec_key -> own-body Design
        clock_formals: dict[str, frozenset] = {}   # spec_key -> the set of its clock FORMAL names (ports)

        def ptuple(inst) -> tuple:
            # only REAL parameters distinguish a spec; localparams are internal constants identical
            # across every instance (folded into the design), so they must not bloat the spec key.
            return tuple(sorted((p.name, self._cv_int(p.value)) for p in inst.body
                                if _enum_name(p.kind) == "Parameter" and not getattr(p, "isLocalParam", False)
                                and self._cv_int(p.value) is not None))

        cid = self._cid   # clingo-constant fixup: leading uppercase → lowercase

        # --- Spec-key naming (two-phase; see docs/implementation/SPECKEY_PATH_PLAN.md) ---
        # A spec is per (module, param-tuple): instances sharing a module AND its real-parameter
        # values share ONE spec.  The KEY STRING uses the hierarchical instance PATH of the
        # first instance that introduced each (module, param-tuple) variant:
        #   - single-variant module → ``module_name``  (no path needed)
        #   - multi-variant module  → ``module_name__parent__instance``
        #     e.g. ``acc_unit__u_lane0__u_acc`` (W=4) and ``acc_unit__u_lane1__u_acc`` (W=8).
        # The path is unique by RTL construction (synthesis forbids duplicate hierarchical paths),
        # bounded by hierarchy depth (not parameter count), and self-documenting.
        # Phase 1 (prewalk): collect all (module, ptuple) pairs and record the first-seen path.
        # Phase 2 (speckey): assign stable keys from that map.
        variants: dict[str, list] = {}              # module_name -> [ptuple, …] first-seen order
        variant_paths: dict[tuple, str] = {}        # (module_name, ptuple) -> first-seen path

        def prewalk(inst, path: str) -> None:
            mod = inst.definition.name
            pt = ptuple(inst)
            seen = variants.setdefault(mod, [])
            pair = (mod, pt)
            if pt not in seen:
                seen.append(pt)
                variant_paths[pair] = path          # record first-seen hierarchical path
            for m in inst.body:
                if _enum_name(m.kind) != "Instance":
                    continue
                if primitives.lookup(m.definition.name) is not None:
                    continue
                if m.definition.name in self._stubs:
                    continue
                if getattr(m, "body", None) is None:
                    continue
                child_path = cid(m.name) if path == cid(top.name) else f"{path}({cid(m.name)})"
                prewalk(m, child_path)

        def speckey(inst) -> str:
            mod = inst.definition.name
            pt = ptuple(inst)
            vs = variants.get(mod, [pt])
            if len(vs) <= 1:
                return cid(mod)                     # single variant → plain module name
            # Multi-variant: label by the hierarchical path of the first-seen instance.
            # Strip the top-module prefix so "top(u_lane0(u_acc))" → "u_lane0__u_acc".
            pair = (mod, pt)
            raw = variant_paths.get(pair, cid(mod))
            top_prefix = cid(top.name) + "__"
            flat = raw.replace("(", "__").replace(")", "")
            label = flat[len(top_prefix):] if flat.startswith(top_prefix) else flat
            return cid(f"{mod}__{label}")           # e.g. acc_unit__u_lane0__u_acc

        def ensure(inst) -> str:
            key = speckey(inst)
            if key not in specs:
                d = self._norm_design(self._lower_body(inst.body, inst.definition.name))
                specs[key] = d
                derived_names = {dc.name for dc in d.derived_clocks}
                # collect EVERY distinct clock domain the module uses -- regular registers, MEMORY writes
                # (a memory-only module has empty d.seq!), VFFs, and the BASE of any gated clock. Each gets
                # its OWN clkof(Inst, formal, actual) in the manifest, so a module with >1 internal clock
                # (or a cross-domain ICG) resolves every clock independently (no collapse to a single one).
                formals = {it.clock for it in d.seq
                           if not it.combinational and it.clock and it.clock not in derived_names}
                formals |= {w.clock for w in d.mem_writes if w.clock and w.clock not in derived_names}
                formals |= {it.clock for it in d.vffs if it.clock and it.clock not in derived_names}
                formals |= {dc.base for dc in d.derived_clocks}    # a gated clock's base is a real clock port
                clock_formals[key] = frozenset(formals)
            return key

        def actual_net(c, inst=None, parent_def: str | None = None) -> str:
            e = c.expression
            if _enum_name(e.kind) == "Assignment":
                e = e.left
            # an EXPRESSION actual was hoisted to a parent-side signal when the parent spec was
            # lowered (`_modular_port_actuals`); bridge to THAT, never to a root-name guess
            if inst is not None:
                h = self._modular_actuals.get((parent_def, inst.name, c.port.name))
                if h is not None:
                    return cid(h)
            try:
                return cid(self._peel(e).symbol.name)
            except AttributeError:
                # Slice/concat/part-select actual: use the root signal name.
                # For a RangeSelect {sig[hi:lo]} -> peel the base; for Concat take the first operand.
                root = e
                while _enum_name(getattr(root, "kind", "")) in ("RangeSelect", "ElementSelect"):
                    root = root.value
                if _enum_name(getattr(root, "kind", "")) == "Concatenation":
                    ops = list(getattr(root, "operands", []))
                    for op in ops:
                        try:
                            return cid(self._peel(op).symbol.name)
                        except AttributeError:
                            continue
                try:
                    return cid(self._peel(root).symbol.name)
                except AttributeError:
                    return cid(str(c.port.name))   # last resort: use the formal port name

        tree: list[dict] = []

        def walk(inst, path: str, parent: str | None, parent_map: dict | None,
                 parent_def: str | None = None, parent_key: str | None = None) -> None:
            key = ensure(inst)
            formals = clock_formals.get(key, frozenset())   # this instance's clock FORMAL names (ports)
            # resolve EACH clock formal to an actual clock domain. The top's clock formals ARE their own
            # domains (the scenario drives them); a child's clock port resolves through the parent's map
            # (a clock port wired to a parent clock formal inherits the parent's resolution). A clock
            # port wired to a parent's DERIVED clock -- an ICG gate, or (F27) a parent-computed net
            # such as a divided clock -- resolves to that clock's per-instance FUNCTOR,
            # `name(parent_path)`: the domain the parent spec's time(name(Inst), T) rules define.
            # The F27 case is CLASSIFIED HERE, at the binding: modular mode lowers each module
            # separately, so the parent never sees its net used as a clock and the child sees only
            # its own port -- only this walk sees the binding. The parent spec gains the
            # edge-derived clock retroactively (kind "rise", base = the driver chain's clock).
            if parent is None:
                my_map = {f: f for f in formals}
            else:
                pd = specs.get(parent_key) if parent_key else None
                my_map = {}
                for f in formals:
                    net = next((actual_net(c) for c in inst.portConnections if cid(c.port.name) == f), None)
                    if net is None:
                        my_map[f] = f
                        continue
                    if pd is not None and net in {dc.name for dc in pd.derived_clocks}:
                        my_map[f] = f"{net}({parent})"
                        continue
                    if net in (parent_map or {}):
                        my_map[f] = parent_map[net]
                        continue
                    # a PASS-THROUGH clock: the parent forwards one of its own INPUT ports (an
                    # unclocked intermediate module has no clock formals, so its map is empty and
                    # the port is not tracked) -- inherit the grandparent's resolution when it
                    # exists, else the raw name, exactly as before F27. Only a parent-COMPUTED
                    # net enters the classify-or-refuse path below.
                    parent_inputs = {s.name for s in pd.signals
                                     if s.is_port and s.direction == "input"} if pd is not None else set()
                    if net in parent_inputs:
                        my_map[f] = (parent_map or {}).get(net, net)
                        continue
                    drivers = {it.reg: it for it in pd.seq if not it.combinational and it.clock} \
                        if pd is not None else {}
                    drv = drivers.get(net)
                    widths = {s.name: s.irtype.width for s in pd.signals} if pd is not None else {}
                    ok = pd is not None and drv is not None and widths.get(net, 1) == 1
                    base, seen = (drv.clock if drv else None), {net}
                    while ok and base not in clock_formals.get(parent_key, frozenset()) \
                            and base not in (parent_map or {}) and base is not None:
                        if base in seen:
                            ok = False
                            break
                        seen.add(base)
                        bdrv = drivers.get(base)
                        if bdrv is None:
                            ok = False
                            break
                        base = bdrv.clock
                    if ok:
                        newdc = _IrDerivedClock(name=net, base=base, gate="", loc=drv.loc, kind="rise")
                        clocks2 = tuple(c for c in pd.clocks if c.name != net) \
                            + (_IrClock(net, derived=True, base=base, gate=""),)
                        specs[parent_key] = dataclasses.replace(
                            pd, derived_clocks=tuple(pd.derived_clocks) + (newdc,), clocks=clocks2)
                        pd = specs[parent_key]
                        my_map[f] = f"{net}({parent})"
                    else:
                        if pd is not None:
                            specs[parent_key] = dataclasses.replace(
                                pd, flagged=tuple(pd.flagged) + ((drv.loc if drv else self._loc(inst),
                                    f"instance {inst.name}: clock port '{f}' is wired to '{net}', "
                                    f"which is not a clock domain and cannot be classified as an "
                                    f"edge-derived clock (no 1-bit register driver chain to a "
                                    f"primary clock) (F27)"),))
                            pd = specs[parent_key]
                        my_map[f] = net
            conns = []
            iconns = []                                 # interface ports: (formal, iface_inst, ((sig,dir),...))
            if parent is not None:                      # the top has no parent to bridge to
                for c in inst.portConnections:
                    if _enum_name(c.port.kind) == "InterfacePort":
                        continue                       # interface ports carry no direction; handled below
                    formal = cid(c.port.name)
                    if formal in formals:              # a clock port -> handled via clkof, not a value bridge
                        continue
                    direction = _enum_name(c.port.direction)
                    if direction not in ("In", "Out"):
                        continue
                    if c.expression is None:
                        # UNCONNECTED PORT -- must behave exactly as the flat path does (hard
                        # rule 1). An unconnected OUTPUT is unobserved and harmless; an
                        # unconnected INPUT gets no driver, and the 1-bit excluded-middle rule
                        # then turns "undriven" into a constant 0, so the design silently
                        # behaves as if the floating input were tied low. Before this, modular
                        # mode did not check at all and crashed here with a raw AttributeError.
                        if direction == "In":
                            self._modular_flags.append(
                                (self._loc(inst), f"instance {inst.name}: input port "
                                 f"'{c.port.name}' is UNCONNECTED. It gets no driver, so every "
                                 f"rule reading it fails and the 1-bit fallback makes it a "
                                 f"constant 0 -- the design would silently behave as if it were "
                                 f"tied low. Connect it, or tie it off explicitly in the RTL"))
                        continue
                    conns.append((formal, direction, actual_net(c, inst, parent_def)))
                # interface ports: a bundle of shared wires connected to a parent interface instance.
                # The modport gives each signal's direction (src=Out drives the net, dst=In reads it);
                # bridge each interface signal to the connected instance's net iface(sig) -- see emit.
                for sm in inst.body:
                    if _enum_name(sm.kind) != "InterfacePort":
                        continue
                    conn = getattr(sm, "connection", None)
                    if not conn or not hasattr(conn[0], "name") or len(conn) < 2:
                        continue
                    sigdirs = tuple((cid(x.name), _enum_name(x.direction)) for x in conn[1])
                    iconns.append((cid(sm.name), cid(conn[0].name), sigdirs))
            # hierarchical READS this module makes into its children (`u.q` -> the flat functor
            # `u(q)`): the manifest bridges each from the child instance's own signal
            hreads = []
            for fname, parts in sorted(self._modular_hier_reads.get(inst.definition.name, ())):
                child = cid(parts[0]) if path == topname else f"{path}({cid(parts[0])})"
                for seg in parts[1:-1]:
                    child = f"{child}({cid(seg)})"
                hreads.append((cid(fname), child, cid(parts[-1])))
            tree.append({"path": path, "parent": parent, "spec": key, "module": inst.definition.name,
                         "clocked": bool(formals), "clks": my_map, "conns": tuple(conns),
                         "iconns": tuple(iconns), "hreads": tuple(hreads)})
            for m in inst.body:
                if _enum_name(m.kind) != "Instance":
                    continue
                if primitives.lookup(m.definition.name) is not None:
                    continue                           # primitive -> inlined in this spec, not a node
                if m.definition.name in self._stubs:
                    continue                           # stubbed module -> flat-only, no modular child spec
                if getattr(m, "body", None) is None:
                    continue
                child_path = cid(m.name) if path == topname else f"{path}({cid(m.name)})"
                walk(m, child_path, path, my_map, inst.definition.name, key)   # children resolve clocks via THIS map

        topname = cid(top.name)
        prewalk(top, topname)        # phase 1: collect variant paths per module (for speckey)
        walk(top, topname, None, None)
        self._modular = False
        # topclk = a representative clock for the scenario stub (the top's own first clock, else any).
        top_clks = next((n["clks"] for n in tree if n["path"] == topname), {})
        topclk = next(iter(top_clks.values()), None) \
            or next((c for fs in clock_formals.values() for c in fs), None)
        # Instance-level problems found while walking the tree (e.g. an unconnected input) belong
        # to no single spec's own body, so attach them to the TOP spec -- that is what cli.py
        # scans for `--strict-coverage`, and it keeps modular in step with flat (hard rule 1).
        if self._modular_flags and specs:
            import dataclasses as _dc
            _tk = topname if topname in specs else next(iter(specs))
            specs[_tk] = _dc.replace(
                specs[_tk], flagged=tuple([*specs[_tk].flagged, *self._modular_flags]))
            self._modular_flags = []
        return {"specs": specs, "tree": tree, "top": topname, "topclk": topclk}

    def _collect_spans(self, tree: object) -> list[Span]:
        """Collect top-level module-member source spans (for the coverage map)."""
        sm = tree.sourceManager
        spans: list[Span] = []
        modules: list[object] = []

        def find(n: object) -> None:
            kind = str(getattr(n, "kind", ""))
            if kind in ("SyntaxKind.ModuleDeclaration", "SyntaxKind.InterfaceDeclaration"):
                modules.append(n)
            elif kind in ("SyntaxKind.TypedefDeclaration",       # file-scope (or nested) type def
                          "SyntaxKind.FunctionDeclaration",     # $unit-scope function / task:
                          "SyntaxKind.TaskDeclaration"):        # INLINED at each call site, so its
                # own lines are a declaration, not an emission. Without this they had NO span at
                # all and came out UNACCOUNTED, failing --strict-coverage on a design that had
                # translated perfectly (verified: the inlined rules were correct). A function
                # declared INSIDE a module was always accounted; only $unit scope was missed.
                sr = n.sourceRange
                spans.append(Span(sm.getFileName(sr.start), sm.getLineNumber(sr.start),
                                  sm.getLineNumber(sr.end), "decl", kind.split(".")[-1]))

        tree.root.visit(find)
        for mod in modules:
            msr = mod.sourceRange
            mstart, mend = sm.getLineNumber(msr.start), sm.getLineNumber(msr.end)
            mfile = sm.getFileName(msr.start)
            members = list(mod.members)
            first = sm.getLineNumber(members[0].sourceRange.start) if members else mend
            # module header (decl + params + port list) up to the first member
            spans.append(Span(mfile, mstart, max(mstart, first - 1), "header", "ModuleHeader"))
            spans.append(Span(mfile, mend, mend, "header", "endmodule"))
            for m in members:
                sr = m.sourceRange
                kind = str(m.kind).rsplit(".", 1)[-1]
                cat = ("design" if kind in _DESIGN_KINDS
                       else "decl" if kind in _DECL_KINDS
                       else "property" if kind in _PROPERTY_KINDS
                       else "unknown")
                spans.append(Span(mfile, sm.getLineNumber(sr.start), sm.getLineNumber(sr.end), cat, kind))
        return spans

    def _live_lines(self, tree: object) -> frozenset[int]:
        """Line numbers that contributed a real token to the parse. A line NOT here is blank / comment
        / `directive / `ifdef-EXCLUDED (the preprocessor dropped it -> no token), so the coverage map
        treats it as structural rather than `unaccounted`."""
        sm = tree.sourceManager
        lines: set[int] = set()

        def collect(n: object) -> None:
            try:
                children = list(n)
            except TypeError:
                return
            for c in children:
                if isinstance(c, pyslang.Token):
                    if c.kind != pyslang.TokenKind.EndOfFile:
                        lines.add(sm.getLineNumber(c.location))
                elif c is not None:
                    collect(c)

        try:
            collect(tree.root)
        except Exception:  # noqa: BLE001 - coverage refinement only; never block translation
            return frozenset()
        return frozenset(lines)

    # -- helpers -------------------------------------------------------------
    #: slang diagnostics the tool tolerates. An UNKNOWN MODULE is expected and handled: vendor
    #: stdcells come from `primitives.REGISTRY` and black boxes from functional stubs, so their
    #: definitions are deliberately absent from the source set. Everything else at error
    #: severity means the parsed design is not the source design.
    _TOLERATED_DIAGS = frozenset({"UnknownModule", "UnknownInterface", "UnknownPackage"})

    def _check_source_errors(self, comp: object, sm: object) -> None:
        """REFUSE a source slang could not compile (Fix 73).

        slang recovers from errors and returns a tree regardless, and nothing downstream can
        tell the difference -- a missing `;` translated to a clean `.lp` with
        `coverage: OK (no design omissions)` and exit 0. That is hard rule 2 broken at the
        intake: the model was not the RTL, and the tool said it was.

        Warnings are NOT errors here (slang warns freely about width conversions that are
        perfectly ordinary in RTL); only error/fatal severity refuses, minus the tolerated
        codes above.

        A file that defines ONLY STUBBED modules is exempt. Declaring a stub is the user
        saying "this body is replaced, do not look inside", so its internals need not
        elaborate -- the production divider's ROM does not, because its dimensions come from
        macros defined in a header the RTL release does not ship. The exemption is narrow and
        DECLARED (a stub that never binds is itself a loud problem), never inferred."""
        de = pyslang.DiagnosticEngine(sm)
        # file -> modules it defines, so an error can be attributed to a stubbed body
        by_file: dict[str, set[str]] = {}
        try:
            for dfn in comp.getDefinitions():
                by_file.setdefault(os.path.realpath(sm.getFileName(dfn.location)),
                                   set()).add(dfn.name)
        except Exception:  # noqa: BLE001 - attribution is best-effort; without it, refuse
            by_file = {}
        bad, stubbed = [], []
        for d in comp.getAllDiagnostics():
            sev = str(de.getSeverity(d.code, d.location)).rsplit(".", 1)[-1]
            if sev not in ("Error", "Fatal"):
                continue
            if str(d.code).replace("DiagCode(", "").rstrip(")") in self._TOLERATED_DIAGS:
                continue
            try:
                mods = by_file.get(os.path.realpath(sm.getFileName(d.location)), set())
            except Exception:  # noqa: BLE001
                mods = set()
            if mods and mods <= set(self._stubs):
                stubbed.append((d, sorted(mods)))
                continue
            bad.append(d)
        if stubbed:   # loud, but not fatal -- the reader must know the body was never read
            names = sorted({m for _d, ms in stubbed for m in ms})
            self._warns.append((Loc(file=sm.getFileName(stubbed[0][0].location), line=0),
                                f"{len(stubbed)} slang error(s) inside STUBBED module(s) "
                                f"{', '.join(names)} -- tolerated because the stub replaces the "
                                f"body, which is therefore never translated"))
        if not bad:
            return
        try:
            text = pyslang.DiagnosticEngine.reportAll(sm, bad).strip()
        except Exception:  # noqa: BLE001 - never let the reporter hide the refusal
            text = "\n".join(str(d.code) for d in bad)
        raise SvSourceError(
            f"the source does not compile -- {len(bad)} error(s) from slang. Nothing was "
            f"translated: slang recovers from errors, so the design the tool would see is not "
            f"the design in the file.\n{text}")

    def _try_lower(self, fn, m, what: str, flagged: list) -> None:
        """Frontend soundness net (mirror of the emitter's _guard): if lowering a construct
        raises, FLAG it (loud, located) rather than crashing the whole translation."""
        try:
            fn()
        except Exception as e:  # noqa: BLE001 - last-resort net: unhandled construct must flag, not crash
            try:
                loc = self._loc(m)
            except Exception:  # noqa: BLE001
                loc = Loc(file="?", line=0)
            flagged.append((loc, f"{what}: {type(e).__name__}: {e}"))

