"""HIERARCHY: authored modules as instances, composed by FLATTENING; contracts as assume/guarantee.

    inst(u_add, add4).  pin(u_add, a, opa).  pin(u_add, y, add_y).  ...     -- an authored module,
                                                                               `add4.lp` next to the
                                                                               design or under units/
    abstract(u_add).                                                        -- CONTRACT-ONLY: its
                                                                               outputs are free, its
                                                                               `add4.contract.lp` is
                                                                               assumed

A module's file is an ordinary design (module/port/net/def/inst/rules); its optional
`<module>.contract.lp` states, over ITS OWN port names, `guarantee(Tag, T)` (what it promises;
violated at T) and `require(Tag, T)` (what it needs from whoever drives its inputs; violated at T).

`compose(path)` flattens the tree into ONE design (the way sv2asp's flat mode names things:
child nets become `u_add__sum`), so lint / refine / expand run unchanged on the composed program;
`print` stays hierarchical (printer.py). Composition of a contract is assume-guarantee:

    child ABSTRACT   -> its outputs are `abstract` nets;    guarantee -> parent's assume(u_add__Tag)
                                                            require   -> parent's viol(u_add__Tag)  (obligation)
    child CONCRETE   -> its body, renamed;                  guarantee -> parent's viol(u_add__Tag)  (re-checked in place)
                                                            require   -> parent's viol(u_add__Tag)  (obligation)

so refining `abstract(u_add)` into the concrete `add4` turns the assumed guarantee into a
discharge obligation of the next level -- the same mechanism as for nets, one level up. Renaming
is a single-pass identifier substitution over the child's own declared names (ports -> the
parent's actual nets or `inst__port`; everything else -> `inst__name`), so a child net `a` and a
child net `all` cannot collide."""
from __future__ import annotations

import pathlib
import re
from dataclasses import dataclass, field

from .libgen import LIB_DIR
from .load import Design, SubsetError, load, parse_rule, term_to_str
from .load import asp_name
from .lanes import LaneTable, axes_of, members
from .model import CELLS, Inst, Net, Port

SEARCH_SUBDIRS = ("", "units", "modules")


class ComposeError(Exception):
    pass


@dataclass
class Composed:
    design: Design                       # the flattened design
    inv: str = ""                        # assume/viol text contributed by the children's contracts
    resets: set = field(default_factory=set)   # reset NETS (arff rstL bindings) learned the same
                                         # way: the base must drive them low at T=0 and the step
                                         # hold them released, even when every register lives
                                         # inside an abstract child
    clocks: set = field(default_factory=set)   # clock NETS learned from children's cells -- an
                                         # all-abstract composition has no cell of its own, so the
                                         # parent would otherwise have NO time axis (live(T) became
                                         # unsatisfiable and every scenario "contradictory")
    inv_abstract: str = ""               # ONLY the ABSTRACT children's blocks (guarantee->assume,
                                         # require->viol): the stimless certificate composes THIS --
                                         # assume-guarantee needs the assumed half, while concrete
                                         # children stay excluded there (proven standalone; the
                                         # rv_ooo_b contract-ghost grounding wall)
    ghost: str = ""                      # the children's contract GHOST INITS (<m>.contract.ghost.lp), renamed
    #                                      the same way -- composed only by the induction step
    modules: dict = field(default_factory=dict)      # module name -> path (every authored module used)
    tree: list = field(default_factory=list)         # (instance path, module name, abstract?)
    lp_path: object = None                           # the composed program on disk (set by lint_composed)
    symfacts: str = ""                               # bnd/2 + dat/1 role facts for the symbolic reading (set by lint_composed)


# ---------------------------------------------------------------------------------------------
# resolution
# ---------------------------------------------------------------------------------------------

def resolve_module(name: str, base: pathlib.Path) -> "pathlib.Path | None":
    for sub in SEARCH_SUBDIRS:
        cand = (base / sub / f"{name}.lp") if sub else base / f"{name}.lp"
        if cand.exists():
            return cand
    cand = LIB_DIR / "modules" / f"{name}.lp"
    return cand if cand.exists() else None


def contract_of(module_path: pathlib.Path) -> "pathlib.Path | None":
    c = module_path.with_name(module_path.stem + ".contract.lp")
    return c if c.exists() else None


# ---------------------------------------------------------------------------------------------
# renaming
# ---------------------------------------------------------------------------------------------

def _renamer(mapping: dict):
    """One-pass whole-identifier substitution."""
    if not mapping:
        return lambda s: s
    pat = re.compile(r"(?<![\w])(" + "|".join(re.escape(k) for k in sorted(mapping, key=len, reverse=True)) + r")(?![\w])")
    return lambda s: pat.sub(lambda m: mapping[m.group(1)], s)


def _rename_term(t, ren):
    if isinstance(t, str):
        return ren(t) if t[0].islower() else t
    if isinstance(t, int):
        return t
    if t[0] == "str":
        return t
    if t[0] == "tag":
        return ("tag", ren(t[1]))
    return (t[0], *(_rename_term(a, ren) for a in t[1:]))


# ---------------------------------------------------------------------------------------------
# serialisation (the composed design as an authoring-subset file)
# ---------------------------------------------------------------------------------------------

def _wtxt(w) -> str:
    return f"enum({w[1]})" if isinstance(w, tuple) else str(w)


def _lane_member(name: str, *idx: int):
    """The term for a member of lane `name`, spelled as the unrolled design spells it."""
    return (name, *idx)


def _expand_pack(t, d: Design):
    """`pack(L)` -> the lane's members as one word, FOR THE SOLVER.

    Lanes are unrolled at load time, so by the time clingo reads the design the lane is gone and
    only `L(0)..L(N-1)` remain -- there is nothing left for a library rule to iterate over. The
    expansion therefore happens here, on the way out to the solver, where the lane table is still
    in hand.

    It is deliberately NOT done in the Design itself. The printer walks these same defs, and a
    lane already prints as a packed vector, so `pack(L)` prints as the bare name `L` -- one line,
    parametric by construction. Expanding in the Design would hand the printer a nested `cat` of
    N members and put the fake parameterisation straight back, which is the defect this exists to
    remove (G20).
    """
    if isinstance(t, tuple) and t and t[0] == "pack":
        name = t[1]
        if name not in d.lanes:
            raise ComposeError(f"pack({name}): {name} is not a declared lane -- `pack` names a "
                               f"`net_lane`, whose members become the word's bits")
        n, w, _dir = d.lanes[name]
        if not (isinstance(n, int) and isinstance(w, int)):
            raise ComposeError(f"pack({name}): the lane's extent and width must be concrete here")
        mem = list(members(axes_of(d.lanes, name)))   # row-major: the flat order of the packed word
        acc = _lane_member(name, *mem[0])            # member 0 is the LSB
        for j in range(1, n):
            acc = ("cat", _lane_member(name, *mem[j]), w, acc, j * w)
        return acc
    if isinstance(t, tuple):
        return tuple(_expand_pack(x, d) for x in t)
    return t


def to_lp(d: Design, header: str = "") -> str:
    """The design as authoring-subset text (what the library and the lint consume)."""
    out = [header] if header else []
    out.append(f"module({asp_name(d.name)}).")
    for p in d.ports:
        out.append(f"port({p.name}, {p.direction}, {_wtxt(p.width)}).")
    for n in d.nets:
        out.append(f"net({n.name}, {_wtxt(n.width)}).")
    for e, ms in d.enums.items():
        for l, v in ms:
            out.append(f"enum_member({e}, {l}, {v}).")
    for k, v in d.params.items():
        out.append(f"param({k}, {v}).")
    for n in d.def_order:
        out.append(f"def({n}, {term_to_str(_expand_pack(d.defs[n], d))}).")
    for r in d.rules:
        out.append(re.sub(r"\s+", " ", r.text) + ".")
    for i in d.insts:
        out.append(f"inst({i.name}, {i.cell}).")
        for p, n in i.pins.items():
            out.append(f"pin({i.name}, {p}, {n}).")
        for p, v in i.iparams.items():
            out.append(f"iparam({i.name}, {p}, {v}).")
    for m, (dp, w) in d.arch_mems.items():
        out.append(f"arch_mem({m}, {dp}, {w}).")
    for a in d.abstracts:
        out.append(f"abstract({a}).")
    for n in d.data:
        out.append(f"data({n}).")
    return "\n".join(out) + "\n"


# ---------------------------------------------------------------------------------------------
# composition
# ---------------------------------------------------------------------------------------------

def compose(path, _seen: "tuple" = (), params: "dict | None" = None) -> Composed:
    """Flatten the design at `path` (recursively) into one Design + the contract text. `params`:
    the parent's `mparam` overrides for this module (a child is loaded with them resolved)."""
    path = pathlib.Path(path)
    top = load(path, params)
    base = path.parent
    if top.name in _seen:
        raise ComposeError(f"module {top.name} instantiates itself (via {' > '.join(_seen)})")
    out = Design(name=top.name, ports=list(top.ports), nets=list(top.nets),
                 enums={e: list(ms) for e, ms in top.enums.items()}, params=dict(top.params),
                 defs=dict(top.defs), def_order=list(top.def_order), insts=[], rules=list(top.rules),
                 abstracts=list(top.abstract_nets()) + list(top.abstract_mems()),   # abstract MEMORIES too (a
                 data=list(top.data), src=dict(top.src),                                # dropped one is dark = vacuous)
                 raw=top.raw, param_exprs=dict(top.param_exprs),
                 opaque_datapath=top.opaque_datapath,
                 lanes=LaneTable(top.lanes), lane_defs=list(top.lane_defs), lane_insts=dict(top.lane_insts),
                 inst_axes=dict(getattr(top, "inst_axes", {})),
                 arch_mems=dict(top.arch_mems))
    comp = Composed(out)
    abstract_insts = set(top.abstract_insts())
    for i in top.insts:
        if i.cell in CELLS:
            out.insts.append(i)
            continue
        mpath = resolve_module(i.cell, base)
        if mpath is None:
            raise ComposeError(f"inst({i.name}, {i.cell}): no library cell of that name and no "
                               f"{i.cell}.lp next to {path.name} (or under units/, modules/)")
        child_c = compose(mpath, _seen + (top.name,), params=i.mparams or None)
        child = child_c.design
        comp.modules[i.cell] = mpath
        comp.modules.update(child_c.modules)
        pfx = f"{i.name}__"
        # -- ports: parent nets (or fresh names); every INPUT must be connected
        ren: dict = {}
        child_ports = {p.name: p for p in child.ports}
        for pin, net in i.pins.items():
            if pin not in child_ports and pin in child.lanes:
                if len(axes_of(child.lanes, pin)) > 1 or (net in top.lanes and len(axes_of(top.lanes, net)) > 1):
                    raise ComposeError(f"pin({i.name}, {pin}, {net}): a lane port with more than one axis is not "
                                       f"composed yet (2026-09-03)")
                # a LANE port of the child (`port_lane(d, input, N, W)`, members d(0)..d(N-1)) connected from a
                # LANE of the parent with the same count and width: member-wise, d(k) <- x(k); the base name too,
                # so the child's rolled lane defs/instances rename onto the parent's lane
                cn, cw, _cd = child.lanes[pin]
                if net not in top.lanes:
                    raise ComposeError(f"pin({i.name}, {pin}, {net}): {pin} is a LANE port of {i.cell} "
                                       f"({cn} x {_wtxt(cw)}); connect it from a lane of {top.name}, not the net {net}")
                pn_, pw_, _pd = top.lanes[net]
                if (pn_, pw_) != (cn, cw):
                    raise ComposeError(f"pin({i.name}, {pin}, {net}): lane {net} is {pn_} x {_wtxt(pw_)}, "
                                       f"the port {pin} of {i.cell} is {cn} x {_wtxt(cw)}")
                ren[pin] = net
                for k in range(cn):
                    ren[f"{pin}({k})"] = f"{net}({k})"
                continue
            if pin not in child_ports:
                raise ComposeError(f"pin({i.name}, {pin}, ..): {i.cell} has no port {pin} "
                                   f"(ports: {', '.join(child_ports)})")
            pw, nw = child_ports[pin].width, top.width_of(net)
            if nw is None:
                raise ComposeError(f"pin({i.name}, {pin}, {net}): {net} is not a declared net of {top.name}")
            if pw != nw:
                raise ComposeError(f"pin({i.name}, {pin}, {net}): width {_wtxt(nw)} vs the port's {_wtxt(pw)}")
            ren[pin] = net
        for p in child.ports:
            if p.name in ren:
                continue
            if p.direction == "input":
                raise ComposeError(f"{i.name} ({i.cell}): input port {p.name} is not connected")
            ren[p.name] = pfx + p.name                          # unconnected output: a private net
            out.nets.append(Net(pfx + p.name, p.width))
        # -- the child's LANES: a connected lane port is the parent's lane (renamed above); every other lane
        # (an unconnected output lane, an internal net_lane, a lane instance) is a private lane of the
        # composed design under the prefix -- registered as a LANE so the flattened print re-rolls it
        for ln, (n_, w_, _dr) in child.lanes.items():
            if ln not in ren:
                ren[ln] = pfx + ln
                out.lanes[pfx + ln] = (n_, w_, None)
                if len(axes_of(child.lanes, ln)) > 1:
                    out.lanes.axes[pfx + ln] = axes_of(child.lanes, ln)
        # -- everything else the child declares
        for n in child.nets:
            ren[n.name] = pfx + n.name
        for ci in child.insts:
            ren[ci.name] = pfx + ci.name
        for e, ms in child.enums.items():
            ren[e] = pfx + e
            for l, _ in ms:
                ren[l] = pfx + l
        for a in child.abstracts:
            ren.setdefault(a, pfx + a)
        R = _renamer(ren)
        # an enum-typed width names the child's enum TYPE, which is renamed like everything else it declares
        # (found by the APB system: the bridge's `state` is `enum(st_t)`; the ALU units had no enums)
        RW = lambda w: ("enum", R(w[1])) if isinstance(w, tuple) and w and w[0] == "enum" else w
        out.nets = [Net(n.name, RW(n.width)) if n.name.startswith(pfx) else n for n in out.nets]   # the private-output nets added above
        comp.tree.append((i.name, i.cell, i.name in abstract_insts))
        comp.tree += [(f"{i.name}.{sub}", m, ab) for sub, m, ab in child_c.tree]
        # -- contract
        cpath = contract_of(mpath)
        ctext = cpath.read_text() if cpath else ""
        # the child's clock bindings, seen through the pin renaming: cells inside an ABSTRACT
        # child never reach the parent, so this is the only record of which parent net clocks it
        for ci in child.insts:
            if ci.cell in CELLS and "clk" in ci.pins:
                cn = ci.pins["clk"]
                comp.clocks.add(ren[cn] if cn in ren else pfx + cn)
            if ci.cell == "arff" and "rstL" in ci.pins:
                rn = ci.pins["rstL"]
                comp.resets.add(ren[rn] if rn in ren else pfx + rn)
        comp.clocks |= {(ren[c] if c in ren else pfx + c) for c in child_c.clocks}
        comp.resets |= {(ren[c] if c in ren else pfx + c) for c in child_c.resets}
        if i.name in abstract_insts:
            # outputs free; guarantee assumed; requirement is our obligation
            for p in child.ports:
                if p.direction == "output":
                    out.abstracts.append(ren[p.name])
            if ctext:
                block = _contract_text(ctext, R, pfx, guarantee_as="assume", require_as="viol",
                                       where=f"{i.name} ({i.cell}, ABSTRACT: contract assumed)")
                comp.inv += block
                comp.inv_abstract += block
                comp.ghost += _contract_ghost(cpath, ctext, R, pfx)
            continue
        # -- concrete: the child's body, renamed
        for m, shape in child.arch_mems.items():                # a child's architectural memory, prefixed like its inst
            out.arch_mems[pfx + m] = shape
        for n in child.nets:
            out.nets.append(Net(pfx + n.name, RW(n.width)))
        for e, ms in child.enums.items():
            out.enums[pfx + e] = [(pfx + l, v) for l, v in ms]
        for n in child.def_order:
            nn = R(n)
            out.defs[nn] = _rename_term(child.defs[n], R)
            out.def_order.append(nn)
            line, stmt = child.src.get(("def", n), (0, ""))
            out.src[("def", nn)] = (line, f"{i.name}: {stmt}")
        for r in child.rules:
            txt = R(re.sub(r"\s+", " ", r.text))
            out.rules.append(parse_rule(r.line, txt))
        for ci in child.insts:
            out.insts.append(Inst(pfx + ci.name, ci.cell, {p: R(n) for p, n in ci.pins.items()},
                                  {p: (R(v) if isinstance(v, str) else v) for p, v in ci.iparams.items()}, dict(ci.mparams)))
            line, stmt = child.src.get(("inst", ci.name), (0, ""))
            out.src[("inst", pfx + ci.name)] = (line, f"{i.name}: {stmt}")
        # the child's rolled lane forms, renamed, so the flattened print keeps its generate blocks
        for ln, iv, e, lo, hi in child.lane_defs:
            out.lane_defs.append((R(ln), iv, _rename_term(e, R), lo, hi))
        for u, (cell, n_) in child.lane_insts.items():
            if u in getattr(child, "inst_axes", {}):
                raise ComposeError(f"{i.name}: the instance lane {u} of {i.cell} has more than one axis, which is "
                                   f"not composed across a module boundary yet (2026-09-03)")
            out.lane_insts[pfx + u] = (cell, n_)
        for a in child.abstracts:
            out.abstracts.append(ren[a])
        for n in child.data:
            if ren[n] not in out.data:
                out.data.append(ren[n])          # a child's data net stays data (ports: the parent's net)
        comp.inv += child_c.inv and _prefix_inv(child_c.inv, R, pfx)
        comp.inv_abstract += child_c.inv_abstract and _prefix_inv(child_c.inv_abstract, R, pfx)
        comp.ghost += child_c.ghost and R(child_c.ghost)
        if ctext:
            comp.inv += _contract_text(ctext, R, pfx, guarantee_as="viol", require_as="viol",
                                       where=f"{i.name} ({i.cell}, concrete: guarantee re-checked, requirement owed)")
            comp.ghost += _contract_ghost(cpath, ctext, R, pfx)
    return comp


def _contract_helpers(body: str) -> set:
    """The private helper predicates a contract defines (heads that are not guarantee/require)."""
    heads = set(re.findall(r"^\s*([a-z_]\w*)\s*\(", body, re.M))
    # `boundary`, `pval` and `dontcare` are SHARED vocabulary with the symbolic layer and the
    # coverage check, not private helpers: a contract that declares a boundary of its own operands
    # must reach the same bp/pval machinery the spec's declarations reach. Prefixing them composed
    # the intdiv calc contract into DEAD rules -- no error, the guarantee could never fire, and the
    # abstract output ran free: silent vacuity in the composition layer. (The head regex is
    # line-anchored, so a continuation line beginning with `pval(` was also swept in.)
    # `data` joined the set the same day, found the same way: a contract declaring `data(a)` for its
    # symbolic ports had it prefixed to u_eng__data -- the ghost's token-helper marker (`data(` in a
    # body) then failed its lookbehind, the helper was not recognised as a token helper, and every
    # carried engine run was "outside the domain".
    return heads - {"assume", "viol", "guarantee", "require", "bad", "val", "time", "model", "cmodel",
                    "obl", "boundary", "pval", "dontcare", "data"}


def _contract_text(text: str, R, pfx: str, guarantee_as: str, require_as: str, where: str) -> str:
    """The contract with the module's port names renamed to the parent's nets, its `guarantee` /
    `require` heads turned into the parent's `assume`/`viol` with instance-prefixed tags, and its
    private helper predicates prefixed."""
    body = R(text)
    body = re.sub(r"(?<![\w])guarantee\(\s*", f"{guarantee_as}({pfx}", body)
    body = re.sub(r"(?<![\w])require\(\s*", f"{require_as}({pfx}", body)
    if guarantee_as == "viol":                     # a CONCRETE child: its models are OBLIGATIONS to check
        body = re.sub(r"(?<![\w])model\(\s*", "cmodel(", body)
    for h in _contract_helpers(body):
        body = re.sub(r"(?<![\w])" + re.escape(h) + r"\(", f"{pfx}{h}(", body)   # goals included: private
    return f"% ---- contract of {where} ----\n{body.rstrip()}\n"


def _contract_ghost(cpath: pathlib.Path, ctext: str, R, pfx: str) -> str:
    """The contract's GHOST INIT (`<m>.contract.ghost.lp`, if present), renamed exactly as the
    contract was: ports -> the parent's nets, the contract's helper predicates prefixed. Only the
    induction step composes it."""
    from .induct import ghost_file_for
    gpath = ghost_file_for(cpath)
    if not gpath.exists():
        return ""
    body = R(gpath.read_text())
    for h in _contract_helpers(R(ctext)):
        body = re.sub(r"(?<![\w])" + re.escape(h) + r"\(", f"{pfx}{h}(", body)
    return f"% ---- ghost init of {cpath.name} as {pfx[:-2]} ----\n{body.rstrip()}\n"


def _prefix_inv(inv: str, R, pfx: str) -> str:
    """A grandchild's already-composed contract text, renamed again for this level."""
    body = R(inv)
    body = re.sub(r"(?<![\w])(assume|viol)\(\s*", lambda m: f"{m.group(1)}({pfx}", body)
    return body


def composed_lp(comp: Composed, src: str = "") -> str:
    hdr = f"% composed by sv2asp.aspfirst from {src} -- the flattened design (children as inst__name)" if src else ""
    return to_lp(comp.design, hdr)
