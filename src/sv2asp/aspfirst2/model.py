"""The in-memory model of an ASP-first design: what the loader reads off the authored `.lp` and
what the linter and printer consume. Terms are plain nested tuples so they can be compared,
hashed and printed without a class per operator:

    "wr_ptr"                    a net (leaf)                    3                 an int
    ("k", 4, 3)                 the constant 4 at 3 bits        ("k", ("str", "4294967296"), 33)  a wide constant
    ("add", "a", "b", 8)        an operator term                ("tag", "idle")   an enum tag
"""
from __future__ import annotations

from dataclasses import dataclass, field
from .lanes import LaneTable

Term = "str | int | tuple"

#: operator arities: name -> number of arguments (as written by the author)
OPS: dict[str, int] = {
    **{o: 3 for o in ("add", "sub", "mul", "and", "or", "xor", "shl", "shr", "ashr",
                       "idiv", "imod", "sidiv", "simod",
                       "lt", "le", "gt", "ge", "slt", "sle", "sgt", "sge")},
    "bnot": 2, "neg": 2, "sext": 3, "slc": 3, "bit": 2, "cat": 4,
    "eq": 2, "ne": 2, "logand": 2, "logor": 2, "lnot": 1,
    **{o: 2 for o in ("ror", "rand", "rxor", "rnand", "rnor", "rxnor", "parity", "popcnt")},
    #: `clz(A, SGN)` -- leading ZEROS of A in a 64-bit field, or leading SIGN bits when SGN=1.
    #: The count is 0..64 whatever the operand's width, because @clz's field is fixed at 64.
    "clz": 2,
    "ite": 3, "k": 2, "tag": 1,
    #: `mrd(M, A)` -- read the cell of flop array M at the value of A. An EXPRESSION, not a port, so a
    #: design may read one array at any number of indices in a cycle (see CELLS["farray"]).
    "mrd": 2,
    #: `pack(L)` -- a LANE as one word, member 0 the LSB. A lane of 1-bit nets already PRINTS as
    #: `logic [N-1:0] L`, so in SystemVerilog the packed word simply IS the lane's name; what was
    #: missing was any way to SAY so in the authoring language, which left a design whose state is
    #: one bit per position writing the weighted sum by hand -- and a hand-written sum bakes its
    #: weights per element, so the printed module carried a parameter it did not honour (G20).
    #: An explicit operator rather than accepting a bare lane name where a net is expected: a lane
    #: of WIDE elements has a packed word too, and its cost is exponential in the element count,
    #: so the reading is DECLARED and can be budgeted rather than inferred and discovered.
    "pack": 1,
}

#: library cells: name -> (pins, iparams, output pins)
CELLS: dict[str, tuple[tuple[str, ...], tuple[str, ...], tuple[str, ...]]] = {
    "ff":    (("clk", "en", "d", "q"), ("width",), ("q",)),
    "arff":  (("clk", "en", "rstL", "d", "q"), ("width", "reset_value"), ("q",)),
    "lata":  (("en", "d", "q"), ("width",), ("q",)),
    "spram": (("clk", "we", "wa", "wd", "ra", "rd"), ("depth", "width"), ("rd",)),
    #: An array of REGISTERS, not a RAM: one write port and ANY number of `mrd(M, A)` readers, plus an
    #: optional async reset that forces EVERY cell at once -- which is what distinguishes a flop array
    #: from an SRAM, and what a table like a predictor's counters actually is.
    "farray": (("clk", "we", "wa", "wd", "rstL"), ("depth", "width", "reset_value"), ()),
}

#: the @func names a guarded comb rule may call, with their arity (value args + width args)
FUNCS: dict[str, int] = {
    "add": 3, "sub": 3, "mul": 3, "idiv": 3, "imod": 3, "sidiv": 3, "simod": 3,
    "band": 3, "bor": 3, "bxor": 3, "shl": 3, "shr": 3, "ashr": 3, "ipow": 3,
    "bnot": 2, "neg": 2, "sext": 3, "slc": 3, "wcmp": 4,
    "parity": 2, "popcnt": 2, "rand": 2, "ror": 2, "rxor": 2, "rnand": 2, "rnor": 2, "rxnor": 2,
    "clz": 3,
}

Width = "int | tuple[str, str]"      # an int, or ("enum", E)


@dataclass(frozen=True)
class Port:
    name: str
    direction: str            # "input" | "output"
    width: object             # int | ("enum", E)


@dataclass(frozen=True)
class Net:
    name: str
    width: object


@dataclass(frozen=True)
class Inst:
    name: str
    cell: str
    pins: dict            # pin -> net
    iparams: dict         # param -> int | str
    mparams: dict = field(default_factory=dict)   # module PARAMETER overrides (an authored module instance)


@dataclass(frozen=True)
class Step:
    """`V2 = @add(V0, V1, 8)` inside a guarded comb rule."""
    var: str
    func: str
    args: tuple           # each a var name (str, uppercase), an int, or ("str", s)


@dataclass(frozen=True)
class Rule:
    """A guarded combinational rule `val(head, value, T) :- ...` in the restricted grammar."""
    head: str
    value: object                       # ("var", V) | int | str (a tag)
    guards: tuple                       # ((sig, const|tag), ...)      -- val(sig, c, T)
    reads: tuple                        # ((sig, var), ...)            -- val(sig, V, T)
    cmps: tuple                         # ((var, op, const), ...)      -- V != c / V = c / V < c ...
    steps: tuple                        # (Step, ...)
    line: int
    text: str


@dataclass
class Design:
    name: str = ""
    ports: list = field(default_factory=list)          # [Port]
    nets: list = field(default_factory=list)           # [Net]
    enums: dict = field(default_factory=dict)          # E -> [(label, value)]
    params: dict = field(default_factory=dict)         # P -> V
    defs: dict = field(default_factory=dict)           # net -> Term
    def_order: list = field(default_factory=list)      # nets in the order their defs appear
    insts: list = field(default_factory=list)          # [Inst]
    rules: list = field(default_factory=list)          # [Rule]
    arch_regs: dict = field(default_factory=dict)      # ARCHITECTURAL single REGISTERS the spec may name: name -> width.
                                                      # The memory's twin: a specification that names one register (the
                                                      # Am2901's Q) had no faithful form, because arch_mem must be built
                                                      # as spram/farray and a depth-1 array cannot be addressed cleanly.
                                                      # An arch_reg IS a net, so abstraction, width checks, the printer
                                                      # and plan_step's state-freeing all apply unchanged.
    arch_mems: dict = field(default_factory=dict)      # ARCHITECTURAL memories the spec may name: name -> (depth, width);
                                                       # built as `inst(name, spram)` of that shape, or `abstract(name)`
    abstracts: list = field(default_factory=list)      # nets left ABSTRACT (a free choice each instant,
    #                                                    constrained only by the level's invariants) --
    #                                                    the refinement loop's unfinished parts
    opaque_datapath: bool = False                      # the `opaque_datapath.` directive: the certificate's
    #                                                    CONTROL solves treat every internal data net as a
    #                                                    fresh token per instant (an en-gated datapath's
    #                                                    hold/load fork otherwise multiplies grounding
    #                                                    candidates through a compressor tree); the delivery
    #                                                    obligation alone computes the real terms, with the
    #                                                    enable/isolation INPUT nets pinned active
    data: list = field(default_factory=list)           # nets declared DATA: their values are never
    #                                                    enumerated in verification -- they carry symbolic
    #                                                    TERMS (the CDS split at authoring time; the
    #                                                    symbolic companion + lint give it meaning)
    src: dict = field(default_factory=dict)            # ("def"|"inst"|"abstract", name) -> (line, text):
    #                                                    provenance for the expanded (emitted-schema) view
    inst_axes: dict = field(default_factory=dict)      # instance lane -> extents per axis (multi-axis only)
    lanes: dict = field(default_factory=LaneTable)     # LANES (generate-for families): name -> (N, W, dir|None); the
    #                                                    ASP sees the UNROLLED members name(0..N-1); the printer re-rolls
    lane_defs: list = field(default_factory=list)      # (name, index-var, expr with lane refs as "x(I)") -- rolled, for the printer
    lane_insts: dict = field(default_factory=dict)     # instance name -> (cell, N) -- rolled, for the printer
    raw: object = None                                 # the UNRESOLVED design (widths as parameter expressions)
    #                                                    when the file declares params -- the printer prints from it
    param_exprs: dict = field(default_factory=dict)    # param -> its expression as written (int, or a term over params)

    # -- lookups ---------------------------------------------------------------------------------
    def width_of(self, name: str):
        for p in self.ports:
            if p.name == name:
                return p.width
        for n in self.nets:
            if n.name == name:
                return n.width
        return None

    def wires(self) -> list:
        """Every declared signal name, ports first, in declaration order."""
        return [p.name for p in self.ports] + [n.name for n in self.nets]

    def inputs(self) -> list:
        return [p for p in self.ports if p.direction == "input"]

    def outputs(self) -> list:
        return [p for p in self.ports if p.direction == "output"]

    def module_insts(self) -> list:
        """Instances of AUTHORED modules (not library cells) -- hierarchy."""
        return [i for i in self.insts if i.cell not in CELLS]

    def cell_insts(self) -> list:
        return [i for i in self.insts if i.cell in CELLS]

    def abstract_mems(self) -> list:
        """Architectural memories left abstract: every cell a free value each instant (the companion)."""
        return [a for a in self.abstracts if a in self.arch_mems]

    def abstract_nets(self) -> list:
        inst_names = {i.name for i in self.insts}
        return [a for a in self.abstracts if a not in inst_names and a not in self.arch_mems]

    def abstract_insts(self) -> list:
        inst_names = {i.name for i in self.insts}
        return [a for a in self.abstracts if a in inst_names]

    def rule_heads(self) -> list:
        seen: list = []
        for r in self.rules:
            if r.head not in seen:
                seen.append(r.head)
        return seen
