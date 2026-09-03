"""THE GENERATION TARGET, printed by the tool that enforces it.

A model in the loop writes two of this route's artifacts by hand -- the design `l1.lp` and
its linkage `l1.inv.lp` -- and reads a third, the generated contract. All three are ASP in a
fixed schema, and until this module existed the schema was written down nowhere: an author
inferred it from one worked example (the user, 2026-09-02: "the translation grammar for
sv2asp is something that the tool should show so that the llm can generate in that manner").

The asymmetry that motivated it is worth keeping in view. The language a person WRITES has a
single gated source (`lib/dsl/grammar.ebnf`, from which the parser is built and the
methodology rendered). The language the tool writes BACK -- and the design language it
accepts -- had no such definition.

So this is DERIVED, never transcribed. `FACT_PREDS` is what `load.py` accepts and refuses
everything outside of; `CELLS` is what `model.py` says a primitive's pins are; `_ROLES` is
how `emit.py` names an auxiliary atom. Printing those tables cannot drift from the tool's
behaviour, because they ARE the behaviour. What is not derivable -- the glosses -- is held to
a completeness test instead: a fact predicate or a cell with no gloss is a build error, so a
new one cannot ship undocumented.
"""
from __future__ import annotations

# ---------------------------------------------------------------------------------------------
# the DESIGN language: glosses beside the tables that define it
# ---------------------------------------------------------------------------------------------

#: What each fact MEANS. The names and arities come from `load.FACT_PREDS`; only these
#: sentences are written here, and `test_v2_schema_is_complete` fails if one is missing.
FACT_GLOSS = {
    "module": ("the block's name -- exactly one per file, and it is the SystemVerilog "
               "module name too. ASP reads a leading capital as a variable, so a name like "
               "TopModule must be QUOTED: `module(\"TopModule\").`"),
    "port": "a boundary wire: (name, input|output, width)",
    "net": ("an internal wire: (name, width) -- or (name, enum(E)) for a wire that carries "
            "a member of the enum declared on E, which is what makes the print use NAMES"),
    "def": "combinational logic: (net_or_term, expression) -- the net IS the expression",
    "inst": "a primitive or submodule instance: (instanceName, cell)",
    "pin": "wires an instance's pin: (instance, pinName, net)",
    "iparam": "sets an instance's parameter: (instance, paramName, value)",
    "param": "a module parameter and its DEFAULT: (name, value)",
    "mparam": "overrides a child's parameter at an instance: (instance, name, value)",
    "enum_member": "one member of an enumerated net: (net, memberName, encoding)",
    "abstract": "this instance is NOT built -- its contract is assumed instead",
    "data": "this net carries DATA: a token compared and routed, never enumerated",
    "opaque_datapath": "the whole datapath is opaque -- no net's value is ever enumerated",
    "arch_mem": "architectural memory the SPECIFICATION names: (name, depth, width)",
    "arch_reg": ("architectural register the specification names: (name, width) -- or "
                 "(name, enum(E)) with enum_member(E, ...) facts, which makes it a NAMED-STATE "
                 "register: it prints with the enum type, resets to a member, compares by name"),
    "net_lane": ("a net replicated per lane: (name, lanes, width). `lanes` is a count or a LIST of counts, "
                 "`(side, side)`: a grid has members `g(r, c)`, row-major, and every axis is indexed on its own. "
                 "Its MEMBERS are `L(0)..`; "
                 "the lane as one word is `pack(L)` (member 0 the LSB), which prints as the "
                 "bare name because a lane already prints as a packed vector"),
    "port_lane": "a port replicated per lane: (name, direction, lanes, width)",
    "def_lane": ("combinational logic per lane: (term, expression, lanes); with a list of loop variables, "
                 "`def_lane(y, (R, C), e)`, one per axis, and a reference `q(R - 1 \\\\ side, C)` wrapping each "
                 "axis on its own -- a torus is eight such lines with no row base. A lane reference in the "
                 "expression is `x(I)`, a neighbour `x(I+k)` / `x(I-k)` (the window shrinks so every "
                 "reference stays inside the lane), or a WRAPPING neighbour `x(I+k \\\\ B)`: the index wraps "
                 "within the block of size B containing I, so B = the extent is a ring and B = one row "
                 "is a row-major grid's column wrap. k and B may each be a number or a PARAMETER "
                 "(`q(I - side \\\\ cells)`), which is what keeps a grid parametric in the print. A "
                 "torus is eight such lines, the diagonals composed through intermediate lanes"),
    "inst_lane": ("an instance replicated per lane: (name, cell, lanes); `lanes` a count or a list of counts "
                  "`(side, side)` -- a grid of cells `u(r, c)`, each lane pin joining member to member, "
                  "which is how a grid of registers holds its state"),
}

#: Why you would reach for each primitive. Pins, parameters and outputs come from
#: `model.CELLS`; these sentences say when to use it, which the table cannot.
CELL_GLOSS = {
    "ff": "an edge-triggered flop with a clock enable -- the ordinary register",
    "arff":  ("a flop with an ASYNCHRONOUS active-low reset that forces `reset_value` -- a "
              "number, or for an enum register the bare member LABEL"),
    "lata": "a level-sensitive latch: transparent while `en`, holding otherwise",
    "spram": "a single-port RAM -- one address, a write port and a read port",
    "farray": ("an array of REGISTERS, not a RAM: one write port, any number of `mrd(M, A)` "
               "readers, and an optional reset that forces EVERY cell at once"),
}

#: The contract's FIXED vocabulary -- the predicates that mean the same thing in every
#: contract, whatever the block. Everything else is generated per declaration.
CONTRACT_FIXED = {
    "gtime(T)": "T is an instant of the run. Every rule needs one positive time literal.",
    "live(T)": ("T is judged. The file's `disable iff` becomes this, so a claim naming the "
                "reset is exempt and uses `gtime` instead."),
    "failType(Name, T)": ("THE VERDICT ATOM. Named wrongness appeared at instant T. A "
                          "certificate proves no failType is derivable."),
    "holds(NameS, T)": "a scenario's SITUATION is satisfied at T",
    "did(NameD)": "a scenario's EXPECTATION was met -- the story was actually reached",
    "scenario(Name, Situation, Inputs, Expectation)": "declares a scenario to the runner",
    "boundary(Question, 1)": ("declares a decision COMPUTED from data -- an equality, a bit "
                              "select. The word behind it is never enumerated."),
    "pval(Question, V)": "reads a declared boundary's answer back as one free value",
    "entryId(E)": "the identity domain of objects -- every slot, live or not",
}

#: PREDICATES generated per declaration or per window. `<name>` is the declaration's own
#: name, `<Window>` a window's; the role suffixes come from `emit._ROLES`.
CONTRACT_FAMILIES = {
    "<name><Role>": ("an auxiliary atom of one declaration, named for the ROLE it plays in "
                     "it (see the roles below) -- never a numbered gensym"),
    "may<Window><Mode>": ("a licensed cause: this behaviour permits that window to change "
                          "here. Mode is Set, Clear or Write."),
    "mayAllocate / mayVanish": "the licensed causes for an object appearing and ceasing",
}

#: THE VERDICT NAMES -- the first argument of `failType`, which is what a person reads when a
#: certificate fails. These are NAMES, not predicates: the predicate is always `failType`.
FAILTYPE_NAMES = {
    "<claimName>": "a `@property` or `@assume` was violated -- its own name, unadorned",
    "<behaviourName>Wrong": "a `@behavior`'s trigger fired and its effect did not happen",
    "<window>Disturbed": ("THE FRAME: the window changed with no licensed cause. You never "
                          "write hold conditions; this is the reason you do not have to."),
    "<window>NotSingleValued": ("the window holds two values at one instant -- a linkage "
                                "mounting it from more than one rule"),
    "entryAppeared / entryVanished": "an object appeared or ceased with no licensed cause",
}

#: The EXPRESSION operators -- what `def(x, <expr>)` is written in. Names and arities come from
#: `model.OPS`; argument ORDER is what this table adds, and it is taken from the library's own
#: evaluation rules (lib/aspfirst/aspfirst.lp), not from memory. `test_v2_schema_is_complete`
#: fails if an operator has no gloss. It was missing from the printed schema until `pack` made
#: the gap visible: a model writing an expression had the facts and the primitives and not
#: the vocabulary between them.
OP_GLOSS = {
    "add": "add(A, B, W): A + B wrapped to W bits",
    "sub": "sub(A, B, W): A - B wrapped to W bits (SystemVerilog subtraction wraps)",
    "mul": "mul(A, B, W): A * B wrapped to W bits",
    "and": "and(A, B, W): bitwise A & B at W bits",
    "or":  "or(A, B, W): bitwise A | B at W bits",
    "xor": "xor(A, B, W): bitwise A ^ B at W bits",
    "shl": "shl(A, N, W): A << N, truncated to W bits",
    "shr": "shr(A, N, W): A >> N, logical (zero-fill)",
    "ashr": "ashr(A, N, W): A >> N, arithmetic (sign-fill) at width W",
    "idiv": "idiv(A, B, W): A / B unsigned, truncated (B = 0 gives 0)",
    "imod": "imod(A, B, W): A mod B unsigned (B = 0 gives 0)",
    "sidiv": "sidiv(A, B, W): A / B signed at width W, toward zero (B = 0 gives 0)",
    "simod": "simod(A, B, W): A mod B signed at width W, sign of the dividend",
    "lt": "lt(A, B, W): 1 if A < B unsigned at width W", "le": "le(A, B, W): A <= B unsigned",
    "gt": "gt(A, B, W): A > B unsigned", "ge": "ge(A, B, W): A >= B unsigned",
    "slt": "slt(A, B, W): A < B signed at width W", "sle": "sle(A, B, W): A <= B signed",
    "sgt": "sgt(A, B, W): A > B signed", "sge": "sge(A, B, W): A >= B signed",
    "bnot": "bnot(A, W): bitwise NOT at W bits",
    "neg": "neg(A, W): two's-complement negation at W bits",
    "sext": "sext(A, F, W): A sign-extended from F bits to W bits",
    "slc": "slc(A, LO, W): the W-bit slice of A starting at bit LO",
    "bit": ("bit(A, I): bit I of A. Inside a def_lane the position may be an expression over the def's "
            "loop variables and parameters -- `bit(data, add(mul(R, side), C))` reads a flat port at the "
            "cell's own position (G30)"),
    "cat": "cat(A, WA, B, WB): A (the HIGH part, WA bits) above B (WB bits)",
    "eq": "eq(A, B): 1 if A == B -- symbol equality; on data, a boundary the theory answers",
    "ne": "ne(A, B): 1 if A != B",
    "logand": "logand(A, B): logical AND of two truths", "logor": "logor(A, B): logical OR",
    "lnot": "lnot(A): logical NOT of a truth",
    "ror": "ror(A, W): OR-reduction of A's W bits", "rand": "rand(A, W): AND-reduction",
    "rxor": "rxor(A, W): XOR-reduction (parity)", "rnand": "rnand(A, W): NAND-reduction",
    "rnor": "rnor(A, W): NOR-reduction", "rxnor": "rxnor(A, W): XNOR-reduction",
    "parity": "parity(A, W): the parity of A's W bits",
    "popcnt": "popcnt(A, W): the number of set bits in A's W bits",
    "clz": "clz(A, SGN): leading zeros of A in a 64-bit field, or leading sign bits when SGN = 1",
    "ite": "ite(S, A, B): A when S != 0, else B",
    "k": "k(V, W): the constant V at width W",
    "tag": "tag(L): the enum member L, as a symbol",
    "mrd": "mrd(M, A): the cell of flop array M at address A -- an expression, so any number of readers",
    "pack": "pack(L): the lane L as ONE word, member 0 the LSB -- prints as the lane's own name",
}

LINKAGE_SHAPE = """\
A window is a DERIVED VIEW of the design's own flops -- never a copy, never state of its own.
One rule per window, reading the signals that already exist:

    entryExists(0, T)     :- val(valid(0), 1, T).
    entryAddress(0, A, T) :- val(addr(0), A, T), val(valid(0), 1, T).
    demanding(0, T)       :- val(dem(0), 1, T), val(valid(0), 1, T).

Three rules that are not optional:

  * MOUNT EVERY WINDOW the contract demands. `compile` prints them
    (`window demanded of the design: X`). A window nothing mounts derives nothing, so every
    claim reading it is vacuously true -- green for the worst reason.
  * GATE A FIELD ON ITS OBJECT'S EXISTENCE, as `entryAddress` does above. A stale value in a
    dead slot is otherwise a live fact.
  * ONE SOURCE PER WINDOW. Two rules mounting one window make it multi-valued, and a claim
    asks whether SOME value matches -- so a spurious second value SATISFIES a claim the
    design violates. The `<window>NotSingleValued` monitor exists to catch exactly this.
"""


def render(design: bool = True, contract: bool = True, linkage: bool = True) -> str:
    """The schema, assembled from the tables that define the tool's behaviour."""
    from .emit_roles import roles                      # kept out of the import cycle
    from .load import FACT_PREDS
    from .model import CELLS
    out: list[str] = []

    if design:
        out += ["THE DESIGN LANGUAGE -- what you write in `l1.lp`.",
                "Facts, one per statement, ending in `.`. Anything outside this list is",
                "REFUSED by name, so the list is exhaustive rather than illustrative.", ""]
        for name in sorted(FACT_PREDS):
            arity = FACT_PREDS[name]
            sig = f"{name}/{arity}" if arity else name
            out.append(f"  {sig:<18} {FACT_GLOSS.get(name, '(no gloss -- a build error)')}")
        out += ["", "  STATE COMES FROM PRIMITIVES, never from a rule you write: hold and set",
                "  semantics live in the cell, so a design cannot get them subtly wrong.", ""]
        for cell in sorted(CELLS):
            pins, params, _outs = CELLS[cell]
            out.append(f"  {cell}({', '.join(pins)})")
            out.append(f"      parameters: {', '.join(params) or 'none'}")
            out.append(f"      {CELL_GLOSS.get(cell, '(no gloss -- a build error)')}")
        out += ["", "  THE OPERATORS an expression is written in (`def(x, <expr>)`), with their",
                "  argument order. W is always a width; a comparison yields one bit.", ""]
        from .model import OPS
        for op in sorted(OPS):
            out.append(f"  {OP_GLOSS.get(op, f'{op}/{OPS[op]} (no gloss -- a build error)')}")
        out.append("")

    if contract:
        out += ["THE CONTRACT -- what `compile` emits into `spec.lp`. You read this; you",
                "never write it. Its fixed vocabulary:", ""]
        for sig, gloss in CONTRACT_FIXED.items():
            out.append(f"  {sig}")
            out.append(f"      {gloss}")
        out += ["", "  Predicates generated per declaration or per window:", ""]
        for sig, gloss in CONTRACT_FAMILIES.items():
            out.append(f"  {sig}")
            out.append(f"      {gloss}")
        out += ["", f"  The role suffixes: {', '.join(sorted(roles()))}.", "",
                "  The VERDICT NAMES -- the first argument of `failType`, and what you read",
                "  when a certificate fails. The predicate is always `failType`; these are",
                "  the names it carries:", ""]
        for sig, gloss in FAILTYPE_NAMES.items():
            out.append(f"  {sig}")
            out.append(f"      {gloss}")
        out.append("")

    if linkage:
        out += ["THE LINKAGE -- what you write in `l1.inv.lp`.", ""]
        out += ["  " + l if l else "" for l in LINKAGE_SHAPE.splitlines()]
        out.append("")

    return "\n".join(out)
