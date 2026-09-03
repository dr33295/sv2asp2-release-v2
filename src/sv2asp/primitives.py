"""Primitive registry: recognize library cells by module name and give their FUNCTIONAL
semantics, without translating their implementation (catalog §2.10 generalized).

A recognized primitive instance is lowered to the SAME IR we already emit — a gate to a
``CombItem``, a flop to a ``SeqItem`` — so the existing stages handle it. The registry is the
table mapping ``module_name -> PrimSpec``; it is built-in here and extensible later via config.
Cell names are VENDOR-NEUTRAL (``FF``, ``INV``, ``VFF``, ...); ``lookup`` also strips a leading
vendor prefix (``VENDOR_FF``, ``ACME_FF`` -> ``FF``) so real corporate RTL still resolves.
See docs/reference/SV_TRANSLATION_CATALOG.md Group 6 (the primitive library) for the catalogued patterns.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass

from .ir.expr import BinOp, Cond, Expr, UnOp


@dataclass(frozen=True)
class PrimSpec:
    """How to functionally lower one primitive instance.

    category:
      "flop" — sequential: pins clk/en/d/q (+ rstL for async reset). ``reset`` in {low,high}
               or None; ``reset_value_param`` names the param holding the reset value.
      "comb" — combinational: ``out`` is the output pin; ``build(inputs)`` returns the IR
               expression over the input-pin actuals (an Expr map keyed by pin name).
      "wire" — passthrough: ``out = in`` (buffers, DV force/release mux collapse).
      "vff"  — vectored flop: ``lanes_param`` independent per-lane flops over the en/d/q
               vectors (catalog §4.6 lane-lifting). Pins clk/en/d/q connect to vector signals.
      "vcmux" — one-hot VECTOR mux: ``out`` (W bits) = the ``sel``-selected W-bit slice of the
               packed input bus ``in`` (N*W bits, N slices). ``sel`` is N-bit ONE-HOT (bit i
               selects input slice i). Sizes (W, N) are read from the port WIDTHS at the call
               site (params are not always elaborable), so no *_param field is needed.
      "clz"  — count-leading-zeros / count-leading-sign-bits unit.
               Pins: ``cntIn`` (64-bit input), ``cntSgn`` (1-bit mode: 0=CLZ, 1=CLS),
               ``clzD`` (7-bit CLZ/CLS result output), ``clzS`` (SIMD half-word CLZ, optional).
               ``clzD`` is driven by ``@clz(cntIn, cntSgn)``; ``clzS`` is tied to 0 when present.

    NEW PRIMITIVES WITHOUT TOUCHING THE TOOL: a "comb" registration's ``build`` may
    return any IR expression — including ``FuncCall`` applying a plugin-registered
    @func — so site plugins can introduce entirely new cells (see config.py).

    WHAT BELONGS HERE vs a functional stub: this registry holds *behavioral models
    expanded INLINE at the instantiation site* with full port mapping (including
    concat-connected output ports split into the parent nets). That fits leaf library
    cells, and also small RTL units deliberately abstracted by a behavioral @func
    (a CLZ unit). A *functional stub* (sources.json "stubs") instead replaces a
    module's translation with hand-written instance-scoped ASP — right for larger
    units with their own state/timing (a pipelined MAC). Registrations that carry
    vendor/design names come from site plugins (sv2asp.toml [primitives]), never
    from this file.
    The vendor-prefix-strip rule in ``lookup`` makes vendor-prefixed cell names
    (``ANY_X`` → ``X``) resolve without per-vendor registrations.
    """

    category: str
    pins: dict[str, str]                       # role -> pin name on the cell
    out: str | None = None                     # comb/wire/mux output pin
    build: Callable[[dict[str, Expr]], Expr] | None = None
    reset: str | None = None                   # "low" | "high" | None
    reset_value_param: str | None = None       # param name for the reset value (e.g. RESET_VALUE)
    inputs: tuple[str, ...] = ()               # mux: input pins, In0..In{N-1}, selected by sel
    lanes_param: str | None = None             # vff: param naming the lane count (NUM_INPUTS)
    width_param: str | None = None             # vff: param naming the per-lane bit width (WIDTH)


def _and(*xs: Expr) -> Expr:
    e = xs[0]
    for x in xs[1:]:
        e = BinOp("and", e, x, 1)
    return e


def _or(*xs: Expr) -> Expr:
    e = xs[0]
    for x in xs[1:]:
        e = BinOp("or", e, x, 1)
    return e


def _not(x: Expr) -> Expr:
    return UnOp("not", x, 1)


# Built-in primitive registry (Phase A). Vendor-neutral cell names; a vendor prefix on a real
# instance (VENDOR_FF, ACME_FF) is stripped by `lookup`.
REGISTRY: dict[str, PrimSpec] = {
    # --- sequential ---
    "FF":        PrimSpec("flop", {"clk": "clk", "en": "en", "d": "d", "q": "q"}),
    "FF_NOSCAN": PrimSpec("flop", {"clk": "clk", "en": "en", "d": "d", "q": "q"}),
    "ARFF":      PrimSpec("flop", {"clk": "clk", "en": "en", "rstL": "rstL", "d": "d", "q": "q"},
                          reset="low", reset_value_param="RESET_VALUE"),
    # --- logic gates (1-bit combinational) ---
    "BUF": PrimSpec("wire", {"in": "I"}, out="Z"),
    "INV": PrimSpec("comb", {"i": "I"}, out="ZN",
                    build=lambda p: UnOp("not", p["I"], 1)),
    "AN2": PrimSpec("comb", {}, out="Z",
                    build=lambda p: BinOp("and", p["A1"], p["A2"], 1)),
    "OR2": PrimSpec("comb", {}, out="Z",
                    build=lambda p: BinOp("or", p["A1"], p["A2"], 1)),
    "XOR2": PrimSpec("comb", {}, out="Z",
                     build=lambda p: BinOp("xor", p["A1"], p["A2"], 1)),
    "ND2": PrimSpec("comb", {}, out="ZN",
                    build=lambda p: UnOp("not", BinOp("and", p["A1"], p["A2"], 1), 1)),
    "NR2": PrimSpec("comb", {}, out="ZN",
                    build=lambda p: UnOp("not", BinOp("or", p["A1"], p["A2"], 1), 1)),
    "XNR2": PrimSpec("comb", {}, out="ZN",
                     build=lambda p: UnOp("not", BinOp("xor", p["A1"], p["A2"], 1), 1)),
    "AN3": PrimSpec("comb", {}, out="Z", build=lambda p: _and(p["A1"], p["A2"], p["A3"])),
    "OR3": PrimSpec("comb", {}, out="Z", build=lambda p: _or(p["A1"], p["A2"], p["A3"])),
    "ND3": PrimSpec("comb", {}, out="ZN", build=lambda p: _not(_and(p["A1"], p["A2"], p["A3"]))),
    "NR3": PrimSpec("comb", {}, out="ZN", build=lambda p: _not(_or(p["A1"], p["A2"], p["A3"]))),
    "ND4": PrimSpec("comb", {}, out="ZN",
                    build=lambda p: _not(_and(p["A1"], p["A2"], p["A3"], p["A4"]))),
    "NR4": PrimSpec("comb", {}, out="ZN",
                    build=lambda p: _not(_or(p["A1"], p["A2"], p["A3"], p["A4"]))),
    "MUX2": PrimSpec("comb", {}, out="Out", build=lambda p: Cond(p["sel"], p["In1"], p["In0"], 1)),
    # encoded-select muxes: Out = In[sel] (a case over the word sel)
    "MUX3": PrimSpec("mux", {"sel": "sel"}, out="Out", inputs=("In0", "In1", "In2")),
    "MUX4": PrimSpec("mux", {"sel": "sel"}, out="Out", inputs=("In0", "In1", "In2", "In3")),
    # one-hot VECTOR mux (ACME_VCMUX): out[W-1:0] = the sel-selected W-bit slice of the packed
    # input bus in[N*W-1:0]; sel is N-bit ONE-HOT. Sizes read from port widths at the call site.
    "VCMUX": PrimSpec("vcmux", {"in": "in", "sel": "sel"}, out="out"),
    # NOTE: vendor-specific cell registrations (company module names, design ROMs) do NOT
    # live here -- they come from site plugins via the [primitives] section of sv2asp.toml
    # (see config.py / register_prims below). The "clz" KIND above stays generic.
    # AND-OR-INVERT / OR-AND-INVERT family (Phase B; <=4 inputs)
    "AOI21": PrimSpec("comb", {}, out="ZN",
                      build=lambda p: _not(_or(_and(p["A1"], p["A2"]), p["B"]))),
    "OAI21": PrimSpec("comb", {}, out="ZN",
                      build=lambda p: _not(_and(_or(p["A1"], p["A2"]), p["B"]))),
    "AOI211": PrimSpec("comb", {}, out="ZN",
                       build=lambda p: _not(_or(_and(p["A1"], p["A2"]), p["B"], p["C"]))),
    "OAI211": PrimSpec("comb", {}, out="ZN",
                       build=lambda p: _not(_and(_or(p["A1"], p["A2"]), p["B"], p["C"]))),
    "AOI22": PrimSpec("comb", {}, out="ZN",
                      build=lambda p: _not(_or(_and(p["A1"], p["A2"]), _and(p["B1"], p["B2"])))),
    "OAI22": PrimSpec("comb", {}, out="ZN",
                      build=lambda p: _not(_and(_or(p["A1"], p["A2"]), _or(p["B1"], p["B2"])))),
    "OAI31": PrimSpec("comb", {}, out="ZN",
                      build=lambda p: _not(_and(_or(p["A1"], p["A2"], p["A3"]), p["B"]))),
    # --- latches & reset-distribution flop (modeled as flops at cycle boundaries) ---
    # LEVEL-SENSITIVE latches. Transparent while `en` is high (zero delay), hold otherwise --
    # NOT flops (see Latch.lean: the flop reading is this schema delayed one cycle, i.e. a
    # different circuit). Instantiating one requires --allow-latches; latches are never
    # INFERRED, and an incomplete always_comb stays a loud problem.
    "LATA": PrimSpec("latch", {"clk": "clk", "en": "en", "d": "d", "q": "q"}),
    "LATB": PrimSpec("latch", {"clk": "clk", "en": "en", "d": "d", "q": "q"}),
    "RSTFF": PrimSpec("flop", {"clk": "clk", "d": "rstd", "q": "rstq"}),  # no en: always captures
    # --- vectored flop: NUM_INPUTS independent per-lane flops (lane-lifting, §4.6) ---
    "VFF": PrimSpec("vff", {"clk": "Clk", "en": "En", "d": "D", "q": "Q"},
                    lanes_param="NUM_INPUTS", width_param="WIDTH"),
    # --- clock gating (ICG): produce a gated CLOCK DOMAIN gclk that ticks only when en is high.
    # gclk becomes a derived clock: time(gclk,T) :- time(clk,T), val(en,1,T)  (catalog §6.7, NOT a flop
    # enable -- the clock edge itself is suppressed). `clkgate` is the vendor-neutral name; CKGL3/CKG are
    # common vendor cells (clkIn/en/clkOut). A vendor prefix (ACME_clkgate) is stripped by `lookup`.
    "clkgate": PrimSpec("clock_gate", {"clk": "clk", "en": "en", "gclk": "gclk"}),
    "CKG":     PrimSpec("clock_gate", {"clk": "clkIn", "en": "en", "gclk": "clkOut"}),
    "CKGL3":   PrimSpec("clock_gate", {"clk": "clkIn", "en": "en", "gclk": "clkOut"}),
}


def lookup(module_name: str) -> PrimSpec | None:
    """Resolve a module name to a primitive spec. Tries the exact (vendor-neutral) name first,
    then strips a leading VENDOR prefix — an all-uppercase token before the first ``_`` — so a
    real ``VENDOR_FF`` / ``ACME_AOI21`` resolves to ``FF`` / ``AOI21``. A user module whose name isn't
    ``<UPPER>_<cell>`` (or whose suffix isn't a known cell) returns None and is flattened normally."""
    spec = REGISTRY.get(module_name)
    if spec is not None:
        return spec
    head, sep, rest = module_name.partition("_")
    if sep and rest and head.isalnum() and head.isupper():   # vendor-style prefix -> strip it
        return REGISTRY.get(rest)
    return None


#: Cells registered by a site plugin rather than declared above. Site cells are
#: design-specific, so they have no documented function in `docs/reference/SV_PRIMITIVE_LIBRARY.md` and
#: are out of scope for the schema proofs (`proofs/gen_prims_lean.py`), which must still
#: refuse a BUILTIN that has no documented spec. Keeping the two sets distinct is what
#: lets that check stay fail-loud without tripping over whatever a plugin registered.
PLUGIN_PRIMS: set[str] = set()


def register_prims(prims: dict[str, "PrimSpec"], origin: str = "<plugin>") -> None:
    """Register site-plugin primitive cells (see config.py). Company cell names and
    design-specific units come from plugins, never from this file. Redefining a
    builtin is refused loudly."""
    for name, spec in prims.items():
        if name in REGISTRY:
            raise ValueError(f"primitive {name!r} already registered; "
                             f"plugin {origin} may not override builtins")
        REGISTRY[name] = spec
        PLUGIN_PRIMS.add(name)
