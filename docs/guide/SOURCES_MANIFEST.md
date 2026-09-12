# `sources.json` — the project manifest (complete reference)

A `sources.json` manifest tells `sv2asp` **what to compile, what to translate, and how to specialize
it** — in one file, so a whole project is one `--sources` argument instead of a long command line. It
is loaded by `src/sv2asp/sources.py`.

```sh
PYTHONPATH=src python -m sv2asp.cli --sources sources.json -o out/
```

All paths inside the manifest resolve **relative to the manifest file** (not the working directory).
Absolute paths are honoured as-is.

---

## Top-level fields

| Field | Required | JSON type | Meaning | Default |
|---|---|---|---|---|
| **`sources`** | **REQUIRED** | array of *entry* objects (below) | the design RTL to **translate** + coverage-check. Must resolve to **≥1 file** (else error). | — |
| `package_files` | optional | array of *entry* objects | SV **packages** (typedefs / functions / params) + interface stubs for library primitives (`FF`/`AN2`). Compiled **first** for name resolution; **not** translated, **not** in coverage. | `[]` |
| `param_files` | optional | array of *entry* objects | parameter / config (`.svh`) files. **Identical** behaviour to `package_files` — the two names are only for the author's organization. | `[]` |
| `incdirs` | optional | array of strings | `` `include `` search paths (for `.svh` headers), resolved vs the manifest. | `[]` |
| `defines` | optional | object `{NAME: VAL}` | `` +define+ `` preprocessor macros — drive `` `ifdef ``/`` `ifndef `` build variants and macro widths (`` `WIDTH ``). Values stringified. | `{}` |
| `params` | optional | object `{NAME: int}` | concrete **parameter overrides**, applied before translation. Values coerced to `int`. | `{}` |
| `top` | optional | string | the **top module** to translate (flattened/elaborated from here). If omitted: flat mode translates **every** module in `sources`; modular mode picks the single elaboration root. | — |
| `style` | optional | `"v1"` \| `"v2"` | boolean encoding for 1-bit signals (see `docs/guide/SV2ASP_USAGE.md` → *Boolean encoding*). | `"v1"` |
| `horizon` | optional | int | **not** how you set the BMC depth — your hand-written *scenario* sets `#const k` (see the note below). This is only the **reset-snapshot** settle depth (how many cycles to unroll the reset sequence). Ignored by the normal translate → scenario → clingo flow. | `8` |
| `primary_clock` | optional | string | the design's **free-running master clock** in a multi-clock design — sets the `% MASTER clock` annotation and the `--scenario-stub`'s `time(<master>,0..k)`. A declared name that isn't a free clock falls back loudly (a `% NOTE`). Single-clock designs don't need it. | inferred (alphabetically-first clock) |
| `stubs` | optional | object `{module: path}` | **project-local functional stubs.** Maps a module NAME to a hand-written `.lp` file (path relative to the manifest) that models the module's behaviour. An instance of a stubbed module is NOT translated (its body is skipped); instead the stub's rules are emitted with the instance's ports bridged in. Use for datapath blocks that are the *means*, not the unit under test (e.g. a multiplier stubbed to `@mul`). Only the named modules are stubbed — nothing is auto-subbed. See below. | `{}` |
| `blackbox` | optional | list of module names, or object `{module: {"outputs": [...]}}` | **black boxes.** A module the tool must NOT translate and whose outputs it must treat as ANY value: every output is declared unconstrained at every instant (the assigned-`x` mechanism, `dontcare_at`), so the power-on companion supplies one answer set per value and a property over the box's consumers must hold for every value the box could produce. With a definition in scope the port list comes from it and `{}` suffices; with NO definition in scope (a memory wrapper whose macros are not in the tree) list the OUTPUT ports, the widths come from the parent's connections. A scenario pins an output with `val(<inst>(<port>), V, T)`; an output wider than 20 bits gets guidance instead of a choice and must be pinned. A declared box that never binds is a loud problem, like a stub. See `docs/guide/FUNCTIONAL_STUBS.md` §"Black boxes". |
| `allow_latches` | optional | bool | permit level-sensitive **latch cells** (`LATA`/`LATB`) and translate inferred latches with latch semantics; OFF by default (a latch is usually an accident — every form is a loud problem without this). Never silently enables latch *inference*. | `false` |
| `x_init` | optional | bool | emit the **exact-X power-on companion** (`__xinit.lp`: one domain choice per unreset 4-state register — `docs/guide/SV2ASP_USAGE.md` §3, `notes/design/X_SEMANTICS.md`). Set `false` to record "this tree is fully reset" with the design; `--no-x-init` remains the per-run override. | `true` |
| `clock_hierarchy` | optional | object `{clk: {base, div}}` | **clock frequency derivation.** For blocks that receive pre-divided clocks as ports (no ICG inside), declares the frequency relationship so the translator emits derivation rules and scenarios need only `time(0..k)`. See below. | `{}` |

Only **`sources`** is compulsory. Everything else is optional with the defaults above.

> **Functional stubs (`stubs`).** Each stub `.lp` is written in terms of the module's port names
> using `@INST@` as a placeholder for the instance name. The translator bridges ports, substitutes
> `@INST@`, and registers `@func` ops into the `#script` block automatically. Works in both flat
> and modular mode. **Full documentation: `docs/guide/FUNCTIONAL_STUBS.md`.**

> **Clock frequency hierarchy (`clock_hierarchy`).** Blocks that receive pre-divided clocks as
> ports (no ICG primitive inside) need this to express the frequency relationship. The translator
> emits derivation rules so the scenario only needs `time(0..k)` — the clock name disappears from
> the scenario. Format:
> ```jsonc
> "clock_hierarchy": {
>   "uncondL6clk": { "base": "time",        "div": 1 },  // fastest clock = global rate
>   "uncondL3clk": { "base": "uncondL6clk", "div": 2 }   // ÷2 of its base
> }
> ```
> `"base": "time"` means this clock IS the global rate → `time(clk, T) :- time(T).`  
> `"div": N` means every N-th parent tick → `time(clk, T) :- time(base, T), T \ N == 0.`  
> Hold rules and `no_tick` use `time(T)` as the global base (instead of `gtime(T)`).  
> Absent (default `{}`) → byte-identical output to today (no change to existing scenarios).

> **Note — `top` is optional but usually wanted.** Without `top`, FLAT mode translates *every* module
> in `sources` (each to its own `.lp`). With a clear hierarchy you almost always want `top` set so the
> tool elaborates from one root.

> **Note — the manifest configures the *translation*; the *scenario* (hand-written, separately) owns the
> run.** A check is **three layers** composed at solve time: the **design** `.lp` (machine-generated by
> this translation) + a **scenario** `.lp` (you write it by hand, *after* translating) + an optional
> **property** `.lp` (also hand-written). The design is **horizon-independent** — it refers to a symbolic
> `k`; your scenario supplies the actual run length (`#const k = N.`), the input stimulus, and the initial
> state, then you run `clingo design.lp scenario.lp [property.lp]`. So **`#const k` lives in the scenario,
> not the manifest** — the `horizon` field above is only the reset-snapshot settle depth, unused by the
> normal flow. See `docs/guide/SV2ASP_USAGE.md` *§3 Write a scenario*.

---

## Entry objects (`sources`, `package_files`, `param_files`)

Each element of those arrays is an object describing a file or a folder:

| Field | Required | JSON type | Meaning | Default |
|---|---|---|---|---|
| **`path`** | **REQUIRED** | string | file or folder path (relative to the manifest, or absolute). | — |
| **`type`** | **REQUIRED** | `"file"` \| `"folder"` | whether `path` is a single file or a directory to expand. | — |
| `recursive` | optional *(folder only)* | bool | recurse into subdirectories. | `true` |
| `ext` | optional *(folder only)* | array of strings | file extensions to include when expanding a folder. | `[".sv", ".v"]` |

- A `"file"` entry must exist (else `FileNotFoundError`); a `"folder"` entry must be a directory.
- Folder expansion is **sorted** (deterministic) and **de-duplicated** by real path across all entries.
- `recursive`/`ext` are ignored for `"file"` entries.

---

## CLI overrides

Explicit CLI flags **merge over / override** the manifest, so one manifest can be re-pointed without
editing it:

| CLI flag | Effect vs manifest |
|---|---|
| `-p NAME=VAL` | overrides / adds to `params` |
| `-D NAME=VAL` | adds to `defines` |
| `-I DIR` | appends to `incdirs` |
| `--top NAME` | overrides `top` |
| `--style {v1,v2}` | overrides `style` |
| `-k, --horizon N` | overrides `horizon` |
| `--primary-clock CLK` | overrides `primary_clock` |
| positional `file.sv …` | appended to the resolved `sources` |

Inspect the fully-resolved parameter set (manifest + headers + CLI) with `--dump-params` (resolve and
exit, prints JSON).

---

## Complete annotated example

```jsonc
{
  // dependencies: compiled first for name resolution, NOT translated, NOT in coverage
  "package_files": [
    { "path": "rtl/types_pkg.sv", "type": "file" },
    { "path": "stubs/cells.sv",   "type": "file" }     // interface stubs for FF/AN2/... primitives
  ],
  "param_files": [
    { "path": "rtl/cfg.svh", "type": "file" }          // identical handling to package_files
  ],

  // the design RTL to translate (REQUIRED; must resolve to >=1 file)
  "sources": [
    { "path": "rtl/core", "type": "folder", "recursive": true, "ext": [".sv"] },
    { "path": "rtl/top.sv", "type": "file" }
  ],

  "incdirs": [ "rtl/include" ],          // `include search paths
  "defines": { "SYNTH": "1", "WIDTH": "8" }, // +define+ macros (ifdef/ifndef + `WIDTH)
  "params":  { "DEPTH_LEN": 2 },         // concrete parameter overrides
  "top":     "my_top",                   // elaboration root
  "style":   "v1",                       // boolean encoding
  "horizon": 8,                          // default k (snapshot mode)
  "primary_clock": "clk_a"               // free-running master clock (multi-clock designs)
}
```

Minimal valid manifest (only the compulsory field):

```json
{ "sources": [ { "path": "design.sv", "type": "file" } ] }
```

See `examples/*/sources.json` for many real manifests (e.g. `examples/rtl2asp/deep_hier_demo/sources.json`
with `package_files` + multiple `sources`, and `examples/rtl2asp/multi_clock_demo/sources.json` minimal form).
