"""Project sources manifest: a JSON file listing source paths (file or folder).

Example ``sources.json``::

    {
      "package_files": [ {"path": "rtl/types_pkg.sv", "type": "file"} ],
      "param_files":   [ {"path": "rtl/cfg.svh",      "type": "file"} ],
      "sources":       [ {"path": "rtl/core", "type": "folder", "recursive": true, "ext": [".sv"]} ],
      "incdirs": [ "rtl/include" ],          // `include search paths (resolved vs the manifest)
      "defines": {"SYNTH": "1", "WIDTH": "8"}, // +define+ macros driving `ifdef/`ifndef + `WIDTH
      "params":  {"DEPTH_LEN": 2},
      "top":     "syncFIFO_v2",
      "style":   "v1",
      "horizon": 8
    }

``package_files`` (SV packages: typedefs/functions/params) and ``param_files``
(parameter/config files) are **definition/dependency** inputs: compiled *first* so the
design's names resolve, but NOT translated as design and not in the design coverage. Both
are treated identically; the two fields are for the author's organization. ``sources`` are
the design RTL to translate. Folder entries expand to all matching files (sorted, for
determinism).

``incdirs`` (relative to the manifest) feed `` `include `` resolution, and ``defines`` are
preprocessor macros: together they drive **conditional compilation** (`` `ifdef ``/`` `ifndef ``)
so one manifest pins a specific build variant. The manifest may also carry default
params/top/style/horizon. Explicit CLI flags override / merge over the manifest (``-D NAME=VAL``
adds to ``defines``, ``-I DIR`` appends to ``incdirs``, ``-p NAME=VAL`` overrides ``params``).
"""

from __future__ import annotations

import json
import os
from dataclasses import dataclass, field

_DEFAULT_EXTS = (".sv", ".v")


@dataclass(frozen=True)
class SourcesConfig:
    files: tuple[str, ...]
    package_files: tuple[str, ...] = ()
    param_files: tuple[str, ...] = ()
    incdirs: tuple[str, ...] = ()           # `include search paths (.svh headers)
    defines: dict[str, str] = field(default_factory=dict)  # +define+ macros
    params: dict[str, int] = field(default_factory=dict)
    top: str | None = None
    style: str | None = None
    horizon: int | None = None
    primary_clock: str | None = None        # the design's free-running master clock (multi-clock master-tick)
    stubs: dict[str, str] = field(default_factory=dict)  # module name -> functional-stub .lp TEXT
    #: permit level-sensitive latch cells (LATA/LATB). OFF by default -- a latch is a
    #: combinational path while enabled, not a register, and is usually instantiated by
    #: mistake. Never enables latch INFERENCE, which stays refused outright.
    allow_latches: bool = False
    #: exact-X power-on companion (__xinit.lp) for unreset 4-state registers. ON by default;
    #: set false to record "this design tree is fully reset" WITH the design rather than on
    #: every command line. The CLI --no-x-init stays as a per-run override (either side may
    #: disable; neither can force it on when the other said off).
    x_init: bool = True
    clock_hierarchy: dict[str, dict] = field(default_factory=dict)
    # Clock frequency hierarchy for designs that receive pre-derived clocks as ports (no ICG inside).
    # Format: { "clk_name": {"base": "parent_clk_or_time", "div": N} }
    # "base": "time"  means this clock runs at the global rate  -> time(clk, T) :- time(T).
    # "base": "parent", "div": 2  ->  time(clk, T) :- time(parent, T), T \ 2 == 0.
    # Emits CLOCK DERIVATION rules and changes hold/no_tick base from gtime(T) to time(T).
    # Absent (default {}) -> byte-identical output to today (backward compatible).

    @property
    def defn_files(self) -> tuple[str, ...]:
        """Definition/dependency files (packages + params), compiled but not translated."""
        return self.package_files + self.param_files


def _expand(entry: dict, base: str) -> list[str]:
    if "path" not in entry or "type" not in entry:
        raise ValueError(f"source entry needs 'path' and 'type': {entry}")
    path = entry["path"]
    if not os.path.isabs(path):
        path = os.path.normpath(os.path.join(base, path))
    typ = entry["type"]
    if typ == "file":
        if not os.path.isfile(path):
            raise FileNotFoundError(f"source file not found: {path}")
        return [path]
    if typ == "folder":
        if not os.path.isdir(path):
            raise NotADirectoryError(f"source folder not found: {path}")
        exts = tuple(entry.get("ext", _DEFAULT_EXTS))
        recursive = entry.get("recursive", True)
        found: list[str] = []
        walker = os.walk(path) if recursive else [(path, [], os.listdir(path))]
        for root, _dirs, names in walker:
            for n in names:
                if n.endswith(exts):
                    found.append(os.path.join(root, n))
        return sorted(found)  # deterministic order
    raise ValueError(f"source 'type' must be 'file' or 'folder', got {typ!r}")


def _resolve(entries: list[dict], base: str) -> list[str]:
    out: list[str] = []
    seen: set[str] = set()
    for entry in entries:
        for fp in _expand(entry, base):
            rp = os.path.realpath(fp)
            if rp not in seen:
                seen.add(rp)
                out.append(fp)
    return out


#: Every key `load` reads. A manifest key outside this set cannot have any effect, so it is
#: refused rather than ignored -- see `_check_manifest_keys`.
MANIFEST_KEYS = frozenset({
    "sources", "package_files", "param_files", "incdirs", "defines", "params",
    "top", "style", "horizon", "primary_clock", "stubs", "allow_latches", "x_init", "clock_hierarchy",
})


def _check_manifest_keys(path: str, data: dict) -> None:
    """A `sources.json` key this loader does not consume is a LOUD error, not a no-op.

    Every key is read with `data.get(...)`, so a misspelt one -- `hrizon`, `styl`, `incdir` --
    simply never fires and the translation proceeds on DEFAULTS. Nothing notices: the design
    still translates, coverage still reports OK. The user believes they set a horizon, a style,
    an include path; they set nothing.

    Same "declared but never consumed" question as the stub / override / define / plugin checks
    (proven in Intake.lean), asked of the manifest itself. Reported with a nearest-match hint,
    because a typo is the overwhelmingly likely cause.

    EXEMPT: keys beginning `//`, the conventional JSON comment. They are inert on purpose."""
    # `//`-prefixed keys are the conventional JSON comment (JSON has no comment syntax), so
    # they are DELIBERATELY inert and must not be mistaken for typos. The real divider's
    # manifest uses several (`//stubs`, `//clock`, …) and this check rejected it until the
    # exemption was added -- a reminder that synthetic manifests do not exercise real ones.
    unknown = sorted(k for k in set(data) - MANIFEST_KEYS if not k.startswith("//"))
    if not unknown:
        return
    import difflib
    hints = []
    for k in unknown:
        near = difflib.get_close_matches(k, sorted(MANIFEST_KEYS), n=1, cutoff=0.6)
        hints.append(f"{k!r}" + (f" (did you mean {near[0]!r}?)" if near else ""))
    raise ValueError(
        f"{path}: unknown manifest key(s): {', '.join(hints)}. Known keys: "
        f"{', '.join(sorted(MANIFEST_KEYS))}. An unread key has NO effect -- the translation "
        f"would silently use defaults -- so it is refused rather than ignored.")


def load(path: str) -> SourcesConfig:
    with open(path) as f:
        data = json.load(f)
    if "sources" not in data:
        raise ValueError(f"{path}: missing required 'sources' list")
    _check_manifest_keys(path, data)
    base = os.path.dirname(os.path.abspath(path))
    files = _resolve(data["sources"], base)
    if not files:
        raise ValueError(f"{path}: 'sources' resolved to zero files")
    incdirs = [d if os.path.isabs(d) else os.path.normpath(os.path.join(base, d))
               for d in data.get("incdirs", [])]
    # functional stubs: {module_name: stub.lp path} -> read each file's TEXT (module -> text).
    stubs: dict[str, str] = {}
    for mod, sp in data.get("stubs", {}).items():
        spath = sp if os.path.isabs(sp) else os.path.normpath(os.path.join(base, sp))
        if not os.path.isfile(spath):
            raise FileNotFoundError(f"stub file not found for module {mod!r}: {spath}")
        with open(spath) as sf:
            stubs[str(mod)] = sf.read()
    return SourcesConfig(
        files=tuple(files),
        package_files=tuple(_resolve(data.get("package_files", []), base)),
        param_files=tuple(_resolve(data.get("param_files", []), base)),
        incdirs=tuple(incdirs),
        defines={str(k): str(v) for k, v in data.get("defines", {}).items()},
        params={str(k): int(v) for k, v in data.get("params", {}).items()},
        top=data.get("top"),
        style=data.get("style"),
        horizon=data.get("horizon"),
        primary_clock=data.get("primary_clock"),
        stubs=stubs,
        allow_latches=bool(data.get("allow_latches", False)),
        x_init=bool(data.get("x_init", True)),
        clock_hierarchy={str(k): dict(v) for k, v in data.get("clock_hierarchy", {}).items()},
    )
