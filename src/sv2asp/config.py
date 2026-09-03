"""Tool configuration: external tool paths and site plugins, from a TOML file.

Nothing site-specific is baked into the translator. Anything that depends on the
machine (where clingo/python/lean live) or on the design environment (extra ``@func``
definitions, vendor primitive-cell registries) comes from a configuration file:

    [tools]
    python  = "/opt/conda/envs/logiclab/bin/python"
    clingo  = "/opt/conda/envs/logiclab/bin/clingo"
    lean    = "/usr/local/bin/lean"          # reserved for the completion->Lean route
    lake    = "/usr/local/bin/lake"
    mathlib = "/path/to/mathlib"             # reserved

    [funcs]
    plugins = ["sv2asp_local/my_funcs.py"]   # paths relative to this config file

    [primitives]
    plugins = ["sv2asp_local/my_prims.py"]

Discovery order (first hit wins):
  1. ``--config PATH`` on the command line
  2. ``$SV2ASP_CONFIG``
  3. ``./sv2asp.toml`` (the current working directory)
  4. ``~/.config/sv2asp/config.toml``

Tool-path resolution order (first hit wins): explicit function argument, the
conventional environment variable (``CLINGO_BIN``, ``SV2ASP_PYTHON``, ``LEAN_BIN``,
``LAKE_BIN``), the config file's ``[tools]`` entry, then ``$PATH`` lookup.

Plugin files are plain Python exec'd with ``PrimSpec`` in scope; they may define:
  * ``FUNCS: dict[str, str]``       -- @func name -> the ``def`` source line(s)
  * ``FUNC_LEGEND: dict[str, str]`` -- @func name -> one legend line
  * ``PRIMS: dict[str, PrimSpec]``  -- cell/module name -> primitive spec

This is how design-specific material (a vendor ROM's contents, company cell names)
stays out of the tool itself: it travels with the design, referenced by the design
tree's own ``sv2asp.toml``.
"""

from __future__ import annotations

import os
import pathlib
import shutil
import tomllib

_APPLIED: set[tuple[str, pathlib.Path]] = set()   # (section, plugin path) already registered

_ENV_FOR_TOOL = {
    "python": "SV2ASP_PYTHON",
    "clingo": "CLINGO_BIN",
    "lean": "LEAN_BIN",
    "lake": "LAKE_BIN",
    "mathlib": "MATHLIB_DIR",
}


class Config:
    """A loaded configuration (possibly empty -- every accessor has a sane fallback)."""

    def __init__(self, data: dict, base: pathlib.Path | None):
        self._data = data
        self._base = base  # directory of the config file; plugin paths resolve against it

    @property
    def path(self) -> pathlib.Path | None:
        return self._base

    # -- tool paths -------------------------------------------------------------------
    def tool(self, name: str, explicit: str | None = None) -> str | None:
        """Resolve a tool path: explicit arg > env var > [tools] entry > $PATH."""
        if explicit:
            return explicit
        env = _ENV_FOR_TOOL.get(name)
        if env and os.environ.get(env):
            return os.environ[env]
        entry = self._data.get("tools", {}).get(name)
        if entry:
            p = pathlib.Path(entry).expanduser()
            if not p.is_absolute() and self._base is not None:
                p = self._base / p
            return str(p)
        return shutil.which(name)

    # -- plugin file lists ------------------------------------------------------------
    def _plugin_paths(self, section: str) -> list[pathlib.Path]:
        out = []
        for item in self._data.get(section, {}).get("plugins", []):
            p = pathlib.Path(item).expanduser()
            if not p.is_absolute() and self._base is not None:
                p = self._base / p
            if not p.is_file():
                raise FileNotFoundError(f"config [{section}] plugin not found: {p}")
            out.append(p)
        return out

    def func_plugins(self) -> list[pathlib.Path]:
        return self._plugin_paths("funcs")

    def prim_plugins(self) -> list[pathlib.Path]:
        return self._plugin_paths("primitives")

    def apply_plugins(self) -> None:
        """Register every configured plugin with the func and primitive registries.

        Idempotent per (section, plugin file): repeated CLI invocations in one process
        (test suites, the example-regeneration script) re-apply the same config without
        tripping the may-not-override guard."""
        from .emit import lib as _lib
        from . import primitives as _prims
        for p in self.func_plugins():
            key = ("funcs", p.resolve())
            if key in _APPLIED:
                continue
            ns = _exec_plugin(p)
            _require_contribution(p, ns, "FUNCS", "funcs")
            _lib.register_funcs(ns.get("FUNCS", {}), ns.get("FUNC_LEGEND", {}), origin=str(p))
            _APPLIED.add(key)
        for p in self.prim_plugins():
            key = ("prims", p.resolve())
            if key in _APPLIED:
                continue
            ns = _exec_plugin(p)
            _require_contribution(p, ns, "PRIMS", "primitives")
            _prims.register_prims(ns.get("PRIMS", {}), origin=str(p))
            _APPLIED.add(key)


def _require_contribution(path: pathlib.Path, ns: dict, var: str, section: str) -> None:
    """A declared plugin that registers NOTHING is a configuration error, not a no-op.

    `apply_plugins` reads the plugin's namespace with `ns.get(var, {})`, so a plugin whose
    dict is misnamed (`FUNC` for `FUNCS`), empty, or listed under the wrong section
    contributes nothing AND says nothing. The design then translates as if the plugin were
    absent: a vendor ROM `@func` or primitive cell you believe is available simply is not, and
    the first sign is a failure much later — or, worse, a cell falling through to a different
    lowering path.

    Same "declared but never consumed" question as the stub / override / define checks; a
    missing plugin FILE already raises here, so an empty one does too, for consistency."""
    got = ns.get(var)
    if isinstance(got, dict) and got:
        return
    names = sorted(k for k, v in ns.items()
                   if isinstance(v, dict) and v and not k.startswith("__"))
    hint = f" (it defines: {', '.join(names)})" if names else " (it defines no non-empty dict)"
    raise ValueError(
        f"config [{section}] plugin {path} registered NOTHING: expected a non-empty "
        f"`{var}` dict{hint}. A plugin that contributes nothing is silently equivalent to "
        f"not declaring it, so it is refused rather than ignored.")


def _exec_plugin(path: pathlib.Path) -> dict:
    from .primitives import PrimSpec
    from .ir.expr import BinOp, Cond, Const, FuncCall, UnOp
    ns: dict = {"PrimSpec": PrimSpec, "FuncCall": FuncCall, "BinOp": BinOp,
                "UnOp": UnOp, "Cond": Cond, "Const": Const, "__file__": str(path)}
    exec(compile(path.read_text(), str(path), "exec"), ns)
    return ns


def load(explicit: str | None = None) -> Config:
    """Load the configuration by the documented discovery order. Missing file -> empty config."""
    candidates: list[pathlib.Path] = []
    if explicit:
        p = pathlib.Path(explicit).expanduser()
        if not p.is_file():
            raise FileNotFoundError(f"--config file not found: {p}")
        candidates.append(p)
    elif os.environ.get("SV2ASP_CONFIG"):
        candidates.append(pathlib.Path(os.environ["SV2ASP_CONFIG"]).expanduser())
    else:
        candidates.append(pathlib.Path.cwd() / "sv2asp.toml")
        candidates.append(pathlib.Path.home() / ".config" / "sv2asp" / "config.toml")
    for c in candidates:
        if c.is_file():
            with open(c, "rb") as fh:
                return Config(tomllib.load(fh), c.parent.resolve())
    return Config({}, None)
