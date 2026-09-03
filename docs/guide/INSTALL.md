# Installing sv2asp

The only hard requirement is: **a Python ≥ 3.11 interpreter that can `import pyslang`**
(pinned `>=10,<11` — the frontend is validated against that API). Everything below is
one of several ways to satisfy that, depending on what your site allows — pick the one
that fits, you don't need the others too. clingo (with embedded Python) is only needed
at *solve* time, not translation time, and most sites already have a wrapper/module for
it — this doc never assumes a specific one.

**None of these commands are prescriptive about paths.** Every variable below
(`$PY`, `$PREFIX`, an index URL) is something *you* set for your site — nothing here
hardcodes a Python location, a package index, or a tools prefix.

## 1. Install the engine

You receive the tool as an installable package from the maintainer, plus a workspace
bundle you unpack into your own design repository (see the suite book's Part C for the
two-artifact picture). There is no source checkout: the tool is installed into a Python
environment and driven by `python -m sv2asp.aspfirst2 <verb>` from wherever your blocks
live.

```sh
pip install /path/to/the/engine-*.whl      # brings pyslang, clingo, lark, PyYAML
```

The rest of this document is about satisfying the one hard requirement underneath —
an interpreter that can `import pyslang` — at a site where the simple path is blocked.

## 2. Get `pyslang` on some interpreter — pick ONE option

### Option A — an interpreter that already has it (try this first)

Many sites provide a shared/pre-approved Python with common packages already vetted and
installed. If `pyslang` is already there, there is nothing to install — no network, no
venv, no installer privileges needed:

```sh
PY=/path/to/that/python3        # <- set this: whatever interpreter already has pyslang
$PY -c "import pyslang; print(pyslang.__file__)"      # sanity check
```

If that prints a path, skip to step 3. At a site with a locked-down network or
restricted install permissions this is usually the only option that works.

### Option B — pip install, PyPI reachable

```sh
PY=python3.11                    # or a full path
PREFIX=/tools/sv2asp/2.0.0       # any directory you control
$PY -m venv $PREFIX
$PREFIX/bin/pip install .
PY=$PREFIX/bin/python            # use this interpreter from here on
```

### Option C — pip install, PyPI blocked (a site package index instead)

Most locked-down sites run an internal package mirror. Point pip at it the way pip
already supports — this repo doesn't need to know your mirror's URL:

```sh
export PIP_INDEX_URL=https://<your internal mirror>/simple
export PIP_TRUSTED_HOST=<your internal mirror host>   # only if it uses an internal CA
PY=python3.11
PREFIX=/tools/sv2asp/2.0.0
$PY -m venv $PREFIX
$PREFIX/bin/pip install .
PY=$PREFIX/bin/python
```

Ask your tools/CAD team for the mirror URL — it's site-specific, so it isn't and
shouldn't be in this repository. (`pip config`, or a `pip.conf` file, work the same way
if you'd rather not export env vars.)

**No GitHub from the install host at all?** Every release also ships a pure-Python
wheel — transfer `sv2asp-2.0.0-py3-none-any.whl` by any means and
`pip install "pyslang>=10,<11" sv2asp-2.0.0-py3-none-any.whl` (Option B/C's install line
becomes this one).

## 3. Smoke test

```sh
PYTHONPATH=$PWD/src $PY -m sv2asp.cli --help
```

(If you did Option B/C, `$PREFIX/bin/sv2asp --help` also works — pip installed the
console script. Option A has none yet; step 6 makes one.)

## 4. Full suite

```sh
$PY -m pip install pytest      # skip if already present (e.g. Option A)
PYTHONPATH=$PWD/src $PY -m pytest tests/ -q      # expected: 319 passed
```

## 5. End-to-end with your site's clingo

```sh
PYTHONPATH=$PWD/src $PY -m sv2asp.cli \
    --sources examples/rtl2asp/plugin_prim_demo/sources.json -o /tmp/m.lp --strict-coverage
clingo /tmp/m.lp examples/rtl2asp/plugin_prim_demo/scenario.lp
```

Expected: `coverage: ... -> OK`, then an answer set containing `gq(1,511)`. This step
proves your `clingo` has **embedded Python** (the `.lp` carries a `#script(python)`
block) — a clingo built without it fails here and nowhere else.

## 6. Expose one command, for everyone

**Option B/C:** pip already gave you `$PREFIX/bin/sv2asp` — point a modulefile or a PATH
symlink at it and you're done.

**Option A:** write a two-line wrapper instead — the whole mechanism, no packaging tool
involved:

```sh
mkdir -p $PREFIX/bin
cat > $PREFIX/bin/sv2asp <<EOF
#!/bin/sh
export PYTHONPATH=$PWD/src
exec $PY -m sv2asp.cli "\$@"
EOF
chmod +x $PREFIX/bin/sv2asp
```

(the clone must stay in place — the wrapper's `PYTHONPATH` points into it)

Either way, expose `$PREFIX/bin` with a modulefile:

```tcl
#%Module1.0
prepend-path PATH /tools/sv2asp/2.0.0/bin
```

Users then run, with nothing else installed:

```sh
sv2asp --sources sources.json -o out/ --strict-coverage
clingo out/*.lp my_scenario.lp
```

## Upgrades

New version → new `$PREFIX` (or clone) + module default bump. Versions coexist;
rollback is a module switch.

## Site configuration for translation itself

Machine-wide tool paths and design-specific plugins (`[funcs]`/`[primitives]`) are a
*separate* mechanism from installing the package — see `docs/guide/SV2ASP_USAGE.md` §Tool
configuration (`sv2asp.toml`). They govern what the tool does once it's running, not how
it got onto disk. At sites where wrappers already put the right `clingo` on `PATH`, no
`[tools]` section is needed there either.
