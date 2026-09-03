#!/bin/sh
# Set up an environment for sv2asp2, on a machine that may have nothing.
#
# This script assumes NOTHING about your setup: no conda, no named environment, no
# particular Python on PATH. It finds what is already there, installs what is missing
# into a self-contained `.venv` beside this file, tells you the one or two things it
# cannot install for you, and writes `sv2asp.toml` so the tool finds everything
# afterwards.
#
#   ./setup.sh                 find, install into ./.venv, configure, verify
#   ./setup.sh --system-too    also install the system tools (clingo, verilator) with
#                              your platform's package manager
#   ./setup.sh --check         change nothing; just report (same as `doctor`)
#
# If you already have the tools somewhere unusual, that is fine: this script finds
# them, or you point `sv2asp.toml`'s [tools] section at them and everything else works.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
cd "$HERE"

SYSTEM_TOO=no
CHECK_ONLY=no
for arg in "$@"; do
  case "$arg" in
    --system-too) SYSTEM_TOO=yes ;;
    --check)      CHECK_ONLY=yes ;;
    -h|--help)    sed -n '2,18p' "$0" | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "unknown option: $arg (try --help)"; exit 2 ;;
  esac
done

say() { printf '%s\n' "$*"; }
have() { command -v "$1" >/dev/null 2>&1; }

# ---------------------------------------------------------------- 1. a Python >= 3.11
PY=""
for c in python3.14 python3.13 python3.12 python3.11 python3 python; do
  if have "$c" && "$c" -c 'import sys; sys.exit(0 if sys.version_info[:2] >= (3, 11) else 1)' 2>/dev/null; then
    PY=$(command -v "$c"); break
  fi
done
if [ -z "$PY" ]; then
  say "No Python 3.11 or newer was found."
  case "$(uname -s)" in
    Darwin) say "  install one with:  brew install python@3.12" ;;
    Linux)  say "  install one with:  apt install python3.12 python3.12-venv" ;;
    *)      say "  install Python 3.11+ from https://www.python.org/downloads/" ;;
  esac
  say "  then re-run this script."
  exit 1
fi
say "python           $("$PY" -c 'import sys; print(sys.version.split()[0])')   ($PY)"

# ---------------------------------------------------------------- 2. the environment
if [ "$CHECK_ONLY" = no ]; then
  if [ ! -d .venv ]; then
    say "creating .venv (self-contained; nothing outside this folder is touched)"
    "$PY" -m venv .venv
  fi
  VPY="$HERE/.venv/bin/python"
  say "installing the tool and its requirements into .venv"
  "$VPY" -m pip install --quiet --upgrade pip
  "$VPY" -m pip install --quiet -e .        # the tool, with the dependencies pyproject names
else
  VPY="$PY"
fi

# ---------------------------------------------------------------- 3. the system tools
# clingo is the solver every certificate runs on, and it MUST be the executable: the pip
# module cannot stand in for it, because the module has no embedded-Python support and
# every solve carries a `#script (python)` block. A SIMULATOR arbitrates the round trip:
# verilator (preferred) or iverilog -- either will do, so only their joint absence is a gap.
MISSING=""
have clingo   || MISSING="$MISSING clingo"
have verilator || have iverilog || MISSING="$MISSING verilator"
if [ -n "$MISSING" ]; then
  case "$(uname -s)" in
    Darwin) PKG="brew install"; NAMES=$(echo "$MISSING" | sed 's/iverilog/icarus-verilog/') ;;
    Linux)  PKG="sudo apt install"; NAMES=$(echo "$MISSING" | sed 's/clingo/gringo/') ;;
    *)      PKG="install"; NAMES="$MISSING" ;;
  esac
  if [ "$SYSTEM_TOO" = yes ] && [ "$CHECK_ONLY" = no ]; then
    say "installing:$NAMES"
    # shellcheck disable=SC2086
    $PKG $NAMES
  else
    say ""
    say "MISSING system tool(s):$MISSING"
    say "  install with:  $PKG$NAMES"
    say "  or re-run:     ./setup.sh --system-too"
    say "  (already installed somewhere unusual? put the paths in sv2asp.toml's [tools])"
  fi
fi

# ---------------------------------------------------------------- 4. the configuration
if [ "$CHECK_ONLY" = no ] && [ ! -f sv2asp.toml ]; then
  CL=$(command -v clingo || true)
  if [ -n "$CL" ]; then
    {
      say "# written by setup.sh -- the tool resolves: argument, then \$CLINGO_BIN etc,"
      say "# then this file, then PATH. Edit freely; delete it to fall back to PATH."
      say "[tools]"
      say "clingo = \"$CL\""
      say "python = \"$HERE/.venv/bin/python\""
    } > sv2asp.toml
    say "wrote sv2asp.toml pointing at what was found"
  fi
fi

# ---------------------------------------------------------------- 5. verify
say ""
"$VPY" -m sv2asp.aspfirst2 doctor || {
  say ""
  say "Fix what doctor listed above and re-run ./setup.sh --check"
  exit 1
}
say ""
say "Ready. Work from YOUR block's folder beside this one, not in here:"
say ""
say "    cd ../myBlock"
say "    $HERE/.venv/bin/python -m sv2asp.aspfirst2 doctor"
say ""
say "  or, once per session:  . $HERE/.venv/bin/activate   then   sv2asp2 <verb>"
say ""
say "Nothing is written into this tools folder -- every artifact of a block belongs to"
say "the block's own folder. Start from its SPECIFICATION.md; the book explains the rest:"
say "  $HERE/docs/spec2rtl2/SUITE.md   (Part C)"
