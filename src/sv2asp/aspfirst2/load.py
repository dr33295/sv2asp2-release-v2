"""Read an authored ASP-first design (`.lp`) into a `model.Design`, enforcing the AUTHORING SUBSET
as it goes: every statement is either a vocabulary FACT or a guarded combinational RULE in the
restricted grammar of `docs/guide/ASP_FIRST_DESIGN.md`. Anything else -- a `T+1` head, a `not`,
a choice, a directive, a `T=0` fact -- is a `SubsetError` naming the line. This is the gate that
keeps hold/set semantics in the library and out of the author's hands.

The parser is deliberately small (clingo's own reader validates the syntax again when the lint
and the solve run); what it adds is the SUBSET decision and line provenance."""
from __future__ import annotations

import pathlib
import re
from .lanes import Index, axes_of, flat_index, member, members, rolled

from .model import CELLS, FUNCS, OPS, Design, Inst, Net, Port, Rule, Step

FACT_PREDS = {"module": 1, "port": 3, "net": 2, "enum_member": 3, "param": 2, "def": 2,
              "inst": 2, "pin": 3, "iparam": 3, "abstract": 1, "data": 1, "mparam": 3,
              "net_lane": 3, "port_lane": 4, "def_lane": 3, "inst_lane": 3, "arch_mem": 3, "arch_reg": 2,
              "opaque_datapath": 0}
def sv_name(term):
    """The IDENTIFIER a name term denotes.

    ASP reads a leading capital as a VARIABLE, so a block whose SystemVerilog name is
    `TopModule` -- fixed by an external contract, and the conventional name for a
    device-under-test in several harness families -- cannot be written bare. Quoting is the
    correct and only ASP escape, and it parsed; the quoted TUPLE then travelled all the way
    into the printed RTL as `module ('str', 'TopModule')`, and into a derived filename as
    quotes inside the path. Unwrapped here, once, at the single place the name is taken.
    """
    return term[1] if isinstance(term, tuple) and len(term) == 2 and term[0] == "str" else term


def asp_name(name: str) -> str:
    """The same identifier written back as ASP: quoted when it is not a bare symbol, so a
    serialized design round-trips through the parser that produced it."""
    import re as _re
    return name if _re.fullmatch(r"[a-z_][A-Za-z0-9_]*", str(name)) else f'"{name}"'


FORBIDDEN_TOKENS = ("#show", "#const", "#program", "#include", "#external", "#minimize",
                    "#maximize", "#script", "#defined", "#heuristic")


class SubsetError(Exception):
    """A statement outside the authoring subset. `.line` is 1-based."""

    def __init__(self, line: int, msg: str, text: str = ""):
        super().__init__(f"line {line}: {msg}" + (f"\n    {text}" if text else ""))
        self.line, self.msg, self.text = line, msg, text


# ---------------------------------------------------------------------------------------------
# statements
# ---------------------------------------------------------------------------------------------

def statements(text: str):
    """Yield (line, statement_text) for every `.`-terminated statement, comments stripped.
    Statements may span lines; the line reported is the one the statement starts on."""
    buf, depth, in_str, start = [], 0, False, None
    i, line = 0, 1
    while i < len(text):
        ch = text[i]
        if in_str:
            buf.append(ch)
            if ch == "\\" and i + 1 < len(text):
                buf.append(text[i + 1])
                i += 1
            elif ch == '"':
                in_str = False
        elif ch == "%":                                    # comment to end of line
            while i < len(text) and text[i] != "\n":
                i += 1
            continue
        elif ch == '"':
            in_str = True
            buf.append(ch)
            if start is None:
                start = line
        elif ch == "\n":
            line += 1
            if buf:
                buf.append(" ")
        elif ch in "([{":
            depth += 1
            buf.append(ch)
        elif ch in ")]}":
            depth -= 1
            buf.append(ch)
        elif ch == "." and depth == 0 and not (i + 1 < len(text) and text[i + 1] == ".") \
                and not (i > 0 and text[i - 1] == "."):
            s = "".join(buf).strip()
            if s:
                yield start or line, s
            buf, start = [], None
        else:
            if not ch.isspace() and start is None:
                start = line
            buf.append(ch)                                # (a `.` here is half of a `..` range)
        i += 1
    if "".join(buf).strip():
        yield start or line, "".join(buf).strip() + "   % <missing final '.'>"


# ---------------------------------------------------------------------------------------------
# terms
# ---------------------------------------------------------------------------------------------

_TOK = re.compile(r'\s*(?:("(?:[^"\\]|\\.)*")|(-?\d+)|([A-Za-z_][A-Za-z0-9_]*)|(@[a-z_]+)|(\S))')


def tokenize(s: str) -> list:
    out = []
    pos = 0
    while pos < len(s):
        m = _TOK.match(s, pos)
        if not m or m.end() == pos:
            break
        pos = m.end()
        if m.group(1) is not None:
            out.append(("str", m.group(1)[1:-1]))
        elif m.group(2) is not None:
            out.append(("num", int(m.group(2))))
        elif m.group(3) is not None:
            out.append(("id", m.group(3)))
        elif m.group(4) is not None:
            out.append(("func", m.group(4)))
        else:
            out.append(("sym", m.group(5)))
    return out


def parse_term(tokens: list, i: int = 0):
    """Parse one term starting at tokens[i]; returns (term, next_index).
    Terms: int | ("str", s) | name (str, lowercase = symbol, uppercase/_ = variable) | (name, *args)."""
    kind, val = tokens[i]
    if kind == "num":
        return val, i + 1
    if kind == "str":
        return ("str", val), i + 1
    if kind == "sym" and val == "(":
        # REDUNDANT PARENTHESES around a lane index -- `a((I+1))`, `a((I+1) \\ 4)` -- read as the
        # index itself, with a wrap after the closing paren attached to it (G28, 2026-09-02: the
        # reporter's first three spellings of a torus neighbour were all "unreadable").
        items, j = [], i + 1
        while True:
            inner, j = parse_term(tokens, j)
            items.append(inner)
            if j < len(tokens) and tokens[j] == ("sym", ","):
                j += 1
                continue
            break
        if j >= len(tokens) or tokens[j] != ("sym", ")"):
            raise ValueError(f"expected ) after a parenthesised term at token {tokens[j] if j < len(tokens) else 'end'}")
        j += 1
        if len(items) == 1:
            inner = items[0]
            if isinstance(inner, tuple) and inner and inner[0] == "$idx" and inner[3] is None:
                m, j = _wrap_after(tokens, j)        # `(I+1) \\ 4`: the wrap AFTER the paren is the index's
                inner = ("$idx", inner[1], inner[2], m)
            return inner, j
        # A COMMA LIST in parentheses is a DIMENSION LIST or an INDEX-VARIABLE LIST:
        # `net_lane(g, (side, side), 1)`, `def_lane(y, (R, C), ...)` (2026-09-03)
        return ("$tuple", *items), j
    if kind in ("id", "func"):
        if kind == "id" and is_var(val) and i + 1 < len(tokens):
            # a lane INDEX with an offset -- `I-1` tokenizes as (id I)(num -1), `I+1` / `I - 1` as
            # (id)(sym)(num); the offset and the wrap block may each be a NUMBER or a PARAMETER
            # NAME (`q(I - side \\ cells)`): a grid whose neighbour offsets are literals prints a
            # module that is parametric in name only (G28).
            nk, nv = tokens[i + 1]
            if nk == "num" and nv < 0:
                m, j = _wrap_after(tokens, i + 2)
                return ("$idx", val, nv, m), j
            if nk == "sym" and nv in ("+", "-") and i + 2 < len(tokens) and tokens[i + 2][0] in ("num", "id") \
                    and (tokens[i + 2][0] == "num" or is_symbol(tokens[i + 2][1])):
                k = tokens[i + 2][1]
                m, j = _wrap_after(tokens, i + 3)
                off = (k if nv == "+" else -k) if isinstance(k, int) else f"{nv}{k}"
                return ("$idx", val, off, m), j
            if nk == "sym" and nv == "\\":
                m, j = _wrap_after(tokens, i + 1)
                if m is not None:
                    return ("$idx", val, 0, m), j
        if i + 1 < len(tokens) and tokens[i + 1] == ("sym", "("):
            args, j = [], i + 2
            if tokens[j] != ("sym", ")"):
                while True:
                    a, j = parse_term(tokens, j)
                    args.append(a)
                    if tokens[j] == ("sym", ","):
                        j += 1
                        continue
                    if tokens[j] == ("sym", ")"):
                        break
                    raise ValueError(f"expected , or ) in term at token {tokens[j]}")
            return (val, *args), j + 1
        return val, i + 1
    if kind == "sym" and val == "-" and i + 1 < len(tokens) and tokens[i + 1][0] == "num":
        return -tokens[i + 1][1], i + 2
    raise ValueError(f"unexpected token {tokens[i]!r}")


def _wrap_after(tokens, j):
    """`\\ B` after an index, clingo's own modulo: `q(I+16 \\ 256)` WRAPS instead of falling
    outside the lane; B is a number or a parameter name. Returns (modulus, next_index)."""
    if j + 1 < len(tokens) and tokens[j] == ("sym", "\\"):
        k, v = tokens[j + 1]
        if k == "num" or (k == "id" and is_symbol(v)):
            return v, j + 2
    return None, j


def parse_full_term(s: str):
    toks = tokenize(s)
    t, j = parse_term(toks, 0)
    if j != len(toks):
        raise ValueError(f"trailing tokens in term: {s!r}")
    return t


def is_var(t) -> bool:
    return isinstance(t, str) and (t[0].isupper() or t[0] == "_")


def is_symbol(t) -> bool:
    return isinstance(t, str) and t[0].islower()


def term_to_str(t) -> str:
    """Canonical clingo text of a term (what the library sees)."""
    if isinstance(t, int):
        return str(t)
    if isinstance(t, str):
        return t
    if t[0] == "str":
        return f'"{t[1]}"'
    if t[0] == "$tuple":
        return "(" + ", ".join(term_to_str(a) for a in t[1:]) + ")"
    if t[0] == "$idx":
        off = f"{t[2]:+d}" if isinstance(t[2], int) else t[2]
        return f"{t[1]}{off}" + (f" \\ {t[3]}" if len(t) > 3 and t[3] is not None else "")
    return f"{t[0]}({', '.join(term_to_str(a) for a in t[1:])})"


# ---------------------------------------------------------------------------------------------
# rules (the hybrid escape hatch)
# ---------------------------------------------------------------------------------------------

_CMP = ("!=", "<=", ">=", "=", "<", ">")


def _split_top(s: str, sep: str = ",") -> list:
    out, depth, cur, in_str = [], 0, [], False
    for ch in s:
        if in_str:
            cur.append(ch)
            if ch == '"':
                in_str = False
            continue
        if ch == '"':
            in_str = True
        elif ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if ch == sep and depth == 0:
            out.append("".join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    if "".join(cur).strip():
        out.append("".join(cur).strip())
    return out


def _find_cmp(lit: str):
    """Top-level comparison operator in a literal, or None. Returns (lhs, op, rhs)."""
    depth, in_str = 0, False
    i = 0
    while i < len(lit):
        ch = lit[i]
        if in_str:
            in_str = ch != '"'
        elif ch == '"':
            in_str = True
        elif ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        elif depth == 0:
            for op in _CMP:
                if lit.startswith(op, i):
                    return lit[:i].strip(), op, lit[i + len(op):].strip()
        i += 1
    return None


def parse_rule(line: int, stmt: str) -> Rule:
    head_s, body_s = stmt.split(":-", 1)
    err = lambda m: SubsetError(line, m, stmt)     # noqa: E731
    if re.search(r"\bT\s*[+-]\s*\d", stmt):
        raise err("T+1 / T-1 does not occur in a comb rule: a value that depends on ANOTHER instant "
                  "is state, and state comes from a primitive instance (ff/arff/lata/spram)")
    try:
        head = parse_full_term(head_s.strip())
    except ValueError as e:
        raise err(f"unreadable rule head ({e})")
    if not (isinstance(head, tuple) and head[0] == "val" and len(head) == 4):
        raise err("a comb rule's head must be val(Net, Value, T)")
    _, hn, hv, ht = head
    if not is_symbol(hn):
        raise err("the head net must be a plain name")
    if ht != "T":
        raise err("the head instant must be exactly T (no T+1: state comes from a primitive instance)")
    if is_var(hv):
        value = ("var", hv)
    elif isinstance(hv, int) or is_symbol(hv):
        value = hv
    else:
        raise err("the head value must be a variable, an integer or an enum tag")
    guards, reads, cmps, steps = [], [], [], []
    bound: set = set()
    for lit in _split_top(body_s):
        if not lit:
            continue
        if lit.startswith("not "):
            raise err("`not` is not allowed in a design rule (the design layer is positive-definite)")
        cmp = _find_cmp(lit)
        if cmp is None:
            try:
                t = parse_full_term(lit)
            except ValueError as e:
                raise err(f"unreadable literal {lit!r} ({e})")
            if not (isinstance(t, tuple) and t[0] == "val" and len(t) == 4):
                raise err(f"only val(Sig, X, T) literals may appear in a comb rule body, not {lit!r}")
            _, s, x, tt = t
            if tt != "T":
                raise err(f"every val literal reads instant T (found {term_to_str(tt)}): a comb rule "
                          "cannot look across a clock edge")
            if not is_symbol(s):
                raise err(f"the signal in {lit!r} must be a plain name (memory cells are read through "
                          "a spram instance's rd pin)")
            if is_var(x):
                if x in bound:
                    raise err(f"variable {x} is bound twice; compare with `{x} = ..` instead")
                reads.append((s, x))
                bound.add(x)
            elif isinstance(x, int) or is_symbol(x):
                guards.append((s, x))
            else:
                raise err(f"the value in {lit!r} must be a variable, an integer or an enum tag")
            continue
        lhs, op, rhs = cmp
        if rhs.startswith("@"):
            if op != "=":
                raise err(f"an @func step must be `Var = @func(...)`, not {lit!r}")
            if not (is_var(lhs) and lhs not in bound):
                raise err(f"the step {lit!r} must bind a NEW variable")
            try:
                ft = parse_full_term(rhs)
            except ValueError as e:
                raise err(f"unreadable step {lit!r} ({e})")
            fname = ft[0][1:] if isinstance(ft, tuple) else None
            if fname not in FUNCS:
                raise err(f"unknown @func in {lit!r} (the library's ops are {sorted(FUNCS)})")
            if len(ft) - 1 != FUNCS[fname]:
                raise err(f"@{fname} takes {FUNCS[fname]} arguments")
            for a in ft[1:]:
                if is_var(a):
                    if a not in bound:
                        raise err(f"variable {a} used before it is bound in {lit!r}")
                elif not (isinstance(a, int) or (isinstance(a, tuple) and a[0] == "str")):
                    raise err(f"@func arguments are variables or constants, not {term_to_str(a)}")
            steps.append(Step(lhs, fname, tuple(ft[1:])))
            bound.add(lhs)
            continue
        # a comparison on a read variable: V != c, V = c, V < c ...
        try:
            l_t, r_t = parse_full_term(lhs), parse_full_term(rhs)
        except ValueError as e:
            raise err(f"unreadable comparison {lit!r} ({e})")
        if is_var(r_t) and not is_var(l_t):
            l_t, r_t = r_t, l_t
            op = {"<": ">", ">": "<", "<=": ">=", ">=": "<="}.get(op, op)
        if not is_var(l_t) or l_t not in bound:
            raise err(f"a comparison must be between a bound variable and a constant: {lit!r}")
        if not (isinstance(r_t, int) or is_symbol(r_t) or (isinstance(r_t, tuple) and r_t[0] == "str")):
            raise err(f"the right side of {lit!r} must be an integer, a tag or a \"wide\" string")
        if op in ("<", ">", "<=", ">=") and not isinstance(r_t, int):
            raise err(f"an ordering compare needs an integer constant: {lit!r}")
        cmps.append((l_t, op, r_t))
    if isinstance(value, tuple) and value[1] not in bound:
        raise err(f"the head value {value[1]} is not bound by any read or step")
    if not guards and not reads:
        raise err("a comb rule must read at least one signal")
    return Rule(hn, value, tuple(guards), tuple(reads), tuple(cmps), tuple(steps), line, stmt)


# ---------------------------------------------------------------------------------------------
# facts
# ---------------------------------------------------------------------------------------------

def is_param_expr(t) -> bool:
    """A parameter expression: a number, a parameter name, or add/sub/mul(A, B) / log2(A) over those."""
    if isinstance(t, int) or (isinstance(t, str) and is_symbol(t)):
        return True
    if isinstance(t, tuple):
        if t[0] in ("add", "sub", "mul") and len(t) == 3:
            return is_param_expr(t[1]) and is_param_expr(t[2])
        if t[0] == "log2" and len(t) == 2:
            return is_param_expr(t[1])
    return False


def eval_param(t, env: dict, line=0, stmt=""):
    """The value of a parameter expression under `env` (param -> int)."""
    if isinstance(t, int):
        return t
    if isinstance(t, tuple) and t and t[0] == "$tuple":
        raise SubsetError(line, "a dimension list `(a, b)` where a NUMBER is expected -- a list of extents is "
                                "for net_lane / port_lane / inst_lane; a width and a count are one number", stmt)
    if isinstance(t, str):
        if t not in env:
            raise SubsetError(line, f"`{t}` is not a declared param (a width is a number, a param, or add/sub/mul/log2 of params)", stmt)
        return env[t]
    op = t[0]
    if op == "log2":
        v = eval_param(t[1], env, line, stmt)
        return max(1, (v - 1).bit_length()) if v > 1 else (0 if v == 1 else 0)
    a, b = eval_param(t[1], env, line, stmt), eval_param(t[2], env, line, stmt)
    return {"add": a + b, "sub": a - b, "mul": a * b}[op]


def _width(t, line, stmt, allow_params: bool = False):
    if isinstance(t, int) and t > 0:
        return t
    if isinstance(t, tuple) and t[0] == "enum" and len(t) == 2 and is_symbol(t[1]):
        return ("enum", t[1])
    if allow_params and is_param_expr(t):
        return t                                    # a parameter expression: resolved later
    raise SubsetError(line, "a width is a positive integer, enum(E), or an expression over params", stmt)


def _lane_index(t, lanes: dict, idx, line, stmt, env: dict = None):
    """(lane, var|None, offset) of a lane reference `x(I)` / `x(I-1)` / `x(3)`, or None if `t` is not one.
    `idx[0]` is the loop variable in force (None outside a def_lane: only NUMERIC indices then)."""
    if not (isinstance(t, tuple) and len(t) == 2 and isinstance(t[0], str) and t[0] in lanes):
        return None
    j = t[1]
    if isinstance(j, int):
        if not 0 <= j < lanes[t[0]][0]:
            raise SubsetError(line, f"{t[0]}({j}) is outside the lane (0..{lanes[t[0]][0] - 1})", stmt)
        return t[0], None, j, None, j, None
    if isinstance(j, str) and is_var(j):
        if j != idx[0]:
            raise SubsetError(line, f"lane index of {t[0]} must be the loop variable{' ' + idx[0] if idx[0] else ''}"
                                    f" (with an optional +k / -k, and an optional \\ N) or a number", stmt)
        return t[0], j, 0, None, 0, None
    if isinstance(j, tuple) and j[0] == "$idx" and j[1] == idx[0]:
        mod = j[3] if len(j) > 3 else None
        off = j[2]
        # a PARAMETER as the offset or the wrap block resolves through the env for the unrolled
        # design and stays a NAME in the rolled form the printer reads (G28)
        def _val(x, what):
            if isinstance(x, int):
                return x
            name, sign = (x[1:], -1) if x[0] == "-" else (x[1:] if x[0] == "+" else x, 1)
            if env is None or name not in env:
                return None                                   # the printer's form keeps the name
            return sign * env[name]
        offv, modv = _val(off, "offset"), _val(mod, "wrap") if mod is not None else None
        if (env is not None) and (offv is None or (mod is not None and modv is None)):
            bad = off if offv is None else mod
            otxt = off if isinstance(off, str) else format(off, "+d")
            wtxt = (" \\ " + str(mod)) if mod is not None else ""
            raise SubsetError(line, f"{t[0]}({idx[0]}{otxt}{wtxt}): {bad} is not a parameter of this design", stmt)
        j = ("$idx", j[1], offv if offv is not None else off, modv if modv is not None else mod, off, mod)
        mod = modv if modv is not None else mod
        # `x(I+k \\ B)` wraps WITHIN THE BLOCK OF SIZE B THAT CONTAINS I:
        #     (I // B) * B  +  ((I % B) + k) mod B
        # B = the lane's whole extent is the flat wrap (a ring); a smaller B is a wrap within a ROW of a
        # row-major grid, which is what a toroid's column neighbour is. B must DIVIDE the extent, or the
        # blocks do not tile the lane and a wrap could still land outside it -- refused by name.
        if isinstance(mod, int) and (mod <= 0 or lanes[t[0]][0] % mod):
            raise SubsetError(line, f"{t[0]}({idx[0]}{j[2]:+d} \\ {mod}) wraps within blocks of {mod}, "
                                    f"but {mod} does not divide the lane's {lanes[t[0]][0]} member(s) -- "
                                    f"the blocks must tile the lane", stmt)
        return t[0], j[1], j[2], mod, j[4], j[5]
    # A lane index may be a PARAMETER EXPRESSION -- `c(top)` where `param(top, sub(w, 1))`. Without
    # this, a PARAMETRIC lane vector cannot be read at its far end: index 0 is always a literal, but
    # the other end is `w-1`, which is never a number once the width is a parameter, and a chain has
    # to put either its boundary or its answer there. `is_var` is tested first because a loop
    # variable is also a valid parameter EXPRESSION by shape, and must keep its own meaning.
    if not (isinstance(j, str) and is_var(j)) and is_param_expr(j):
        if env is None:
            # No env = the PRINTER's form, which must keep the index SYMBOLIC (`c(top)` -> `c[TOP]`).
            # Only a bare parameter NAME can survive: a compound expression has no localparam to
            # print, so `param(top, sub(w,1))` then `c(top)` is the shape. Range is checked on the
            # resolving pass below, which runs for the same statement.
            if isinstance(j, str):
                return t[0], None, j, None, j, None
        else:
            v = eval_param(j, env, line, stmt)
            if not 0 <= v < lanes[t[0]][0]:
                raise SubsetError(line, f"{t[0]}({v}) is outside the lane (0..{lanes[t[0]][0] - 1})", stmt)
            return t[0], None, v, None, v, None
    raise SubsetError(line, f"lane index of {t[0]} must be the loop variable"
                            f"{' ' + idx[0] if idx[0] else ''} (with an optional +k / -k, and an optional"
                            f" \\ N) or a number", stmt)


def _lanify(t, lanes: dict, idx, line, stmt, env: dict = None):
    """Rewrite lane references `x(I)` / `x(I-1)` / `x(3)` (a lane name applied to an index) into leaf strings:
    `x(i)` for a concrete index (idx = (I, i)), `x(I)` / `x(I-1)` for the printer's ROLLED form (idx = (I, None)).
    Outside a def_lane (idx = (None, None)) only numeric indices are lane references."""
    if (isinstance(t, tuple) and t and t[0] in ("bit", "slc") and len(t) >= 3 and not isinstance(t[2], int)
            and idx[0] is not None):
        rest = [_lanify(a, lanes, idx, line, stmt, env) for a in t[3:]]
        return (t[0], _lanify(t[1], lanes, idx, line, stmt, env),
                _position_over(t[2], (idx[0],), None if idx[1] is None else (idx[1],), line, stmt), *rest)
    li = _lane_index(t, lanes, idx, line, stmt, env)
    if li is not None:
        ln, var, off, mod, offtxt, modtxt = li
        if var is None:
            return member(ln, off)
        if idx[1] is None:                              # the printer's ROLLED form
            ot = (f"{offtxt:+d}" if offtxt else "") if isinstance(offtxt, int) else offtxt
            return rolled(ln, Index(var=var, off=ot, mod=None if modtxt is None else str(modtxt)))
        if not isinstance(off, int) or (mod is not None and not isinstance(mod, int)):
            raise SubsetError(line, f"{ln}({var}{offtxt} \\ {modtxt}): a parameter here needs a value to unroll", stmt)
        i = (idx[1] // mod) * mod + (idx[1] % mod + off) % mod if mod else idx[1] + off
        assert 0 <= i < lanes[ln][0], (t, idx)          # the WINDOW keeps every reference inside its lane
        return member(ln, i)
    if isinstance(t, tuple):
        return tuple([t[0]] + [_lanify(a, lanes, idx, line, stmt, env) for a in t[1:]])
    return t


def _axis_ref(j, var: str, extent: int, value, line, stmt, env, what: str):
    """ONE axis of a multi-axis lane reference: `j` is a number, the axis's own loop variable, or
    `$idx` over it (offset and wrap block as numbers or parameter names). Returns
    (Index for the rolled text, concrete value or None, (lo, hi) clip for the window)."""
    if isinstance(j, int):
        if not 0 <= j < extent:
            raise SubsetError(line, f"{what}: index {j} is outside the axis (0..{extent - 1})", stmt)
        return Index(const=j), j, (0, extent - 1)
    if isinstance(j, str) and is_var(j):
        if j != var:
            raise SubsetError(line, f"{what}: the index must be this axis's variable {var} (with an optional "
                                    f"+k / -k and an optional \\ B), or a number", stmt)
        return Index(var=var), value, (0, extent - 1)
    if isinstance(j, tuple) and j[0] == "$idx" and j[1] == var:
        off, mod = j[2], (j[3] if len(j) > 3 else None)
        def val_of(x):
            if x is None or isinstance(x, int):
                return x
            name, sign = (x[1:], -1) if x[0] == "-" else (x[1:] if x[0] == "+" else x, 1)
            if env is None or name not in env:
                return None
            return sign * env[name]
        offv, modv = val_of(off), val_of(mod)
        if env is not None and (offv is None or (mod is not None and modv is None)):
            raise SubsetError(line, f"{what}: {off if offv is None else mod} is not a parameter of this design", stmt)
        if isinstance(modv, int) and (modv <= 0 or extent % modv):
            raise SubsetError(line, f"{what}: \\ {mod} wraps within blocks of {modv}, but {modv} does not divide "
                                    f"the axis's {extent} member(s)", stmt)
        otxt = (f"{off:+d}" if off else "") if isinstance(off, int) else off
        ix = Index(var=var, off=otxt, mod=None if mod is None else str(mod))
        if value is None:
            clip = (0, extent - 1) if mod is not None or not isinstance(offv, int) else \
                   (max(0, -offv), min(extent - 1, extent - 1 - offv))
            return ix, None, clip
        if not isinstance(offv, int) or (mod is not None and not isinstance(modv, int)):
            raise SubsetError(line, f"{what}: a parameter here needs a value to unroll", stmt)
        v = (value // modv) * modv + (value % modv + offv) % modv if modv else value + offv
        return ix, v, (0, extent - 1)
    raise SubsetError(line, f"{what}: an index is a number, the axis variable, or the variable +k / -k "
                            f"(with an optional \\ B)", stmt)


def _position_over(t, vars_: tuple, values, line, stmt):
    """The POSITION argument of `bit(x, p)` / `slc(x, p, w)` inside a lane def may name the def's
    loop variables: `bit(data, add(mul(R, side), C))` reads a FLAT port at the cell's own position
    (G30, 2026-09-03 -- a grid could not read a wide input per cell without unrolling). With
    `values` the variables are substituted and the parameter folding makes it a number; with
    None (the printer's rolled form) the expression is kept and prints as `data[r*SIDE + c]`.
    A variable that is not one of the def's is refused by name -- never read as zero."""
    def walk(x):
        if isinstance(x, str) and is_var(x):
            if x not in vars_:
                raise SubsetError(line, f"{x} in a position: only this def's loop variables "
                                        f"({', '.join(vars_)}), parameters and numbers may index a bit or slice", stmt)
            return x if values is None else values[vars_.index(x)]
        if isinstance(x, tuple):
            return tuple([x[0]] + [walk(a) for a in x[1:]])
        return x
    return walk(t)


def _lanify_nd(t, lanes, vars_: tuple, values, line, stmt, env: dict = None):
    """Rewrite every lane reference in `t` inside a multi-axis `def_lane(y, (R, C), e)`. A
    reference to a lane with k axes carries k indices, each handled by `_axis_ref` on its own
    axis; `values` None gives the printer's rolled text, a tuple gives the concrete member."""
    if isinstance(t, tuple) and t and t[0] in ("bit", "slc") and len(t) >= 3 and not isinstance(t[2], int):
        rest = [_lanify_nd(a, lanes, vars_, values, line, stmt, env) for a in t[3:]]
        return (t[0], _lanify_nd(t[1], lanes, vars_, values, line, stmt, env),
                _position_over(t[2], vars_, values, line, stmt), *rest)
    if isinstance(t, tuple) and t and isinstance(t[0], str) and t[0] in lanes:
        ln = t[0]
        axes = axes_of(lanes, ln)
        if len(t) - 1 != len(axes):
            raise SubsetError(line, f"{ln}(..) carries {len(t) - 1} index(es); {ln} has {len(axes)} axis(es)", stmt)
        if len(axes) == 1:
            j = t[1]
            v = j if (isinstance(j, str) and is_var(j)) else (j[1] if isinstance(j, tuple) and j[0] == "$idx" else None)
            if v is not None and v in vars_:
                k = vars_.index(v)
                return _lanify(t, lanes, (v, None if values is None else values[k]), line, stmt, env)
            return _lanify(t, lanes, (None, None), line, stmt, env)
        ixs, vals = [], []
        what = f"{ln}({', '.join(term_to_str(x) for x in t[1:])})"
        for k, (j, var, ext) in enumerate(zip(t[1:], vars_, axes)):
            ix, v, _clip = _axis_ref(j, var, ext, None if values is None else values[k], line, stmt, env, what)
            ixs.append(ix); vals.append(v)
        if values is None:
            return rolled(ln, *ixs)
        return member(ln, *vals)
    if isinstance(t, tuple):
        return tuple([t[0]] + [_lanify_nd(a, lanes, vars_, values, line, stmt, env) for a in t[1:]])
    return t


def _lane_window_nd(e, lanes, vars_: tuple, axes: tuple, line, stmt, env: dict = None) -> list:
    """Per axis, the (lo, hi) at which every multi-axis reference in `e` stays inside its lane."""
    wins = [[0, n - 1] for n in axes]
    def walk(t):
        if isinstance(t, tuple) and t and isinstance(t[0], str) and t[0] in lanes and len(axes_of(lanes, t[0])) > 1:
            for k, (j, var, ext) in enumerate(zip(t[1:], vars_, axes_of(lanes, t[0]))):
                _ix, _v, (lo, hi) = _axis_ref(j, var, ext, None, line, stmt, env, f"{t[0]}(..)")
                wins[k][0], wins[k][1] = max(wins[k][0], lo), min(wins[k][1], hi)
            return
        if isinstance(t, tuple):
            for a in t[1:]:
                walk(a)
    walk(e)
    for k, (lo, hi) in enumerate(wins):
        if lo > hi:
            raise SubsetError(line, f"def_lane over an EMPTY window on axis {k}: no index keeps every lane "
                                    f"reference inside its lane", stmt)
    return [tuple(w) for w in wins]


def _lane_window(e, lanes: dict, iv: str, N: int, line, stmt, env: dict = None) -> tuple:
    """The index range (lo, hi) of lane def `def_lane(y, I, e)` over `0..N-1`: the indices at which every
    lane reference `x(I+k)` in `e` lands inside its lane. `x(I-1)` starts the window at 1, `x(I+1)` ends it
    at N-2 -- the lanes outside it are given by ordinary `def(y(0), ...)` facts (an idiom's BOUNDARY lane)."""
    lo, hi = 0, N - 1
    def walk(t):
        nonlocal lo, hi
        li = _lane_index(t, lanes, (iv, None), line, stmt, env)
        if li is not None:
            ln, var, off, mod, _ot, _mt = li
            if var is not None and mod is None and isinstance(off, int):   # a WRAPPING reference is total
                lo, hi = max(lo, -off), min(hi, lanes[ln][0] - 1 - off)
            return
        if isinstance(t, tuple):
            for a in t[1:]:
                walk(a)
    walk(e)
    if lo > hi:
        raise SubsetError(line, f"def_lane over an EMPTY window: no index in 0..{N - 1} keeps every lane "
                                f"reference inside its lane", stmt)
    return lo, hi


def _check_expr(t, line, stmt):
    """Structural check of an expression term: known operators at their arity; leaves are net
    names, ints only inside k(...), strings only inside k(...)."""
    if isinstance(t, str):
        if is_var(t):
            raise SubsetError(line, f"variable {t} in an expression (facts are ground)", stmt)
        return
    if isinstance(t, int):
        raise SubsetError(line, f"bare number {t} in an expression: write k({t}, W)", stmt)
    if t[0] == "str":
        raise SubsetError(line, "a bare string in an expression: write k(\"..\", W)", stmt)
    op, args = t[0], t[1:]
    if op not in OPS:
        raise SubsetError(line, f"unknown operator {op}/{len(args)} in an expression", stmt)
    if len(args) != OPS[op]:
        raise SubsetError(line, f"{op} takes {OPS[op]} arguments, got {len(args)}", stmt)
    if op == "k":
        v, w = args
        if not (isinstance(v, int) or (isinstance(v, tuple) and v[0] == "str")):
            raise SubsetError(line, "k(V, W): V is an integer or a \"decimal\" string", stmt)
        if isinstance(v, int) and v >= 2 ** 31:
            raise SubsetError(line, f"k({v}, ..): a value >= 2^31 must be a \"string\" (hard rule 4)", stmt)
        if not (isinstance(w, int) and w > 0):
            raise SubsetError(line, "k(V, W): W is a positive integer", stmt)
        return
    if op == "tag":
        if not is_symbol(args[0]):
            raise SubsetError(line, "tag(Label): Label is a plain name", stmt)
        return
    # width-position args must be ints; value args are expressions
    value_pos = {"add": (0, 1), "sub": (0, 1), "mul": (0, 1), "and": (0, 1), "or": (0, 1),
                 "xor": (0, 1), "shl": (0, 1), "shr": (0, 1), "ashr": (0, 1), "idiv": (0, 1),
                 "imod": (0, 1), "sidiv": (0, 1), "simod": (0, 1), "lt": (0, 1), "le": (0, 1),
                 "gt": (0, 1), "ge": (0, 1), "slt": (0, 1), "sle": (0, 1), "sgt": (0, 1),
                 "sge": (0, 1), "bnot": (0,), "neg": (0,), "sext": (0,), "slc": (0,), "bit": (0,),
                 "cat": (0, 2), "eq": (0, 1), "ne": (0, 1), "logand": (0, 1), "logor": (0, 1),
                 "lnot": (0,), "ror": (0,), "rand": (0,), "rxor": (0,), "rnand": (0,), "rnor": (0,),
                 "rxnor": (0,), "parity": (0,), "popcnt": (0,), "ite": (0, 1, 2), "clz": (0,),
                 "mrd": (1,), "pack": ()}[op]
    for i, a in enumerate(args):
        if i in value_pos:
            _check_expr(a, line, stmt)
        elif op == "mrd" and i == 0:
            # `mrd(M, A)`'s first argument is the flop ARRAY's name, not a width
            if not is_symbol(a):
                raise SubsetError(line, "the first argument of mrd is the flop array's NAME "
                                        "(`mrd(pht, idx)`)", stmt)
        elif op == "pack":
            # `pack(L)`'s argument is the LANE's name -- the whole point is to name a lane where
            # a value is wanted, so nothing else can appear here
            if not is_symbol(a):
                raise SubsetError(line, "the argument of pack is a LANE's name "
                                        "(`pack(cap)` -- the lane as one word, member 0 the LSB)",
                                  stmt)
        elif not (isinstance(a, int) and a >= 0):
            raise SubsetError(line, f"argument {i + 1} of {op} is a width/position and must be a "
                              f"non-negative integer", stmt)


_VALUE_POS = {"add": (0, 1), "sub": (0, 1), "mul": (0, 1), "and": (0, 1), "or": (0, 1),
              "xor": (0, 1), "shl": (0, 1), "shr": (0, 1), "ashr": (0, 1), "idiv": (0, 1),
              "imod": (0, 1), "sidiv": (0, 1), "simod": (0, 1), "lt": (0, 1), "le": (0, 1),
              "gt": (0, 1), "ge": (0, 1), "slt": (0, 1), "sle": (0, 1), "sgt": (0, 1),
              "sge": (0, 1), "bnot": (0,), "neg": (0,), "sext": (0,), "slc": (0,), "bit": (0,),
              "cat": (0, 2), "eq": (0, 1), "ne": (0, 1), "logand": (0, 1), "logor": (0, 1),
              "lnot": (0,), "ror": (0,), "rand": (0,), "rxor": (0,), "rnand": (0,), "rnor": (0,),
              "rxnor": (0,), "parity": (0,), "popcnt": (0,), "ite": (0, 1, 2), "clz": (0,),
                 "mrd": (1,), "pack": ()}


def resolve_term(t, env: dict, line=0, stmt=""):
    """The term with every WIDTH / position argument that is a parameter expression evaluated
    under `env`; value arguments recursed; leaves untouched. `k(V, W)`: both V and W may be params."""
    if not isinstance(t, tuple) or not t or t[0] in ("str", "tag"):
        return t
    op = t[0]
    if op == "k":
        v, w = t[1], t[2]
        if not (isinstance(v, tuple) and v[0] == "str"):
            v = eval_param(v, env, line, stmt) if is_param_expr(v) else v
        return ("k", v, eval_param(w, env, line, stmt) if is_param_expr(w) else w)
    if op not in _VALUE_POS:
        return t
    out = [op]
    for i, a in enumerate(t[1:]):
        if i in _VALUE_POS[op]:
            out.append(resolve_term(a, env, line, stmt))
        elif op == "mrd" and i == 0:
            out.append(a)     # the flop array's NAME -- a symbol, never a param (the subset
                              # checker has the same exemption; v1 never combined params with
                              # mrd, so this walker's copy of it was missing until the v2 FIFO)
        elif op == "pack":
            out.append(a)     # the LANE's name, for the same reason -- and the same trap: this
                              # walker keeps its own copy of the exemption, so a form added to
                              # the checker alone is refused here as an undeclared param
        elif is_param_expr(a) and not isinstance(a, int):
            out.append(eval_param(a, env, line, stmt))
        else:
            out.append(a)
    return tuple(out)


def _param_env(text: str, overrides: "dict | None") -> tuple:
    """(env, exprs): every `param(P, V)` in file order, evaluated; an OVERRIDE replaces a numeric
    param's value (an expression param is recomputed from the overridden ones)."""
    env: dict = {}
    exprs: dict = {}
    for line, stmt in statements(text):
        if not stmt.startswith("param("):
            continue
        t = parse_full_term(stmt)
        if len(t) != 3 or not is_symbol(t[1]):
            raise SubsetError(line, "param(P, V): a name and a number or an expression over earlier params", stmt)
        name, v = t[1], t[2]
        if not is_param_expr(v):
            raise SubsetError(line, "param(P, V): V is a number, a param, or add/sub/mul/log2 of params", stmt)
        exprs[name] = v
        if overrides and name in overrides and isinstance(v, int):
            env[name] = int(overrides[name])
        else:
            env[name] = eval_param(v, env, line, stmt)
    if overrides:
        unknown = set(overrides) - set(exprs)
        if unknown:
            raise SubsetError(0, f"mparam overrides unknown parameter(s) {sorted(unknown)}")
    return env, exprs


def load(path: "str | pathlib.Path", params: "dict | None" = None) -> Design:
    text = pathlib.Path(path).read_text()
    return load_text(text, params)


class RawParts:
    """What the printer needs to print PARAMETRICALLY: the unresolved widths and terms."""
    def __init__(self):
        self.port_w: dict = {}      # port -> raw width
        self.net_w: dict = {}       # net -> raw width
        self.defs: dict = {}        # net -> raw def term
        self.iparams: dict = {}     # (inst, p) -> raw value
        self.lane_n: dict = {}      # lane / lane-instance name -> raw COUNT (a param or an expression), for `x [N]` / `i < N`
        self.lane_axes: dict = {}   # lane name -> the extents AS WRITTEN, per axis (a multi-axis lane only)
        self.lane_w: dict = {}      # lane name -> raw WIDTH (Design.lanes holds the evaluated one, for the harness and the ASP)
        self.lane_defs: dict = {}   # lane name -> the ROLLED def with raw (param) terms; Design.lane_defs holds it resolved
        self.def_targets: dict = {} # resolved lane member -> its RAW form, when a def's TARGET carries a
                                    # parametric index: `def(seen(top), ..)` must print `seen[TOP]`, not the
                                    # default width's literal. Keyed by the resolved name because the printer
                                    # walks `def_order`, which is resolved.


def load_text(text: str, params: "dict | None" = None) -> Design:
    d = Design()
    env, pexprs = _param_env(text, params)
    d.param_exprs = dict(pexprs)
    raw = RawParts() if pexprs else None
    if raw is not None:
        d.raw = raw
    # parameter names inside guarded-rule text (a @func width, a compare constant) are substituted textually
    _sub_params = (lambda txt: re.sub(r"(?<![\w])(" + "|".join(map(re.escape, sorted(env, key=len, reverse=True)))
                                     + r")(?![\w(])", lambda m: str(env[m.group(1)]), txt)) if env else (lambda txt: txt)
    for tok in FORBIDDEN_TOKENS:
        if tok in text:
            ln = text[: text.index(tok)].count("\n") + 1
            raise SubsetError(ln, f"{tok} is not allowed in a design file (scenarios and companions "
                              "carry directives; the design is facts + comb rules)")
    for line, stmt in statements(text):
        if "{" in stmt:
            raise SubsetError(line, "a choice rule belongs to a scenario/companion, not the design", stmt)
        if ":-" in stmt:
            if stmt.startswith(":-"):
                raise SubsetError(line, "an integrity constraint belongs to the property layer, "
                                  "not the design", stmt)
            d.rules.append(parse_rule(line, _sub_params(stmt)))
            continue
        try:
            t = parse_full_term(stmt)
        except ValueError as e:
            raise SubsetError(line, f"unreadable statement ({e})", stmt)
        if t == "opaque_datapath" or t == ("opaque_datapath",):
            d.opaque_datapath = True
            continue
        if not isinstance(t, tuple) or t[0] not in FACT_PREDS:
            name = t[0] if isinstance(t, tuple) else t
            if name == "val":
                raise SubsetError(line, "a val(..) FACT is a fixed value at an instant: initial state "
                                  "belongs to a companion (aspfirst_init0.lp), stimulus to the scenario",
                                  stmt)
            raise SubsetError(line, f"'{name}' is not in the authoring vocabulary "
                              f"({', '.join(FACT_PREDS)})", stmt)
        pred, args = t[0], t[1:]
        if len(args) != FACT_PREDS[pred]:
            raise SubsetError(line, f"{pred} takes {FACT_PREDS[pred]} arguments", stmt)
        if pred != "def_lane" and any(is_var(a) for a in args if isinstance(a, str)):
            raise SubsetError(line, "facts are ground: no variables", stmt)
        # ---- LANES: unrolled here into ordinary nets / defs / instances (the ASP's shape); the rolled form kept
        if pred in ("net_lane", "port_lane"):
            if pred == "net_lane":
                n, N, w = args; dr = None
            else:
                n, dr, N, w = args
                if dr not in ("input", "output"):
                    raise SubsetError(line, "port_lane direction is input or output", stmt)
            rawN = N
            axes_raw = tuple(N[1:]) if isinstance(N, tuple) and N and N[0] == "$tuple" else (N,)
            axes = tuple(eval_param(a, env, line, stmt) if not isinstance(a, int) else a for a in axes_raw)
            if not all(isinstance(a, int) and a > 0 for a in axes) or not is_symbol(n):
                raise SubsetError(line, "net_lane(x, N, W) / port_lane(x, dir, N, W): a name, a positive count "
                                        "(or a list of them, `(side, side)`), a width", stmt)
            N = 1
            for a in axes:
                N *= a
            if n in OPS or n in ("k", "tag", "str"):
                raise SubsetError(line, f"a lane cannot be named after an operator ({n}): x(I) must read as a lane member", stmt)
            if raw is not None:
                raw.lane_n[n] = rawN                     # the count as WRITTEN (a param prints as itself, item 2 of the lane list)
            rw = _width(w, line, stmt, allow_params=raw is not None)
            wv = _width(eval_param(rw, env, line, stmt) if is_param_expr(rw) and not isinstance(rw, int) else rw, line, stmt)
            d.lanes[n] = (N, wv, dr)
            if len(axes) > 1:
                d.lanes.axes[n] = axes
                if raw is not None:
                    raw.lane_axes[n] = axes_raw
            if raw is not None:
                raw.lane_w[n] = rw
            for idx in members(axes):
                m = member(n, *idx)
                if dr:
                    d.ports.append(Port(m, dr, wv))
                else:
                    d.nets.append(Net(m, wv))
                if raw is not None:
                    (raw.port_w if dr else raw.net_w)[m] = rw
            continue
        if pred == "def_lane" and isinstance(args[1], tuple) and args[1] and args[1][0] == "$tuple":
            n, iv, e = args
            vars_ = tuple(iv[1:])
            axes = axes_of(d.lanes, n) if n in d.lanes else ()
            if not (is_symbol(n) and n in d.lanes and all(isinstance(v, str) and is_var(v) for v in vars_)):
                raise SubsetError(line, "def_lane(x, (R, C), Expr): x a declared lane, one variable per axis", stmt)
            if len(vars_) != len(axes):
                raise SubsetError(line, f"def_lane({n}, ({', '.join(vars_)}), ..): {n} has {len(axes)} axis(es) "
                                        f"({' x '.join(str(a) for a in axes)}), the index list names {len(vars_)}", stmt)
            wins = _lane_window_nd(e, d.lanes, vars_, axes, line, stmt, env)
            rolled_ = _lanify_nd(e, d.lanes, vars_, None, line, stmt)
            if raw is not None:
                raw.lane_defs[n] = rolled_
                rolled_ = resolve_term(rolled_, env, line, stmt)
            d.lane_defs.append((n, vars_, rolled_, tuple(lo for lo, _ in wins), tuple(hi for _, hi in wins)))
            import itertools as _it
            for idx in _it.product(*(range(lo, hi + 1) for lo, hi in wins)):
                ei = _lanify_nd(e, d.lanes, vars_, idx, line, stmt, env)
                if raw is not None:
                    raw.defs[member(n, *idx)] = ei
                    ei = resolve_term(ei, env, line, stmt)
                _check_expr(ei, line, stmt)
                m = member(n, *idx)
                if m in d.defs:
                    raise SubsetError(line, f"{m} is defined twice", stmt)
                d.defs[m] = ei
                d.def_order.append(m)
                d.src[("def", m)] = (line, stmt)
            continue
        if pred == "def_lane":
            n, iv, e = args
            if not (is_symbol(n) and n in d.lanes and isinstance(iv, str) and is_var(iv)):
                raise SubsetError(line, "def_lane(x, I, Expr): x a declared lane, I a variable", stmt)
            if len(axes_of(d.lanes, n)) > 1:
                raise SubsetError(line, f"def_lane({n}, {iv}, ..): {n} has {len(axes_of(d.lanes, n))} axes -- "
                                        f"name one variable per axis, `def_lane({n}, (R, C), ..)`", stmt)
            N = d.lanes[n][0]
            lo, hi = _lane_window(e, d.lanes, iv, N, line, stmt)
            rolled = _lanify(e, d.lanes, (iv, None), line, stmt)
            if raw is not None:
                raw.lane_defs[n] = rolled                      # the printer's parametric form
                rolled = resolve_term(rolled, env, line, stmt)  # the composed / flattened form
            d.lane_defs.append((n, iv, rolled, lo, hi))
            for i in range(lo, hi + 1):
                ei = _lanify(e, d.lanes, (iv, i), line, stmt, env)   # a parameter offset/wrap resolves here
                if raw is not None:
                    raw.defs[f"{n}({i})"] = ei
                    ei = resolve_term(ei, env, line, stmt)
                _check_expr(ei, line, stmt)
                m = f"{n}({i})"
                if m in d.defs:
                    raise SubsetError(line, f"{m} is defined twice", stmt)
                d.defs[m] = ei
                d.def_order.append(m)
                d.src[("def", m)] = (line, stmt)
            continue
        if pred == "inst_lane":
            u, c, N = args
            rawN = N
            axes_raw = tuple(N[1:]) if isinstance(N, tuple) and N and N[0] == "$tuple" else (N,)
            axes = tuple(eval_param(a, env, line, stmt) if not isinstance(a, int) else a for a in axes_raw)
            if not (is_symbol(u) and is_symbol(c) and all(isinstance(a, int) and a > 0 for a in axes)):
                raise SubsetError(line, "inst_lane(u, cell, N): a name, a library cell, a positive count "
                                        "(or a list of them, `(side, side)`)", stmt)
            N = 1
            for a in axes:
                N *= a
            d.lane_insts[u] = (c, N)
            if len(axes) > 1:
                d.inst_axes[u] = axes                  # a grid of cells: instances u(r, c), row-major
                if raw is not None:
                    raw.lane_axes[u] = axes_raw
            if raw is not None:
                raw.lane_n[u] = rawN
            for idx in members(axes):
                d.insts.append(Inst(member(u, *idx), c, {}, {}))
            d.src[("inst", u)] = (line, stmt)
            continue
        if pred in ("pin", "iparam") and args[0] in d.lane_insts:
            u = args[0]
            c, N = d.lane_insts[u]
            u_axes = d.inst_axes.get(u, (N,))
            for idx in members(u_axes):
                i = idx[0] if len(idx) == 1 else idx
                inst = next(x for x in d.insts if x.name == member(u, *idx))
                if pred == "pin":
                    _, pn, net = args
                    if not is_symbol(net):
                        raise SubsetError(line, "a pin connects to a NET (tie constants through a def)", stmt)
                    if net in d.lanes and axes_of(d.lanes, net) != u_axes and \
                            (len(axes_of(d.lanes, net)) > 1 or len(u_axes) > 1):
                        raise SubsetError(line, f"pin({u}, {pn}, {net}): the instance lane has axes "
                                                f"{u_axes} and the lane {net} has {axes_of(d.lanes, net)} -- a "
                                                f"pin joins a member to a member, so the shapes must agree", stmt)
                    inst.pins[pn] = member(net, *idx) if net in d.lanes else net   # a lane pin per member, a scalar shared
                else:
                    _, pn, v = args
                    if raw is not None:
                        raw.iparams[(f"{u}({i})", pn)] = v
                        raw.iparams[(u, pn)] = v                       # and under the ROLLED name, for the printer's one generate block
                        if is_param_expr(v) and not isinstance(v, int) and not (isinstance(v, str) and v not in env):
                            v = eval_param(v, env, line, stmt)
                    inst.iparams[pn] = v
            continue
        if pred == "module":
            if d.name:
                raise SubsetError(line, "one module per design file", stmt)
            d.name = sv_name(args[0])
        elif pred == "port":
            n, dr, w = args
            if dr not in ("input", "output"):
                raise SubsetError(line, "port direction is input or output", stmt)
            rw = _width(w, line, stmt, allow_params=raw is not None)
            if raw is not None:
                raw.port_w[n] = rw
            d.ports.append(Port(n, dr, _width(eval_param(rw, env, line, stmt) if is_param_expr(rw) and not isinstance(rw, int) else rw, line, stmt)))
        elif pred == "net":
            n, w = args
            rw = _width(w, line, stmt, allow_params=raw is not None)
            if raw is not None:
                raw.net_w[n] = rw
            d.nets.append(Net(n, _width(eval_param(rw, env, line, stmt) if is_param_expr(rw) and not isinstance(rw, int) else rw, line, stmt)))
        elif pred == "enum_member":
            e, lab, v = args
            if not (is_symbol(e) and is_symbol(lab) and isinstance(v, int)):
                raise SubsetError(line, "enum_member(E, label, Value): names + an integer", stmt)
            d.enums.setdefault(e, []).append((lab, v))
        elif pred == "param":
            d.params[args[0]] = env[args[0]]
        elif pred == "def":
            n, e = args
            n_raw = n
            if _lane_index(n, d.lanes, (None, None), line, stmt, env) is not None:
                # The TARGET needs the same two forms as the expression below: `def(seen(top), ...)`
                # must print as `assign seen[TOP] = ...`, not with the default width's literal baked
                # in. At the default width the literal is accidentally right, so only an instance at
                # another width exposes it -- as a multiple-driver error, or silently.
                n_raw = _lanify(n, d.lanes, (None, None), line, stmt)     # the printer's form
                n = _lanify(n, d.lanes, (None, None), line, stmt, env)    # the ASP's form
            elif not is_symbol(n):
                raise SubsetError(line, "def(Net, Expr): Net is a plain name or a lane member x(3)", stmt)
            # TWO forms: the printer's keeps a parametric index symbolic (`c(top)` -> `c[TOP]`), the
            # ASP's resolves it. Resolving before `raw.defs` captured it baked `c[7]` into a module
            # parametric in its width -- silently wrong at any other width.
            e_raw = _lanify(e, d.lanes, (None, None), line, stmt)
            e = _lanify(e, d.lanes, (None, None), line, stmt, env)         # `x(3)` / `x(top)` is that member
            if raw is not None:
                raw.defs[n] = e_raw
                if n_raw != n:
                    raw.def_targets[n] = n_raw
                e = resolve_term(e, env, line, stmt)
            _check_expr(e, line, stmt)
            if n in d.defs:
                raise SubsetError(line, f"{n} is defined twice", stmt)
            d.defs[n] = e
            d.def_order.append(n)
            d.src[("def", n)] = (line, stmt)
        elif pred == "inst":
            i, c = args
            if not is_symbol(c):
                raise SubsetError(line, "inst(I, Cell): a library cell or an authored MODULE name", stmt)
            # a name that is not a library cell is an authored MODULE (`<name>.lp` next to the design
            # or under units/ or modules/): the composer resolves it; the loader only records it
            if any(x.name == i for x in d.insts):
                raise SubsetError(line, f"instance {i} declared twice", stmt)
            d.insts.append(Inst(i, c, {}, {}))
            d.src[("inst", i)] = (line, stmt)
        elif pred == "pin":
            i, p, n = args
            inst = next((x for x in d.insts if x.name == i), None)
            if inst is None:
                raise SubsetError(line, f"pin on undeclared instance {i} (declare inst({i}, cell) first)", stmt)
            if _lane_index(n, d.lanes, (None, None), line, stmt, env) is not None:
                n = _lanify(n, d.lanes, (None, None), line, stmt, env)    # a lane MEMBER on a scalar instance's pin
            if not is_symbol(n):
                raise SubsetError(line, "a pin connects to a NET (tie constants through a def)", stmt)
            if p in inst.pins:
                raise SubsetError(line, f"pin {p} of {i} connected twice", stmt)
            inst.pins[p] = n
        elif pred == "iparam":
            i, p, v = args
            inst = next((x for x in d.insts if x.name == i), None)
            if inst is None:
                raise SubsetError(line, f"iparam on undeclared instance {i}", stmt)
            if raw is not None:
                raw.iparams[(i, p)] = v
                if is_param_expr(v) and not isinstance(v, int) and not (isinstance(v, str) and v not in env):
                    v = eval_param(v, env, line, stmt)     # (an enum tag reset_value is a symbol NOT in env: kept)
            inst.iparams[p] = v
        elif pred == "mparam":
            i, p, v = args
            inst = next((x for x in d.insts if x.name == i), None)
            if inst is None:
                raise SubsetError(line, f"mparam on undeclared instance {i}", stmt)
            if not isinstance(v, int) and not (is_param_expr(v)):
                raise SubsetError(line, "mparam(I, P, V): V is a number or an expression over this module's params", stmt)
            inst.mparams[p] = eval_param(v, env, line, stmt) if not isinstance(v, int) else v
        elif pred == "arch_mem":
            # an ARCHITECTURAL memory: state the specification may name (a cache's arrays, a predictor's
            # tables, a register file) -- as opposed to staging/control flops, which it may not. The
            # level builds it as `inst(M, spram)` of exactly this shape, or leaves it `abstract(M)`
            # (every cell a free value each instant, or what a `model(cell(M, A), V, T)` says).
            n, dp, w = args
            dp = eval_param(dp, env, line, stmt) if not isinstance(dp, int) else dp
            w = eval_param(w, env, line, stmt) if not isinstance(w, int) else w
            if not (is_symbol(n) and isinstance(dp, int) and dp > 0 and isinstance(w, int) and w > 0):
                raise SubsetError(line, "arch_mem(M, Depth, Width): a name, a positive depth, a positive width", stmt)
            if n in d.arch_mems:
                raise SubsetError(line, f"arch_mem {n} declared twice", stmt)
            d.arch_mems[n] = (dp, w)
            d.src[("arch_mem", n)] = (line, stmt)
        elif pred == "arch_reg":
            # an ARCHITECTURAL single register: state the specification NAMES, as opposed to a staging
            # flop, which it may not. The memory's twin -- and the reason it exists is that `arch_mem`
            # must be built as spram/farray, so naming ONE register forced a depth-1 array, which the
            # translator refuses (any address net has a bit, so it reaches past a single cell).
            # It DECLARES A NET, which is what keeps this small: abstraction (`abstract(N)` frees a net
            # per instant), width checking, the printer and plan_step's state-freeing then all apply
            # with no new machinery. The level either abstracts it or builds it as a register whose `q`
            # pin is this net; the lint checks exactly that.
            n, w = args
            # `arch_reg(N, enum(E))` -- a NAMED-STATE register, the twin of `net(N, enum(E))`.
            # The width goes through `_width`, which already returns ("enum", E) for a net; an
            # arch_reg refused it and took only a number, so a state machine the specification
            # names could be declared enum-typed as an INTERMEDIATE and not as the register that
            # holds it -- and its RTL carried encodings, not names (G21, 2026-09-02).
            if isinstance(w, tuple) and w and w[0] == "$tuple":
                raise SubsetError(line, f"arch_reg({n}, {term_to_str(w)}): arch_reg names ONE register and takes a "
                                        f"width. An architectural array of one-bit cells is a lane of registers: "
                                        f"`net_lane({n}, {term_to_str(w)}, 1)` with `inst_lane(u, ff, {term_to_str(w)})` "
                                        f"and `pin(u, q, {n})`; the linkage mounts windows on {n}(r, c)", stmt)
            if isinstance(w, tuple) and w and w[0] == "enum":
                w = _width(w, line, stmt)
            else:
                w = eval_param(w, env, line, stmt) if not isinstance(w, int) else w
            if not (is_symbol(n) and ((isinstance(w, int) and w > 0) or isinstance(w, tuple))):
                raise SubsetError(line, "arch_reg(N, Width): a name and a positive width, "
                                        "or enum(E) for a named-state register", stmt)
            if n in d.arch_regs:
                raise SubsetError(line, f"arch_reg {n} declared twice", stmt)
            if any(x.name == n for x in d.nets):
                raise SubsetError(line, f"{n} is declared both as a net and as an arch_reg", stmt)
            d.arch_regs[n] = w
            d.nets.append(Net(n, w))
            d.src[("arch_reg", n)] = (line, stmt)
        elif pred == "abstract":
            n = args[0]
            if not is_symbol(n):
                raise SubsetError(line, "abstract(X): a net, an architectural memory, or an instance of an authored module", stmt)
            if n in d.abstracts:
                raise SubsetError(line, f"{n} is abstract twice", stmt)
            # a LANE is abstract member by member -- lanes are unrolled into ordinary nets before
            # anything downstream sees them, so `abstract(q)` on a 256-lane grid means all 256 of
            # `q(0)..q(255)`. Without this it declared an undeclared scalar `q` and every member came
            # out multi-driven, which is a confusing way to say "abstract does not know about lanes".
            if n in d.lanes:
                for idx in members(axes_of(d.lanes, n)):
                    d.abstracts.append(member(n, *idx))
                    d.src[("abstract", member(n, *idx))] = (line, stmt)
                continue
            d.abstracts.append(n)                # a net, or a MODULE INSTANCE (contract-only)
            d.src[("abstract", n)] = (line, stmt)
        elif pred == "data":
            n = args[0]
            if not is_symbol(n):
                raise SubsetError(line, "data(N): a declared net or port whose values are symbolic", stmt)
            if n in d.data:
                raise SubsetError(line, f"{n} is data twice", stmt)
            if n in d.lanes:
                # a LANE declared data makes every member data -- the regeneration run's
                # slot payloads (addr, entryTag, line) are lanes of tokens, and without
                # this a lane and the symbolic reading could not coexist
                for idx in members(axes_of(d.lanes, n)):
                    m = member(n, *idx)
                    if m in d.data:
                        raise SubsetError(line, f"{m} is data twice", stmt)
                    d.data.append(m)
                d.src[("data", n)] = (line, stmt)
            else:
                d.data.append(n)
                d.src[("data", n)] = (line, stmt)
    if not d.name:
        raise SubsetError(1, "no module(Name) fact")
    return d
