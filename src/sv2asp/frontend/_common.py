"""pyslang frontend: compile (for cross-file binding) -> IR Design.

Decision (v1): resolve all parameters to CONCRETE values before translation (via
``paramOverrides``). We then read pyslang's elaborated concrete widths and constant
values directly, so no symbolic-width / param-expression recovery is needed. This is
the ONLY module that imports pyslang AST types.
"""

from __future__ import annotations

import re



# CST member kind -> coverage category
_DESIGN_KINDS = {"ContinuousAssign", "AlwaysBlock", "AlwaysFFBlock", "AlwaysCombBlock",
                 "AlwaysLatchBlock", "HierarchyInstantiation", "LoopGenerate",
                 "IfGenerate", "CaseGenerate", "GenerateRegion"}
_DECL_KINDS = {"PortDeclaration", "DataDeclaration", "NetDeclaration", "ParameterDeclaration",
               "ParameterDeclarationStatement", "TypedefDeclaration", "LocalParamDeclaration",
               # a function/task definition is CONSUMED by inlining -> its logic appears at the
               # call site (which is `design`/emitted); the definition itself is a declaration.
               "FunctionDeclaration", "TaskDeclaration",
               # a genvar declaration is consumed by the generate loop (which lane-rolls); the decl
               # line itself is structural, not a translatable construct.
               "GenvarDeclaration",
               "ModportDeclaration"}  # an interface modport: a directional view, consumed structurally
# SVA / verification = the property layer (recognized + handled separately, NOT an omission)
_PROPERTY_KINDS = {"PropertyDeclaration", "SequenceDeclaration", "ConcurrentAssertionMember",
                   "ImmediateAssertionMember"}

# pyslang BinaryOperator name -> catalog op name
_BINOP = {
    "Add": "add",
    "Subtract": "sub",
    "Multiply": "mul",
    "Equality": "eq",
    "Inequality": "ne",
    # 4-state case (in)equality: under our 2-state model (no X/Z in the state) `a === b` is
    # identical to `a == b`, so it routes through the same word/tag compare. (X/Z matching is a
    # non-synthesizable concern that cannot arise in the positive-definite state we model.)
    "CaseEquality": "eq",
    "CaseInequality": "ne",
    "LessThan": "lt",
    "LessThanEqual": "le",
    "GreaterThan": "gt",
    "GreaterThanEqual": "ge",
    "LogicalAnd": "logand",
    "LogicalOr": "logor",
    "BinaryAnd": "and",
    "BinaryOr": "or",
    "BinaryXor": "xor",
    "LogicalShiftLeft": "shl",
    "ArithmeticShiftLeft": "shl",   # same as logical left
    "LogicalShiftRight": "shr",
    "Power": "pow",
    "Divide": "div",
    "Mod": "mod",
    # ArithmeticShiftRight (>>>): signedness-dependent -> resolved in the BinaryOp lowering
    # ("ashr" when the shifted operand is signed, "shr" when unsigned).
    "ArithmeticShiftRight": "ashr",
}
_CMP_OPS = {"eq", "ne", "lt", "le", "gt", "ge"}  # lowered comparison ops _cond_branches emits directly
_ID_RUN = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")  # one identifier component (for clingo-constant fixup)
_UNOP = {"LogicalNot": "lnot", "BitwiseNot": "not", "Minus": "neg",
         # unary forms of the bitwise ops are REDUCTIONS over the operand's bits/lanes
         "BitwiseOr": "ror", "BitwiseAnd": "rand", "BitwiseXor": "rxor",
         "BitwiseNor": "rnor", "BitwiseNand": "rnand", "BitwiseXnor": "rxnor"}


def _enum_name(v: object) -> str:
    return str(v).rsplit(".", 1)[-1]


