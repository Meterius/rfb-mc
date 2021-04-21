import z3
from typing import List, NamedTuple, Dict, Optional

CloneExpressionOutput = NamedTuple("CloneExpressionOutput", [
    ("clones", List[z3.BoolRef]), ("var_map", Dict[z3.ExprRef, List[z3.ExprRef]])
])


def serialize_expression(expression: z3.ExprRef) -> str:
    s = z3.Solver()
    s.add(expression)
    return s.sexpr()


def deserialize_expression(serialized_expression: str, ctx: Optional[z3.Context] = None) -> z3.ExprRef:
    return z3.And(z3.parse_smt2_string(serialized_expression, ctx=ctx))


def get_variables(expression: z3.ExprRef) -> List[z3.ExprRef]:
    """
    Returns all variables that are contained in the expression.
    :param expression: Expression from which variables are extracted
    """

    class AstRefKey:
        def __init__(self, n):
            self.n = n

        def __hash__(self):
            return self.n.hash()

        def __eq__(self, other):
            return self.n.eq(other.n)

        def __repr__(self):
            return str(self.n)

    def askey(n):
        assert isinstance(n, z3.AstRef)
        return AstRefKey(n)

    variables = set()

    def collect(f):
        if z3.is_const(f):
            if f.decl().kind() == z3.Z3_OP_UNINTERPRETED and not askey(f) in variables:
                variables.add(askey(f))
        else:
            for c in f.children():
                collect(c)

    collect(expression)
    return [elem.n for elem in variables]


def recreate_variable(key: str, variable: z3.ExprRef) -> z3.ExprRef:
    """
    Recreates the variable but renames it with a key that is used
    to make it distinct.
    :param key:
    :param variable:
    """

    return z3.Const(f"{key}_{variable}", variable.sort())


def clone_expression(expression: z3.ExprRef, q: int) -> CloneExpressionOutput:
    """
    Clones expression by generating q instances of the expression where each
    variable is substituted by a unique newly generated variable for each variable in each clone.
    The output will list each clone and a dictionary where each entry corresponds to
    a mapping from variable in the original formula to the substituted cloned variables for each clone
    listed in the same order as the clone list.
    :param expression: Expression to be cloned
    :param q: Amount of clones created
    """

    variables = get_variables(expression)

    var_map = {
        x: [recreate_variable(f"clone{{{i}}}", x) for i in range(q)] for x in variables
    }

    clones = [z3.substitute(expression, [(x, var_map[x][i]) for x in variables]) for i in range(q)]

    return CloneExpressionOutput(
        clones=clones,
        var_map=var_map,
    )
