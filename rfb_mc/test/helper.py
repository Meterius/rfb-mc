from typing import List
import z3


def count_models_by_boolean_branching(formula: z3.BoolRef, variables: List[z3.BoolRef]) -> int:
    mc = 0

    solver = z3.Solver()
    solver.add(formula)

    def explore_branch(partial_assignment: List[bool]):
        nonlocal mc

        solver.push()
        solver.add(partial_assignment[-1] == variables[len(partial_assignment) - 1])

        if solver.check() == z3.sat:
            if len(partial_assignment) == len(variables):
                mc += 1
            else:
                explore_branch(partial_assignment + [False])
                explore_branch(partial_assignment + [True])

        solver.pop()

    explore_branch([False])
    explore_branch([True])

    return mc


def count_models_by_branching(formula: z3.BoolRef, variables: List[z3.BitVecRef]) -> int:
    bits = [z3.Extract(i, i, x) == 1 for x in variables for i in range(x.size())]
    return count_models_by_boolean_branching(formula, bits)
