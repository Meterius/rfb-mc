import z3
from collections import Counter
from typing import NamedTuple, Optional, List, Tuple, Dict, cast
from rfb_mc.component.helper.z3_helper import clone_expression, deserialize_expression, \
    serialize_expression
from rfb_mc.runner import RunnerBase
from rfb_mc.types import Params, RfBmcTask, RfBmcResult

FormulaParamsZ3 = NamedTuple("FormulaParamsZ3", [("formula", z3.BoolRef), ("variables", List[z3.BitVecRef])])

RfmiGenerationArgsZ3 = NamedTuple("RfmiGenerationArgsZ3", [("variables", List[z3.BitVecRef])])


class RunnerZ3(RunnerBase[FormulaParamsZ3, RfmiGenerationArgsZ3, z3.BoolRef]):
    def __init__(
        self,
        params: Params,
        formula_params: FormulaParamsZ3,
    ):
        super().__init__(params, formula_params)

        # maps q to a solver that has a q-times conjunction asserted
        self._solver_map: Dict[int, Tuple[z3.Solver, List[z3.BitVecRef]]] = {}

    def _get_solver(self, q: int) -> (z3.Solver, List[z3.BitVecRef]):
        """
        Returns the solver and cloned variables, of which the solver
        has the q-times conjunction of the formula asserted.
        """

        if q not in self._solver_map:
            formula_clone = clone_expression(self.formula_params.formula, q)

            variables = [
                cast(z3.BitVecRef, q_bv)
                for bv in self.formula_params.variables
                for q_bv in formula_clone.var_map[bv]
            ]

            # TODO: investigate performance of different configurations
            #  and allow for custom solver configurations
            solver = z3.Solver()
            solver.add(z3.And(formula_clone.clones))

            self._solver_map[q] = (solver, variables)

        return self._solver_map[q]

    @classmethod
    def check_params_and_formula_params_compatibility(
        cls,
        params: Params,
        formula_params: FormulaParamsZ3,
    ):
        formula_variable_counter = Counter([x.size() for x in formula_params.variables])
        assert formula_variable_counter == params.bit_width_counter, \
               "bit widths of the formula params must match bit widths of the params"

    @staticmethod
    def _z3_bounded_model_count(solver: z3.Solver, variables: List[z3.ExprRef], u: int) -> Optional[int]:
        """
        If the solver assertions have less than u models that are distinct for the given variables it
        returns the exact model count, otherwise it returns None.
        :param solver:
        :param variables:
        :param u:
        """

        solver.push()

        for i in range(u):
            response = solver.check()

            if response == z3.unknown:
                solver.pop()
                raise RuntimeError("Solver responded with unknown")
            elif response == z3.unsat:
                solver.pop()
                return i

            # in the last iteration adding the constraint would be unnecessary, thus is skipped
            if i != u-1:
                # add assertion that found model cannot be satisfying again
                m = solver.model()
                solver.add(z3.Or([x != m[x] for x in variables]))

        solver.pop()

        return None

    def get_restrictive_formula_instance_generation_args(self, q: int) -> RfmiGenerationArgsZ3:
        _, variables = self._get_solver(q)

        return RfmiGenerationArgsZ3(
            variables=variables,
        )

    def rf_bmc(self, task: RfBmcTask) -> RfBmcResult:
        solver, variables = self._get_solver(task.q)

        # TODO: ensure solver stack is maintained correctly even on error

        solver.push()
        solver.add(
            self.generate_restrictive_formula_instance(task.rfm_guid, task.rfm_formula_params, task.q)
        )

        # is None if solver has at least a models for q_bits
        bmc = self._z3_bounded_model_count(solver, variables, task.a)

        solver.pop()

        return RfBmcResult(bmc=bmc)


SerializedFormulaParamsZ3 = NamedTuple(
    "SerializedFormulaParamsZ3",
    [("serialized_formula", str), ("serialized_variables", List[Tuple[str, int]])],
)


def serialize_formula_params_z3(formula_params: FormulaParamsZ3) -> SerializedFormulaParamsZ3:
    return SerializedFormulaParamsZ3(
        serialized_formula=serialize_expression(formula_params.formula),
        serialized_variables=[(str(x), x.size()) for x in formula_params.variables],
    )


def deserialize_formula_params_z3(
    serialized_formula_params: SerializedFormulaParamsZ3,
) -> FormulaParamsZ3:
    return FormulaParamsZ3(
        formula=cast(z3.BoolRef, deserialize_expression(serialized_formula_params.serialized_formula)),
        variables=[z3.BitVec(name, k) for name, k in serialized_formula_params.serialized_variables],
    )
