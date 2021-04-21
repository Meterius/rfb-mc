from typing import Generic
from rfb_mc.component.multi_processing_integrator import MultiProcessingIntegratorBase, \
    IntermediateResult, Result
from rfb_mc.component.runner_z3 import RunnerZ3, FormulaParamsZ3, \
    serialize_formula_params_z3, deserialize_formula_params_z3, SerializedFormulaParamsZ3


class MultiProcessingIntegratorZ3(
    Generic[IntermediateResult, Result],
    MultiProcessingIntegratorBase[IntermediateResult, Result, FormulaParamsZ3, SerializedFormulaParamsZ3]
):
    @classmethod
    def get_runner_class(cls):
        return RunnerZ3

    @classmethod
    def deserialize_formula_params(cls, serialized_formula_params: SerializedFormulaParamsZ3) -> FormulaParamsZ3:
        return deserialize_formula_params_z3(serialized_formula_params)

    @classmethod
    def serialize_formula_params(cls, formula_params: FormulaParamsZ3) -> SerializedFormulaParamsZ3:
        return serialize_formula_params_z3(formula_params)
