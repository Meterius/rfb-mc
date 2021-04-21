from typing import Generic
from rfb_mc.component.direct_integrator import DirectIntegratorBase, IntermediateResult, Result
from rfb_mc.component.runner_z3 import RunnerZ3, FormulaParamsZ3


class DirectIntegratorZ3(
    Generic[IntermediateResult, Result],
    DirectIntegratorBase[IntermediateResult, Result, FormulaParamsZ3]
):
    @classmethod
    def get_runner_class(cls):
        return RunnerZ3
