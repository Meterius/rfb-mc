from typing import Type
from rfb_mc.component.direct_integrator import DirectIntegrator
from rfb_mc.component.runner_z3 import RunnerZ3, FormulaParamsZ3


class DirectIntegratorZ3(DirectIntegrator[FormulaParamsZ3]):
    @classmethod
    def get_runner_class(cls) -> Type[RunnerZ3]:
        return RunnerZ3
