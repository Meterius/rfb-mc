from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Counter, Generic, TypeVar, Generator, Type
from rfb_mc.store import StoreBase
from rfb_mc.restrictive_formula_module import RestrictiveFormulaModuleBase
from rfb_mc.types import RfBmcTask

IntermediateResult = TypeVar("IntermediateResult")

Result = TypeVar("Result")

RestrictiveFormulaModule = TypeVar("RestrictiveFormulaModule", bound=RestrictiveFormulaModuleBase)


class SchedulerBase(ABC, Generic[IntermediateResult, Result, RestrictiveFormulaModule]):
    @dataclass
    class AlgorithmYield:
        required_tasks: Counter[RfBmcTask]
        predicted_required_tasks: Counter[RfBmcTask]
        intermediate_result: IntermediateResult

    def __init__(self, store: StoreBase, rf_module: Type[RestrictiveFormulaModule]):
        self.store = store
        self.rf_module = rf_module

    @abstractmethod
    def _run_algorithm(self) -> Generator[AlgorithmYield, None, Result]:
        """
        Generator function that yields algorithm step results and will
        return the desired result. It is expected to be deterministic and
        only use information from the store without running anything itself.

        Each generator instance should be completely independent of one another.
        """

        raise NotImplementedError()

    def run(self) -> Generator[AlgorithmYield, None, Result]:
        """
        Runs the scheduler algorithm and yields intermediate results and tasks required for
        continuing the algorithm. Note that the required tasks are only relevant to an individual step i.e.
        executing all of them will not guarantee the algorithm can complete. But continuously running the required
        tasks will mean that it will eventually complete. At which point it will return the result.
        """

        return self._run_algorithm()
