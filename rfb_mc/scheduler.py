from abc import ABC, abstractmethod
from dataclasses import dataclass
from typing import Counter, Generic, TypeVar, Generator, Union
from rfb_mc.store import Store
from rfb_mc.types import RfBmcTask, BmcTask


IntermediateResult = TypeVar("IntermediateResult")
Result = TypeVar("Result")


@dataclass
class SchedulerAlgorithmYield(Generic[IntermediateResult]):
    required_tasks: Counter[Union[BmcTask, RfBmcTask]]
    predicted_required_tasks: Counter[Union[BmcTask, RfBmcTask]]
    intermediate_result: IntermediateResult


class Scheduler(ABC, Generic[IntermediateResult, Result]):
    def __init__(self, store: Store):
        self.store = store

    @abstractmethod
    def _run_algorithm(self) -> Generator[SchedulerAlgorithmYield[IntermediateResult], None, Result]:
        """
        Generator function that yields algorithm step results and will
        return the desired result. It is expected to be deterministic and
        only use information from the store without running anything itself.

        Each generator instance should be completely independent of one another.
        """

        raise NotImplementedError()

    def run(self) -> Generator[SchedulerAlgorithmYield[IntermediateResult], None, Result]:
        """
        Runs the scheduler algorithm and yields intermediate results and tasks required for
        continuing the algorithm. Note that the required tasks are only relevant to an individual step i.e.
        executing all of them will not guarantee the algorithm can complete. But continuously running the required
        tasks will mean that it will eventually complete. At which point it will return the result.
        """

        return self._run_algorithm()
