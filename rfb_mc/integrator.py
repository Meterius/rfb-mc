from abc import abstractmethod, ABC
from typing import Generator, Generic, Any
from rfb_mc.runner import FormulaParams
from rfb_mc.scheduler import SchedulerBase, IntermediateResult, Result


class IntegratorBase(ABC, Generic[IntermediateResult, Result]):
    def __init__(self, formula_params: FormulaParams):
        self.formula_params = formula_params

    @abstractmethod
    def run(self, scheduler: SchedulerBase[IntermediateResult, Result, Any]) -> Generator[IntermediateResult, None, Result]:
        """
        Runs the scheduler algorithm and orchestrates runners to execute the tasks that are required for
        its completion. Thus this runs the scheduler algorithm and only returns the intermediate results and the end
        result.
        """

        raise NotImplementedError()

    def run_all(self, scheduler: SchedulerBase[IntermediateResult, Result, Any]) -> Result:
        """
        Like run, but will discard intermediate results and thus instead of being a generator this is
        a proper function that will only return the end result.
        """

        run_generator = self.run(scheduler)

        try:
            while True:
                next(run_generator)
        except StopIteration as err:
            return err.value
