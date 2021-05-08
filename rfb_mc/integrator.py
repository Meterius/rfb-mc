from abc import abstractmethod, ABC
from typing import Generator
from rfb_mc.scheduler import Scheduler, IntermediateResult, Result


class Integrator(ABC):
    @abstractmethod
    def run(self, scheduler: Scheduler[IntermediateResult, Result]) -> Generator[IntermediateResult, None, Result]:
        """
        Runs the scheduler algorithm and orchestrates runners to execute the tasks that are required for
        its completion. Thus this runs the scheduler algorithm and only returns the intermediate results and the end
        result.
        """

        raise NotImplementedError()

    def run_all(self, scheduler: Scheduler[IntermediateResult, Result]) -> Result:
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
