from abc import abstractmethod
from datetime import datetime
from time import perf_counter, sleep
from typing import Generic, Iterable, Type, Any
from rfb_mc.runner import FormulaParams, RunnerBase
from rfb_mc.integrator import IntegratorBase, IntermediateResult, Result
from rfb_mc.scheduler import SchedulerBase
from threading import Thread


class DirectIntegratorBase(
    Generic[IntermediateResult, Result, FormulaParams],
    IntegratorBase[IntermediateResult, Result]
):
    """
    Class that implements instantiating runners directly.

    Class is abstract since the runner that is used must be specified.
    """

    # whether the integrator should print debug information
    PRINT_DEBUG: bool = True

    @classmethod
    def _print_debug(cls, *messages: Iterable[str]):
        """ Timestamped version of print that only prints if PRINT_DEBUG is True """
        if cls.PRINT_DEBUG:
            for message in messages:
                print(f"[{datetime.now().strftime('%H:%M:%S:%f')}] {message}")

    @classmethod
    @abstractmethod
    def get_runner_class(cls) -> Type[RunnerBase[FormulaParams, Any, Any]]:
        """
        Returns class used for the runner in worker processes.
        """
        raise NotImplementedError()

    def __init__(self, formula_params: FormulaParams):
        super().__init__(formula_params)

    def run(self, scheduler: SchedulerBase):
        runner = self.get_runner_class()(
            params=scheduler.store.data.params,
            formula_params=self.formula_params,
        )

        algorithm_generator = scheduler.run()
        prev_intermediate_result = None

        s1 = perf_counter()

        try:
            # execute tasks until the algorithm stops the iteration thus indicating the final result
            while True:
                # execute an algorithm step
                algorithm_yield = next(algorithm_generator)

                # if the intermediate result has changed, it should be published via a yield
                if algorithm_yield.intermediate_result != prev_intermediate_result:
                    prev_intermediate_result = algorithm_yield.intermediate_result
                    yield prev_intermediate_result

                if sum(algorithm_yield.required_tasks.values()) > 0:
                    task = next(algorithm_yield.required_tasks.elements())

                    s = perf_counter()
                    result = runner.rf_bmc(task)
                    self._print_debug(f"Ran {task} returning {result} which took {perf_counter() - s:.3f} seconds")

                    # starts result synchronization with store asynchronously
                    Thread(
                        target=scheduler.store.add_rf_bmc_results,
                        kwargs={
                          "task_results": [(task, result)],
                        },
                        daemon=True,
                    ).start()

                    # switch thread to allow adding results to store before executing next algorithm iteration,
                    # thus the synchronous part of the add_rf_bmc_results function will execute before the algorithm
                    # is continued
                    sleep(0)
        except StopIteration as err:
            d1 = perf_counter() - s1
            self._print_debug(f"Running scheduler tasks until result was available took {d1:.2f} seconds")
            self._print_debug(f"Result: {err.value}")

            return err.value
