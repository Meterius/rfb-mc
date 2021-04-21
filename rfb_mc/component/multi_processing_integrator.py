from abc import abstractmethod
from datetime import datetime
from multiprocessing import Lock, Queue, Process
from queue import Empty
from time import perf_counter, sleep
from collections import Counter
from threading import Thread
from typing import Generic, Iterable, Type, TypeVar, Any
from rfb_mc.runner import FormulaParams, RunnerBase
from rfb_mc.integrator import IntegratorBase, IntermediateResult, Result
from rfb_mc.scheduler import SchedulerBase
from rfb_mc.types import Params, RfBmcTask

SerializedFormulaParams = TypeVar("SerializedFormulaParams")


class MultiProcessingIntegratorBase(
    Generic[IntermediateResult, Result, FormulaParams, SerializedFormulaParams],
    IntegratorBase[IntermediateResult, Result]
):
    """
    Class that implements instantiating runners in created processes thus enabling parallel
    execution of scheduler tasks on multiple CPU cores.

    Class is abstract since the runner that is used must be specified and it must be specified how the formula params
    are serialized to enable them being transferred using the python multiprocessing process arguments.
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

    @classmethod
    @abstractmethod
    def serialize_formula_params(cls, formula_params: FormulaParams) -> SerializedFormulaParams:
        """
        Returns a serialized version of the formula params that can be transferred
        via multiprocessing process arguments.
        """
        raise NotImplementedError()

    @classmethod
    @abstractmethod
    def deserialize_formula_params(cls, serialized_formula_params: SerializedFormulaParams) -> FormulaParams:
        """
        Returns formula params from the serialized formula params.
        """
        raise NotImplementedError()

    @classmethod
    def _run_worker(
        cls,
        worker_idx: int,
        worker_count: int,
        stdio_lock: Lock,
        task_queue: Queue,
        result_queue: Queue,
        params: Params,
        serialized_formula_params: FormulaParams,
    ):
        worker_number = worker_idx + 1

        def print_debug(*messages: Iterable[str]):
            """
            Print debug version that ensures only one source is writing to the standard input output at a time
            """

            # PRINT_DEBUG is checked because even tough it is already enforced in _print_debug,
            # using it here will prevent the lock from being acquired as it would waste time if
            # printing is not used
            if cls.PRINT_DEBUG:
                with stdio_lock:
                    cls._print_debug(
                        *[f"Worker[{worker_number}/{worker_count}]: {message}" for message in messages],
                    )

        runner = cls.get_runner_class()(
            params=params,
            formula_params=cls.deserialize_formula_params(serialized_formula_params),
        )

        print_debug("Initialized")

        # retrieve and execute tasks, until the queued task is None,
        # which the integrator puts if it has finished

        task = task_queue.get()

        while task is not None:
            s = perf_counter()
            result = runner.rf_bmc(task)
            result_queue.put((task, result))
            print_debug(f"Ran {task} returning {result} which took {perf_counter() - s:.3f} seconds")

            task = task_queue.get()

    def __init__(self, formula_params: FormulaParams, worker_count: int):
        super().__init__(formula_params)
        self.worker_count = worker_count

    def run(self, scheduler: SchedulerBase):
        task_queue = Queue()
        result_queue = Queue()
        stdio_lock = Lock()

        def print_debug(*messages: Iterable[str]):
            # same as for the workers
            if self.PRINT_DEBUG:
                with stdio_lock:
                    self._print_debug(
                        *[f"Integrator: {message}" for message in messages]
                    )

        print_debug("Starting integrator run")

        processes = [
            Process(
                target=self._run_worker,
                kwargs={
                    "worker_idx": worker_idx,
                    "worker_count": self.worker_count,
                    "stdio_lock": stdio_lock,
                    "task_queue": task_queue,
                    "result_queue": result_queue,
                    "params": scheduler.store.data.params,
                    "serialized_formula_params": self.serialize_formula_params(self.formula_params),
                },
                daemon=True,
            ) for worker_idx in range(self.worker_count)
        ]

        for process in processes:
            process.start()

        s1 = perf_counter()

        try:
            tasks_in_progress: Counter[RfBmcTask] = Counter()

            algorithm_generator = scheduler.run()
            prev_intermediate_result = None

            try:
                # execute tasks until the algorithm stops the iteration thus indicating the final result
                while True:
                    # execute an algorithm step
                    algorithm_yield = next(algorithm_generator)

                    # if the intermediate result has changed, it should be published via a yield
                    if algorithm_yield.intermediate_result != prev_intermediate_result:
                        prev_intermediate_result = algorithm_yield.intermediate_result

                        print_debug(f"Intermediate Result: {prev_intermediate_result}")

                        yield prev_intermediate_result

                    # determine how many tasks should be queued, by first considering what tasks
                    # are not yet in progress and how many idle workers exist
                    required_tasks = algorithm_yield.required_tasks - tasks_in_progress
                    idle_workers = self.worker_count - sum(tasks_in_progress.values())
                    tasks_to_queue = min(sum(required_tasks.values()), idle_workers)

                    # TODO: consider queueing predicted tasks if workers are idle and no additional required tasks exist

                    # queue as many tasks as are available and can be directly forwarded to an idle worker
                    if tasks_to_queue > 0:
                        for _ in range(tasks_to_queue):
                            task = [task for task, count in required_tasks.items() if count > 0][0]

                            required_tasks -= Counter([task])
                            tasks_in_progress += Counter([task])
                            task_queue.put(task)

                    # if tasks are in progress we wait until a result is available, since either all workers are
                    # processing or no more tasks are available until existing tasks have been finished
                    if sum(tasks_in_progress.values()) > 0:
                        # waits for at least one result and if multiple are available, retrieves all
                        task_results = []
                        task_result = result_queue.get()
                        while task_result is not None:
                            task_results.append(task_result)

                            try:
                                task_result = result_queue.get_nowait()
                            except Empty as err:
                                task_result = None

                        # add all results to the store
                        Thread(
                            target=scheduler.store.add_rf_bmc_results,
                            kwargs={
                                "task_results": task_results,
                            },
                        ).start()

                        # switch thread to allow adding results to store before executing next algorithm iteration,
                        # thus the synchronous part of the add_rf_bmc_results function will execute before the algorithm
                        # is continued
                        sleep(0)

                        # remove accomplished tasks from in progress counter
                        for task, result in task_results:
                            tasks_in_progress -= Counter([task])
            except StopIteration as err:
                d1 = perf_counter() - s1
                print_debug(f"Running schedulers tasks until result was available took {d1:.2f} seconds")
                print_debug(f"Result: {err.value}")

                return err.value
        finally:
            for process in processes:
                process.terminate()
