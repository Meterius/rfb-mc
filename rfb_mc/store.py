from abc import ABC, abstractmethod
from typing import Dict, Counter, Iterable, Tuple, Optional, cast, Union
from dataclasses import dataclass, field
from rfb_mc.types import Params, RfBmcTask, RfBmcResult, BmcResult, BmcTask
from threading import Lock


@dataclass
class StoreData:
    # general and problem specific parameter for the hash based model counting framework
    params: Params
    # results from hashed bounded model counting calls
    rf_bmc_results_map: Dict[RfBmcTask, Counter[RfBmcResult]] = field(default_factory=dict)
    # result from the bounded model count with the highest parameter for "a"
    bmc_task_result: Optional[Tuple[BmcTask, BmcResult]] = None


class StoreBase(ABC):
    def __init__(self, data: StoreData):
        self.data = data
        self.data_lock = Lock()

    @abstractmethod
    def sync(self):
        """
        Synchronizes the memory with the storage location
        used by the store implementation.

        (Possibly causes a blocking operation)
        """

        raise NotImplementedError()

    @abstractmethod
    def _add_results(
        self,
        bmc_task_result: Optional[Tuple[BmcTask, BmcResult]],
        rf_bmc_task_results: Iterable[Tuple[RfBmcTask, RfBmcResult]],
    ):
        """
        Should implement adding the results and synchronizing the external store.
        """

        raise NotImplementedError()

    def add_results(self, task_results: Iterable[Union[Tuple[RfBmcTask, RfBmcResult], Tuple[BmcTask, BmcResult]]]):
        """
        Adds a result of a rf bmc call to the data.
        Based on the store implementation this operation should also
        synchronize with the storage location.

        (Possibly causes a blocking operation)
        """

        bmc_task_results: Iterable[Tuple[BmcTask, BmcResult]] = [
            cast(Tuple[BmcTask, BmcResult], task_result) for task_result in task_results
            if isinstance(task_result[0], BmcTask)
        ]

        rf_bmc_task_results: Iterable[Tuple[RfBmcTask, RfBmcResult]] = [
            cast(Tuple[RfBmcTask, RfBmcResult], task_result) for task_result in task_results
            if isinstance(task_result[0], RfBmcTask)
        ]

        # only bmc task result with highest "a" value can possibly be set
        bmc_task_result = max(bmc_task_results, key=lambda task_result: task_result[0].a, default=None)

        with self.data_lock:
            for task, result in rf_bmc_task_results:
                if task not in self.data.rf_bmc_results_map:
                    self.data.rf_bmc_results_map[task] = Counter[RfBmcResult]()

                self.data.rf_bmc_results_map[task][result] += 1

            if self.data.bmc_task_result is None or self.data.bmc_task_result[0].a <= bmc_task_result[0].a:
                self.data.bmc_task_result = bmc_task_result

        self._add_results(bmc_task_result, rf_bmc_task_results)
