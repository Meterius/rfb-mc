from abc import ABC, abstractmethod
from typing import Dict, Counter, Iterable, Tuple
from dataclasses import dataclass, field
from rfb_mc.types import Params, RfBmcTask, RfBmcResult
from threading import Lock


@dataclass
class StoreData:
    # general and problem specific parameter for the hash based model counting framework
    params: Params
    # results from hashed bounded model counting calls
    rf_bmc_results_map: Dict[RfBmcTask, Counter[RfBmcResult]] = field(default_factory=dict)


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
    def _add_rf_bmc_results(self, task_results: Iterable[Tuple[RfBmcTask, RfBmcResult]]):
        """
        Should implement adding the results and synchronizing the external store.
        """

        raise NotImplementedError()

    def add_rf_bmc_results(self, task_results: Iterable[Tuple[RfBmcTask, RfBmcResult]]):
        """
        Adds a result of a rf bmc call to the data.
        Based on the store implementation this operation should also
        synchronize with the storage location.

        (Possibly causes a blocking operation)
        """
        with self.data_lock:
            for task, result in task_results:
                if task not in self.data.rf_bmc_results_map:
                    self.data.rf_bmc_results_map[task] = Counter[RfBmcResult]()

                self.data.rf_bmc_results_map[task][result] += 1

        self._add_rf_bmc_results(task_results)
