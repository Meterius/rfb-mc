from typing import Iterable, Tuple
from rfb_mc.store import StoreBase
from rfb_mc.types import RfBmcTask, RfBmcResult, BmcTask, BmcResult


class InMemoryStore(StoreBase):
    """
    Only stores in memory
    """

    def sync(self):
        pass

    def _add_results(
        self,
        bmc_task_results: Iterable[Tuple[BmcTask, BmcResult]],
        rf_bmc_task_results: Iterable[Tuple[RfBmcTask, RfBmcResult]],
    ):
        pass
