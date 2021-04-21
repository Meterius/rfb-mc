from typing import Iterable, Tuple
from rfb_mc.store import StoreBase
from rfb_mc.types import RfBmcTask, RfBmcResult


class InMemoryStore(StoreBase):
    """
    Only stores in memory
    """

    def sync(self):
        pass

    def _add_rf_bmc_results(self, task_results: Iterable[Tuple[RfBmcTask, RfBmcResult]]):
        pass
