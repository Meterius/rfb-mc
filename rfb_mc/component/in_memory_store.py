from typing import Iterable, Tuple, Optional
from rfb_mc.store import Store
from rfb_mc.types import RfBmcTask, RfBmcResult, BmcTask, BmcResult


class InMemoryStore(Store):
    """
    Only stores in memory
    """

    def sync(self):
        pass

    def _add_results(
        self,
        bmc_task_result: Optional[Tuple[BmcTask, BmcResult]],
        rf_bmc_task_results: Iterable[Tuple[RfBmcTask, RfBmcResult]],
    ):
        pass
