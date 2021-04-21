from fractions import Fraction
from math import sqrt, log2, ceil, floor, log
from collections import Counter

from rfb_mc.component.cdm.xor_rfm import XorRfm, XorParams
from rfb_mc.scheduler import SchedulerBase
from rfb_mc.store import StoreBase
from rfb_mc.types import RfBmcTask


class CdmScheduler(SchedulerBase[None, float, XorRfm]):
    def __init__(
        self,
        store: StoreBase,
        confidence: Fraction,
        a: int,
        q: int,
    ):
        super().__init__(store, XorRfm)

        assert a >= 1, "a >= 1"
        assert q >= 1, "q >= 1"
        assert 0 <= confidence < 1, "Confidence is < 1 and >= 0"

        self.confidence: Fraction = confidence
        self.a: int = a
        self.q: int = q

    def _run_algorithm_once(self):
        n = sum([
            bit_width * count for bit_width, count in self.store.data.params.bit_width_counter.items()
        ]) * self.q

        g = (sqrt(self.a + 1) - 1) ** 2
        G = (sqrt(self.a + 1) + 1) ** 2

        beta = 1 - self.confidence

        mp = int(floor(n - log2(G)))
        p = int(ceil(g ** (1 / self.q)))
        r = int(ceil(8 * log((1 / beta) * mp)))

        # TODO: implement bounded model count for case mc <= p

        m = 1

        while m < mp:
            while True:
                task = RfBmcTask(
                    rfm_guid=self.rf_module.get_guid(),
                    rfm_formula_params=XorParams(
                        m=m,
                    ),
                    a=self.a,
                    q=self.q,
                )
                results = self.store.data.rf_bmc_results_map.get(task, Counter())
                result_count = sum(results.values())

                if result_count < r:
                    yield SchedulerBase.AlgorithmYield(
                        required_tasks=Counter([task] * (r - result_count)),
                        predicted_required_tasks=Counter(),
                        intermediate_result=None,
                    )
                else:
                    positive_votes = sum([
                        count for result, count in results.items() if result.bmc is None
                    ])
                    break

            if positive_votes <= result_count / 2:
                break

            m += 1

        return (self.a * 2 ** (m - 0.5)) ** (1 / self.q)

    def _run_algorithm(self):
        yield from self._run_algorithm_once()
        # second iteration ensures updated results are used
        return (yield from self._run_algorithm_once())
