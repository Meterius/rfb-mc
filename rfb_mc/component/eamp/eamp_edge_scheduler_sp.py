from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import log2, ceil, floor, prod
from typing import Tuple, Optional, List, Union

from rfb_mc.component.eamp.eamp_edge_scheduler import EampEdgeScheduler
from rfb_mc.component.eamp.eamp_edge_scheduler_base import EampEdgeSchedulerBase
from rfb_mc.component.eamp.eamp_rfm import EampParams, EampTransformMethod, EampRfm
from rfb_mc.component.eamp.primes import get_closest_prime, get_lowest_prime_above_or_equal_power_of_power_of_two
from rfb_mc.store import Store


@dataclass
class EampEdgeSchedulerSPPartialEampParams:
    j: int
    c: List[int]
    p2_lmu: Optional[Tuple[int, int, int]] = None


class EampEdgeSchedulerSP(EampEdgeSchedulerBase[EampEdgeSchedulerSPPartialEampParams]):
    def __init__(
        self,
        store: Store,
        confidence: Union[Fraction, float],
        a: int,
        q: int,
        min_model_count: Optional[int] = None,
        max_model_count: Optional[int] = None,
    ):
        super().__init__(store, confidence, a, q, min_model_count, max_model_count)

        self._cn: int = int(
            floor(log2(log2(self.max_model_count ** self.q / self.lg) + 1) + 1)
        ) if self.max_model_count ** self.q / self.lg >= 1 else 1

        self._p: Tuple[int, ...] = tuple([
            get_lowest_prime_above_or_equal_power_of_power_of_two(j)
            for j in range(self._cn)
        ])

        self._get_closest_prime = lru_cache(get_closest_prime)

    @lru_cache(1)
    def _get_upper_bound_on_estimate_iteration_count(self) -> int:
        return self._cn - 1 + 10  # TODO: replace by correct formula

    @lru_cache(1)
    def _get_required_minimal_min_model_count_when_no_lower_bound_could_be_established(self):
        return int(ceil(self.g ** (1 / self.q)))

    def _make_eamp_params(self, partial_eamp_params: EampEdgeSchedulerSPPartialEampParams) -> EampParams:
        j, c, p2_lmu = partial_eamp_params.j, partial_eamp_params.c, partial_eamp_params.p2_lmu

        if p2_lmu is not None:
            rl, rm, ru = p2_lmu
            return EampParams(p=(rm,), c=(1,), transform_method=EampTransformMethod.SORTED_ROLLING_WINDOW)
        else:
            cp = prod([(2 ** (2 ** i)) ** c[i] for i in range(1, len(c))])
            x = self._get_closest_prime(cp) if cp >= 2 else None

            em_c: Tuple[int, ...]
            em_p: Tuple[int, ...]

            if x is None:
                em_c = (c[0],)
                em_p = (2,)
            elif c[0] == 0:
                em_c = (1,)
                em_p = (x,)
            else:
                em_c = (1, c[0])
                em_p = (x, 2)

            return EampParams(p=em_p, c=em_c, transform_method=EampTransformMethod.SORTED_ROLLING_WINDOW)

    def _make_initial_partial_eamp_params(self) -> EampEdgeSchedulerSPPartialEampParams:
        return EampEdgeSchedulerSPPartialEampParams(
            j=self._cn - 1,
            c=[0] * (self._cn - 1) + [1],
        )

    def _advance_partial_eamp_params(
        self,
        partial_eamp_params: EampEdgeSchedulerSPPartialEampParams,
        estimate_result: bool
    ) -> Optional[EampEdgeSchedulerSPPartialEampParams]:
        j, c, p2_lmu = partial_eamp_params.j, partial_eamp_params.c, partial_eamp_params.p2_lmu

        def range_size(p: EampEdgeSchedulerSPPartialEampParams) -> int:
            return EampRfm.get_restrictive_formula_properties(
                self.store.data.params, self._make_eamp_params(p),
            ).range_size

        if p2_lmu is not None:
            rl, rm, ru = p2_lmu

            rnl = rm if estimate_result else rl
            rnu = ru if estimate_result else rm
            rnm = self._get_closest_prime(int(round(float(rnu + rnl) / 2)), (rnl + 1, rnu - 1))

            if rnm is None or rnm == rm:
                return None

            neg = EampParams(p=(rnu,), c=(1,), transform_method=EampTransformMethod.SORTED_ROLLING_WINDOW)
            mid = EampParams(p=(rnm,), c=(1,), transform_method=EampTransformMethod.SORTED_ROLLING_WINDOW)
            pos = EampParams(p=(rnl,), c=(1,), transform_method=EampTransformMethod.SORTED_ROLLING_WINDOW)

            gap = self._multiplicative_gap(pos, neg) - min(
                self._multiplicative_gap(pos, mid), self._multiplicative_gap(mid, neg)
            )

            if gap < 0.01:
                return None

            return EampEdgeSchedulerSPPartialEampParams(
                j=0,
                c=c.copy(),
                p2_lmu=(rnl, rnm, rnu),
            )
        else:
            c_next = c.copy()

            if estimate_result is True:
                if j == 0:
                    c_next[0] += 1
                    return EampEdgeSchedulerSPPartialEampParams(j=0, c=c_next)
                else:
                    c_next[j - 1] = 1
                    return EampEdgeSchedulerSPPartialEampParams(j=j - 1, c=c_next)
            else:
                if j == 0:
                    ru = range_size(partial_eamp_params)
                    rl = ru // 2
                    rm = self._get_closest_prime(int(round(float(ru + rl) / 2)), (rl + 1, ru - 1))
                    return EampEdgeSchedulerSPPartialEampParams(
                        j=0,
                        c=c.copy(),
                        p2_lmu=(rl, rm, ru),
                    ) if rm is not None else None
                else:
                    c_next[j] = 0
                    c_next[j - 1] = 1
                    return EampEdgeSchedulerSPPartialEampParams(j=j - 1, c=c_next)

    @staticmethod
    def get_upper_bound_for_multiplicative_gap_of_result(a: int, q: int) -> float:
        return EampEdgeScheduler.get_upper_bound_for_multiplicative_gap_of_result(a, q)
