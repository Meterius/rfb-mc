from fractions import Fraction
from functools import lru_cache
from math import sqrt, prod, log2, ceil, floor, log
from typing import Tuple, Optional, List, Union
from rfb_mc.component.eamp.eamp_edge_scheduler_base import EampEdgeSchedulerBase
from rfb_mc.component.eamp.primes import get_lowest_prime_above_or_equal_power_of_power_of_two
from rfb_mc.component.eamp.eamp_rfm import EampParams, EampTransformMethod
from rfb_mc.store import Store


class EampEdgeScheduler(EampEdgeSchedulerBase[Tuple[int, List[int]]]):
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

    @lru_cache(1)
    def _get_upper_bound_on_estimate_iteration_count(self) -> int:
        # maximum amount of values that need to be iterated for c[0]
        max_c0 = int(ceil(max([
            log2(self._p[i] / prod([self._p[j] for j in range(1, i)]))
            for i in range(1, self._cn)
        ]))) - 1 if self._cn > 1 else 1

        # maximum amount of required estimate iterations
        return self._cn - 1 + max_c0

    @lru_cache(1)
    def _get_required_minimal_min_model_count_when_no_lower_bound_could_be_established(self):
        return int(ceil(self.g ** (1 / self.q)))

    def _make_eamp_params(self, partial_eamp_params: Tuple[int, List[int]]) -> EampParams:
        j, c = partial_eamp_params

        return EampParams(
            p=self._p,
            c=tuple(c),
            transform_method=EampTransformMethod.SORTED_ROLLING_WINDOW,
        )

    def _make_initial_partial_eamp_params(self) -> Tuple[int, List[int]]:
        return self._cn - 1, [0] * (self._cn - 1) + [1]

    def _advance_partial_eamp_params(
        self,
        partial_eamp_params: Tuple[int, List[int]],
        estimate_result: bool
    ) -> Optional[Tuple[int, List[int]]]:
        j, c = partial_eamp_params
        c_next = c.copy()

        if estimate_result is True:
            if j == 0:
                c_next[0] += 1
                return 0, c_next
            else:
                c_next[j - 1] = 1
                return j - 1, c_next
        else:
            if j == 0:
                return None
            else:
                c_next[j] = 0
                c_next[j - 1] = 1
                return j - 1, c_next

    @staticmethod
    def get_q_for_fixed_a_that_ensures_upper_bound_for_multiplicative_gap_of_result(
        a: int,
        epsilon: float,
    ) -> int:
        """
        Returns the minimal parameter q that ensures that for the given a we have,
        get_upper_bound_for_multiplicative_gap_of_result(a, q) <= (1 + epsilon) ** 2.
        That condition is equivalent to the statement that the geometric mean of the final edge interval
        is a multiplicative approximation with error epsilon i.e.
        model_count / (1 + epsilon) <= geometric_mean <= model_count * (1 + epsilon).
        """

        g, lg = EampEdgeScheduler.get_g_and_lg(a)
        return int(ceil(0.5 * log(2 * lg / g, 1 + epsilon)))

    @staticmethod
    def get_a_for_fixed_q_that_ensures_upper_bound_for_multiplicative_gap_of_result(
        q: int,
        epsilon: float,
    ) -> int:
        """
        Returns the minimal parameter a that ensures that for the given q we have,
        get_upper_bound_for_multiplicative_gap_of_result(a, q) <= (1 + epsilon) ** 2.
        That condition is equivalent to the statement that the geometric mean of the final edge interval
        is a multiplicative approximation with error epsilon i.e.
        model_count / (1 + epsilon) <= geometric_mean <= model_count * (1 + epsilon).
        """

        if 2 ** (1 / q) >= (1 + epsilon) ** 2:
            raise ValueError(f"For epsilon={epsilon} and q={q} "
                             f"i.e. (1 + epsilon) ** 2 = {(1 + epsilon) ** 2}, higher a "
                             f"values will only be able to converge to {2 ** (1 / q)} thus epsilon "
                             f"{sqrt(2 ** (1 / q)) - 1}")

        # TODO: replace by proper formula
        a = 1
        while EampEdgeScheduler.get_upper_bound_for_multiplicative_gap_of_result(a, q) > (1 + epsilon) ** 2:
            a += 1

        return a

    @staticmethod
    def get_upper_bound_for_multiplicative_gap_of_result(a: int, q: int) -> float:
        """
        Returns an upper bound on the multiplicative gap of the final edge interval returned
        by the eamp edge scheduler.
        """

        g, lg = EampEdgeScheduler.get_g_and_lg(a)
        return (2 * lg / g) ** (1 / q)
