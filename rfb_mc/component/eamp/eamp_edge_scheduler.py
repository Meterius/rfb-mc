from fractions import Fraction
from math import sqrt, prod, log2, ceil, floor, log
from typing import NamedTuple, Tuple, Optional, Iterable, List
from collections import Counter
from rfb_mc.component.eamp.primes import get_pj
from rfb_mc.component.eamp.eamp_rfm import EampRfm, EampParams, EampTransformMethod
from rfb_mc.component.eamp.utility import multi_majority_vote_iteration_count_to_ensure_beta, \
    majority_vote_error_probability, probability_of_correctness
from rfb_mc.scheduler import SchedulerBase
from rfb_mc.store import StoreBase
from rfb_mc.types import RfBmcTask, RfBmcResult

EampEdgeInterval = NamedTuple("EampEdgeInterval", [
    ("interval", Tuple[int, int]),
    ("confidence", Fraction),
])


class EampEdgeScheduler(SchedulerBase[EampEdgeInterval, EampEdgeInterval, EampRfm]):
    def __init__(
        self,
        store: StoreBase,
        confidence: Fraction,
        a: int,
        q: int,
        min_model_count: Optional[int] = None,
        max_model_count: Optional[int] = None,
    ):
        super().__init__(store, EampRfm)

        assert a >= 1, "a >= 1"
        assert q >= 1, "q >= 1"
        assert 0 <= confidence < 1, "Confidence is < 1 and >= 0"

        self.confidence: Fraction = confidence
        self.a: int = a
        self.q: int = q
        self.max_model_count: int = max_model_count if max_model_count is not None else prod([
            2 ** (bit_width * count) for bit_width, count in self.store.data.params.bit_width_counter.items()
        ])
        self.min_model_count: int = min_model_count if min_model_count is not None else 0

    def _run_algorithm_once(self):
        if self.max_model_count == 0:
            return EampEdgeInterval(interval=(0, 0), confidence=Fraction(1))

        g, lg = self.get_g_and_lg(self.a)

        cn = max(int(floor(log2(log2(self.max_model_count ** self.q / lg) + 1) + 1)), 1)

        p = tuple([
            get_pj(j) for j in range(cn)
        ])

        beta = 1 - self.confidence

        # maximum amount of values that need to be iterated for c[0]
        max_c0 = int(ceil(max([
            log2(p[i] / prod([p[j] for j in range(1, i)]))
            for i in range(1, cn)
        ]))) - 1 if cn > 1 else 1

        # maximum amount of expected majority vote counting procedures
        max_majority_vote_countings = cn - 1 + max_c0

        # probability that an estimate call returns the less likely result
        alpha = Fraction(1, 4)

        r = multi_majority_vote_iteration_count_to_ensure_beta(
            alpha,
            beta,
            max_majority_vote_countings,
        )

        def make_eamp_params(c: Iterable[int]):
            return EampParams(
                c=tuple(c),
                p=p,
                transform_method=EampTransformMethod.SORTED_ROLLING_WINDOW,
            )

        def make_rf_bmc_task(eamp_params: EampParams):
            return RfBmcTask(
                rfm_guid=self.rf_module.get_guid(),
                rfm_formula_params=eamp_params,
                a=self.a,
                q=self.q,
            )

        def range_size(c: Iterable[int]):
            return self.rf_module.get_restrictive_formula_properties(
                self.store.data.params, make_eamp_params(c),
            ).range_size

        def pre_estimate(c: List[int]) -> Optional[bool]:
            if self.max_model_count ** self.q < range_size(c) * lg:
                return False
            elif self.min_model_count ** self.q > range_size(c) * g:
                return True
            elif c_neg is not None and range_size(c_neg) <= range_size(c):
                return False
            elif c_pos is not None and range_size(c) <= range_size(c_pos):
                return True
            else:
                return None

        c_pos: Optional[List[int]] = None

        c_neg: Optional[List[int]] = None

        # error probability of the independent probabilistic execution that have occurred
        error_probabilities: List[Fraction] = []

        min_model_count = self.min_model_count
        max_model_count = self.max_model_count

        def get_edge_interval():
            if c_pos is not None:
                lower_bound = int(floor(max(float(min_model_count), (range_size(c_pos) * g) ** (1 / self.q))))
            else:
                lower_bound = min_model_count

            if c_neg is not None:
                upper_bound = int(ceil(min(float(max_model_count), (range_size(c_neg) * lg) ** (1 / self.q))))
            else:
                upper_bound = max_model_count

            return EampEdgeInterval(
                interval=(lower_bound, upper_bound),
                confidence=probability_of_correctness(error_probabilities),
            )

        def majority_vote_estimate(c: List[int]):
            while True:
                rf_bmc_task = make_rf_bmc_task(make_eamp_params(c))

                # copies the required results data in order for it not to be modified while using them
                rf_bmc_results: Counter[RfBmcResult] = \
                    self.store.data.rf_bmc_results_map.get(rf_bmc_task, Counter()).copy()

                positive_voters = sum([
                    count
                    for result, count in rf_bmc_results.items()
                    if result.bmc is None
                ])

                negative_voters = sum([
                    count
                    for result, count in rf_bmc_results.items()
                    if result.bmc is not None
                ])

                remaining = max(0, r - (positive_voters + negative_voters))

                if positive_voters >= negative_voters and positive_voters >= negative_voters + remaining:
                    r_eff = positive_voters + negative_voters + abs(negative_voters - positive_voters)
                    return True, majority_vote_error_probability(alpha, r_eff)

                if negative_voters > positive_voters and negative_voters > positive_voters + remaining:
                    r_eff = positive_voters + negative_voters + abs(negative_voters - positive_voters)
                    return False, majority_vote_error_probability(alpha, r_eff)

                yield EampEdgeScheduler.AlgorithmYield(
                    required_tasks=Counter(remaining * [rf_bmc_task]),
                    predicted_required_tasks=Counter(),
                    intermediate_result=get_edge_interval(),
                )

        c = [0] * (cn - 1) + [1]
        j = cn - 1

        while True:
            while pre_estimate(c) is False and j != 0:
                c[j] = 0
                c[j - 1] = 1
                j -= 1

            if pre_estimate(c) is False and j == 0:
                break

            mv_estimate, mv_error_prob = yield from majority_vote_estimate(c)
            error_probabilities.append(mv_error_prob)

            if mv_estimate:
                c_pos = c.copy()

                if j == 0:
                    c[j] += 1
                else:
                    c[j - 1] = 1
                    j -= 1
            else:
                c_neg = c.copy()

                if j == 0:
                    break
                else:
                    c[j] = 0
                    c[j - 1] = 1
                    j -= 1

        # TODO: implement BMC tasks and catch case of c_pos = None

        return get_edge_interval()

    def _run_algorithm(self):
        yield from self._run_algorithm_once()
        # second iteration ensures updated results are used
        return (yield from self._run_algorithm_once())

    @staticmethod
    def get_g_and_lg(a: int) -> Tuple[float, float]:
        """
        Returns the internal parameters g and G for the given a.
        """

        return (sqrt(a + 1) - 1) ** 2, (sqrt(a + 1) + 1) ** 2

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
    def get_upper_bound_for_multiplicative_gap_of_result(a: int, q: int) -> float:
        """
        Returns an upper bound on the multiplicative gap of the final edge interval returned
        by the eamp edge scheduler.
        """

        g, lg = EampEdgeScheduler.get_g_and_lg(a)
        return (2 * lg / g) ** (1 / q)
