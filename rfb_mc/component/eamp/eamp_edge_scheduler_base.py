from abc import abstractmethod
from fractions import Fraction
from math import sqrt, prod, ceil, floor
from typing import Tuple, Optional, Union, Generic, TypeVar, List, Counter
from rfb_mc.component.eamp.eamp_rfm import EampParams, EampRfm
from rfb_mc.component.eamp.types import ProbabilisticInterval
from rfb_mc.component.eamp.utility import majority_vote_error_probability, \
    multi_majority_vote_iteration_count_to_ensure_beta, probability_of_correctness
from rfb_mc.scheduler import Scheduler, SchedulerAlgorithmYield
from rfb_mc.store import Store
from rfb_mc.types import RfBmcTask, RfBmcResult, BmcTask, BmcResult

PartialEampParams = TypeVar("PartialEampParams")


class EampEdgeSchedulerBase(Generic[PartialEampParams], Scheduler[ProbabilisticInterval, ProbabilisticInterval]):
    def __init__(
        self,
        store: Store,
        confidence: Union[Fraction, float],
        a: int,
        q: int,
        min_model_count: Optional[int] = None,
        max_model_count: Optional[int] = None,
    ):
        super().__init__(store)

        # amount of models that are at most possible for a formula having the amount of bits specified
        theoretical_max_model_count = prod([
            2 ** (bit_width * amount) for bit_width, amount in store.data.params.bit_width_counter.items()
        ])

        assert 0 <= confidence < 1, "Parameter 'confidence' is at least 0 and less than 1"
        assert 1 <= a, "Parameter 'a' is at least 1"
        assert 1 <= q, "Parameter 'q' is at least 1"
        assert min_model_count is None or 0 <= min_model_count, "Parameter 'min_model_count' is at least 0"
        assert min_model_count is None or max_model_count is None or min_model_count <= max_model_count, \
            "Parameter 'min_model_count' is less than or equal parameter 'max_model_count'"
        assert min_model_count is None or min_model_count <= theoretical_max_model_count, \
            "Parameter 'min_model_count' is less than or equal the theoretical maximal model count of the formula," \
            " i.e. 2**(amount of bits in variables)"

        self.min_model_count: int = min_model_count if min_model_count is not None else 0
        self.max_model_count: int = \
            min(max_model_count, theoretical_max_model_count) if max_model_count is not None \
            else theoretical_max_model_count

        self.a: int = a
        self.q: int = q
        self.confidence: Fraction = Fraction(confidence)
        self.store: Store = store

        g, lg = EampEdgeSchedulerBase.get_g_and_lg(a)
        self.g: float = g
        self.lg: float = lg

    @abstractmethod
    def _get_upper_bound_on_estimate_iteration_count(self) -> int:
        """
        Returns an upper bound on the necessary amount of majority vote counting estimate calls that
        will need to be performed.
        """
        
        raise NotImplementedError()

    @abstractmethod
    def _get_required_minimal_min_model_count_when_no_lower_bound_could_be_established(self) -> int:
        """
        Returns the minimal min_model_count required to ensure that, if estimate never responded with True,
        the lower bound, established by min_model_count, will satisfy the multiplicative gap constraints on
        the final interval.
        """

        raise NotImplementedError()

    @abstractmethod
    def _make_eamp_params(self, partial_eamp_params: PartialEampParams) -> EampParams:
        raise NotImplementedError()

    @abstractmethod
    def _make_initial_partial_eamp_params(self) -> PartialEampParams:
        """
        Returns the initial partial eamp parameters with which the algorithm will
        start the estimate iterations.
        """

        raise NotImplementedError()

    @abstractmethod
    def _advance_partial_eamp_params(
        self,
        partial_eamp_params: PartialEampParams,
        estimate_result: bool
    ) -> Optional[PartialEampParams]:
        """
        Returns the next partial eamp parameters as a response to the estimate result.
        If the return value is None, it is assumed the iteration procedure has finished.
        """

        raise NotImplementedError()

    def _range_size(self, partial_eamp_params: Union[PartialEampParams, EampParams]) -> int:
        """
        Returns range size of the given eamp params.
        """

        return EampRfm.get_restrictive_formula_properties(
            self.store.data.params,
            partial_eamp_params if isinstance(partial_eamp_params, EampParams)
            else self._make_eamp_params(partial_eamp_params),
        ).range_size

    def _multiplicative_gap(
        self,
        positive_eamp_params: Union[PartialEampParams, EampParams],
        negative_eamp_params: Union[PartialEampParams, EampParams]
    ):
        """
        Returns multiplicative gap of interval given by eamp params that caused a positive and negative estimate result.
        """

        return (
            float(self._range_size(negative_eamp_params)) / float(self._range_size(positive_eamp_params))
            * (self.lg / self.g)
        ) ** (1 / self.q)

    def _run_algorithm_once(self):
        if self.min_model_count == self.max_model_count:
            return ProbabilisticInterval(
                lower_bound=self.min_model_count,
                upper_bound=self.max_model_count,
                confidence=Fraction(1)
            )

        g, lg = EampEdgeSchedulerBase.get_g_and_lg(self.a)
        
        mv_estimate_count_upper_bound = self._get_upper_bound_on_estimate_iteration_count()

        # maximal allowed error probability of the algorithm
        beta = 1 - self.confidence

        r = multi_majority_vote_iteration_count_to_ensure_beta(
            Fraction(1, 4),
            beta,
            mv_estimate_count_upper_bound,
        )

        def make_rf_bmc_task(eamp_params: EampParams):
            return RfBmcTask(
                rfm_guid=EampRfm.get_guid(),
                rfm_formula_params=eamp_params,
                a=self.a,
                q=self.q,
            )

        def pre_estimate(p: PartialEampParams) -> Optional[bool]:
            if self.max_model_count ** self.q < self._range_size(p) * lg:
                return False
            elif self.min_model_count ** self.q > self._range_size(p) * g:
                return True
            elif p_neg is not None and self._range_size(p_neg) <= self._range_size(p):
                return False
            elif p_pos is not None and self._range_size(p) <= self._range_size(p_pos):
                return True
            else:
                return None

        p_pos: Optional[PartialEampParams] = None

        p_neg: Optional[PartialEampParams] = None

        # error probability of the independent probabilistic execution that have occurred
        error_probabilities: List[Fraction] = []

        min_model_count = self.min_model_count
        max_model_count = self.max_model_count

        def get_edge_interval():
            if p_pos is not None:
                lower_bound = max(int(ceil((self._range_size(p_pos) * g) ** (1 / self.q))), min_model_count)
            else:
                lower_bound = min_model_count

            if p_neg is not None:
                upper_bound = min(int(floor((self._range_size(p_neg) * lg) ** (1 / self.q))), max_model_count)
            else:
                upper_bound = max_model_count

            upper_bound = max(lower_bound, upper_bound)

            return ProbabilisticInterval(
                lower_bound=lower_bound,
                upper_bound=upper_bound,
                confidence=probability_of_correctness(error_probabilities),
            )

        def majority_vote_estimate(p: PartialEampParams):
            while True:
                rf_bmc_task = make_rf_bmc_task(self._make_eamp_params(p))

                # copies the required results data in order for it not to be modified while using them
                rf_bmc_results: Counter[RfBmcResult] = \
                    self.store.data.rf_bmc_results_map.get(rf_bmc_task, Counter[RfBmcResult]()).copy()

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
                    return True, majority_vote_error_probability(Fraction(1, 4), r)

                if negative_voters > positive_voters and negative_voters > positive_voters + remaining:
                    return False, majority_vote_error_probability(Fraction(1, 4), r)

                yield SchedulerAlgorithmYield[ProbabilisticInterval](
                    required_tasks=Counter[Union[RfBmcTask, BmcTask]](remaining * [rf_bmc_task]),
                    predicted_required_tasks=Counter[Union[RfBmcTask, BmcTask]](),
                    intermediate_result=get_edge_interval(),
                )

        p = self._make_initial_partial_eamp_params()
        mv_estimate_count = 0

        while True:
            while pre_estimate(p) is False:
                next_p = self._advance_partial_eamp_params(p, False)

                if next_p is None:
                    break
                else:
                    p = next_p

            if pre_estimate(p) is False and self._advance_partial_eamp_params(p, False) is None:
                break

            if mv_estimate_count + 1 > mv_estimate_count_upper_bound and False:
                raise RuntimeError(
                    "Estimate iteration upper bound was incorrect. "
                    "This error is caused by an incorrect implementation "
                    "of _get_upper_bound_on_estimate_iteration_count."
                )
            else:
                mv_estimate_count += 1

            mv_estimate, mv_error_prob = yield from majority_vote_estimate(p)
            error_probabilities.append(mv_error_prob)

            if mv_estimate:
                p_pos = p

                next_p = self._advance_partial_eamp_params(p, True)

                if next_p is None:
                    if p_neg is None:
                        raise RuntimeError(
                            "Iteration procedure cannot be terminated when no negative estimate result has been found. "
                            "This error is caused by an incorrect implementation of _advance_partial_eamp_params."
                        )
                    else:
                        break
                else:
                    p = next_p
            else:
                p_neg = p

                next_p = self._advance_partial_eamp_params(p, False)

                if next_p is None:
                    break
                else:
                    p = next_p

        if p_pos is None:
            s = self._get_required_minimal_min_model_count_when_no_lower_bound_could_be_established()

            if min_model_count < s:
                bmc_task_result: Optional[Tuple[BmcTask, BmcResult]] = self.store.data.bmc_task_result

                while bmc_task_result is None or bmc_task_result[0].a < s:
                    yield SchedulerAlgorithmYield[ProbabilisticInterval](
                        required_tasks=Counter[Union[RfBmcTask, BmcTask]]([BmcTask(a=s)]),
                        predicted_required_tasks=Counter[Union[RfBmcTask, BmcTask]](),
                        intermediate_result=get_edge_interval(),
                    )

                    bmc_task_result = self.store.data.bmc_task_result

                if bmc_task_result[1].bmc is not None and bmc_task_result[1].bmc < s:
                    return ProbabilisticInterval(
                        lower_bound=bmc_task_result[1].bmc,
                        upper_bound=bmc_task_result[1].bmc,
                        confidence=Fraction(1),
                    )
                else:
                    min_model_count = s

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
    @abstractmethod
    def get_upper_bound_for_multiplicative_gap_of_result(a: int, q: int) -> float:
        """
        Returns an upper bound on the multiplicative gap of the final edge interval returned
        by the eamp edge scheduler.
        """

        raise NotImplementedError()
