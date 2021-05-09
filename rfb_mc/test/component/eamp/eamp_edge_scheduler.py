import unittest
from abc import ABC, abstractmethod
from time import perf_counter
from typing import Type, Optional, Counter
import z3
from rfb_mc.component.direct_integrator_z3 import DirectIntegratorZ3
from rfb_mc.component.eamp.eamp_edge_scheduler_base import EampEdgeSchedulerBase
from rfb_mc.component.eamp.eamp_rfmi_z3 import EampRfmiZ3
from rfb_mc.component.eamp.types import ProbabilisticInterval
from rfb_mc.component.in_memory_store import InMemoryStore
from rfb_mc.component.runner_z3 import FormulaParamsZ3, RunnerZ3
from rfb_mc.store import StoreData
from rfb_mc.test.helper import count_models_by_branching
from rfb_mc.types import Params

RUN_MINI_BENCHMARK = True


class EampEdgeSchedulerTestCaseBase(ABC):
    @abstractmethod
    def get_test_case(self) -> unittest.TestCase:
        raise NotImplementedError()

    @abstractmethod
    def get_eamp_edge_scheduler_class(self) -> Type[EampEdgeSchedulerBase]:
        raise NotImplementedError()

    def assert_eamp_edge_scheduler_result(
        self,
        interval: ProbabilisticInterval,
        a: int,
        q: int,
        confidence: float,
    ):
        g, lg = EampEdgeSchedulerBase.get_g_and_lg(a)

        if interval.lower_bound != interval.upper_bound:
            self.get_test_case().assertLessEqual(
                interval.upper_bound / interval.lower_bound,
                (2 * lg / g) ** (1 / q),
                msg="Final interval is either only a single value or the multiplicative "
                    "gap is at most (2 * G / g) ** (1 / q)"
            )

            self.get_test_case().assertLessEqual(
                interval.upper_bound / interval.lower_bound,
                self.get_eamp_edge_scheduler_class().get_upper_bound_for_multiplicative_gap_of_result(a, q),
                msg="Final interval is either only a single value or the multiplicative "
                    "gap is below the given get_upper_bound_for_multiplicative_gap_of_result"
            )

        self.get_test_case().assertGreaterEqual(
            interval.confidence,
            confidence,
            msg="Final confidence is at least the desired confidence"
        )

    def assert_eamp_edge_scheduler_execution(
        self,
        a: int,
        q: int,
        confidence: float,
        formula_params: FormulaParamsZ3,
        model_count: Optional[int] = None,
    ):
        RunnerZ3.register_restrictive_formula_module_implementation(EampRfmiZ3)

        model_count = model_count if model_count is not None else \
            count_models_by_branching(formula_params.formula, formula_params.variables)

        store = InMemoryStore(
            data=StoreData(
                params=Params(
                    bit_width_counter=Counter[int]([x.size() for x in formula_params.variables])
                )
            )
        )

        scheduler = self.get_eamp_edge_scheduler_class()(
            store=store,
            confidence=confidence,
            a=a,
            q=q,
        )

        integrator = DirectIntegratorZ3(
            formula_params=formula_params
        )

        result: ProbabilisticInterval = integrator.run_all(scheduler)

        self.get_test_case().assertTrue(
            result.lower_bound <= model_count <= result.upper_bound,
            msg=f"The model count {model_count} is contained in the final "
                f"interval [{result.lower_bound}, {result.upper_bound}]"
        )

        self.assert_eamp_edge_scheduler_result(
            result, a, q, confidence,
        )

    def run_test_execution(self):
        # for upper_bound in (0, 1, 50):
        #     x, y = z3.BitVec("x", 4), z3.BitVec("y", 8)
        #     formula: z3.BoolRef = z3.ULT(z3.ZeroExt(4, x) + y, z3.BitVecVal(upper_bound, 8))
        #     self.assert_eamp_edge_scheduler_execution(100, 2, 0.99, FormulaParamsZ3(formula=formula, variables=[x, y]))

        x, y = z3.BitVec("x", 8), z3.BitVec("y", 8)
        formula: z3.BoolRef = z3.ULT(y, 100)
        model_count = (2 ** 8) * 100

        for q in (1, 2, 3, 4) if RUN_MINI_BENCHMARK else (1,):
            t0 = perf_counter()

            self.assert_eamp_edge_scheduler_execution(100, q, 0.99, FormulaParamsZ3(
                formula=formula, variables=[x, y]
            ), model_count)

            print(f"Mini Benchmark {self.get_eamp_edge_scheduler_class()} q={q} took {perf_counter() - t0:.2f}")

        # zs = [z3.BitVec(f"z{idx}", 1) for idx in range(50)]
        # formula: z3.BoolRef = z3.And([zs[idx] == 1 for idx in range(25)])
        # model_count = 2 ** 25
        #
        # self.assert_eamp_edge_scheduler_execution(
        #     100, 1, 0.99, FormulaParamsZ3(
        #         formula=formula, variables=zs
        #     ), model_count)
