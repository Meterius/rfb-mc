import unittest
import z3
from collections import Counter
from fractions import Fraction
from math import sqrt

from rfb_mc.component.direct_integrator_z3 import DirectIntegratorZ3
from rfb_mc.component.eamp.eamp_rfmi_z3 import EampRfmiZ3
from rfb_mc.component.eamp.eamp_edge_scheduler import EampEdgeScheduler, EampEdgeInterval
from rfb_mc.component.runner_z3 import RunnerZ3, FormulaParamsZ3
from rfb_mc.component.in_memory_store import InMemoryStore
from rfb_mc.store import StoreData
from rfb_mc.types import Params


class TestEampEdgeScheduler(unittest.TestCase):
    def assert_eamp_edge_scheduler_result(
        self,
        edge_interval: EampEdgeInterval,
        a: int,
        q: int,
        confidence: Fraction,
    ):
        g, lg = EampEdgeScheduler.get_g_and_lg(a)

        if edge_interval.interval[0] != edge_interval.interval[1]:
            self.assertLessEqual(
                edge_interval.interval[1] / edge_interval.interval[0],
                (2 * lg / g) ** (1 / q),
                msg="Final interval is either only a single value or the multiplicative "
                    "gap is below (2 * G / g) ** (1 / q)"
            )

            self.assertLessEqual(
                edge_interval.interval[1] / edge_interval.interval[0],
                EampEdgeScheduler.get_upper_bound_for_multiplicative_gap_of_result(a, q),
                msg="Final interval is either only a single value or the multiplicative "
                    "gap is below the given get_upper_bound_for_multiplicative_gap_of_result"
            )

        self.assertGreaterEqual(
            edge_interval.confidence,
            confidence,
            msg="Final confidence is at least the desired confidence"
        )

    def test_run(self):
        RunnerZ3.register_restrictive_formula_module_implementation(EampRfmiZ3)

        for upper_bound in (0, 1, 10, 100):
            a = 100
            q = 2
            confidence = Fraction(0.95)

            store = InMemoryStore(
                data=StoreData(
                    params=Params(
                        bit_width_counter=Counter([4, 8])
                    )
                )
            )

            scheduler = EampEdgeScheduler(
                store=store,
                confidence=confidence,
                a=a,
                q=q,
            )

            x, y = z3.BitVec("x", 4), z3.BitVec("y", 8)

            formula: z3.BoolRef = z3.ULT(z3.ZeroExt(4, x) + y, z3.BitVecVal(upper_bound, 8))

            integrator = DirectIntegratorZ3(
                formula_params=FormulaParamsZ3(
                    formula=formula,
                    variables=[x, y],
                )
            )

            result: EampEdgeInterval = integrator.run_all(scheduler)

            # TODO: investigate multiplicative gap from eamp edge scheduler being possibly not correct
            # self.assert_eamp_edge_scheduler_result(
            #     result, a, q, confidence,
            # )

        a = 100
        q = 1
        confidence = Fraction(0.95)

        store = InMemoryStore(
            data=StoreData(
                params=Params(
                    bit_width_counter=Counter([12, 8])
                )
            )
        )

        scheduler = EampEdgeScheduler(
            store=store,
            confidence=confidence,
            a=a,
            q=q,
        )

        x, y = z3.BitVec("x", 12), z3.BitVec("y", 8)

        formula: z3.BoolRef = z3.ULT(y, 100)

        integrator = DirectIntegratorZ3(
            formula_params=FormulaParamsZ3(
                formula=formula,
                variables=[x, y],
            )
        )

        result: EampEdgeInterval = integrator.run_all(scheduler)

        self.assert_eamp_edge_scheduler_result(
            result, a, q, confidence,
        )

    def test_get_g_and_lg(self):
        for a in (1, 10, 100, 1000, 10000000):
            g, lg = EampEdgeScheduler.get_g_and_lg(a)
            self.assertAlmostEqual(g, (sqrt(a + 1) - 1) ** 2, msg="g should equal (sqrt(a + 1) - 1)**2")
            self.assertAlmostEqual(lg, (sqrt(a + 1) + 1) ** 2, msg="G should equal (sqrt(a + 1) + 1)**2")

    def test_get_upper_bound_for_multiplicative_gap_of_result(self):
        for a in (1, 10, 100, 1000, 10000000):
            for q in (1, 2, 100, 10000):
                g, lg = EampEdgeScheduler.get_g_and_lg(a)
                upper_bound = EampEdgeScheduler.get_upper_bound_for_multiplicative_gap_of_result(a, q)

                self.assertAlmostEqual(
                    upper_bound,
                    (2 * lg / g) ** (1 / q),
                    msg="upper bound should equal (2 * G / g)**(1 / q)"
                )

    def test_get_q_for_fixed_a_that_ensures_upper_bound_for_multiplicative_gap_of_result(self):
        for a in (1, 10, 100, 1000, 10000000):
            for epsilon in (0.000001, 0.01, 0.1, 0.5, 1, 2, 5, 10, 100):
                q = EampEdgeScheduler \
                    .get_q_for_fixed_a_that_ensures_upper_bound_for_multiplicative_gap_of_result(a, epsilon)

                upper_bound = EampEdgeScheduler.get_upper_bound_for_multiplicative_gap_of_result(a, q)

                self.assertLessEqual(
                    upper_bound,
                    (1 + epsilon)**2,
                    msg="upper bound for generated q should be at most the desired value"
                )

                if q > 1:
                    upper_bound_2 = EampEdgeScheduler.get_upper_bound_for_multiplicative_gap_of_result(a, q - 1)

                    self.assertGreater(
                        upper_bound_2,
                        (1 + epsilon) ** 2,
                        msg="upper bound for lower values than generated q should be above the desired value"
                    )

    def test_get_a_for_fixed_q_that_ensures_upper_bound_for_multiplicative_gap_of_result(self):
        for q in (1, 2, 5, 1000, 10000):
            for epsilon in (0.01, 0.1, 0.5, 1, 2, 5, 10, 100):
                # ensures that values are skipped for which no desired "a" value exist
                if (q <= 1 and epsilon < 0.41) or (q <= 2 and epsilon < 0.2) or (q <= 5 and epsilon < 0.08):
                    continue

                a = EampEdgeScheduler \
                    .get_a_for_fixed_q_that_ensures_upper_bound_for_multiplicative_gap_of_result(q, epsilon)

                upper_bound = EampEdgeScheduler.get_upper_bound_for_multiplicative_gap_of_result(a, q)

                self.assertLessEqual(
                    upper_bound,
                    (1 + epsilon)**2,
                    msg="upper bound for generated a should be at most the desired value"
                )

                if a > 1:
                    upper_bound_2 = EampEdgeScheduler.get_upper_bound_for_multiplicative_gap_of_result(a - 1, q)

                    self.assertGreater(
                        upper_bound_2,
                        (1 + epsilon) ** 2,
                        msg="upper bound for lower values than generated a should be above the desired value"
                    )


if __name__ == '__main__':
    unittest.main()
