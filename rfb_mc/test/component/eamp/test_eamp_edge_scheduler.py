import unittest
from math import sqrt

from rfb_mc.component.eamp.eamp_edge_scheduler import EampEdgeScheduler


class TestEampEdgeScheduler(unittest.TestCase):
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
