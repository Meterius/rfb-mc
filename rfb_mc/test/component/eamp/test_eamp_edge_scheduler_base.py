import unittest
from math import sqrt
from rfb_mc.component.eamp.eamp_edge_scheduler_base import EampEdgeSchedulerBase


class TestEampEdgeSchedulerBase(unittest.TestCase):
    def test_get_g_and_lg(self):
        for a in (1, 10, 100, 1000, 10000000):
            g, lg = EampEdgeSchedulerBase.get_g_and_lg(a)
            self.assertAlmostEqual(g, (sqrt(a + 1) - 1) ** 2, msg="g should equal (sqrt(a + 1) - 1)**2")
            self.assertAlmostEqual(lg, (sqrt(a + 1) + 1) ** 2, msg="G should equal (sqrt(a + 1) + 1)**2")


if __name__ == "__main__":
    unittest.main()
