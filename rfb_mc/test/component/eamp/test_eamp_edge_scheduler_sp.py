import unittest
from rfb_mc.component.eamp.eamp_edge_scheduler_sp import EampEdgeSchedulerSP
from rfb_mc.test.component.eamp.eamp_edge_scheduler import EampEdgeSchedulerTestCaseBase


class TestEampEdgeSchedulerSP(unittest.TestCase, EampEdgeSchedulerTestCaseBase):
    def get_test_case(self):
        return self

    def get_eamp_edge_scheduler_class(self):
        return EampEdgeSchedulerSP

    def test_run(self):
        self.run_test_execution()


if __name__ == '__main__':
    unittest.main()
