import unittest
from collections import Counter
import os
from fractions import Fraction

import boto3
import z3

from rfb_mc.component.aws.dynamodb_store import DynamodbStore
from rfb_mc.component.direct_integrator_z3 import DirectIntegratorZ3
from rfb_mc.component.eamp.eamp_edge_scheduler import EampEdgeScheduler
from rfb_mc.component.eamp.eamp_rfm import EampRfm, EampParams, EampTransformMethod
from rfb_mc.component.eamp.eamp_rfmi_z3 import EampRfmiZ3
from rfb_mc.component.runner_z3 import RunnerZ3, FormulaParamsZ3
from rfb_mc.restrictive_formula_module import register_restrictive_formula_module
from rfb_mc.types import Params, RfBmcResult, RfBmcTask, BmcTask, BmcResult

skip_dynamodb_tests = True


os.environ["AWS_SDK_LOAD_CONFIG"] = "true"
# os.environ["AWS_PROFILE"] = ""


class TestDynamodbStore(unittest.TestCase):
    @unittest.skipIf(skip_dynamodb_tests, "Skip DynamodbStore tests that require aws account and table")
    def test_storage(self):
        RunnerZ3.register_restrictive_formula_module_implementation(EampRfmiZ3)

        client = boto3.resource("dynamodb")
        table = client.Table("rfb_mc_store_test")

        params = Params(
            bit_width_counter=Counter([4, 8])
        )

        ident = DynamodbStore.create_store_data_entry(table, params)
        store = DynamodbStore(table, ident)

        register_restrictive_formula_module(EampRfm)

        task_a = RfBmcTask(rfm_guid=EampRfm.get_guid(), rfm_formula_params=EampParams(
            c=(2, 3, 1),
            p=(2, 3, 5),
            transform_method=EampTransformMethod.SORTED_ROLLING_WINDOW,
        ), a=100, q=2)

        store.add_results([
            (task_a, RfBmcResult(bmc=564)),
            (task_a, RfBmcResult(bmc=521)),
            (task_a, RfBmcResult(bmc=521)),
            (task_a, RfBmcResult(bmc=None)),
            (BmcTask(15), BmcResult(bmc=5))
        ])

        self.assertIn(task_a, store.data.rf_bmc_results_map, "Tasks have been added")

        self.assertEqual(
            store.data.bmc_task_result,
            (BmcTask(15), BmcResult(bmc=5)),
            "Tasks have been added"
        )

        self.assertEqual(
            store.data.rf_bmc_results_map[task_a][RfBmcResult(bmc=521)],
            2,
            "Tasks have been added in the correct amounts"
        )

        store.add_results([
            (BmcTask(5), BmcResult(bmc=1)),
            (BmcTask(7), BmcResult(bmc=2))
        ])

        self.assertEqual(
            store.data.bmc_task_result,
            (BmcTask(15), BmcResult(bmc=5)),
            "BmcResult is not overwritten for lower values"
        )

        store.add_results([
            (BmcTask(5), BmcResult(bmc=5)),
            (BmcTask(20), BmcResult(bmc=8))
        ])

        self.assertEqual(
            store.data.bmc_task_result,
            (BmcTask(20), BmcResult(bmc=8)),
            "BmcResult is overwritten for higher values"
        )

        store.add_results([
            (BmcTask(20), BmcResult(bmc=12))
        ])

        self.assertEqual(
            store.data.bmc_task_result,
            (BmcTask(20), BmcResult(bmc=12)),
            "BmcResult is overwritten for equal values"
        )

    @unittest.skipIf(skip_dynamodb_tests, "Skip DynamodbStore tests that require aws account and table")
    def test_integration(self):
        RunnerZ3.register_restrictive_formula_module_implementation(EampRfmiZ3)

        for upper_bound in (10, 100):
            a = 100
            q = 2
            confidence = Fraction(0.95)

            client = boto3.resource("dynamodb")
            table = client.Table("rfb_mc_store_test")

            params = Params(
                bit_width_counter=Counter([4, 8])
            )

            ident = DynamodbStore.create_store_data_entry(table, params)
            store = DynamodbStore(table, ident)

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

            integrator.run_all(scheduler)

            self.assertTrue(True, msg="Integration run did not raise an exception")
