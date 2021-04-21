import z3
from typing import Type, Tuple
from rfb_mc.component.cdm.xor_rfm import XorInstanceParams, XorRfm
from rfb_mc.component.runner_z3 import RfmiGenerationArgsZ3
from rfb_mc.restrictive_formula_module_implementation import RestrictiveFormulaModuleImplementationBase
from rfb_mc.types import Params


class XorRfmiZ3(RestrictiveFormulaModuleImplementationBase[XorInstanceParams, RfmiGenerationArgsZ3, z3.BoolRef]):
    @classmethod
    def get_restrictive_formula_module(
        cls,
    ) -> Type[XorRfm]:
        return XorRfm

    @classmethod
    def generate_restrictive_formula(
        cls,
        params: Params,
        instance_params: XorInstanceParams,
        args: RfmiGenerationArgsZ3,
    ) -> z3.BoolRef:
        bit_variables = [z3.Extract(i, i, x) for x in args.variables for i in range(x.size())]

        def make_hash_equation(coefficients: Tuple[int, ...]):
            return z3.URem(
                z3.BitVecVal(coefficients[-1], 1) + z3.Sum([
                    coefficients[i] * bit_variables[i]
                    for i in range(len(bit_variables))
                ]), 2
            ) == z3.BitVecVal(0, 1)

        return z3.And([
            make_hash_equation(coefficients)
            for coefficients in instance_params.coefficients
        ])
