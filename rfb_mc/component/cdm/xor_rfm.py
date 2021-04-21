from typing import NamedTuple, Tuple, Any
from rfb_mc.restrictive_formula_module import RestrictiveFormulaModuleBase
from rfb_mc.runner import RunnerRandom
from rfb_mc.types import Params


XorParams = NamedTuple("XorParams", [
    ("m", int),
])

XorParamProperties = NamedTuple("XorParamProperties", [
    ("range_size", int),
])

XorInstanceParams = NamedTuple("XorInstanceParams", [
    ("params", XorParams),
    ("coefficients", Tuple[Tuple[int, ...], ...]),
])


class XorRfm(RestrictiveFormulaModuleBase[XorParams, XorParamProperties, XorInstanceParams]):
    @classmethod
    def get_guid(cls):
        return "xor-rfm"

    @classmethod
    def encode_restrictive_formula_params(
        cls,
        params: XorParams,
    ) -> Any:
        return (
            params.m,
        )

    @classmethod
    def decode_restrictive_formula_params(
        cls,
        params: Any,
    ) -> XorParams:
        m = params[0]

        return XorParams(
            m=m,
        )

    @classmethod
    def get_restrictive_formula_properties(
        cls,
        params: Params,
        restrictive_formula_params: XorParams,
    ) -> XorParamProperties:
        return XorParamProperties(
            range_size=get_range_size(restrictive_formula_params.m)
        )

    @classmethod
    def generate_restrictive_formula_instance_params(
        cls,
        params: Params,
        restrictive_formula_params: XorParams,
        q: int,
        random: RunnerRandom,
    ) -> XorInstanceParams:
        variable_bits = sum([
            bit_width * count for bit_width, count in params.bit_width_counter.items()
        ]) * q

        return XorInstanceParams(
            params=restrictive_formula_params,
            coefficients=tuple([
                tuple([
                    random.get_random_int(0, 1)
                    for _ in range(variable_bits + 1)
                ]) for _ in range(restrictive_formula_params.m)
            ]),
        )


def get_range_size(m: int) -> int:
    """
    Returns the size of the range of the hash family for
    the given m parameter.
    """

    return 2 ** m
