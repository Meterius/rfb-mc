from enum import Enum, unique
from math import prod, log2, ceil
from typing import NamedTuple, Tuple, Any
from rfb_mc.restrictive_formula_module import RestrictiveFormulaModuleBase
from rfb_mc.runner import RunnerRandom
from rfb_mc.types import Params


@unique
class EampTransformMethod(Enum):
    SORTED_ROLLING_WINDOW = "SRW"


EampParams = NamedTuple("EampParams", [
    ("c", Tuple[int, ...]),
    ("p", Tuple[int, ...]),
    ("transform_method", EampTransformMethod),
])

EampParamProperties = NamedTuple("EampParamProperties", [
    ("range_size", int),
])

EampInstanceParams = NamedTuple("EampInstanceParams", [
    ("params", EampParams),
    ("coefficients", Tuple[Tuple[Tuple[Tuple[int, ...], int], ...], ...]),
    ("p", Tuple[int, ...]),
])


class EampRfm(RestrictiveFormulaModuleBase[EampParams, EampParamProperties, EampInstanceParams]):
    @classmethod
    def get_guid(cls):
        return "eamp-rfm"

    @classmethod
    def encode_restrictive_formula_params(
        cls,
        params: EampParams,
    ) -> Any:
        return (
            params.c,
            params.p,
            params.transform_method.value
        )

    @classmethod
    def decode_restrictive_formula_params(
        cls,
        params: Any,
    ) -> EampParams:
        c, p, transform_method = params

        return EampParams(
            c=c,
            p=p,
            transform_method=EampTransformMethod(transform_method)
        )

    @classmethod
    def get_restrictive_formula_properties(
        cls,
        params: Params,
        restrictive_formula_params: EampParams,
    ) -> EampParamProperties:
        return EampParamProperties(
            range_size=get_range_size(restrictive_formula_params.c, restrictive_formula_params.p)
        )

    @classmethod
    def generate_restrictive_formula_instance_params(
        cls,
        params: Params,
        restrictive_formula_params: EampParams,
        q: int,
        random: RunnerRandom,
    ) -> EampInstanceParams:
        variables = []

        for size in sorted(params.bit_width_counter.keys()):
            # add amount of variables with size q-times as they are cloned q-times
            variables += [size] * params.bit_width_counter[size] * q

        def get_slice_count_sorted_rolling_window(domain_bit_count: int) -> int:
            slice_count = 0

            queue = sorted(variables)

            while len(queue) > 0:
                x = queue.pop(0)

                if x >= domain_bit_count:
                    for i in range(x // domain_bit_count):
                        slice_count += 1

                    if (x // domain_bit_count) * domain_bit_count != x:
                        slice_count += 1
                else:
                    slice_item = [x]

                    while len(queue) > 0 and sum([y for y in slice_item]) + queue[0] <= domain_bit_count:
                        slice_item.append(queue.pop(0))

                    slice_count += 1

            return slice_count

        def get_slice_count(domain_bit_count: int) -> int:
            if restrictive_formula_params.transform_method == EampTransformMethod.SORTED_ROLLING_WINDOW:
                return get_slice_count_sorted_rolling_window(domain_bit_count)
            else:
                raise RuntimeError(f"Not implemented transform method {restrictive_formula_params.transform_method}")

        def generate_coefficients(j: int) -> Tuple[Tuple[int, ...], int]:
            pj = restrictive_formula_params.p[j]

            return (
                tuple([
                    random.get_random_int(0, pj - 1) for _ in range(
                        get_slice_count(
                            int(ceil(log2(pj)))
                        )
                    )
                ]),
                random.get_random_int(0, pj - 1),
            )

        return EampInstanceParams(
            params=restrictive_formula_params,
            coefficients=tuple([
                tuple([
                    generate_coefficients(j) for _ in range(restrictive_formula_params.c[j])
                ]) for j in range(len(restrictive_formula_params.c))
            ]),
            p=restrictive_formula_params.p,
        )


def get_range_size(c: Tuple[int, ...], p: Tuple[int, ...]) -> int:
    """
    Returns the size of the range of the hash family for
    the given c and p parameters.
    """

    return prod([p[i] ** c[i] for i in range(len(c))])
