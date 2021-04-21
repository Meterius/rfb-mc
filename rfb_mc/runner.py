from abc import ABC, abstractmethod
from typing import TypeVar, Generic, Dict, Any, Type
from rfb_mc.restrictive_formula_module import register_restrictive_formula_module
from rfb_mc.restrictive_formula_module_implementation import RestrictiveFormulaModuleImplementationBase, \
    RestrictiveFormulaInstance
from rfb_mc.runner_random import RunnerRandom
from rfb_mc.types import Params, RfBmcTask, RfBmcResult

FormulaParams = TypeVar("FormulaParams")

RestrictiveFormulaInstanceGenerationArgs = TypeVar("RestrictiveFormulaInstanceGenerationArgs")


class RunnerBase(ABC, Generic[FormulaParams, RestrictiveFormulaInstanceGenerationArgs, RestrictiveFormulaInstance]):
    def __init__(self, params: Params, formula_params: FormulaParams):
        self.check_params_and_formula_params_compatibility(params, formula_params)

        # random class used to introduce randomness to the restrictive formula implementors
        self.random: RunnerRandom = RunnerRandom()

        self.params: Params = params
        self.formula_params: FormulaParams = formula_params

    restrictive_formula_module_implementation_map: Dict[str, Type[RestrictiveFormulaModuleImplementationBase]] = {}
    """
    Map from restrictive formula module uid to implementation class.
    """

    @classmethod
    def register_restrictive_formula_module_implementation(cls, rfmi: Type[RestrictiveFormulaModuleImplementationBase]):
        register_restrictive_formula_module(
            rfmi.get_restrictive_formula_module(),
        )

        cls.restrictive_formula_module_implementation_map[rfmi.get_restrictive_formula_module().get_guid()] = rfmi

    @classmethod
    @abstractmethod
    def check_params_and_formula_params_compatibility(cls, params: Params, formula_params: FormulaParams):
        """
        Raises an error if the params and formula_params are not compatible.
        """

        raise NotImplementedError()

    @abstractmethod
    def get_restrictive_formula_instance_generation_args(self, q: int) -> RestrictiveFormulaInstanceGenerationArgs:
        """
        Returns additional arguments required for generating the restrictive formula instance from the params.
        """

        raise NotImplementedError()

    def generate_restrictive_formula_instance(
        self, rfm_uid: str, rfm_formula_params: Any, q: int,
    ) -> RestrictiveFormulaInstance:
        imp_map = self.restrictive_formula_module_implementation_map

        if rfm_uid not in imp_map:
            raise RuntimeError(f"Restrictive Formula Module \"{rfm_uid}\" is not implemented")

        rfmi = imp_map[rfm_uid]
        rfm = rfmi.get_restrictive_formula_module()

        instance_params = rfm.generate_restrictive_formula_instance_params(
            self.params, rfm_formula_params, q, self.random,
        )
        instance_args = self.get_restrictive_formula_instance_generation_args(q)

        return rfmi.generate_restrictive_formula(self.params, instance_params, instance_args)

    @abstractmethod
    def rf_bmc(self, task: RfBmcTask) -> RfBmcResult:
        """
        Performs bounded model counting on the formula resulting from
        first replicating the original formula q-times and
        then introducing a restrictive formula condition.
        """

        raise NotImplementedError()
