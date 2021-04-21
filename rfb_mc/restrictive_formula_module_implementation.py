from abc import ABC, abstractmethod
from typing import TypeVar, Generic, Type, Any
from rfb_mc.restrictive_formula_module import RestrictiveFormulaInstanceParams, RestrictiveFormulaModuleBase
from rfb_mc.types import Params

RestrictiveFormulaInstance = TypeVar("RestrictiveFormulaInstance")

RestrictiveFormulaInstanceGenerationArgs = TypeVar("RestrictiveFormulaInstanceGenerationArgs")


class RestrictiveFormulaModuleImplementationBase(
    ABC,
    Generic[RestrictiveFormulaInstanceParams, RestrictiveFormulaInstanceGenerationArgs, RestrictiveFormulaInstance],
):
    @classmethod
    @abstractmethod
    def get_restrictive_formula_module(
        cls,
    ) -> Type[RestrictiveFormulaModuleBase[Any, Any, RestrictiveFormulaInstanceParams]]:
        """
        Restrictive formula module this class implements.
        """

        raise NotImplementedError()

    @classmethod
    @abstractmethod
    def generate_restrictive_formula(
        cls,
        params: Params,
        instance_params: RestrictiveFormulaInstanceParams,
        args: RestrictiveFormulaInstanceGenerationArgs,
    ) -> RestrictiveFormulaInstance:
        """
        Implements the restrictive formula that is given by the instance params for the restrictive formula module.
        """

        raise NotImplementedError()
