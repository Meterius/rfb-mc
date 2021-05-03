from typing import List, Any
from copy import copy


def omit_typed_dict(typed_dict: Any, keys: List[str]):
    typed_dict_copy = copy(typed_dict)

    for key in keys:
        del typed_dict_copy[key]

    return typed_dict_copy
