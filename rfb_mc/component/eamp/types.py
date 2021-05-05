from fractions import Fraction
from typing import NamedTuple, Tuple

EampEdgeInterval = NamedTuple("EampEdgeInterval", [
    ("interval", Tuple[int, int]),
    ("confidence", Fraction),
])