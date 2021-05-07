from fractions import Fraction
from typing import NamedTuple

ProbabilisticInterval = NamedTuple("ProbabilisticInterval", [
    ("lower_bound", int),
    ("upper_bound", int),
    ("confidence", Fraction),
])
