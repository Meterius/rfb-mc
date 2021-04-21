from typing import Dict, Tuple
from functools import lru_cache
import os

primes_dict_file_name = os.path.join(os.path.dirname(__file__), "primes.txt")


@lru_cache(1)
def read_primes_dict() -> Dict[int, int]:
    def parse_line(line: str) -> Tuple[int, int]:
        ns, ps = line.split(" ")
        return int(ns, 10), int(ps, 10)

    with open(primes_dict_file_name, "r") as f:
        lines = f.readlines()

    return {
        n: p for n, p in map(parse_line, lines)
    }


def get_pj(j: int) -> int:
    """
    Returns the smallest prime that above or equal 2 ** (2 ** j)
    """

    primes_dict = read_primes_dict()

    if j in primes_dict:
        return primes_dict[j]
    else:
        raise ValueError(f"Eamp has insufficient primes for {j} >= {max(primes_dict.keys())}")
