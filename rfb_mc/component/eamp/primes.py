from typing import Dict, Tuple, Optional, overload
from functools import lru_cache
import os
import random


lowest_prime_above_or_equal_power_of_power_of_two_dic_file_name = os.path.join(
    os.path.dirname(__file__),
    "lowest_prime_above_or_equal_power_of_power_of_two_dict.txt"
)


@lru_cache(1)
def read_lowest_prime_above_or_equal_power_of_power_of_two_dict() -> Dict[int, int]:
    def parse_line(line: str) -> Tuple[int, int]:
        ns, ps = line.split(" ")
        return int(ns, 10), int(ps, 10)

    with open(lowest_prime_above_or_equal_power_of_power_of_two_dic_file_name, "r") as f:
        lines = f.readlines()

    return {
        n: p for n, p in map(parse_line, lines)
    }


def get_lowest_prime_above_or_equal_power_of_power_of_two(j: int) -> int:
    """
    Returns the smallest prime that above or equal 2 ** (2 ** j)
    """

    primes_dict = read_lowest_prime_above_or_equal_power_of_power_of_two_dict()

    if j in primes_dict:
        return primes_dict[j]
    else:
        raise ValueError(f"No stored primes for the lowest prime above or equal 2 ** (2 ** {j}),"
                         f" the highest available is for 2 ** (2 ** {max(primes_dict.keys())})")


def miller_rabin(n: int, k: int = 40) -> bool:
    """
    Takes in a possible prime n and the number of testing iterations k.
    Returns True if n is a prime, returns False with a probability >= (1/4)**(-k) if it is not.
    Note: If n < 2, False will always be returned
    """

    # Implementation uses the Miller-Rabin Primality Test
    # The optimal number of rounds for this test is 40
    # See http://stackoverflow.com/questions/6325576
    #     /how-many-iterations-of-rabin-miller-should-i-use-for-cryptographic-safe-primes
    # for justification

    if n <= 3:
        return True if n == 2 or n == 3 else False
    elif n % 2 == 0:
        return False

    r, s = 0, n - 1
    while s % 2 == 0:
        r += 1
        s //= 2

    for _ in range(k):
        a = random.randrange(2, n - 1)
        x = pow(a, s, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = pow(x, 2, n)
            if x == n - 1:
                break
        else:
            return False
    return True


@overload
def get_closest_prime(x: int) -> int: pass


@overload
def get_closest_prime(x: int, bounds: Tuple[Optional[int], None]) -> int: pass


@overload
def get_closest_prime(x: int, bounds: Tuple[Optional[int], int]) -> Optional[int]: pass


def get_closest_prime(
    x: int,
    bounds: Tuple[Optional[int], Optional[int]] = (None, None),
) -> Optional[int]:
    """
    Generates the prime nearest to the given "x" (including x itself).
    The generated prime will be within the given bounds (unless none exists in which case None is returned),
    a bound of None will mean the side is unbounded i.e. (12, None) means the generated prime needs to be >= 12.
    There is a small probability that the generated prime is not a prime.
    """

    lower_bound = max(bounds[0] or 0, 2)
    upper_bound = bounds[1]

    def in_bounds(y: int) -> bool:
        return lower_bound <= y and (upper_bound is None or y <= upper_bound)

    if in_bounds(x) and miller_rabin(x, k=40):
        return x

    k = 1

    while in_bounds(x - k) or in_bounds(x + k):
        if in_bounds(x - k) and miller_rabin(x - k, k=40):
            return x - k
        elif in_bounds(x + k) and miller_rabin(x + k, k=40):
            return x + k
        else:
            k += 1

    return None
