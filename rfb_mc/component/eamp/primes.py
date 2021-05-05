from typing import Dict, Tuple
from functools import lru_cache
import os
import random


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


def miller_rabin(n: int, k: int = 40) -> bool:
    # Implementation uses the Miller-Rabin Primality Test
    # The optimal number of rounds for this test is 40
    # See http://stackoverflow.com/questions/6325576/how-many-iterations-of-rabin-miller-should-i-use-for-cryptographic-safe-primes
    # for justification

    # If number is even, it's a composite number

    if n == 2 or n == 3:
        return True

    if n % 2 == 0:
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


def get_closest_prime(x: int, only_larger: bool = False) -> int:
    """
    Generates the prime nearest to the given "x" (including x itself).
    Unless only_larger is True in which case the lowest prime above or equal x is generated.
    There is a small probability that the generated prime is not a prime.
    """

    if miller_rabin(x, k=40):
        return x

    k = 1

    while True:
        if not only_larger and x - k > 1 and miller_rabin(x - k, k=40):
            return x - k
        elif miller_rabin(x + k, k=40):
            return x + k
        else:
            k += 1
