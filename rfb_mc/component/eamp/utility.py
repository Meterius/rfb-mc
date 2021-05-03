from typing import Iterable
from fractions import Fraction
from math import ceil, comb, prod


def probability_of_correctness(
    error_probabilities: Iterable[Fraction],
) -> Fraction:
    """
    Takes in the error probabilities of independent probabilistic execution.
    Returns the probability of an error occurring in any of them.
    """

    return Fraction(prod([1 - err_prob for err_prob in error_probabilities]))


def majority_vote_error_probability(
    alpha: Fraction, r: int,
) -> Fraction:
    return sum([
        comb(r, rj) * (alpha ** r) * ((1 - alpha) ** (r - rj))
        for rj in range(ceil(r / 2), r + 1)
    ])


def multi_majority_vote_iteration_count_to_ensure_beta(
    alpha: Fraction, beta: Fraction, max_majority_voting_countings: int,
) -> int:
    """
    Returns an amount of iterations for each majority vote counting such that
    the error probability of any of the majority vote counting to fail is below beta.
    :param alpha: Error probability of the procedures in the majority vote counting
    :param beta: Desired upper bound on error probability of any majority vote counting failing
    :param max_majority_voting_countings: Maximum amount of expected majority vote counting procedures
    """

    r = 1
    while (1 - majority_vote_error_probability(alpha, r))**max_majority_voting_countings < 1 - beta:
        r += 1

    return r
