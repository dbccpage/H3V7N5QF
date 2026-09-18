"""Counting the results of the second seed without listing them.

Computed.  The results within a bound are the legal states with at most that
many terms that contain what is given (a theorem of the paper); so their
number by terms and assertions is a restriction of the first derivation's
orbit counts.

Cited from the first derivation (`xry.orbits`) and re-checked
    `count_free`, `count_one_way`, `count_named` count legal states up to
    sameness; they mention no change.  With names, the kinds "arb only" and
    "arb and bra" are the states containing `arb` with `a`, `b` two terms;
    "arb and bra" alone contains `bra` as well.  Without names, the states
    with an asserted pair are all but the one with nothing asserted, and the
    states with a pair asserted both ways are all but the "one way" ones.
"""

from __future__ import annotations

from xry.orbits import count_free, count_named, count_one_way
from xry.state import Sameness

__all__ = ["count_results", "layer_counts"]


def count_results(sameness: Sameness, bra: bool, n: int, degree: int | None = None) -> list[int]:
    """Results with `n` terms under `sameness` and the alternative for `bra`, by assertions."""
    if sameness is Sameness.ANCHORED:
        named = count_named(n, degree)
        kinds = ["arb and bra"] if bra else ["arb only", "arb and bra"]
        return [sum(named[k][m] for k in kinds) for m in range(len(named["arb only"]))]
    every = count_free(n, degree)
    if bra:
        one_way = count_one_way(n, degree)
        return [c - o for c, o in zip(every, one_way)]
    return [0, *every[1:]]


def layer_counts(sameness: Sameness, bra: bool, upto: int) -> list[int]:
    """How many results need exactly `k` changes, for `k = 0..upto`, with no bound.

    A result needing `k` changes has size `size(given) + k`, so at most
    `k + 2` terms and at most `k + 2` assertions.
    """
    size0 = 2 + (2 if bra else 1)
    layers = [0] * (upto + 1)
    for n in range(2, upto + 3):
        for m, count in enumerate(count_results(sameness, bra, n, upto + 2)):
            k = n + m - size0
            if 0 <= k <= upto:
                layers[k] += count
    return layers
