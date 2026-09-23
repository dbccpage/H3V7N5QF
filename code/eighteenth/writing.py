"""Sameness when a writing is part of the result.

The base says two results that differ only in how their terms are written
are the same result (`xry.state.same`, via `canonical`). This seed says they
are different results. Equality of the written state is the finest relation
that still identifies two results.

A rewriting is still computed, so the base's collapse can be counted: the
writings of one state are the states a permutation of its terms produces.
"""

from __future__ import annotations

from itertools import permutations
from math import factorial

from xry.state import State, rewrite


def same_written(left: State, right: State) -> bool:
    """The eighteenth sameness: the same terms, assertions and names, as written."""
    return left == right


def orbit(state: State) -> frozenset[State]:
    """Every writing of `state` obtained by permuting its terms."""
    return frozenset(rewrite(state, perm) for perm in permutations(range(state.n)))


def orbit_size(state: State) -> int:
    """How many distinct writings a permutation of the terms produces."""
    return len(orbit(state))


def aut_size(state: State) -> int:
    """How many permutations of the terms leave `state` as written."""
    return sum(1 for perm in permutations(range(state.n)) if rewrite(state, perm) == state)


def orbit_splits_factorial(state: State) -> bool:
    """`n!` is the number of writings times the permutations that fix the state."""
    return factorial(state.n) == orbit_size(state) * aut_size(state)


def letter_supply(n: int, aut: int, letters: int) -> int:
    """Writings of `n` terms by `letters` distinct letters, up to the permutations that fix a state.

    `aut` of those permutations leave the state as written, so they are not
    further writings. An infinite letter supply is not a value of `letters`.
    """
    if letters < n or aut <= 0:
        raise ValueError("a writing needs a letter for every term")
    ways = 1
    for offset in range(n):
        ways *= letters - offset
    return ways // aut
