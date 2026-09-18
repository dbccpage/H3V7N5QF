"""A number that no change of the second seed lowers.

Derived (paper, `lean4/Second/Carry.lean`, `Reach3.split_mono`)
    Split the terms of a state into classes so that no class holds two
    related terms (`xry` or `yrx` asserted).  The fewest classes of such a
    split never decreases along a change: a split of the outcome pulls back
    along the carrying map to a split of the state.  (Adding a term keeps the
    number; adding an assertion or identifying two terms can raise it.)

Computed
    `fewest_classes` finds the number by backtracking; `second.evidence`
    checks the monotonicity on every unobstructed change within the bound.
"""

from __future__ import annotations

from xry.state import State

__all__ = ["fewest_classes"]


def fewest_classes(state: State) -> int:
    """The fewest classes of a split with no two related terms in one class."""
    n = state.n
    if not state.legal:
        raise ValueError("a term related to itself fits in no class")
    related = [[state.related(x, y) for y in range(n)] for x in range(n)]
    colour = [-1] * n

    def fill(x: int, k: int) -> bool:
        if x == n:
            return True
        for c in range(k):
            if all(colour[y] != c or not related[x][y] for y in range(x)):
                colour[x] = c
                if fill(x + 1, k):
                    return True
        colour[x] = -1
        return False

    for k in range(n + 1):
        if fill(0, k):
            return k
    raise AssertionError("n classes always suffice")  # pragma: no cover
