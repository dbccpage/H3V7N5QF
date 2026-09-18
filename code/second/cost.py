"""The fewest changes that reach a result, in closed form, under the second seed.

Derived (paper, `lean4/Second/Cost.lean`)
    Let what is given have `n0 = 2` terms and `m0` assertions (`1` without
    `bra`, `2` with).  A state with names is a result exactly when `a` and
    `b` are two terms and every given assertion is asserted between them
    (`contains_given`); then the fewest changes to it is

        (n + m) - (n0 + m0),

    its size minus the size of what is given.  Every change raises the size
    by at most one (an identification lowers it), and additions alone reach
    every such state.  No given is ever destroyed, so the first derivation's
    term `2 * destroyed` is always zero on a result, and states that would
    have it positive are unreachable (`cost` returns `None` for them).

    Under FREE sameness the names may be placed at will: a state is a result
    exactly when some placement contains what is given, that is, when some
    assertion is asserted (without `bra`) or some pair is asserted both ways
    (with `bra`); the cost is the same size difference.  `cost_free_by_placement`
    computes it the long way for the computed check.

Cited from the first derivation (`xry.cost`) and re-checked
    `given_size` and `has_two_way` mention no change.
"""

from __future__ import annotations

from xry.cost import given_size, has_two_way
from xry.state import State

__all__ = [
    "contains_given",
    "cost",
    "cost_anchored",
    "cost_free",
    "cost_free_by_placement",
    "given_size",
    "has_two_way",
]


def contains_given(state: State, bra: bool) -> bool:
    """Are `a`, `b` two terms with `arb` (and `bra`, if given) asserted between them?"""
    if state.names is None:
        raise ValueError("what is given is looked for on a state with names")
    a, b = state.names
    return a != b and state.has(a, b) and (state.has(b, a) or not bra)


def cost_anchored(state: State, bra: bool) -> int | None:
    """Fewest changes from what is given to `state`, names kept; `None` if unreachable.

    An illegal state (some `xrx` asserted) is never a result, so it is
    unreachable and its cost is `None`, whatever it asserts between `a` and `b`.
    """
    if not state.legal or not contains_given(state, bra):
        return None
    return state.n + state.m - given_size(bra)


def cost_free(state: State, bra: bool) -> int | None:
    """Fewest changes to `state`, any rewriting allowed; `None` if unreachable.

    An illegal state is unreachable, so it is `None` here too; without this an
    `xrx`-only state would count as reached and give a negative size difference.
    """
    reachable = state.legal and (has_two_way(state) if bra else state.m > 0)
    if not reachable:
        return None
    return state.n + state.m - given_size(bra)


def cost_free_by_placement(state: State, bra: bool) -> int | None:
    """`cost_free` computed the long way: the best placement of the names."""
    costs = [
        c
        for a in range(state.n)
        for b in range(state.n)
        if (c := cost_anchored(State(state.n, state.mask, (a, b)), bra)) is not None
    ]
    return min(costs) if costs else None


def cost(state: State, bra: bool) -> int | None:
    """Fewest changes to `state` under the sameness its names imply."""
    if state.names is None:
        return cost_free(state, bra)
    return cost_anchored(state, bra)
