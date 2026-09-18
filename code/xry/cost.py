"""The fewest changes that reach a result, in closed form.

Derived (paper, Theorem on cost; lower bound also in `lean4/`)
    Let a state have `n` terms and `m` assertions, and let what is given have
    `n0 = 2` terms and `m0` assertions (`m0 = 1` without `bra`, `2` with).
    Count the *destroyed givens* of the state: each given assertion between
    the named terms that is no longer asserted, plus one if `a` and `b` have
    been identified (then every given assertion is destroyed too).  Then

        fewest changes = (n + m) - (n0 + m0) + 2 * destroyed.

    Under FREE sameness the names may be placed at will, so the fewest
    changes is the least value over all placements; `cost_free` gives it
    in closed form and `cost_free_by_placement` by trying every placement.

Computed
    `xry.evidence` compares these formulas with the explored rounds.
"""

from __future__ import annotations

from xry.state import State


def given_size(bra: bool) -> int:
    """Terms plus assertions of what is given, under the alternative for `bra`."""
    return 2 + (2 if bra else 1)


def destroyed(state: State, bra: bool) -> int:
    """How many givens a state with names has destroyed."""
    if state.names is None:
        raise ValueError("destroyed givens are counted on a state with names")
    a, b = state.names
    initial = [(a, b), (b, a)] if bra else [(a, b)]
    if a == b:
        return 1 + len(initial)
    return sum(1 for x, y in initial if not state.has(x, y))


def cost_anchored(state: State, bra: bool) -> int:
    """Fewest changes from what is given to `state`, names kept."""
    return state.n + state.m - given_size(bra) + 2 * destroyed(state, bra)


def has_two_way(state: State) -> bool:
    """Are some `xry` and `yrx` both asserted?"""
    return any(state.has(y, x) for x, y in state.pairs)


def cost_free(state: State, bra: bool) -> int:
    """Fewest changes from what is given to `state`, any rewriting allowed."""
    if state.n < 1:
        raise ValueError("no result is without terms")
    m0 = 2 if bra else 1
    if state.n == 1:
        lost = 1 + m0
    elif state.m == 0:
        lost = m0
    elif bra and not has_two_way(state):
        lost = 1
    else:
        lost = 0
    return state.n + state.m - given_size(bra) + 2 * lost


def cost_free_by_placement(state: State, bra: bool) -> int:
    """`cost_free` computed the long way: the best placement of the names."""
    if state.n < 1:
        raise ValueError("no result is without terms")
    return min(
        cost_anchored(State(state.n, state.mask, (a, b)), bra)
        for a in range(state.n)
        for b in range(state.n)
    )


def cost(state: State, bra: bool) -> int:
    """Fewest changes to `state` under the sameness its names imply."""
    if state.names is None:
        return cost_free(state, bra)
    return cost_anchored(state, bra)
