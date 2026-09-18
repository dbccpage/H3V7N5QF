"""The fewest changes that reach a result, in closed form, under the fourth seed.

Derived (paper, `lean4/Fourth/Cost.lean`)
    Let what is given have `n0 = 2` terms and total multiplicity `m0` (`1`
    without `bra`, `2` with).  A state with names is a result exactly when
    `a` and `b` are two terms and every given assertion is asserted between
    them (`contains_given`); the fewest changes to it is `(n + m) - (n0 + m0)`,
    its size minus that of what is given, `m` being the sum of the
    multiplicities — and every sequence of changes reaching it has exactly
    that length, since each change raises the size by one.  Without names a
    state is a result exactly when some assertion is asserted (without `bra`)
    or some pair is asserted both ways (with `bra`).

Cited from the first, second and third derivations (`xry.cost`, `second.cost`,
`third.cost`) and re-checked
    `given_size` counts what is given: two terms and one or two assertions,
    each with multiplicity one, so the number survives the counting and is
    imported.  The closed form is the third's with `m` read as the sum of
    the multiplicities (the third's `m` counted each assertion once, which is
    the same number on states asserting nothing twice); it is proved again
    from the fourth seed (`fewest_changes4_A`, `fewest_changes4_B`,
    `Reach4.length_unique`), and `fourth.evidence` compares it with the round
    of every explored result.
"""

from __future__ import annotations

from xry.cost import given_size

from fourth.state import MState

__all__ = [
    "contains_given",
    "cost",
    "cost_anchored",
    "cost_free",
    "cost_free_by_placement",
    "given_size",
    "has_two_way",
]


def contains_given(state: MState, bra: bool) -> bool:
    """Are `a`, `b` two terms with `arb` (and `bra`, if given) asserted between them?"""
    if state.names is None:
        raise ValueError("what is given is looked for on a state with names")
    a, b = state.names
    return a != b and state.has(a, b) and (state.has(b, a) or not bra)


def has_two_way(state: MState) -> bool:
    """Are some `xry` and `yrx` both asserted?"""
    return any(state.has(y, x) for x, y in state.pairs)


def cost_anchored(state: MState, bra: bool) -> int | None:
    """Fewest changes from what is given to `state`, names kept; `None` if unreachable.

    An illegal state (some `xrx` asserted) is never a result, so it is
    unreachable and its cost is `None`, whatever it asserts between `a` and `b`.
    """
    if not state.legal or not contains_given(state, bra):
        return None
    return state.size - given_size(bra)


def cost_free(state: MState, bra: bool) -> int | None:
    """Fewest changes to `state`, any rewriting allowed; `None` if unreachable."""
    reachable = state.legal and (has_two_way(state) if bra else state.m > 0)
    if not reachable:
        return None
    return state.size - given_size(bra)


def cost_free_by_placement(state: MState, bra: bool) -> int | None:
    """`cost_free` computed the long way: the best placement of the names."""
    costs = [
        c
        for a in range(state.n)
        for b in range(state.n)
        if (c := cost_anchored(MState(state.n, state.mult, (a, b)), bra)) is not None
    ]
    return min(costs) if costs else None


def cost(state: MState, bra: bool) -> int | None:
    """Fewest changes to `state` under the sameness its names imply."""
    if state.names is None:
        return cost_free(state, bra)
    return cost_anchored(state, bra)
