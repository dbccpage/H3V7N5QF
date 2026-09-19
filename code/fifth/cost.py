"""The fewest changes that reach a result, in closed form, under the fifth seed.

Derived (paper, `lean4/Fifth/Cost.lean`)
    Let `size = terms + Σ multiplicities` and let `lost` count the destroyed
    givens as the first derivation did: with `a ≠ b`, the given assertions
    (`arb`; `bra` too if given) whose multiplicity is zero; with `a = b`, one
    more than the number of given assertions.  Then `size + 2·lost` rises by
    at most one per change and the fewest changes from what is given to a
    legal state is

        size − size(given) + 2·lost,

    the first derivation's formula with size counting multiplicities.  Under
    FREE the names may be placed at will and `lost` takes the first's closed
    form: `m0 + 1` for one term, `m0` for nothing asserted, `1` with `bra`
    given and no pair asserted both ways, `0` otherwise.  A change raises the
    cost by exactly one (names kept) exactly when it adds a term, adds an
    assertion that restores no given, removes a given assertion, or
    identifies `a` with `b` (`raises_by_one`).

Cited from the first derivation (`xry.cost`) and re-checked
    `given_size` counts what is given (two terms, one or two assertions of
    multiplicity one) and survives.  The formula, `destroyed` and the FREE
    closed form are the first's, re-proved for multiplicities (the proofs
    change where a multiplicity falls by one instead of an assertion
    vanishing).  Under the fourth seed the same formula had `lost = 0` on
    every result (4:D8): that is what survives, and only on results
    containing what is given.

Cited from the fourth derivation (`fourth.cost`) and re-checked
    `has_two_way` and `contains_given` are about a state and survive.
"""

from __future__ import annotations

from fourth.cost import contains_given, has_two_way
from xry.changes import Kind
from xry.cost import given_size

from fifth.changes import Change
from fifth.state import MState

__all__ = [
    "contains_given",
    "cost",
    "cost_anchored",
    "cost_free",
    "cost_free_by_placement",
    "given_size",
    "has_two_way",
    "lost",
    "lost_free",
    "raises_by_one",
]


def lost(state: MState, bra: bool) -> int:
    """How many givens a state with names has destroyed."""
    if state.names is None:
        raise ValueError("destroyed givens are counted on a state with names")
    a, b = state.names
    initial = [(a, b), (b, a)] if bra else [(a, b)]
    if a == b:
        return 1 + len(initial)
    return sum(1 for x, y in initial if not state.has(x, y))


def lost_free(state: MState, bra: bool) -> int:
    """The least `lost` over all placements of the names, in closed form."""
    m0 = 2 if bra else 1
    if state.n == 1:
        return 1 + m0
    if state.m == 0:
        return m0
    if bra and not has_two_way(state):
        return 1
    return 0


def cost_anchored(state: MState, bra: bool) -> int | None:
    """Fewest changes from what is given to `state`, names kept; `None` if it is not a result."""
    if not state.legal or state.n < 1:
        return None
    return state.size - given_size(bra) + 2 * lost(state, bra)


def cost_free(state: MState, bra: bool) -> int | None:
    """Fewest changes to `state`, any rewriting allowed; `None` if it is not a result."""
    if not state.legal or state.n < 1:
        return None
    return state.size - given_size(bra) + 2 * lost_free(state, bra)


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


def raises_by_one(state: MState, change: Change, bra: bool) -> bool:
    """Does `change` (unobstructed, names kept) raise the cost by exactly one?

    A term always; an assertion unless it restores a given; a removal only of
    a given asserted once; an identification only of `a` with `b`.
    """
    if state.names is None:
        raise ValueError("the rule is for states with names")
    a, b = state.names
    givens = {(a, b), (b, a)} if bra else {(a, b)}
    if change.kind is Kind.ADD_TERM:
        return True
    if change.kind is Kind.ADD_ASSERTION:
        return not (a != b and (change.x, change.y) in givens and not state.has(change.x, change.y))
    if change.kind is Kind.REMOVE:
        return a != b and (change.x, change.y) in givens and state.mult_of(change.x, change.y) == 1
    return a != b and {change.x, change.y} == {a, b}
