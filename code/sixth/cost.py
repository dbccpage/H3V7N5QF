"""The fewest changes that reach a result, in closed form, under the sixth seed.

Derived (paper, `lean4/Sixth/Cost.lean`)
    Let `size = terms + Σ multiplicities` and let `lost` count the destroyed
    givens: with `a ≠ b`, the given assertions (`arb`; `bra` too if given)
    whose multiplicity is zero, as the first and fifth derivations; with `a`
    and `b` one term `c`, `m0 + 1 − min(M(c,c), m0)` — the merge itself, plus
    the given assertions the merge did not carry into `crc`.  Then
    `size + 2·lost` rises by at most one per change (the identification of
    `a` with `b` no longer needs nothing asserted between them: its outcome
    asserts `crc` at least as often as the givens were present) and the
    fewest changes from what is given to any well-formed state with a term
    is

        size − size(given) + 2·lost.

    Under FREE the names may be placed at will: `lost_free` is the least of
    the names-apart closed form (`lost_apart_free`, the first derivation's:
    `m0` with nothing off-diagonal, `1` with `bra` given and no pair asserted
    both ways, `0` otherwise) and the names-one-term form at the term with
    the largest `crc` (`lost_merged_free`).  A change raises the cost by
    exactly one (names kept) exactly as `raises_by_one` says.

Cited from the fifth derivation (`fifth.cost`) and re-checked
    `lost` there is the destroyed givens with `m0 + 1` for the names one
    term: it agrees with this module's on every state asserting no `xrx` and
    on every state with the names apart (`lost_fifth`, compared in
    `sixth.evidence`), and disagrees on a state with the names one term and
    `crc` asserted.  Its cost therefore survives on those states only.
    `contains_given` (the fourth's) and `given_size` (the first's) mention
    no legality and survive.  The fourth's `has_two_way` does *not* survive:
    it takes a pair `(x, y)` with `(y, x)` asserted as asserted both ways,
    which counts `xrx` once it is allowed; it is written again for pairs of
    two terms.
"""

from __future__ import annotations

from fifth.cost import contains_given, given_size
from fifth.cost import lost as lost_fifth
from xry.changes import Kind

from sixth.changes import Change
from sixth.state import MState, largest_xrx

__all__ = [
    "contains_given",
    "cost",
    "cost_anchored",
    "cost_free",
    "cost_free_by_placement",
    "given_size",
    "has_off_diagonal",
    "has_two_way",
    "lost",
    "lost_apart_free",
    "lost_fifth",
    "lost_free",
    "lost_merged_free",
    "merged_optimal",
    "raises_by_one",
]


def lost(state: MState, bra: bool) -> int:
    """How many givens a state with names has destroyed."""
    if state.names is None:
        raise ValueError("destroyed givens are counted on a state with names")
    a, b = state.names
    m0 = 2 if bra else 1
    if a == b:
        return m0 + 1 - min(state.mult_of(a, a), m0)
    initial = [(a, b), (b, a)] if bra else [(a, b)]
    return sum(1 for x, y in initial if not state.has(x, y))


def has_off_diagonal(state: MState) -> bool:
    """Is some `xry` with `x ≠ y` asserted?"""
    return any(x != y for x, y in state.pairs)


def has_two_way(state: MState) -> bool:
    """Are some `xry` and `yrx` with `x ≠ y` both asserted?"""
    return any(x != y and state.has(y, x) for x, y in state.pairs)


def lost_apart_free(state: MState, bra: bool) -> int | None:
    """The least `lost` over placements of the names on two terms; `None` with fewer than two."""
    if state.n < 2:
        return None
    if bra:
        return 0 if has_two_way(state) else (1 if has_off_diagonal(state) else 2)
    return 0 if has_off_diagonal(state) else 1


def lost_merged_free(state: MState, bra: bool) -> int:
    """The least `lost` over placements of both names on one term."""
    if state.n < 1:
        raise ValueError("no result is without terms")
    m0 = 2 if bra else 1
    return m0 + 1 - min(largest_xrx(state), m0)


def lost_free(state: MState, bra: bool) -> int:
    """The least `lost` over all placements of the names, in closed form."""
    merged = lost_merged_free(state, bra)
    apart = lost_apart_free(state, bra)
    return merged if apart is None else min(apart, merged)


def merged_optimal(state: MState, bra: bool) -> bool:
    """Does some optimal placement of the names put them on one term?"""
    return lost_merged_free(state, bra) == lost_free(state, bra)


def cost_anchored(state: MState, bra: bool) -> int | None:
    """Fewest changes from what is given to `state`, names kept; `None` if it is not a result."""
    if state.n < 1:
        return None
    return state.size - given_size(bra) + 2 * lost(state, bra)


def cost_free(state: MState, bra: bool) -> int | None:
    """Fewest changes to `state`, any rewriting allowed; `None` if it is not a result."""
    if state.n < 1:
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
    """Does `change` (names kept) raise the cost by exactly one?

    A term always.  An assertion unless it restores a given (names apart) or
    is `crc` with `crc` asserted fewer than `m0` times (names one term).  A
    removal only of a given asserted once (names apart) or of `crc` asserted
    at most `m0` times (names one term).  An identification only of `a` with
    `b`, and only when `min(S, m0) = p`, where `S` is what `crc` will be
    asserted (`arb + bra + ara + brb`) and `p` the number of givens present.
    """
    if state.names is None:
        raise ValueError("the rule is for states with names")
    a, b = state.names
    m0 = 2 if bra else 1
    givens = {(a, b), (b, a)} if bra else {(a, b)}
    if change.kind is Kind.ADD_TERM:
        return True
    x, y = change.x, change.y
    if change.kind is Kind.ADD_ASSERTION:
        if a != b:
            return not ((x, y) in givens and not state.has(x, y))
        return not (x == y == a and state.mult_of(a, a) < m0)
    if change.kind is Kind.REMOVE:
        if a != b:
            return (x, y) in givens and state.mult_of(x, y) == 1
        return x == y == a and state.mult_of(a, a) <= m0
    if a == b or {x, y} != {a, b}:
        return False
    present = sum(1 for p in givens if state.has(*p))
    merged = state.mult_of(a, b) + state.mult_of(b, a) + state.mult_of(a, a) + state.mult_of(b, b)
    return min(merged, m0) == present
