"""Coarser writings of the thirteenth seed.

Given by the thirteenth seed
    A coarser writing of an assertion forgets whether it was written with
    `r` or with `s`.  For every result, record also its coarser writing.
    Two results that differ only in which relation wrote their assertions
    may be the same coarser result.

Chosen here (reading C-C1 of the paper)
    The coarser writing of a two-relation state is the one-relation state
    whose multiplicity at each ordered pair is the sum of the `r` and `s`
    multiplicities.  It is computed from the result, not stored as a third
    multiplicity.  Two finer results are the same coarser result when their
    coarser writings are the same up to rewriting of terms.  The coarser
    writing determines the finer one when it has a unique two-relation
    preimage: that holds exactly when nothing is asserted.

Cited from the ninth derivation (`ninth.state`) and re-checked
    `same`, `swap`, `canonical` mention no coarser writing: they survive
    and are imported.  The coarser writing is not a third multiplicity
    beside `r` and `s` (the state is the ninth's).
"""

from __future__ import annotations

from fourth.state import canonical as canonical_one
from ninth.changes import Change, Kind, perform
from ninth.state import DState, MState, same, swap

__all__ = [
    "add_r_or_s_same_coarser",
    "coarse",
    "coarse_key",
    "determines",
    "same_coarser",
    "splits",
    "swap_keeps_coarse",
]


def coarse(state: DState) -> MState:
    """The coarser writing: one multiplicity, the sum of `r` and `s`."""
    return MState(state.n, tuple(a + b for a, b in zip(state.r, state.s)), None)


def coarse_key(state: DState) -> str:
    """A compact identifier of the coarser writing, after rewriting of terms."""
    return canonical_one(coarse(state)).key()


def determines(state: DState) -> bool:
    """Does the coarser writing have a unique finer preimage?

    The splits of a sum `N` are the pairs `(A, B)` with `A + B = N`
    componentwise.  That pair is unique exactly when `N` is zero, i.e. when
    nothing is asserted.
    """
    return state.m == 0


def same_coarser(left: DState, right: DState) -> bool:
    """Are `left` and `right` the same coarser result (up to rewriting of terms)?"""
    return canonical_one(coarse(left)) == canonical_one(coarse(right))


def splits(state: DState) -> int:
    """How many finer splits of this writing of the terms have this coarser writing.

    For each ordered pair the multiplicity `N = r + s` admits `N + 1` ways
    to split between the two relations.  The product is 1 exactly when
    nothing is asserted.
    """
    n = 1
    for a, b in zip(state.r, state.s):
        n *= a + b + 1
    return n


def add_r_or_s_same_coarser(state: DState, x: int, y: int) -> bool:
    """Do adding `xry` and adding `xsy` land on the same coarser writing and differ as finer results?"""
    added_r = perform(state, Change(Kind.ADD_ASSERTION, "r", x, y))
    added_s = perform(state, Change(Kind.ADD_ASSERTION, "s", x, y))
    return same_coarser(added_r, added_s) and not same(added_r, added_s)


def swap_keeps_coarse(state: DState) -> bool:
    """Does exchanging the two relations keep the coarser writing?"""
    return coarse(swap(state)) == coarse(state)
