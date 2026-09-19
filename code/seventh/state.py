"""Counted states without names, and the empty beginning (seventh seed).

Given by the seventh seed
    Terms are written with letters.  An assertion `xry` is asserted a number
    of times, its multiplicity; adding raises it by one, removing lowers it
    by one.  Nothing is given: to begin with there are no terms and nothing
    is asserted.  Identifying two terms replaces both by one term in every
    assertion.  Two results that differ only in how their terms are written
    are the same result.

Cited from the fourth, fifth and sixth derivations (`fourth.state`,
`fifth.state`, `sixth.state`) and re-checked
    The counted state `MState` carries its names optionally; with
    `names = None` it is a state of this seed, and `canonical`, `same`,
    `rewrite` (sameness under any rewriting), `support`, `of_state`,
    `remove`, `identify` and the cache of least writings mention no given and
    no name: they survive and are imported.  A state with no terms
    (`MState(0, ())`) was always representable and is now the beginning.
    Not imported: `given`, `GIVEN_TERMS`, `GIVEN_ASSERTIONS`, `added`,
    `names_one_term`, `named_xrx` — every one is about the given or the
    names, which the seed does not have.

Derived (paper, `lean4/Seventh/State.lean`)
    With no names, the rewritings "keeping the names" are all rewritings, so
    the two readings of sameness of the earlier derivations coincide: one
    reading, one beginning.

Defined here
    `empty` (the beginning), `has_term`, `added` (what a result adds to what
    is given: its terms and its total multiplicity, nothing being given),
    `written` (the empty state written in words), `forget_names` (the map
    from a sixth state to a seventh state) and `name_terms` (its converse:
    a seventh state with the names put on one term).
"""

from __future__ import annotations

from fifth.state import forget_canonical_forms, identify, remove
from fourth.state import MState, Pair, canonical, of_state, rewrite, same, support
from sixth.state import asserts_some_xrx, largest_xrx

__all__ = [
    "MState",
    "Pair",
    "added",
    "asserts_some_xrx",
    "canonical",
    "empty",
    "forget_canonical_forms",
    "forget_names",
    "has_term",
    "identify",
    "largest_xrx",
    "name_terms",
    "of_state",
    "remove",
    "rewrite",
    "same",
    "support",
    "written",
]


def empty() -> MState:
    """What is given: no terms, nothing asserted, no names."""
    return MState(0, ())


def has_term(state: MState) -> bool:
    """Does `state` have at least one term?"""
    return state.n >= 1


def added(state: MState) -> tuple[int, int]:
    """How many terms and assertions (counted with multiplicity) `state` adds to what is given.

    Nothing is given, so a state adds all of its terms and all of its
    assertions; nothing is ever negative.
    """
    return state.n, state.m


def written(state: MState) -> str:
    """The state written in the seed's notation; the empty state in words."""
    if state.n == 0:
        return "no terms; asserted nothing"
    return state.written()


def forget_names(state: MState) -> MState:
    """A state of the sixth seed read as a state of the seventh: the names dropped."""
    return MState(state.n, state.mult, None)


def name_terms(state: MState, c: int) -> MState:
    """A state of the seventh seed read as a state of the sixth: both names on the term `c`."""
    if state.names is not None:
        raise ValueError("a state of the seventh seed carries no names")
    if not 0 <= c < state.n:
        raise ValueError("the names go on a term that is there")
    return MState(state.n, state.mult, (c, c))
