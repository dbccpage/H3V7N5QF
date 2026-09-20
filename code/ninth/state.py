"""Two-relation states without names, and the empty beginning (ninth seed).

Given by the ninth seed
    Terms are written with letters.  An assertion is written `xry` or `xsy`,
    where `x` and `y` are terms and `r` and `s` are the two relations; it is
    asserted a number of times, its multiplicity; adding raises it by one,
    removing lowers it by one.  Nothing is given: to begin with there are no
    terms and nothing is asserted.  Identifying two terms replaces both by
    one term in every assertion.  Two results that differ only in how their
    terms are written are the same result.

Cited from the eighth derivation (`eighth.state`) and re-checked
    The two-relation state `DState` carries its names optionally; with
    `names = None` it is a state of this seed, and `canonical`, `same`,
    `rewrite` (sameness under any rewriting, acting on both relations at
    once), `pair`, `of_r`, `remove`, `identify` and the cache of least
    writings mention no given and no name: they survive and are imported.  A
    state with no terms (`DState(0, (), ())`) was always representable and
    is now the beginning.  Not imported: `given`, `GIVEN_TERMS`,
    `GIVEN_ASSERTIONS`, `added`, `names_one_term` — every one is about the
    given or the names, which the seed does not have.

Cited from the seventh derivation (`seventh.state`) and re-checked
    `empty`, `has_term`, `added`, `written`, `forget_names` and `name_terms`
    are written again for two relations with the same meaning; the seventh's
    act on one multiplicity function and are used on a part.

Derived (paper, `lean4/Ninth/State.lean`)
    With no names, the rewritings "keeping the names" are all rewritings, so
    the two readings of sameness coincide (the seventh's collapse), and the
    one rewriting still acts on both relations at once (the eighth's C4).

Defined here
    `empty` (the beginning), `has_term`, `added` (what a result adds to what
    is given: its terms and its total multiplicity in both relations, nothing
    being given), `written` (the empty state written in words), `forget_names`
    (the map from an eighth state to a ninth state) and `name_terms` (its
    converse: a ninth state with the names put on one term), `swap` (the two
    relations exchanged — a symmetry the eighth seed did not have, its given
    living in `r`), `of_s` (a seventh state read as a ninth state asserting
    nothing with `r`), `nothing_in`.
"""

from __future__ import annotations

from eighth.state import (
    RELATIONS,
    DState,
    MState,
    Pair,
    canonical,
    forget_canonical_forms,
    identify,
    of_r,
    pair,
    remove,
    rewrite,
    same,
)

__all__ = [
    "RELATIONS",
    "DState",
    "MState",
    "Pair",
    "added",
    "canonical",
    "empty",
    "forget_canonical_forms",
    "forget_names",
    "has_term",
    "identify",
    "name_terms",
    "nothing_in",
    "of_r",
    "of_s",
    "pair",
    "remove",
    "rewrite",
    "same",
    "swap",
    "written",
]


def empty() -> DState:
    """What is given: no terms, nothing asserted in either relation, no names."""
    return DState(0, (), ())


def has_term(state: DState) -> bool:
    """Does `state` have at least one term?"""
    return state.n >= 1


def added(state: DState) -> tuple[int, int]:
    """How many terms and assertions (both relations, with multiplicity) `state` adds to what is given.

    Nothing is given, so a state adds all of its terms and all of its
    assertions; nothing is ever negative.
    """
    return state.n, state.m


def written(state: DState) -> str:
    """The state written in the seed's notation; the empty state in words."""
    if state.n == 0:
        return "no terms; asserted nothing"
    return state.written()


def forget_names(state: DState) -> DState:
    """A state of the eighth seed read as a state of the ninth: the names dropped."""
    return DState(state.n, state.r, state.s, None)


def name_terms(state: DState, c: int) -> DState:
    """A state of the ninth seed read as a state of the eighth: both names on the term `c`."""
    if state.names is not None:
        raise ValueError("a state of the ninth seed carries no names")
    if not 0 <= c < state.n:
        raise ValueError("the names go on a term that is there")
    return DState(state.n, state.r, state.s, (c, c))


def swap(state: DState) -> DState:
    """The same terms with the two relations exchanged: every `xry` read as `xsy` and the converse."""
    return DState(state.n, state.s, state.r, state.names)


def of_s(part: MState) -> DState:
    """A state of the seventh seed read as a two-relation state asserting nothing with `r`."""
    return pair(MState(part.n, (0,) * (part.n * part.n), part.names), part)


def nothing_in(state: DState, rel: str) -> bool:
    """Is nothing asserted with `rel` (`r` or `s`)?"""
    return state.part(rel).m == 0
