from __future__ import annotations

import pytest

from fifth.state import identify as identify_fifth
from fourth.state import MState as MStateFourth
from fourth.state import canonical as canonical_fourth
from seventh.state import (
    MState,
    added,
    asserts_some_xrx,
    canonical,
    empty,
    forget_canonical_forms,
    forget_names,
    has_term,
    identify,
    largest_xrx,
    name_terms,
    remove,
    rewrite,
    same,
    support,
    written,
)


def test_the_state_is_the_fourth_derivations_without_names() -> None:
    assert MState is MStateFourth and canonical is canonical_fourth and identify is identify_fifth
    start = empty()
    assert start == MState(0, ()) and start.n == 0 and start.m == 0 and start.size == 0 and start.names is None
    assert canonical(start) == start and rewrite(start, ()) == start and support(start).n == 0
    assert not has_term(start) and has_term(MState.of(1, []))
    assert added(start) == (0, 0) and added(MState.of(2, [(0, 1), (0, 1), (1, 1)])) == (2, 3)
    assert written(start) == "no terms; asserted nothing"
    assert written(MState.of(2, [(0, 1)])) == "terms a b; asserted arb"
    assert start.key() == "0::" and start.legal and start.simple and not asserts_some_xrx(start)
    assert largest_xrx(start) == 0 and largest_xrx(MState.of(1, [(0, 0), (0, 0)])) == 2


def test_the_two_readings_of_sameness_coincide_without_names() -> None:
    # A rewriting keeps the names when there are none: every rewriting does, so
    # the least writing is the least over all rewritings.
    s = MState.of(2, [(1, 1), (1, 0)])
    assert same(s, MState.of(2, [(0, 0), (0, 1)])) and canonical(s) == MState.of(2, [(1, 0), (1, 1)])
    assert remove(MState.of(1, [(0, 0)]), 0, 0) == MState.of(1, [])
    assert identify(MState.of(2, [(0, 1), (1, 0), (1, 1)]), 0, 1) == MState.of(1, [(0, 0)] * 3)


def test_the_maps_to_and_from_the_sixth_seeds_states() -> None:
    named = MState.of(2, [(0, 1)], (0, 1))
    assert forget_names(named) == MState.of(2, [(0, 1)]) and forget_names(forget_names(named)).names is None
    assert name_terms(MState.of(2, [(0, 1)]), 1) == MState.of(2, [(0, 1)], (1, 1))
    assert forget_names(name_terms(MState.of(1, [(0, 0)]), 0)) == MState.of(1, [(0, 0)])
    with pytest.raises(ValueError):
        name_terms(named, 0)
    with pytest.raises(ValueError):
        name_terms(empty(), 0)
    with pytest.raises(ValueError):
        name_terms(MState.of(1, []), 1)


def test_the_cache_of_least_writings_can_be_emptied() -> None:
    canonical(MState.of(2, [(1, 1)]))
    assert forget_canonical_forms() >= 1
    assert forget_canonical_forms() == 0
