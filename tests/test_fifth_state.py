from __future__ import annotations

import pytest

from fifth.state import (
    GIVEN_ASSERTIONS,
    GIVEN_TERMS,
    MState,
    canonical,
    forget_canonical_forms,
    given,
    identification_map,
    identify,
    names_one_term,
    remove,
    same,
)
from fourth.state import MState as MStateFourth
from fourth.state import canonical as canonical_fourth
from xry.state import Sameness


def test_the_state_is_the_fourth_derivations() -> None:
    assert MState is MStateFourth and canonical is canonical_fourth
    assert (GIVEN_TERMS, GIVEN_ASSERTIONS) == (2, 1)
    assert given(False, Sameness.ANCHORED) == MState.of(2, [(0, 1)], (0, 1))
    assert given(True, Sameness.FREE) == MState.of(2, [(0, 1), (1, 0)])


def test_remove_lowers_by_one() -> None:
    s = MState.of(2, [(0, 1), (0, 1), (1, 0)], (0, 1))
    assert remove(s, 0, 1) == MState.of(2, [(0, 1), (1, 0)], (0, 1))
    assert remove(remove(s, 0, 1), 0, 1) == MState.of(2, [(1, 0)], (0, 1))
    assert remove(s, 1, 0) == MState.of(2, [(0, 1), (0, 1)], (0, 1))
    with pytest.raises(ValueError):
        remove(remove(s, 1, 0), 1, 0)  # not asserted
    with pytest.raises(ValueError):
        remove(s, 0, 2)  # no such term


def test_identify_adds_up_multiplicities_and_carries_the_names() -> None:
    s = MState.of(3, [(0, 2), (0, 2), (1, 2), (2, 0)], (0, 1))
    merged = identify(s, 0, 1)
    assert merged == MState.of(2, [(0, 1), (0, 1), (0, 1), (1, 0)], (0, 0))
    assert names_one_term(merged) and not names_one_term(s)
    assert identify(MState.of(3, [(0, 1)], (0, 2)), 1, 2) == MState.of(2, [(0, 1)], (0, 1))
    assert identify(MState.of(2, [(0, 1)]), 0, 1) == MState.of(1, [(0, 0)])  # illegal outcome
    assert not identify(MState.of(2, [(0, 1)]), 0, 1).legal
    with pytest.raises(ValueError):
        identify(s, 1, 0)  # written x < y
    assert identification_map(3, 0, 1) == (0, 0, 1)
    assert not names_one_term(MState.of(2, [(0, 1)]))


def test_the_cache_of_least_writings_can_be_emptied() -> None:
    canonical(MState.of(2, [(1, 0)], (1, 0)))
    assert forget_canonical_forms() >= 1
    assert forget_canonical_forms() == 0
    assert same(MState.of(2, [(1, 0)], (1, 0)), MState.of(2, [(0, 1)], (0, 1)))
