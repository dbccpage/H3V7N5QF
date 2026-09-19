from __future__ import annotations

import pytest

from fifth.state import MState as MStateFifth
from fifth.state import identify as identify_fifth
from fourth.state import MState as MStateFourth
from fourth.state import canonical as canonical_fourth
from sixth.state import (
    GIVEN_ASSERTIONS,
    GIVEN_TERMS,
    MState,
    asserts_some_xrx,
    canonical,
    forget_canonical_forms,
    given,
    identify,
    largest_xrx,
    named_xrx,
    names_one_term,
    remove,
    same,
)
from xry.state import Sameness


def test_the_state_is_the_fourth_derivations_and_the_operations_the_fifths() -> None:
    assert MState is MStateFourth is MStateFifth and canonical is canonical_fourth and identify is identify_fifth
    assert (GIVEN_TERMS, GIVEN_ASSERTIONS) == (2, 1)
    assert given(False, Sameness.ANCHORED) == MState.of(2, [(0, 1)], (0, 1))
    assert given(True, Sameness.FREE) == MState.of(2, [(0, 1), (1, 0)])


def test_xrx_is_a_pair_like_any_other() -> None:
    loop = MState.of(2, [(0, 1), (0, 0), (0, 0)], (0, 1))
    assert asserts_some_xrx(loop) and not loop.legal and largest_xrx(loop) == 2
    assert not asserts_some_xrx(given(False, Sameness.FREE)) and largest_xrx(given(False, Sameness.FREE)) == 0
    assert largest_xrx(MState(0, ())) == 0
    assert remove(loop, 0, 0) == MState.of(2, [(0, 1), (0, 0)], (0, 1))
    assert identify(MState.of(2, [(0, 1), (1, 0), (1, 1)], (0, 1)), 0, 1) == MState.of(1, [(0, 0)] * 3, (0, 0))
    assert same(MState.of(2, [(1, 1)]), MState.of(2, [(0, 0)]))
    assert canonical(MState.of(2, [(1, 1)], (1, 0))) == MState.of(2, [(0, 0)], (0, 1))


def test_the_xrx_at_the_named_term() -> None:
    merged = MState.of(2, [(0, 0), (0, 0), (1, 1)], (0, 0))
    assert names_one_term(merged) and named_xrx(merged) == 2
    assert named_xrx(MState.of(1, [], (0, 0))) == 0
    with pytest.raises(ValueError):
        named_xrx(given(False, Sameness.ANCHORED))
    with pytest.raises(ValueError):
        named_xrx(MState.of(1, [(0, 0)]))


def test_the_cache_of_least_writings_can_be_emptied() -> None:
    canonical(MState.of(2, [(1, 1)], (1, 0)))
    assert forget_canonical_forms() >= 1
    assert forget_canonical_forms() == 0
