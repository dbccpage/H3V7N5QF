from __future__ import annotations

from itertools import product
from math import comb

import pytest

from eighth.changes import KINDS, Change, Kind, attempt_counts, changes, is_change, makes_some_loop, perform
from eighth.state import DState, given
from sixth.changes import attempt_counts as attempt_counts_part
from xry.state import Sameness


def test_the_changes_of_what_is_given() -> None:
    g = given(False, Sameness.ANCHORED)
    listed = changes(g)
    assert [c.written(g) for c in listed] == [
        "identify a and b", "remove arb", "add a term",
        "add ara", "add arb", "add bra", "add brb", "add asa", "add asb", "add bsa", "add bsb",
    ]  # fmt: skip
    assert attempt_counts(g) == (11, 3, 2) and len(KINDS) == 4 and all(is_change(c) for c in listed)
    assert Change(Kind.ADD_TERM).additions == (1, 0) and Change(Kind.ADD_ASSERTION, "s", 0, 0).additions == (0, 1)
    assert Change(Kind.IDENTIFY, "", 0, 1).additions == (0, 0)
    assert Change(Kind.REMOVE, "s", 0, 1).part().kind is Kind.REMOVE
    with pytest.raises(ValueError):
        Change(Kind.REMOVE, "", 0, 1)
    with pytest.raises(ValueError):
        Change(Kind.ADD_TERM, "r")
    assert perform(g, Change(Kind.ADD_ASSERTION, "s", 0, 1)) == DState.of(2, [(0, 1)], [(0, 1)], (0, 1))
    assert perform(g, Change(Kind.ADD_TERM)) == DState.of(3, [(0, 1)], [], (0, 1))
    assert perform(g, Change(Kind.IDENTIFY, "", 0, 1)) == DState.of(1, [(0, 0)], [], (0, 0))
    assert perform(g, Change(Kind.REMOVE, "r", 0, 1)) == DState.of(2, [], [], (0, 1))
    assert perform(g, Change(Kind.ADD_ASSERTION, "r", 1, 0)) == given(True, Sameness.ANCHORED)


@pytest.mark.parametrize("n", [1, 2])
def test_attempt_counts_agree_with_the_list_and_the_sixths(n: int) -> None:
    for r in product(range(2), repeat=n * n):
        for s in product(range(2), repeat=n * n):
            state = DState(n, r, s)
            listed = changes(state)
            total, xrx, xsx = attempt_counts(state)
            assert len(listed) == comb(n, 2) + state.distinct + 1 + 2 * n * n == total
            assert xrx == attempt_counts_part(state.r_part())[1] and xsx == attempt_counts_part(state.s_part())[1]
            assert sum(1 for c in listed if makes_some_loop(state, c, "r")) == xrx
            assert sum(1 for c in listed if makes_some_loop(state, c, "s")) == xsx
            for c in listed:
                out = perform(state, c)
                assert abs(out.size - state.size) == 1 and out.n >= 1
