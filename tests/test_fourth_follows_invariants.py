from __future__ import annotations

import pytest

from fourth.changes import Change, Kind, perform
from fourth.explore import explore
from fourth.follows import (
    COUNTED,
    NAMED,
    UNNAMED,
    arb_once,
    both_ways_equal,
    lifted,
    nothing_twice,
    same_multiplicity,
    something_twice,
    verdict,
    verdicts,
)
from fourth.invariants import fewest_classes, never_decreases
from fourth.state import MState, given
from second.invariants import fewest_classes as fewest_classes_support
from xry.follows import bra_asserted
from xry.state import Sameness, State


def test_lifted_statements_keep_their_name_and_wording() -> None:
    on_counted = lifted(bra_asserted)
    assert on_counted.__name__ == "bra_asserted" and on_counted.__doc__ == bra_asserted.__doc__
    assert on_counted(MState.of(2, [(0, 1), (1, 0), (1, 0)], (0, 1)))
    assert not on_counted(MState.of(2, [(0, 1), (0, 1)], (0, 1)))
    assert [s.__name__ for s in NAMED] == ["bra_asserted", "arb_asserted", "names_apart", "arb_once"]
    assert len(UNNAMED) == 11 and UNNAMED[-1].__name__ == "at_least_two_terms"
    assert [s.__name__ for s in COUNTED] == [
        "nothing_twice", "something_twice", "same_multiplicity", "both_ways_equal"
    ]  # fmt: skip


def test_counted_statements() -> None:
    once = given(False, Sameness.ANCHORED)
    twice = MState.of(2, [(0, 1), (0, 1)], (0, 1))
    mixed = MState.of(2, [(0, 1), (0, 1), (1, 0)], (0, 1))
    assert nothing_twice(once) and not nothing_twice(twice)
    assert something_twice(twice) and not something_twice(once)
    assert arb_once(once) and not arb_once(twice) and not arb_once(MState.of(2, [(0, 1)], (0, 0)))
    with pytest.raises(ValueError):
        arb_once(given(False, Sameness.FREE))
    assert same_multiplicity(once) and same_multiplicity(twice) and not same_multiplicity(mixed)
    assert same_multiplicity(MState.of(2, [])) and same_multiplicity(MState.of(2, [(0, 1), (0, 1), (1, 0), (1, 0)]))
    assert both_ways_equal(once) and both_ways_equal(twice) and not both_ways_equal(mixed)
    assert both_ways_equal(given(True, Sameness.ANCHORED))


def test_verdicts_on_an_exploration() -> None:
    for bra in (False, True):
        expl = explore(given(bra, Sameness.ANCHORED), 3, rounds=4)
        found = {v.statement: v for v in verdicts(expl)}
        for name in ("arb_asserted", "names_apart", "something_asserted", "at_least_two_terms", "no_xrx"):
            assert found[name].follows_within_bound and not found[name].independent
        assert found["bra_asserted"].follows_within_bound == bra
        for name in ("exactly_two_terms", "any_two_related", "every_term_mentioned", "nothing_twice",
                     "something_twice", "arb_once", "same_multiplicity", "both_ways_equal"):
            assert found[name].independent, name
        assert found["passes_on"].independent == (not bra)
        assert found["nothing_twice"].in_given and found["nothing_twice"].fails_round == 1
        assert found["arb_once"].in_given and found["arb_once"].fails_round == 1
        assert not found["something_twice"].in_given and found["something_twice"].holds_round == 1
    free = {v.statement: v for v in verdicts(explore(given(True, Sameness.FREE), 3, rounds=4))}
    assert "bra_asserted" not in free and "arb_once" not in free
    assert free["both_ways_never"].holds_at is None and free["nothing_twice"].independent
    one = verdict(explore(given(False, Sameness.FREE), 2, rounds=0), nothing_twice)
    assert one.follows_within_bound and one.holds_round == 0 and one.fails_round is None and one.wording


def test_fewest_classes_is_the_supports() -> None:
    for state in [
        given(False, Sameness.ANCHORED),
        MState.of(2, [(0, 1), (0, 1), (1, 0)], (0, 1)),
        MState.of(3, [(0, 1), (1, 2), (2, 0), (2, 0)], (0, 1)),
        MState.of(3, [(0, 1), (0, 1), (0, 2)]),
    ]:
        assert fewest_classes(state) == fewest_classes_support(State.of(state.n, state.pairs, state.names))
    assert fewest_classes(MState.of(3, [(0, 1), (1, 2), (2, 0), (2, 0)], (0, 1))) == 3
    assert fewest_classes(MState.of(3, [(0, 1), (0, 1), (0, 2)])) == 2
    with pytest.raises(ValueError):
        fewest_classes(MState.of(1, [(0, 0)]))


def test_never_decreases() -> None:
    s = MState.of(2, [(0, 1), (0, 1)], (0, 1))
    assert never_decreases(s, perform(s, Change(Kind.ADD_TERM)))
    assert never_decreases(s, perform(s, Change(Kind.ADD_ASSERTION, 0, 1)))
    assert never_decreases(s, perform(s, Change(Kind.ADD_ASSERTION, 1, 0)))
    assert not never_decreases(s, MState.of(2, [(0, 1)], (0, 1)))  # a multiplicity lowered
    assert not never_decreases(s, MState.of(2, [(0, 1), (0, 1), (1, 0), (1, 0)], (0, 1)))  # size up by two
    assert not never_decreases(s, MState.of(1, [], (0, 0)))  # fewer terms
    assert not never_decreases(s, s)  # size unchanged
    assert not never_decreases(s, MState.of(2, [(0, 1), (1, 0), (1, 0)], (0, 1)))  # arb lowered, size up by one
