from __future__ import annotations

from sixth.changes import Change, Kind, perform
from sixth.explore import explore, performed
from sixth.follows import COUNTED, EXTRA_NAMED, EXTRA_SIXTH, EXTRA_UNNAMED, NAMED, UNNAMED, some_xrx, verdict, verdicts
from sixth.invariants import cost_rises_by_at_most_one, fewest_classes, lowered, names_stay_merged, never_decreases
from sixth.state import MState, given
from xry.state import Sameness


def test_the_statements() -> None:
    assert [s.__name__ for s in NAMED] == ["bra_asserted", "arb_asserted", "names_apart", "arb_once"]
    assert len(UNNAMED) == 11 and len(COUNTED) == 4
    assert [s.__name__ for s in EXTRA_NAMED] == ["names_merged"] and [s.__name__ for s in EXTRA_UNNAMED] == ["nothing_asserted"]
    assert [s.__name__ for s in EXTRA_SIXTH] == ["some_xrx"]
    assert some_xrx(MState.of(2, [(1, 1)])) and not some_xrx(given(False, Sameness.FREE))


def test_verdicts_on_an_exploration() -> None:
    for bra in (False, True):
        expl = explore(given(bra, Sameness.ANCHORED), 3, rounds=4)
        found = {v.statement: v for v in verdicts(expl)}
        assert found["at_least_one_term"].follows_within_bound and not found["at_least_one_term"].independent
        assert [v.statement for v in verdicts(expl) if v.follows_within_bound] == ["at_least_one_term"]
        for name in (
            "no_xrx", "some_xrx", "arb_asserted", "names_apart", "something_asserted", "at_least_two_terms",
            "bra_asserted", "exactly_two_terms", "nothing_twice", "something_twice", "arb_once", "names_merged",
            "nothing_asserted", "passes_on", "both_ways_never",
        ):  # fmt: skip
            assert found[name].independent, name
        assert found["no_xrx"].in_given and found["no_xrx"].fails_round == 1
        assert found["some_xrx"].holds_round == 1 and not found["some_xrx"].in_given
        assert found["names_merged"].holds_round == 1  # identify a and b, `ara` asserted
        assert found["names_apart"].fails_round == 1
    free = {v.statement: v for v in verdicts(explore(given(True, Sameness.FREE), 3, rounds=3))}
    assert "bra_asserted" not in free and "names_merged" not in free and "some_xrx" in free
    one = verdict(explore(given(False, Sameness.FREE), 2, rounds=0), some_xrx)
    assert one.fails_round == 0 and one.holds_round is None and not one.in_given and one.wording


def test_cost_rises_by_at_most_one_and_names_stay_merged() -> None:
    for sameness in Sameness:
        for bra in (False, True):
            expl = explore(given(bra, sameness), 3, rounds=4)
            for state, change, out in performed(expl):
                assert cost_rises_by_at_most_one(state, out, bra)
                assert names_stay_merged(state, out)
    s = given(False, Sameness.ANCHORED)
    assert not cost_rises_by_at_most_one(s, MState.of(4, [(0, 1)], (0, 1)), False)
    assert not cost_rises_by_at_most_one(s, MState(0, (), None), False)
    assert cost_rises_by_at_most_one(s, MState.of(1, [(0, 0)], (0, 0)), False)  # the identification now costs one
    assert not names_stay_merged(MState.of(2, [], (0, 0)), s)
    assert names_stay_merged(s, MState.of(2, [], (0, 0))) and names_stay_merged(s, s)


def test_what_a_change_can_lower() -> None:
    s = MState.of(3, [(0, 1), (0, 1), (1, 2)], (0, 1))
    assert lowered(s, perform(s, Change(Kind.ADD_TERM))) == ()
    assert lowered(s, perform(s, Change(Kind.REMOVE, 0, 1))) == ("total_multiplicity", "a_multiplicity", "size")
    assert lowered(s, perform(s, Change(Kind.ADD_ASSERTION, 2, 2))) == ("no_xrx",)
    assert lowered(s, perform(s, Change(Kind.IDENTIFY, 1, 2))) == ("terms", "size", "no_xrx")
    tri = MState.of(3, [(0, 1), (1, 2), (2, 0)], (0, 1))
    assert lowered(tri, perform(tri, Change(Kind.REMOVE, 1, 2))) == ("total_multiplicity", "a_multiplicity", "size", "fewest_classes")
    loop = MState.of(2, [(0, 1), (1, 1)], (0, 1))
    assert lowered(loop, perform(loop, Change(Kind.REMOVE, 1, 1))) == ("total_multiplicity", "a_multiplicity", "size")
    assert never_decreases(s, perform(s, Change(Kind.ADD_TERM))) and not never_decreases(s, perform(s, Change(Kind.REMOVE, 0, 1)))
    assert fewest_classes(s) == 2
    expl = explore(given(False, Sameness.ANCHORED), 3, rounds=4)
    seen: set[str] = set()
    for state, change, out in performed(expl):
        seen |= set(lowered(state, perform(state, change)))
    assert seen == {"terms", "total_multiplicity", "a_multiplicity", "size", "fewest_classes", "no_xrx"}
