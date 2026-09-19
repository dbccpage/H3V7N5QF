from __future__ import annotations

from seventh.changes import changes, perform
from seventh.explore import explore
from seventh.follows import STATEMENTS, nothing_at_all, verdict, verdicts
from seventh.invariants import fewest_classes, lowered, size_moves_by_one, term_stays
from seventh.state import MState, empty


def test_no_statement_holds_in_every_result() -> None:
    expl = explore(empty(), 3, 5)
    found = verdicts(expl)
    assert len(found) == len(STATEMENTS) == 18
    assert all(v.independent and not v.follows_within_bound for v in found)
    by_name = {v.statement: v for v in found}
    assert by_name["nothing_at_all"].in_given and by_name["nothing_at_all"].holds_at == empty()
    assert by_name["nothing_at_all"].fails_round == 1 and by_name["nothing_at_all"].holds_round == 0
    assert not by_name["at_least_one_term"].in_given and by_name["at_least_one_term"].fails_at == empty()
    assert by_name["at_least_one_term"].holds_round == 1
    assert by_name["no_xrx"].fails_round == 2 and by_name["some_xrx"].holds_round == 2
    assert by_name["nothing_asserted"].wording == "Nothing is asserted."
    assert nothing_at_all(empty()) and not nothing_at_all(MState.of(1, []))
    single = verdict(explore(empty(), 2, 0), nothing_at_all)
    assert single.follows_within_bound and not single.independent and single.fails_at is None


def test_what_a_change_keeps_and_what_it_does_not() -> None:
    assert size_moves_by_one(empty(), MState.of(1, [])) and not size_moves_by_one(empty(), empty())
    assert term_stays(empty(), empty()) and term_stays(MState.of(1, []), MState.of(2, []))
    assert not term_stays(MState.of(1, []), empty())
    assert fewest_classes(empty()) == 0 and fewest_classes(MState.of(2, [(0, 1)])) == 2
    assert lowered(empty(), MState.of(1, [])) == ()
    two = MState.of(2, [(0, 1)])
    assert lowered(two, MState.of(1, [(0, 0)])) == ("terms", "size", "no_xrx")  # fewest classes compared between states with no xrx only
    assert lowered(two, MState.of(2, [])) == ("total_multiplicity", "a_multiplicity", "size", "fewest_classes")
    for state in explore(empty(), 3, 4).depth:
        for change in changes(state):
            out = perform(state, change)
            assert size_moves_by_one(state, out) and term_stays(state, out)
