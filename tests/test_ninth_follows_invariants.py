from __future__ import annotations

from ninth.changes import changes, perform
from ninth.explore import explore
from ninth.follows import STATEMENTS, nothing_at_all, unchanged_by_exchange, verdict, verdicts
from ninth.invariants import fewest_classes, lowered, size_moves_by_one, term_stays
from ninth.state import DState, empty, swap


def test_no_statement_holds_in_every_result() -> None:
    expl = explore(empty(), 3, 5)
    found = verdicts(expl)
    assert len(found) == len(STATEMENTS) == 42
    assert all(v.independent and not v.follows_within_bound for v in found)
    by_name = {v.statement: v for v in found}
    assert by_name["nothing_at_all"].in_given and by_name["nothing_at_all"].holds_at == empty()
    assert by_name["nothing_at_all"].fails_round == 1 and by_name["nothing_at_all"].holds_round == 0
    assert not by_name["at_least_one_term_r"].in_given and by_name["at_least_one_term_r"].fails_at == empty()
    assert by_name["at_least_one_term_r"].holds_round == 1
    assert by_name["nothing_in_s"].fails_round == 2 and by_name["nothing_in_r"].fails_round == 2
    assert by_name["unchanged_by_exchange"].holds_round == 0 and by_name["unchanged_by_exchange"].fails_round == 2
    assert by_name["some_pair_in_both"].holds_round == 3
    assert by_name["no_xrx_s"].wording == "In `s`: No `xsx` is asserted."
    assert nothing_at_all(empty()) and not nothing_at_all(DState.of(1, [], []))
    assert unchanged_by_exchange(empty()) and not unchanged_by_exchange(DState.of(1, [(0, 0)], []))
    assert unchanged_by_exchange(DState.of(1, [(0, 0)], [(0, 0)])) and swap(DState.of(1, [(0, 0)], [])) == DState.of(1, [], [(0, 0)])
    single = verdict(explore(empty(), 2, 0), nothing_at_all)
    assert single.follows_within_bound and not single.independent and single.fails_at is None


def test_what_a_change_keeps_and_what_it_does_not() -> None:
    assert size_moves_by_one(empty(), DState.of(1, [], [])) and not size_moves_by_one(empty(), empty())
    assert term_stays(empty(), empty()) and term_stays(DState.of(1, [], []), DState.of(2, [], []))
    assert not term_stays(DState.of(1, [], []), empty())
    assert fewest_classes(empty().r_part()) == 0 and fewest_classes(DState.of(2, [(0, 1)], []).r_part()) == 2
    assert lowered(empty(), DState.of(1, [], [])) == ()
    two = DState.of(2, [(0, 1)], [(0, 1)])
    assert lowered(two, DState.of(1, [(0, 0)], [(0, 0)])) == ("terms", "size", "no_xrx", "no_xsx")
    assert lowered(two, DState.of(2, [], [])) == (
        "total_r",
        "total_s",
        "a_multiplicity",
        "size",
        "fewest_classes_r",
        "fewest_classes_s",
    )
    for state in explore(empty(), 3, 4).depth:
        for change in changes(state):
            out = perform(state, change)
            assert size_moves_by_one(state, out) and term_stays(state, out)
