from __future__ import annotations

from eighth.changes import changes, perform
from eighth.explore import explore
from eighth.follows import JOINT, nothing_in_s, on_part, relations_agree, statements, verdict, verdicts
from eighth.invariants import cost_rises_by_at_most_one, fewest_classes, lowered, names_stay_merged
from eighth.state import DState, given
from fourth.follows import UNNAMED
from xry.state import Sameness


def test_statements_on_each_part_and_jointly() -> None:
    expl = explore(given(False, Sameness.ANCHORED), 3, 4)
    found = verdicts(expl)
    assert len(found) == len(statements(True)) == 2 * (4 + 1 + 11 + 1 + 1 + 4) + len(JOINT) == 50
    by_name = {v.statement: v for v in found}
    assert [v.statement for v in found if v.follows_within_bound] == ["at_least_one_term_r", "at_least_one_term_s"]
    assert by_name["nothing_in_s"].in_given and by_name["nothing_in_s"].fails_round == 1
    assert by_name["arb_asserted_r"].in_given and not by_name["arb_asserted_s"].in_given
    assert by_name["arb_asserted_s"].wording == "In `s`: `asb` is asserted."
    assert by_name["no_xrx_s"].wording == "In `s`: No `xsx` is asserted."
    assert by_name["relations_agree"].holds_round == 1 and by_name["some_pair_in_both"].holds_round == 1
    assert by_name["nothing_in_r"].holds_round == 1 and by_name["s_within_r"].in_given and not by_name["r_within_s"].in_given
    free = verdicts(explore(given(True, Sameness.FREE), 2, 3))
    assert len(free) == len(statements(False)) == 2 * (11 + 1 + 1 + 4) + len(JOINT) == 40
    lifted = on_part(UNNAMED[0], "s")
    assert lifted.__name__ == "both_ways_always_s" and lifted(DState.of(2, [(0, 1)], [(0, 1), (1, 0)]))
    assert nothing_in_s(given(False, Sameness.FREE)) and relations_agree(DState.of(2, [(0, 1)], [(0, 1)]))
    single = verdict(explore(given(False, Sameness.FREE), 2, 0), nothing_in_s)
    assert single.follows_within_bound and not single.independent


def test_what_a_change_keeps_and_what_it_does_not() -> None:
    g = given(False, Sameness.ANCHORED)
    with_s = DState.of(2, [(0, 1)], [(0, 1)], (0, 1))
    assert cost_rises_by_at_most_one(g, with_s, False) and not cost_rises_by_at_most_one(g, DState(0, (), ()), False)
    assert names_stay_merged(g, with_s) and not names_stay_merged(DState.of(1, [], [], (0, 0)), g)
    assert fewest_classes(with_s.s_part()) == 2
    assert lowered(with_s, g) == ("total_s", "a_multiplicity", "size", "fewest_classes_s")
    assert lowered(with_s, DState.of(1, [(0, 0)], [(0, 0)], (0, 0))) == ("terms", "size", "no_xrx", "no_xsx")
    assert lowered(DState.of(2, [(0, 1)], [(0, 1)], (0, 1)), DState.of(2, [], [], (0, 1))) == (
        "total_r", "total_s", "a_multiplicity", "size", "fewest_classes_r", "fewest_classes_s",
    )  # fmt: skip
    for state in explore(g, 2, 3).depth:
        for change in changes(state):
            out = perform(state, change)
            assert cost_rises_by_at_most_one(state, out, False) and names_stay_merged(state, out)
