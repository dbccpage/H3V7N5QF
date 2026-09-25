"""What filled triples tell, the twenty-third mapped in, reachability, the readings and the statements."""

from __future__ import annotations

from itertools import combinations

from ninth.changes import Change, Kind
from twentythird.explore import explore as explore23
from twentythird.state import DState, is_nothing, plain_of

from twentyfifth.embed import compare_twentythird, forget_fibres, read_back, read_back_of_mark
from twentyfifth.embed import seventh_pairs_merged, smallest_none
from twentyfifth.explore import explore
from twentyfifth.follows import FILLED, on_state, verdicts
from twentyfifth.reach import reachable, reached_by_search, search_graph
from twentyfifth.readings import CHOSEN, READINGS, Reading, balances_under, explore_reading, i3_reach_failures
from twentyfifth.state import FState, embed, empty25, oriented_triples, result_mark
from twentyfifth.told import (
    antisymmetric_rows,
    blind,
    blind_by_description,
    decides,
    keeping_sets,
    keeping_sets_by_restriction,
    rank,
    record_differs_from_nothing,
    restrict,
    told,
    undecided_witness,
    why_not_told,
)


def z(n: int) -> DState:
    return DState(n, (0,) * (n * n), (0,) * (n * n))


def test_told_and_why_not() -> None:
    arc = DState.of(3, [(0, 1)], [(1, 0)])
    assert told(FState(arc, ((0, 1, 2),))) and record_differs_from_nothing(FState(arc, ((0, 1, 2),)))
    assert why_not_told(FState(arc, ((0, 1, 2),))) == "told"
    assert why_not_told(FState(z(3), ((0, 1, 2),))) == "the result asserting nothing"
    assert why_not_told(FState(arc, ())) == "nothing filled"
    loop = DState.of(3, [(0, 0)], [])
    assert why_not_told(FState(loop, ((0, 1, 2), (0, 2, 1)))) == "differs from nothing only at loops"
    blind3 = DState.of(3, [(0, 1), (0, 2)], [(2, 1), (2, 0)])
    assert why_not_told(FState(blind3, ((0, 1, 2),))) == "blind: every sum around zero both ways round"
    two = DState.of(4, [(2, 3)], [(3, 2)])
    assert why_not_told(FState(two, ((0, 1, 2), (0, 1, 3)))) == "a sum around not zero only off the filled triples"
    assert not record_differs_from_nothing(FState(two, ((0, 1, 2), (0, 1, 3))))


def test_blind_and_its_description() -> None:
    blind3 = DState.of(3, [(0, 1), (0, 2)], [(2, 1), (2, 0)])
    blind4 = DState.of(4, [(1, 0), (2, 3)], [(0, 2), (3, 1)])
    assert blind(blind3) and blind_by_description(blind3) and not is_nothing(blind3)
    assert blind(blind4) and blind_by_description(blind4) and not is_nothing(blind4)
    assert blind(DState.of(2, [(0, 1)], [])) and blind_by_description(DState.of(2, [(0, 1)], []))
    five = DState.of(5, [(0, 0)], [])
    assert blind(five) and blind_by_description(five)
    assert not blind(DState.of(5, [(0, 1)], [])) and not blind_by_description(DState.of(5, [(0, 1)], []))
    assert not blind_by_description(DState.of(3, [(0, 1)], [(1, 0)]))
    assert not blind_by_description(DState.of(4, [(0, 1)], []))
    assert not told(FState(blind4, oriented_triples(4)))


def test_keeping_sets_by_sums_and_by_restriction() -> None:
    for state, want in (
        (DState.of(3, [(0, 0)], [(1, 1)]), ((0,), (1,))),
        (DState.of(3, [(0, 1)], [(1, 2)]), ((0, 1), (1, 2))),
        (DState.of(3, [(0, 1)], [(1, 0)]), ((0, 1, 2),)),
        (z(3), ()),
    ):
        assert keeping_sets(state) == want
        assert keeping_sets_by_restriction(state) == want
    assert keeping_sets_by_restriction(DState.of(3, [(0, 1)], [(1, 0)]), most=2) == ()
    assert restrict(DState.of(3, [(1, 2)], []), (1, 2)).r == (0, 1, 0, 0)


def test_rank_decides_and_witnesses() -> None:
    assert rank([[1, 2], [2, 4]]) == 1 and rank([[0, 1], [1, 0]]) == 2 and rank([]) == 0
    assert decides(2, []) and not decides(3, []) and decides(3, [(0, 1, 2)])
    assert decides(4, [(0, 1, 2), (0, 1, 3), (0, 2, 3)]) and not decides(4, [(0, 1, 2), (0, 1, 3)])
    assert antisymmetric_rows(3, [(0, 2, 1)]) == [[-1, 1, -1]]
    assert undecided_witness(3, [(0, 1, 2)]) is None
    w = undecided_witness(4, [(0, 1, 2), (0, 1, 3)])
    assert w is not None
    state = plain_of(4, w)
    assert not is_nothing(state)
    cone = [t for t in combinations(range(5), 3) if 0 in t]
    assert decides(5, cone) and undecided_witness(5, cone) is None
    halves = undecided_witness(5, [(0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 2, 3), (1, 2, 4)])
    assert halves is not None and not is_nothing(plain_of(5, halves))


def test_the_twentythird_mapped_in_and_the_map_back() -> None:
    g = explore(3, 5)
    report = compare_twentythird(g, explore23(3, 5))
    assert report.missing_here == report.extra_here == report.rounds_differing == 0
    assert report.returned_the_original == report.twentythird_results == report.results_with_nothing_filled
    assert seventh_pairs_merged() == (True, True)
    first = smallest_none(g)
    assert first == (3, (0,) * 9, ((0, 1, 2),))
    assert smallest_none(explore(2, 5)) is None
    assert read_back(FState(z(3), ((0, 1, 2),))) is None and read_back(embed(z(2))) == (2, (0,) * 4)
    assert read_back_of_mark((3, (0,) * 9, ((0, 1, 2),))) is None
    fibres = forget_fibres(g)
    assert fibres[(3, (0,) * 9)] == 3
    g23 = explore23(2, 3)
    bogus = (2, (9, 9, 9, 9))
    g23.round_of[bogus] = 1
    g23.members[bogus] = (z(2),)
    mislabelled = compare_twentythird(explore(2, 3), g23)
    assert mislabelled.returned_the_original == mislabelled.twentythird_results - 1


def test_reachability() -> None:
    g = explore(3, 4)
    graph = search_graph(g)
    empty = result_mark(empty25())
    one = result_mark(FState(z(3), ((0, 1, 2),)))
    assert one in reached_by_search(g, graph, empty)
    assert empty not in reached_by_search(g, graph, one)
    assert result_mark(embed(z(1))) in reached_by_search(g, graph, one)
    assert reachable(empty25(), embed(z(1))) and not reachable(embed(z(1)), empty25())


def test_readings_at_a_small_bound() -> None:
    runs = {r.name: explore_reading(r, 3, 5) for r in READINGS}
    chosen = runs[CHOSEN.name]
    assert chosen.round_of == explore(3, 5).round_of
    for name, run in runs.items():
        if run.reading.identify != "keep":
            assert all(run.cost(m) == r for m, r in run.round_of.items()), name
    keep = next(r for r in runs.values() if r.reading.identify == "keep")
    assert any(keep.cost(m) != r for m, r in keep.round_of.items())
    reaching, filled = i3_reach_failures(keep)
    assert reaching == 0 and filled > 0
    reaching_chosen, filled_chosen = i3_reach_failures(chosen)
    assert reaching_chosen == filled_chosen > 0
    arc = DState.of(3, [(0, 1)], [(1, 0)])
    assert balances_under(Reading("b2", along="either"), arc, (0, 1, 2))
    assert not balances_under(Reading("b2", along="either"), DState.of(3, [(0, 1)], []), (0, 1, 2))
    assert not balances_under(Reading("o2", way_round="set-both"), DState.of(3, [(0, 1)], []), (0, 1, 2))
    assert balances_under(Reading("o3", way_round="set-either"), DState.of(3, [(0, 1)], []), (0, 1, 2))
    counted = runs["C-M2: fillings counted"]
    assert len(counted.round_of) > len(chosen.round_of) and counted.per_round()[0] == 1
    assert any(counted.told(m) for m in counted.round_of)


def test_statements() -> None:
    g = explore(3, 5)
    found = verdicts(g)
    names = {v.statement for v in found}
    assert {f.__name__ for f in FILLED} <= names
    assert not any(v.in_every_result for v in found)
    filled = next(v for v in found if v.statement == "some_triple_filled")
    assert filled.independent
    assert on_state(is_nothing)(embed(z(2)))
    identify = Change(Kind.IDENTIFY, "", 0, 1)
    assert identify.kind is Kind.IDENTIFY
