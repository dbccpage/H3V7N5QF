"""The earlier seeds mapped in, the map back, reachability, the unchosen readings, the statements."""

from __future__ import annotations

from twentythird.embed import (
    canonical_seventh,
    first_pair,
    order_part,
    read_back,
    read_back_direct,
    returns_on_mapped,
    seventh_merges,
    seventh_pair,
    smallest_none,
)
from twentythird.explore import explore
from twentythird.follows import HERE, verdicts
from twentythird.reach import reachable, reached_by_search, search_graph
from twentythird.readings import (
    box_states,
    cost_j3,
    explore_j3,
    generated_classes,
    key_j2,
    key_j3,
    raise_all,
    steps_h1,
)
from twentythird.state import DState, of_r, plain_result, raise_term, result_key


def test_pairs_merge() -> None:
    for a, b in (seventh_pair(), first_pair()):
        assert canonical_seventh(a) != canonical_seventh(b)
        assert result_key(of_r(a)) == result_key(of_r(b))
        assert plain_result(of_r(a)) != plain_result(of_r(b))
    merges = seventh_merges(2, 4)
    assert merges.first_merge_round == 4 and merges.first_merge is not None
    assert merges.seventh_results > merges.results_here
    assert order_part(seventh_pair()[0]) == (2, (0, 2, 0, 0))
    assert seventh_merges(2, 3).first_merge is None


def test_map_back() -> None:
    g = explore(2, 4)
    first = smallest_none(g)
    assert first is not None and g.round_of[first] == 4 and first[0] == 2
    for k in g.round_of:
        assert read_back(g, k) == read_back_direct(g.representative(k))
    counts = returns_on_mapped(g)
    assert counts["answers_none"] > 0 and counts["returns_another"] > 0 and counts["returns_the_original"] > 0
    assert smallest_none(explore(2, 3)) is None
    raised = raise_term(DState(2, (0,) * 4, (0,) * 4), 0)
    assert read_back_direct(raised) == DState(2, (0,) * 4, (0,) * 4)


def test_reach() -> None:
    g = explore(2, 3)
    graph = search_graph(g)
    for s in g.round_of:
        found = reached_by_search(g, graph, s)
        for t in g.round_of:
            assert reachable(g.representative(s), g.representative(t)) == (t in found)


def test_readings() -> None:
    two = DState(2, (0,) * 4, (0,) * 4)
    assert raise_all(two) == DState.of(2, [(0, 1), (1, 0)], [(0, 1), (1, 0)])
    assert plain_result(raise_all(two)) == plain_result(two)
    assert key_j2(raise_term(DState.of(2, [(0, 1)]), 1)) == key_j2(DState.of(2, [(0, 1)]))
    assert len(box_states(1, 1)) == 4
    roots = generated_classes(2, 1, 3, steps_h1)
    same_root = {r for s, r in roots.items() if result_key(s) == result_key(two)}
    assert len(same_root) == 1
    j3 = explore_j3(2, 4)
    assert all(cost_j3(s) == r for r, s in j3.values())
    # loops keep both multiplicities under C-J3
    assert key_j3(DState.of(1, [(0, 0)], [(0, 0)])) != key_j3(DState(1, (0,), (0,)))


def test_statements() -> None:
    g = explore(2, 4)
    found = verdicts(g)
    assert len(found) == 45
    names = {v.statement: v for v in found}
    assert names["nothing_asserted_up_to_raising"].independent
    assert names["one_state_asserting_the_fewest"].fails_at is not None
    assert any(v.depends_at is not None for v in found)
    assert len(HERE) == 2
