"""The exploration, the grouping, the twenty-third mapped in, the maps back, reachability, readings, statements."""

from __future__ import annotations

import pytest

from ninth.changes import Change, Kind
from twentyfourth.changes import ID_BOTH, ID_NEVER, Fill, Reading
from twentyfourth.embed import (
    compare_with_twentythird,
    forget_key,
    lift_key,
    read_back,
    record_question,
    record_witnesses,
    smallest_none,
    unfilled_key,
)
from twentyfourth.explore import explore, explore_states, order, performed, shortest_sequences
from twentyfourth.follows import EARLIER, HERE, on_base, verdicts
from twentyfourth.reach import reachable, reached_by_search, search_graph
from twentyfourth.readings import box_fstates, fill_steps, generated_classes, identification_outcomes
from twentyfourth.state import DState, FState, empty, result_key
from twentythird.explore import explore as explore23
from twentythird.state import result_key as key23


def test_explore_protocol() -> None:
    with pytest.raises(ValueError):
        explore_states(0, 3)
    with pytest.raises(ValueError):
        explore_states(2, -1)
    e = explore_states(1, 3, keep_log=True)
    assert e.new_per_round[0] == 1 and len(e.attempts_per_round) == 4
    assert all(x.change == Change(Kind.ADD_TERM) and x.state.n == 1 for x in e.frontier)
    beyond = [a for a in e.log if a.beyond]
    assert beyond and all(a.outcome is None for a in beyond)
    assert all(a.outcome is not None for a in e.log if not a.beyond)
    g = explore(2, 3)
    assert g.bound == 2 and g.rounds == 3
    keys = g.ordered_keys()
    assert keys[0] == (0, (), ()) and g.round_of[keys[0]] == 0
    rep = g.representative(keys[1])
    assert rep.n == 1 and g.fewest_members(keys[1]) == (rep,)
    assert all(g.states.depth[s] < 3 for s, _, _, _ in performed(g.states))
    assert order(empty()) == (0, (), (), ())


def test_not_plain_exploration() -> None:
    g = explore(2, 3, plain_states=False)
    assert g.round_of == explore(2, 3).round_of
    assert len(g.states.depth) > len(explore(2, 3).states.depth)


def test_shortest_sequences() -> None:
    g = explore(2, 4)
    seq = shortest_sequences(g)
    one_filled_two_loops = result_key(FState(DState.of(1, [(0, 0)]), (1,)))
    assert seq[one_filled_two_loops] == 2
    assert seq[(0, (), ())] == 1


def test_twentythird_mapped_in() -> None:
    g = explore(2, 4)
    comp = compare_with_twentythird(g)
    assert not (comp.missing or comp.extra or comp.round_differs or comp.sequences_differ)
    assert comp.forgotten_onto == len(comp.twentythird.round_of) and comp.largest_fibre >= 2
    base = DState.of(2, [(0, 1)])
    assert unfilled_key(base) == lift_key(key23(base))
    k = result_key(FState(base, (1, 0)))
    assert read_back(k) is None and forget_key(k) == key23(base)
    assert read_back(unfilled_key(base)) == key23(base)
    assert smallest_none(g) == (1, (0,), (1,))
    assert smallest_none(explore(2, 1)) is None


def test_record_question() -> None:
    (a, b), (c, d) = record_witnesses()
    assert a.written() == "terms a b; asserted ara" and d.written() == "terms a b c; asserted arb bsa"
    q = record_question(explore23(2, 4))
    assert q.whether_shown and q.records_with_several_sizes >= 1 and q.first is not None
    assert record_question(explore23(1, 2)).first is None


def test_reachability() -> None:
    filled = FState(DState.of(1, []), (1,))
    unfilled = FState(DState.of(1, []), (0,))
    assert not reachable(filled, unfilled, Reading())
    assert reachable(filled, unfilled, Reading(identify=ID_BOTH))
    assert reachable(empty(), unfilled, Reading()) and not reachable(filled, empty(), Reading(identify=ID_NEVER))
    for how in ("either", ID_BOTH, ID_NEVER):
        g = explore(2, 3, Reading(identify=how))
        graph = search_graph(g)
        kf = result_key(filled)
        ku = result_key(unfilled)
        assert (ku in reached_by_search(g, graph, kf)) == (how != "either")


def test_readings_module() -> None:
    assert len(box_fstates(1, 1)) == 8
    s = FState(DState.of(2, [(0, 1)]), (1, 0))
    steps = list(fill_steps(s))
    assert len(steps) == 2 + 4 + 2 and all(result_key(t) == result_key(s) for t in steps)
    classes = generated_classes(1, 1, 2)
    assert len(set(classes.values())) == len({result_key(x) for x in classes})
    out = identification_outcomes(explore(2, 4), Reading(identify=ID_BOTH))
    assert out["identifications"] > 0 and out["other_result"] > 0
    assert out["even_move_other"] > out["even_move_chosen"]


def test_statements() -> None:
    g = explore(2, 3)
    vs = verdicts(g)
    assert len(vs) == len(EARLIER) + len(HERE)
    names = {v.statement: v for v in vs}
    assert not names["some_term_filled"].in_every_result
    assert names["told_apart"].holds_at is not None and names["told_apart"].fails_at is not None
    assert on_base(lambda d: d.n == 1)(FState(DState.of(1, []), (1,)))
    depends = [v for v in verdicts(explore(2, 5)) if v.depends_at is not None]
    assert depends and all(v.results_where_it_depends > 0 for v in depends)


def test_performed_skips_beyond() -> None:
    e = explore_states(1, 2)
    seen = [(s, c) for s, c, _, _ in performed(e)]
    assert all(c != Change(Kind.ADD_TERM) or s.n == 0 for s, c in seen)
    assert any(isinstance(c, Fill) for _, c in seen)
