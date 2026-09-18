from __future__ import annotations

import pytest

from xry import follows as f
from xry.explore import explore
from xry.state import Sameness, State, given


def test_statements_about_a_and_b() -> None:
    a = given(False, Sameness.ANCHORED)
    b = given(True, Sameness.ANCHORED)
    one = State.of(1, [], (0, 0))
    assert f.arb_asserted(a) and not f.bra_asserted(a) and f.names_apart(a)
    assert f.arb_asserted(b) and f.bra_asserted(b)
    assert not f.arb_asserted(one) and not f.bra_asserted(one) and not f.names_apart(one)
    with pytest.raises(ValueError):
        f.bra_asserted(given(True, Sameness.FREE))


def test_statements_about_the_asserting() -> None:
    edge = State.of(2, [(0, 1)])
    both = State.of(2, [(0, 1), (1, 0)])
    path = State.of(3, [(0, 1), (1, 2)])
    closed = State.of(3, [(0, 1), (1, 2), (0, 2)])
    assert not f.both_ways_always(edge) and f.both_ways_always(both)
    assert f.both_ways_never(edge) and not f.both_ways_never(both)
    assert f.passes_on(edge) and not f.passes_on(path) and f.passes_on(closed)
    assert not f.passes_on(both)  # arb and bra would pass on to ara
    assert f.any_two_related(edge) and not f.any_two_related(path) and f.any_two_related(closed)
    assert f.every_term_first(both) and not f.every_term_first(edge)
    assert f.every_term_mentioned(path) and not f.every_term_mentioned(State.of(3, [(0, 1)]))
    assert f.exactly_two_terms(edge) and not f.exactly_two_terms(path)
    assert f.something_asserted(edge) and not f.something_asserted(State.of(2, []))
    assert f.at_least_one_term(State.of(1, [])) and not f.at_least_one_term(State(0, 0))
    assert f.no_xrx(edge) and not f.no_xrx(State.of(1, [(0, 0)]))


def test_bra_does_not_follow_and_neither_does_its_denial() -> None:
    for bra in (False, True):
        expl = explore(given(bra, Sameness.ANCHORED), 3, rounds=30)
        found = {v.statement: v for v in f.verdicts(expl)}
        v = found["bra_asserted"]
        assert v.independent and v.in_given == bra and not v.follows_within_bound
        assert {v.holds_round, v.fails_round} == {0, 1}
        assert found["no_xrx"].follows_within_bound and not found["no_xrx"].independent
        assert found["at_least_one_term"].follows_within_bound
        for name in ("arb_asserted", "names_apart", "passes_on", "both_ways_never"):
            assert found[name].independent
        assert found["bra_asserted"].wording == "`bra` is asserted."


def test_free_explorations_skip_the_statements_that_need_names() -> None:
    expl = explore(given(False, Sameness.FREE), 3, rounds=30)
    names = [v.statement for v in f.verdicts(expl)]
    assert "bra_asserted" not in names and "passes_on" in names


def test_a_statement_that_never_holds() -> None:
    expl = explore(given(False, Sameness.FREE), 2, rounds=5)
    v = f.verdict(expl, lambda state: state.n > 5)
    assert v.holds_at is None and v.holds_round is None and not v.independent
    assert v.fails_round == 0 and v.wording == ""
