from __future__ import annotations

from second.explore import explore
from second.follows import at_least_two_terms, verdicts
from xry.state import Sameness, State, given


def test_at_least_two_terms() -> None:
    assert at_least_two_terms(State.of(2, [])) and not at_least_two_terms(State.of(1, []))


def test_what_is_given_survives_under_the_second_seed() -> None:
    for bra in (False, True):
        expl = explore(given(bra, Sameness.ANCHORED), 3, rounds=30)
        found = {v.statement: v for v in verdicts(expl)}
        for name in ("arb_asserted", "names_apart", "something_asserted", "at_least_two_terms", "no_xrx"):
            assert found[name].follows_within_bound and not found[name].independent
        assert found["bra_asserted"].follows_within_bound == bra
        assert found["bra_asserted"].in_given == bra
        for name in ("exactly_two_terms", "any_two_related", "every_term_mentioned"):
            assert found[name].independent
        # With `bra` asserted, passing on would force `ara`; it holds in no result.
        assert found["passes_on"].independent == (not bra)
        assert (found["passes_on"].holds_at is None) == bra
        assert found["at_least_two_terms"].wording == "There are at least two terms."


def test_free_explorations_skip_the_statements_that_need_names() -> None:
    expl = explore(given(True, Sameness.FREE), 3, rounds=30)
    found = {v.statement: v for v in verdicts(expl)}
    assert "bra_asserted" not in found and "passes_on" in found
    assert found["at_least_two_terms"].follows_within_bound
    assert found["something_asserted"].follows_within_bound
    assert found["both_ways_never"].fails_round == 0 and found["both_ways_never"].holds_at is None
