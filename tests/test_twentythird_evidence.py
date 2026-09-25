"""The evidence writer, and an injection test for every disagreement branch of every check."""

from __future__ import annotations

import json
from collections.abc import Iterator
from pathlib import Path
from typing import Any

import pytest

from ninth.changes import Change, Kind
from ninth.explore import explore as real_ninth
from twentythird import evidence
from twentythird.embed import Merges, seventh_pair
from twentythird.evidence import (
    Plan,
    RaisingCheck,
    audit,
    check_changes,
    check_read_back,
    check_reach,
    check_readings,
    check_respect,
    check_results,
    check_sameness,
    compare_with_ninth,
    compare_with_plain,
    compare_with_seventh,
    four_term_witness,
    key_text,
    run_tag,
    write_all,
    write_given,
)
from twentythird.explore import Grouped, explore
from twentythird.state import DState, excess_table, raise_term

SMALL = Plan(
    bound=2,
    rounds=4,
    ninth_rounds=4,
    deep_bound=3,
    deep_rounds=4,
    deep_ninth_rounds=3,
    two_term_rounds=5,
    two_term_ninth_rounds=4,
    log_bound=2,
    log_rounds=2,
    reach_bound=2,
    reach_rounds=3,
    same_small=1,
    same_large=3,
    readings_bound=2,
    readings_rounds=4,
    search_terms=3,
    layers_upto=5,
    count_upto=4,
    closed_form_upto=6,
    witness_weight=1,
)


def small() -> Grouped:
    return explore(2, 4)


def test_plan_and_tag() -> None:
    assert Plan().runs() == ((5, 8, 8), (3, 10, 9), (2, 24, 12))
    assert run_tag(3, 4) == "bound3_rounds4"
    assert key_text((2, (0, 1, -1, 0))) == "2:0,1,-1,0"


def test_audit_is_clean() -> None:
    check = audit(3, 5, 5)
    assert check.clean()
    assert set(check.as_dict()) == {f for f in RaisingCheck.__dataclass_fields__}


def test_write_all(tmp_path: Path) -> None:
    summary = write_all(tmp_path, SMALL)
    assert summary["every_check_clean"] is True
    names = {p.name for p in tmp_path.iterdir()}
    assert {"given.json", "summary.json", "counts.csv", "readings.json", "MANIFEST.sha256"} <= names
    assert "results_bound2_rounds4.csv" in names and "reach_bound2_rounds3.csv" in names
    assert "attempts_bound2_rounds2.jsonl" in names
    given = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    assert given["raising_a_on_two_terms"]["the_result_asserting_nothing_here"] is True
    assert given["raising_a_on_two_terms"]["the_twentysecond_result_asserting_nothing"] is False
    assert given["adding_a_term_to_two_states_of_one_result"]["one_result_after"] is False
    assert given["identifying_two_terms_in_two_states_of_one_result"]["one_result_after"] is False
    assert [x["cost_after_adding_a_term"] for x in given["adding_a_term_can_raise_the_cost_by_2k_plus_1"]] == [5, 7, 9]
    assert given["four_terms_single_terms_do_not_find_the_fewest"] is None
    assert given["the_map_back"]["on_a_b_arb_arb"] is None
    assert given["the_map_back"]["on_a_b_arb_bsa"] == "terms a b; asserted nothing"
    runs = summary["runs"]
    assert isinstance(runs, dict)
    for run in runs.values():
        assert all(run["rounds_agreeing_with_unbounded_count"])


def test_given_with_the_four_term_witness(tmp_path: Path) -> None:
    write_given(tmp_path, Plan())
    given = json.loads((tmp_path / "given.json").read_text(encoding="utf-8"))
    w = given["four_terms_single_terms_do_not_find_the_fewest"]
    assert w["assertions"] == 5 and w["fewest"] == 3 and w["sets_that_lower_it"]
    assert four_term_witness(1) is None


# --- injections: each forces one disagreement and proves its branch fires ------------------


def test_round_closed_form_and_search(monkeypatch: pytest.MonkeyPatch) -> None:
    g = explore(3, 4)
    monkeypatch.setattr(evidence, "cost", lambda s: -1)
    monkeypatch.setattr(evidence, "cost_closed", lambda s: -5)
    monkeypatch.setattr(evidence, "search_fewest", lambda s: 99)
    check = RaisingCheck()
    check_results(g, check, search_terms=3)
    assert check.round_not_cost and check.closed_form_mismatch
    assert any(x.startswith("search") for x in check.closed_form_mismatch)
    assert any(x.startswith("closed form") for x in check.closed_form_mismatch)


def test_fewest_and_record(monkeypatch: pytest.MonkeyPatch) -> None:
    g = small()
    monkeypatch.setattr(evidence, "fewest_states", lambda s: [])
    monkeypatch.setattr(evidence, "record", lambda s: (0, 0, 0))
    check = RaisingCheck()
    check_results(g, check)
    assert check.fewest_mismatch and check.record_mismatch


def test_characterization(monkeypatch: pytest.MonkeyPatch) -> None:
    g = small()
    monkeypatch.setattr(evidence, "set_moves_least", lambda n, t: True)
    check = RaisingCheck()
    check_results(g, check)
    assert any(x.startswith("sets") for x in check.characterization_mismatch)
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "single_moves_least", lambda n, t: False)
    monkeypatch.setattr(evidence, "together_free_of_opposites", lambda n, t: False)
    check = RaisingCheck()
    check_results(g, check)
    assert any(x.startswith("single terms") for x in check.characterization_mismatch)
    assert any(x.startswith("two terms") for x in check.characterization_mismatch)


def test_nothing_exchange_counts(monkeypatch: pytest.MonkeyPatch) -> None:
    g = small()
    monkeypatch.setattr(evidence, "sum_profile", lambda s: s)
    monkeypatch.setattr(evidence, "nothing_certificate", lambda s: None)
    monkeypatch.setattr(evidence, "swap", lambda s: s)
    monkeypatch.setattr(evidence, "counts_within", lambda b, r: {})
    monkeypatch.setattr(evidence, "two_term_round_count", lambda r: -1)
    check = RaisingCheck()
    check_results(g, check)
    assert any(x.startswith("sums differ") for x in check.nothing_mismatch)
    assert any(not x.startswith("sums differ") for x in check.nothing_mismatch)
    assert check.exchange_mismatch and check.count_mismatch and check.two_term_mismatch


def test_one_term_bound_skips_the_two_term_form() -> None:
    check = RaisingCheck()
    g = explore(1, 3)
    check_results(g, check)
    compare_with_seventh(g, check)
    check_read_back(g, check)
    assert check.clean()


def test_changes(monkeypatch: pytest.MonkeyPatch) -> None:
    g = small()
    start = DState(0, (), ())
    add = Change(Kind.ADD_TERM, "", 0, 0)
    far = DState.of(2, [(0, 1)])  # cost 3
    outside = DState.of(3, [(0, 1)])  # three terms: not formed within two
    one = DState(1, (0,), (0,))

    def fake(_expl: Any) -> Iterator[tuple[DState, Change, DState, DState]]:
        yield start, add, far, far
        yield start, add, outside, outside
        yield one, add, one, one

    monkeypatch.setattr(evidence, "performed", fake)
    check = RaisingCheck()
    check_changes(g, check)
    kinds = {x.split(":")[0] for x in check.change_mismatch}
    assert kinds == {"from a state asserting the fewest", "outcome not formed", "parity"}


def test_respect(monkeypatch: pytest.MonkeyPatch) -> None:
    g = small()
    monkeypatch.setattr(evidence, "outcome_key", lambda s, c: (s.n, excess_table(s)))
    check = RaisingCheck()
    check_respect(g, check)
    assert check.respect_mismatch


def test_plain_ninth_seventh(monkeypatch: pytest.MonkeyPatch) -> None:
    g = small()
    monkeypatch.setattr(evidence, "plain_cost", lambda s: -1)
    monkeypatch.setattr(
        evidence, "explore_ninth", lambda start, bound, rounds: real_ninth(start, bound, max(rounds - 1, 0))
    )
    a, _ = seventh_pair()
    monkeypatch.setattr(evidence, "seventh_pair", lambda: (a, a))
    monkeypatch.setattr(evidence, "first_pair", lambda: (a, a))
    monkeypatch.setattr(evidence, "seventh_merges", lambda b, r: Merges(1, 1, 1, None, None))
    check = RaisingCheck()
    compare_with_plain(g, check)
    compare_with_ninth(g, 4, check)
    compare_with_seventh(g, check)
    assert check.plain_mismatch and check.ninth_mismatch
    assert set(check.seventh_mismatch) == {"the seventh pair", "the first seed's pair", "no merge of seventh results at round 4"}


def test_read_back_and_reach(monkeypatch: pytest.MonkeyPatch) -> None:
    g = small()
    monkeypatch.setattr(evidence, "read_back_direct", lambda s: None)
    monkeypatch.setattr(evidence, "smallest_none", lambda gr: None)
    monkeypatch.setattr(evidence, "reachable", lambda s, t: True)
    check = RaisingCheck()
    check_read_back(g, check)
    check_reach(g, check)
    assert check.reach_mismatch
    assert "the first result answered none is not a two-term result of round 4" in check.read_back_mismatch
    assert len(check.read_back_mismatch) > 1


def test_sameness(monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(evidence, "result_key", lambda s: (s.n, excess_table(s)))
    check = RaisingCheck()
    check_sameness(1, 3, check)
    assert any(x.startswith("joined but not the same") for x in check.sameness_mismatch)
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "steps_h1", lambda s: iter(()))
    check = RaisingCheck()
    check_sameness(1, 3, check)
    assert any(x.startswith("the same but not joined") for x in check.sameness_mismatch)


def test_readings(monkeypatch: pytest.MonkeyPatch) -> None:
    g = small()
    monkeypatch.setattr(evidence, "raise_all", lambda s: raise_term(s, 0) if s.n else s)
    monkeypatch.setattr(evidence, "key_j2", lambda s: (s.n, s.m))
    monkeypatch.setattr(evidence, "cost_j3", lambda s: -1)
    check = RaisingCheck()
    check_readings(2, 3, check, g)
    kinds = {x.split(":")[0] for x in check.readings_mismatch}
    assert kinds == {"C-H2", "C-J2", "C-J3"}
