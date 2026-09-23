"""The eighteenth sameness keeps each writing."""

from __future__ import annotations

from pathlib import Path

import pytest

from eighteenth import evidence, explore, writing
from eighteenth.evidence import audit, write_all
from eighteenth.explore import answer_other_writing, explore_written
from eighteenth.writing import (
    aut_size,
    letter_supply,
    orbit,
    orbit_size,
    orbit_splits_factorial,
    same_written,
)
from xry.explore import explore as explore_base
from xry.state import Sameness, State, canonical, given, rewrite


def test_the_swap_of_what_is_given_is_another_writing() -> None:
    start = given(False, Sameness.ANCHORED)
    swapped = rewrite(start, (1, 0))
    assert swapped in orbit(start)
    assert not same_written(start, swapped)
    assert orbit_size(start) == 2 and aut_size(start) == 1
    assert orbit_splits_factorial(start)
    bare = State(start.n, start.mask, None)
    swapped_bare = State(swapped.n, swapped.mask, None)
    assert canonical(bare) == canonical(swapped_bare)


def test_letter_supply_counts_injections() -> None:
    assert letter_supply(2, 1, 25) == 25 * 24
    assert letter_supply(3, 1, 25) == 25 * 24 * 23
    with pytest.raises(ValueError):
        letter_supply(3, 1, 2)
    with pytest.raises(ValueError):
        letter_supply(1, 0, 2)


def test_written_exploration_keeps_more_than_the_base() -> None:
    start = given(False, Sameness.ANCHORED)
    written = explore_written(start, 3, 12)
    base = explore_base(start, 3, 12)
    assert len(written.depth) == 137
    assert len(base.depth) == 109
    assert len({canonical(state) for state in written.depth}) == 109
    classes: dict[State, int] = {}
    for state in written.depth:
        classes[canonical(state)] = classes.get(canonical(state), 0) + 1
    assert sum(1 for count in classes.values() if count > 1) == 28
    assert answer_other_writing(written) == []
    assert written.new_per_round[-1] == 0
    free = explore_written(given(False, Sameness.FREE), 3, 12)
    anchored_bra = explore_written(given(True, Sameness.ANCHORED), 3, 12)
    assert set(written.depth) == set(anchored_bra.depth)
    assert len(free.depth) == 69


def test_audit_records_a_collapse_a_bad_count_and_a_short_round(monkeypatch: pytest.MonkeyPatch) -> None:
    start = given(False, Sameness.ANCHORED)
    other = rewrite(start, (1, 0))
    depth = explore_written(start, 2, 4).depth
    clean = audit(depth, False, start, other)
    assert clean == evidence.WritingCheck([], [], [])
    monkeypatch.setattr(evidence, "same_written", lambda _left, _right: True)
    assert f"{start.key()} = {other.key()}" in audit(depth, False, start, other).writings_called_the_same
    monkeypatch.undo()
    # The base's sameness would call the two writings one result; the key does not.
    monkeypatch.setattr(evidence, "same_written", lambda left, right: canonical(left) == canonical(right))
    assert audit(depth, False, start, other).writings_called_the_same
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "orbit_splits_factorial", lambda _state: False)
    assert start.key() in audit(depth, False, start, other).orbit_formula_fails
    monkeypatch.undo()
    monkeypatch.setattr(evidence, "cost", lambda _state, _bra: 99)
    assert start.key() in audit(depth, False, start, other).rounds_below_the_base_cost


def test_base_count_is_the_same_for_every_writing() -> None:
    start = given(True, Sameness.FREE)
    for state in explore_written(start, 3, 12).depth:
        counts = {evidence.base_count(writing, True) for writing in orbit(state)}
        assert counts == {evidence.base_count(state, True)}


def test_letter_supply_grows_with_every_letter() -> None:
    assert evidence.letter_supply_grows(3, 1)
    assert evidence.letter_supply_grows(1, 1, 1)
    assert not evidence.letter_supply_grows(0, 1, 1)


def test_explore_rejects_a_bad_start_and_an_illegal_outcome(monkeypatch: pytest.MonkeyPatch) -> None:
    start = given(False, Sameness.ANCHORED)
    with pytest.raises(ValueError):
        explore_written(State.of(1, [(0, 0)], (0, 0)), 3, 1)
    with pytest.raises(ValueError):
        explore_written(start, 1, 1)

    def illegal(state: State, change: object) -> State:
        del change
        return State.of(state.n, [(0, 0)], state.names)

    monkeypatch.setattr(explore, "perform", illegal)
    with pytest.raises(RuntimeError):
        explore_written(start, 3, 1)


def test_write_and_check(tmp_path: Path) -> None:
    summary = write_all(tmp_path, 3, 12)
    assert summary["given_orbit"] == 2
    assert summary["anchored_closures_equal_for_both_bra"] is True
    assert summary["free_closures_equal_for_both_bra"] is True
    runs = summary["runs"]
    assert isinstance(runs, list)
    for run in runs:
        assert run["writings_called_the_same"] == run["orbit_formula_fails"] == []
        assert run["rounds_below_the_base_cost"] == []
        assert run["sample_letter_supply_grows"] is True
    excess = [(run["rounds_above_the_base_cost"], run["greatest_excess_over_the_base_cost"]) for run in runs]
    assert excess == [(0, 0), (32, 2), (0, 0), (29, 4)]
    from eighteenth.__main__ import main

    assert main(["--out", str(tmp_path), "--check", "--bound", "3", "--rounds", "12"]) == 0
    assert main(["--out", str(tmp_path / "missing"), "--check"]) == 1


def test_main_writes_and_reports_a_difference(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    from eighteenth.__main__ import main

    out = tmp_path / "eighteenth"
    assert main(["--out", str(out), "--bound", "2", "--rounds", "4"]) == 0
    assert f"wrote {out}" in capsys.readouterr().out
    assert main(["--out", str(out), "--check", "--bound", "2", "--rounds", "4"]) == 0
    (out / "summary.json").write_text("{}\n", encoding="utf-8")
    assert main(["--out", str(out), "--check", "--bound", "2", "--rounds", "4"]) == 1
