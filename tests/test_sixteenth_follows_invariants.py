from __future__ import annotations

import pytest

from fourteenth.leftover import leftover_nothing, leftover_pair
from sixteenth import invariants
from sixteenth.changes import Change16, Kind, changes16
from sixteenth.explore import explore16
from sixteenth import follows
from sixteenth.follows import (
    CHANGE_STATEMENTS,
    RECORD_STATEMENTS,
    STATEMENTS16,
    change_verdicts,
    every_recorded_pair_unasserted,
    is_admission,
    leaves_admissible,
    nothing_recorded,
    on_state,
    some_recorded_pair_asserted,
    something_recorded,
    verdicts16,
)
from sixteenth.invariants import RecordCheck, check_records
from sixteenth.state import RState, add_assertion16, admit16, empty16


def test_record_statements() -> None:
    plain = RState.of(1, [(0, 0)])
    recorded = RState.of(1, [(0, 0)], [], [(0, 0)])
    unasserted = RState.of(1, [], [], [(0, 0)])
    assert nothing_recorded(plain) and not something_recorded(plain) and every_recorded_pair_unasserted(plain)
    assert something_recorded(recorded) and some_recorded_pair_asserted(recorded) and not every_recorded_pair_unasserted(recorded)
    assert not some_recorded_pair_asserted(unasserted) and every_recorded_pair_unasserted(unasserted)
    assert len(RECORD_STATEMENTS) == 4 and len(STATEMENTS16) > 4
    assert "STATEMENTS16" in follows.__all__ and "STATEMENTS" not in follows.__all__
    read = on_state(lambda s: s.n == 1)
    assert read(plain) and not read(empty16())


def test_verdicts_on_states_and_changes() -> None:
    expl = explore16(empty16(), 2, 5)
    found = verdicts16(expl)
    assert found and all(not v.follows_within_bound for v in found)
    by_name = {v.statement: v for v in found}
    assert by_name["nothing_recorded"].in_given and by_name["nothing_recorded"].independent
    assert by_name["something_recorded"].holds_round == 3 and by_name["something_recorded"].fails_round == 0
    changes_found = change_verdicts(expl)
    names = [v.name for v in changes_found]
    assert names == [name for name, _ in CHANGE_STATEMENTS]
    by = {v.name: v for v in changes_found}
    assert all(not v.follows for v in changes_found)
    assert by["is_assertion_writing"].holds_at is None and by["is_assertion_writing"].fails_at is not None
    assert by["is_admission"].holds_at is not None and by["leaves_admissible"].holds_at is not None
    rs = RState.of(1, [(0, 0)])
    writing = leftover_pair(0, 0)
    assert leaves_admissible(rs, Change16(Kind.REMOVE, "r", 0, 0), writing)
    assert not leaves_admissible(rs, Change16(Kind.ADD_TERM), leftover_nothing())
    assert is_admission(rs, Change16(Kind.ADD_ASSERTION, "r", 0, 0, True), leftover_nothing())


def _nonempty(check: RecordCheck) -> set[str]:
    return {k for k, v in check.__dict__.items() if isinstance(v, list) and v}


def test_check_records_is_clean_and_every_field_bites(monkeypatch: pytest.MonkeyPatch) -> None:
    expl = explore16(empty16(), 2, 4)
    clean = check_records(expl)
    assert clean.checked > 0 and clean.raised > clean.lowered > 0 and clean.admissions > 0
    assert _nonempty(clean) == set()

    monkeypatch.setattr(invariants, "potential", lambda rs: 0)
    assert {"potential_not_moved_by_one", "round_not_potential"} <= _nonempty(check_records(expl))
    monkeypatch.undo()
    monkeypatch.setattr(invariants, "raises_potential", lambda c: True)
    assert "direction_mismatch" in _nonempty(check_records(expl))
    monkeypatch.undo()
    monkeypatch.setattr(invariants, "mass", lambda rs: -(rs.state.m + rs.record_total))
    assert "mass_fell" in _nonempty(check_records(expl))
    monkeypatch.undo()
    monkeypatch.setattr(invariants, "diag_mass", lambda rs: -rs.diagonal_mass)
    assert "diagonal_mass_fell" in _nonempty(check_records(expl))
    monkeypatch.undo()
    monkeypatch.setattr(invariants, "admit16", add_assertion16)
    assert "same_relation_not_identity" in _nonempty(check_records(expl))
    monkeypatch.undo()
    monkeypatch.setattr(invariants, "canonical16", lambda rs: rs.n)
    assert "other_relation_same_as_start" in _nonempty(check_records(expl))
    monkeypatch.undo()
    monkeypatch.setattr(invariants, "add_assertion16", admit16)
    assert "other_relation_same_as_direct" in _nonempty(check_records(expl))
    monkeypatch.undo()
    monkeypatch.setattr(invariants, "leftover_of16", lambda s, c: leftover_pair(0, 0))
    assert {"admission_left_something", "writing_not_the_fourteenth"} <= _nonempty(check_records(expl))
    monkeypatch.undo()
    monkeypatch.setattr("fourteenth.leftover.LeftWriting.is_assertion", lambda self: True)
    assert "unadmitted_asserted" in _nonempty(check_records(expl))
    monkeypatch.undo()

    def extra(rs: RState) -> tuple[Change16, ...]:
        listed = changes16(rs)
        return (*listed, Change16(Kind.ADD_ASSERTION, "r", 0, 0, True)) if rs.n >= 1 else listed

    monkeypatch.setattr(invariants, "changes16", extra)
    assert "admissions_not_recorded" in _nonempty(check_records(expl))
    monkeypatch.undo()

    def missing(rs: RState) -> tuple[Change16, ...]:
        return tuple(c for c in changes16(rs) if not c.admits)

    monkeypatch.setattr(invariants, "changes16", missing)
    assert "admissions_not_recorded" in _nonempty(check_records(expl))
    monkeypatch.undo()

    def out_of_range(rs: RState) -> tuple[Change16, ...]:
        return (*changes16(rs), Change16(Kind.ADD_ASSERTION, "r", 7, 7, True))

    monkeypatch.setattr(invariants, "changes16", out_of_range)
    assert "admissions_not_recorded" in _nonempty(check_records(expl))
