from __future__ import annotations

import pytest

from fourteenth.leftover import leftover_merge, leftover_nothing, leftover_pair
from ninth.changes import Change as NinthChange
from ninth.changes import changes as changes_ninth
from sixteenth.changes import (
    KINDS,
    Change16,
    Kind,
    admissions_of,
    attempt_counts16,
    changes16,
    first_changes16,
    is_addition16,
    is_admission,
    is_direct_addition,
    perform16,
    raises_potential,
)
from sixteenth.leftover import admissible, admissions_of_writing, leftover_of16, other_relation, unadmitted_is_assertion
from sixteenth.state import RState, Reading, empty16


def test_change_shape() -> None:
    assert KINDS == (Kind.IDENTIFY, Kind.REMOVE, Kind.ADD_TERM, Kind.ADD_ASSERTION)
    with pytest.raises(ValueError, match="r or with s"):
        Change16(Kind.REMOVE, "t", 0, 0)
    with pytest.raises(ValueError, match="no relation"):
        Change16(Kind.ADD_TERM, "r")
    with pytest.raises(ValueError, match="only an assertion"):
        Change16(Kind.REMOVE, "r", 0, 0, True)
    admit = Change16(Kind.ADD_ASSERTION, "s", 0, 1, True)
    assert admit.additions == (0, 1) and admit.ninth() == NinthChange(Kind.ADD_ASSERTION, "s", 0, 1)
    assert Change16(Kind.ADD_TERM).additions == (1, 0) and Change16(Kind.IDENTIFY, "", 0, 1).additions == (0, 0)
    assert is_addition16(admit) and is_admission(admit) and not is_direct_addition(admit) and not raises_potential(admit)
    direct = Change16(Kind.ADD_ASSERTION, "r", 0, 0)
    assert is_direct_addition(direct) and raises_potential(direct) and raises_potential(Change16(Kind.REMOVE, "r", 0, 0))
    assert not raises_potential(Change16(Kind.IDENTIFY, "", 0, 1))
    rs = RState.of(2, [(0, 1)], [], [(0, 1)])
    assert admit.written(rs) == "admit aℓb into s" and direct.written(rs) == "add ara"


def test_changes_are_the_ninth_list_then_the_admissions() -> None:
    assert first_changes16() == (Change16(Kind.ADD_TERM),)
    rs = RState.of(2, [(0, 1)], [(1, 1)], [(0, 1), (1, 0)])
    listed = changes16(rs)
    ninth = changes_ninth(rs.state)
    assert [c.ninth() for c in listed[: len(ninth)]] == list(ninth)
    tail = listed[len(ninth) :]
    assert tail == admissions_of(0, 1)[:1] + admissions_of(1, 0)[:1] + admissions_of(0, 1)[1:] + admissions_of(1, 0)[1:]
    total, direct, admissions = attempt_counts16(rs)
    assert total == len(listed) and admissions == 4 and direct == 1 + 2 * 4
    assert attempt_counts16(empty16()) == (1, 1, 0)


def test_perform_each_kind() -> None:
    rs = RState.of(2, [(0, 1)], [], [(1, 0)])
    assert perform16(rs, Change16(Kind.ADD_TERM)).n == 3
    assert perform16(rs, Change16(Kind.ADD_ASSERTION, "s", 1, 1)).state.s == (0, 0, 0, 1)
    removed = perform16(rs, Change16(Kind.REMOVE, "r", 0, 1))
    assert removed.state.total_r == 0 and removed.recorded(0, 1) == 1 and removed.recorded(1, 0) == 1
    admitted = perform16(rs, Change16(Kind.ADD_ASSERTION, "r", 1, 0, True))
    assert admitted.state.r == (0, 1, 1, 0) and admitted.record_empty
    merged = perform16(rs, Change16(Kind.IDENTIFY, "", 0, 1))
    assert merged.n == 1 and merged.state.r == (1,) and merged.recorded(0, 0) == 1
    assert perform16(rs, Change16(Kind.IDENTIFY, "", 0, 1), Reading.DROP).record_empty
    assert perform16(RState.of(1, [(0, 0)], [], [(0, 0)]), Change16(Kind.REMOVE, "r", 0, 0), Reading.SET).recorded(0, 0) == 1


def test_leftover_writings_and_admissibility() -> None:
    rs = RState.of(2, [(0, 1)], [], [(1, 1)])
    assert leftover_of16(rs, Change16(Kind.ADD_TERM)) == leftover_nothing()
    assert leftover_of16(rs, Change16(Kind.REMOVE, "r", 0, 1)) == leftover_pair(0, 1)
    assert leftover_of16(rs, Change16(Kind.IDENTIFY, "", 0, 1)) == leftover_merge(0, 1)
    assert leftover_of16(rs, Change16(Kind.ADD_ASSERTION, "r", 1, 1, True)) == leftover_nothing()
    assert not admissible(leftover_pair(0, 1), rs) and admissible(leftover_pair(1, 1), rs)
    assert not admissible(leftover_merge(1, 1), rs) and not admissible(leftover_nothing(), rs)
    assert not admissible(leftover_pair(5, 5), rs)
    assert admissions_of_writing(leftover_pair(1, 1), rs) == admissions_of(1, 1)
    assert admissions_of_writing(leftover_pair(0, 1), rs) == ()
    assert not unadmitted_is_assertion(leftover_pair(0, 1))
    assert other_relation("r") == "s" and other_relation("s") == "r"
    # after the removal its own writing is admissible on the outcome
    out = perform16(rs, Change16(Kind.REMOVE, "r", 0, 1))
    assert admissible(leftover_pair(0, 1), out)
