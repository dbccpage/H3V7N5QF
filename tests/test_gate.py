from __future__ import annotations

import json
from pathlib import Path

import pytest

from xry import gate


def write(tmp_path: Path, lines: int, branches: int) -> Path:
    totals = {
        "covered_lines": lines,
        "num_statements": 100,
        "covered_branches": branches,
        "num_branches": 100,
    }
    path = tmp_path / "coverage.json"
    path.write_text(json.dumps({"totals": totals}), encoding="utf-8")
    return path


def test_rates() -> None:
    totals = {"covered_lines": 3, "num_statements": 4, "covered_branches": 1, "num_branches": 2}
    assert gate.rates(totals) == (75.0, 50.0)
    empty = {"covered_lines": 0, "num_statements": 0, "covered_branches": 0, "num_branches": 0}
    assert gate.rates(empty) == (0.0, 0.0)


@pytest.mark.parametrize(
    ("lines", "branches", "code"), [(95, 95, 0), (100, 94, 1), (94, 100, 1), (100, 100, 0)]
)
def test_both_rates_must_pass(
    tmp_path: Path, capsys: pytest.CaptureFixture[str], lines: int, branches: int, code: int
) -> None:
    assert gate.main([str(write(tmp_path, lines, branches))]) == code
    assert "branch coverage" in capsys.readouterr().out
