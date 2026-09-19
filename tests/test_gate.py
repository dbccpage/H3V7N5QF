from __future__ import annotations

import json
from collections.abc import Mapping
from pathlib import Path

import pytest

from xry import gate


def write(tmp_path: Path, lines: int, branches: int, files: Mapping[str, object] | None = None) -> Path:
    report: dict[str, object] = {
        "totals": {
            "covered_lines": lines,
            "num_statements": 100,
            "covered_branches": branches,
            "num_branches": 100,
        }
    }
    if files is not None:
        report["files"] = files
    path = tmp_path / "coverage.json"
    path.write_text(json.dumps(report), encoding="utf-8")
    return path


def file_entry(missing_lines: list[int], missing_branches: list[list[int]] | None = None) -> dict[str, object]:
    """A coverage-JSON per-file record with the given misses (branches as [from, to] pairs)."""
    branches = missing_branches or []
    return {
        "summary": {"missing_lines": len(missing_lines), "missing_branches": len(branches)},
        "missing_lines": missing_lines,
        "missing_branches": branches,
    }


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


# -- the meta-gate: every evidence module is fully covered -------------------
# A dead differential-check branch in an `evidence.py` is an uncovered line;
# it slipped past the 95% floor in three successive derivations. These prove
# the gate now catches exactly that, so the injection discipline is enforced
# and not merely remembered.


def test_uncovered_evidence_names_only_evidence_modules() -> None:
    report = {
        "files": {
            "code/fifth/evidence.py": file_entry([678]),  # a dead check branch
            "code/fifth/reach.py": file_entry([1, 2, 3]),  # not an evidence module
            "code/fourth/evidence.py": file_entry([]),  # fully covered
        }
    }
    found = gate.uncovered_evidence(report)
    assert set(found) == {"code/fifth/evidence.py"}
    assert "678" in found["code/fifth/evidence.py"]


def test_uncovered_evidence_catches_a_partial_branch() -> None:
    # Line run but a branch of it never taken: 0 missing lines, 1 missing branch.
    report = {"files": {"code/sixth/evidence.py": file_entry([], [[376, 377]])}}
    found = gate.uncovered_evidence(report)
    assert set(found) == {"code/sixth/evidence.py"}
    assert "[376, 377]" in found["code/sixth/evidence.py"]


def test_uncovered_evidence_normalises_windows_paths() -> None:
    report = {"files": {"code\\fourth\\evidence.py": file_entry([723])}}
    assert set(gate.uncovered_evidence(report)) == {"code/fourth/evidence.py"}


def test_main_fails_when_an_evidence_module_is_not_fully_covered(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    files = {"code/fifth/evidence.py": file_entry([452, 678])}
    assert gate.main([str(write(tmp_path, 100, 100, files))]) == 1  # rates pass, evidence does not
    out = capsys.readouterr().out
    assert "evidence not fully covered" in out and "code/fifth/evidence.py" in out
    assert "injection test" in out


def test_main_passes_when_evidence_is_clean_though_other_files_are_not(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    files = {
        "code/fifth/evidence.py": file_entry([]),
        "code/fifth/explore.py": file_entry([10, 11]),  # a non-evidence miss does not fail this gate
    }
    assert gate.main([str(write(tmp_path, 100, 100, files))]) == 0
    assert "evidence not fully covered" not in capsys.readouterr().out


def test_main_without_a_files_section_still_reads_the_rates(tmp_path: Path) -> None:
    assert gate.main([str(write(tmp_path, 100, 100))]) == 0
