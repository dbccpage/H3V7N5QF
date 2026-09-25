"""The launcher (`--check`) and the Lean report writer of the twenty-fourth derivation."""

from __future__ import annotations

from collections.abc import Sequence
from pathlib import Path

import pytest

import lean_report_twentyfourth
import run_twentyfourth
from twentyfourth import __main__ as cli
from twentyfourth import leanreport
from twentyfourth.evidence import Plan
from xry.leanreport import Runner

SMALL = Plan(
    bound=2,
    rounds=3,
    deep_bound=2,
    deep_rounds=2,
    two_term_rounds=3,
    log_bound=2,
    log_rounds=1,
    reach_bound=2,
    reach_rounds=3,
    same_small=1,
    same_large=3,
    readings_bound=2,
    readings_rounds=2,
    layers_upto=3,
    closed_form_upto=3,
    points_upto=2,
)


def test_launchers_import() -> None:
    assert getattr(run_twentyfourth, "main") is cli.main
    assert getattr(lean_report_twentyfourth, "main") is leanreport.main


def test_write_then_check(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    out = tmp_path / "ev"
    assert cli.main(["--out", str(out)], SMALL) == 0
    assert cli.main(["--out", str(out), "--check"], SMALL) == 0
    (out / "counts.csv").write_text("changed\n", encoding="utf-8")
    assert cli.main(["--out", str(out), "--check"], SMALL) == 1
    assert cli.main(["--out", str(tmp_path / "missing"), "--check"], SMALL) == 1
    assert "missing evidence directory" in capsys.readouterr().out


def test_write_reports_a_disagreement(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    monkeypatch.setattr(cli, "write_all", lambda _out, _plan: {"every_check_clean": False})
    assert cli.main(["--out", str(tmp_path)], SMALL) == 1


def test_default_plan(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    seen: list[Plan] = []

    def fake(_out: Path, plan: Plan) -> dict[str, object]:
        seen.append(plan)
        return {"every_check_clean": True}

    monkeypatch.setattr(cli, "write_all", fake)
    assert cli.main(["--out", str(tmp_path)]) == 0
    assert seen == [Plan()]


GOOD = "'Twentyfourth.cost24' depends on axioms: [propext, Quot.sound]\n'Twentyfourth.x' does not depend on any axioms\n"


def runner_for(build: tuple[int, str], axioms: tuple[int, str]) -> Runner:
    def runner(cmd: Sequence[str], _cwd: Path) -> tuple[int, str]:
        return build if "build" in cmd else axioms

    return runner


def test_report_passes(tmp_path: Path, capsys: pytest.CaptureFixture[str]) -> None:
    lean = tmp_path / "lean"
    lean.mkdir()
    (lean / "A.lean").write_text("theorem t : True := trivial -- no sorry here\n", encoding="utf-8")
    out = tmp_path / "out"
    assert leanreport.main(["--lean", str(lean), "--out", str(out)], runner_for((0, "ok"), (0, GOOD))) == 0
    text = (out / "lean_axioms.txt").read_text(encoding="utf-8")
    assert "axioms allowed: propext, Quot.sound" in text and "cost24" in text
    assert "lake build Twentyfourth" in text
    assert (out / "MANIFEST.sha256").is_file()
    assert "passed" in capsys.readouterr().out


@pytest.mark.parametrize(
    ("build", "axioms", "message"),
    [
        ((1, "boom"), (0, GOOD), "lake build failed"),
        ((0, "declaration uses 'sorry'"), (0, GOOD), "uses sorry"),
        ((0, "ok"), (1, "error"), "axiom report failed"),
        ((0, "ok"), (0, "'T.x' depends on axioms: [propext, Classical.choice, Quot.sound]\n"), "other than propext"),
    ],
)
def test_report_refuses(tmp_path: Path, build: tuple[int, str], axioms: tuple[int, str], message: str) -> None:
    with pytest.raises(RuntimeError, match=message):
        leanreport.report(tmp_path, runner_for(build, axioms))


def test_report_refuses_a_sorry_in_the_sources(tmp_path: Path) -> None:
    (tmp_path / "B.lean").write_text("theorem t : True := by sorry\n", encoding="utf-8")
    with pytest.raises(RuntimeError, match="forbidden"):
        leanreport.report(tmp_path, runner_for((0, "ok"), (0, GOOD)))
