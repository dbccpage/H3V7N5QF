"""The eighteenth axiom report refuses a bad build and writes a good one."""

from __future__ import annotations

from collections.abc import Sequence
from pathlib import Path

import pytest

from eighteenth import leanreport
from xry.leanreport import Runner

AXIOMS = "'Seed.Eighteenth.t' does not depend on any axioms\r\n\r\n'Seed.Eighteenth.u' depends on axioms: [propext]\n"


def lean_dir(tmp_path: Path, body: str = "theorem t : True := trivial\n") -> Path:
    root = tmp_path / "lean4"
    (root / "Eighteenth").mkdir(parents=True)
    (root / "Eighteenth" / "Writing.lean").write_text(body, encoding="utf-8")
    return root


def runner(build: int = 0, axioms: int = 0, build_out: str = "Build completed successfully.\n") -> Runner:
    def run(cmd: Sequence[str], cwd: Path) -> tuple[int, str]:
        del cwd
        if list(cmd) == ["lake", "build", "Eighteenth"]:
            return build, build_out
        assert list(cmd) == ["lake", "env", "lean", leanreport.AXIOMS_FILE]
        return axioms, AXIOMS

    return run


def test_report(tmp_path: Path) -> None:
    assert leanreport.AXIOMS_FILE == "Eighteenth/Axioms.lean"
    text = leanreport.report(lean_dir(tmp_path), runner())
    assert text.startswith("lake build Eighteenth: passed\n")
    assert "#print axioms (Eighteenth/Axioms.lean):\n'Seed.Eighteenth.t' does not" in text
    assert "\r" not in text and text.endswith("[propext]\n")


def test_report_fails_loudly(tmp_path: Path) -> None:
    root = lean_dir(tmp_path)
    with pytest.raises(RuntimeError, match="lake build failed"):
        leanreport.report(root, runner(build=1))
    with pytest.raises(RuntimeError, match="axiom report failed"):
        leanreport.report(root, runner(axioms=1))
    warned = "warning: Eighteenth/X.lean:1:8: declaration uses `sorry`\n"
    with pytest.raises(RuntimeError, match="uses sorry"):
        leanreport.report(root, runner(build_out=warned))
    with pytest.raises(RuntimeError, match="forbidden"):
        leanreport.report(lean_dir(tmp_path / "b", "axiom bad : False\n"), runner())

    def odd(cmd: Sequence[str], cwd: Path) -> tuple[int, str]:
        del cwd
        if list(cmd) == ["lake", "build", "Eighteenth"]:
            return 0, "ok\n"
        return 0, "'Seed.u' depends on axioms: [sorryAx]\n"

    with pytest.raises(RuntimeError, match="standard axioms"):
        leanreport.report(root, odd)


def test_main_writes_the_report_and_the_manifest(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    root = lean_dir(tmp_path)
    out = tmp_path / "evidence" / "eighteenth"
    assert leanreport.main(["--lean", str(root), "--out", str(out)], runner()) == 0
    assert (out / "lean_axioms.txt").read_text(encoding="utf-8") == capsys.readouterr().out
    assert "lean_axioms.txt" in (out / "MANIFEST.sha256").read_text(encoding="utf-8")
