from __future__ import annotations

import re
from collections.abc import Sequence
from pathlib import Path

import pytest

import lean_report_seventeenth
from seventeenth import leanreport
from xry.leanreport import Runner

REPO = Path(__file__).resolve().parents[1]

AXIOMS ="'Seed.Seventeenth.t' does not depend on any axioms\r\n\r\n'Seed.Seventeenth.u' depends on axioms: [propext]\n"


def lean_dir(tmp_path: Path, body: str = "theorem t : True := trivial\n") -> Path:
    root = tmp_path / "lean4"
    (root / "Seventeenth").mkdir(parents=True)
    (root / "Seventeenth" / "Step.lean").write_text(body, encoding="utf-8")
    return root


def runner(build: int = 0, axioms: int = 0, build_out: str = "Build completed successfully.\n") -> Runner:
    def run(cmd: Sequence[str], cwd: Path) -> tuple[int, str]:
        if list(cmd) == ["lake", "build"]:
            return build, build_out
        assert list(cmd) == ["lake", "env", "lean", leanreport.AXIOMS_FILE]
        return axioms, AXIOMS

    return run


def test_report(tmp_path: Path) -> None:
    assert lean_report_seventeenth.main is leanreport.main
    assert leanreport.AXIOMS_FILE == "Seventeenth/Axioms.lean"
    text = leanreport.report(lean_dir(tmp_path), runner())
    assert text.startswith("lake build: passed\n")
    assert "#print axioms (Seventeenth/Axioms.lean):\n'Seed.Seventeenth.t' does not" in text
    assert "\r" not in text and text.endswith("[propext]\n")


def test_report_fails_loudly(tmp_path: Path) -> None:
    root = lean_dir(tmp_path)
    with pytest.raises(RuntimeError, match="lake build failed"):
        leanreport.report(root, runner(build=1))
    with pytest.raises(RuntimeError, match="axiom report failed"):
        leanreport.report(root, runner(axioms=1))
    warned = "warning: Seventeenth/X.lean:1:8: declaration uses `sorry`\n"
    with pytest.raises(RuntimeError, match="uses sorry"):
        leanreport.report(root, runner(build_out=warned))
    with pytest.raises(RuntimeError, match="forbidden"):
        leanreport.report(lean_dir(tmp_path / "b", "axiom bad : False\n"), runner())

    def odd(cmd: Sequence[str], cwd: Path) -> tuple[int, str]:
        return 0, "ok\n" if list(cmd) == ["lake", "build"] else "'Seed.u' depends on axioms: [sorryAx]\n"

    with pytest.raises(RuntimeError, match="standard axioms"):
        leanreport.report(root, odd)


def test_every_cited_seventeenth_theorem_is_reported() -> None:
    """Each theorem of `lean4/Seventeenth/` that the ledger or the paper cites
    has its `#print axioms` line in the committed `lean_axioms.txt`."""
    lean = "\n".join(
        path.read_text(encoding="utf-8") for path in sorted((REPO / "lean4" / "Seventeenth").glob("*.lean"))
    )
    theorems = set(re.findall(r"(?m)^theorem\s+([\w.']+)", lean))
    cited: set[str] = set()
    for doc in ("claim_ledger.md", "paper.md"):
        text = (REPO / "paper" / "seventeenth" / doc).read_text(encoding="utf-8")
        cited.update(re.findall(r"`([\w.']+)`", text))
    report = (REPO / "evidence" / "seventeenth" / "lean_axioms.txt").read_text(encoding="utf-8")
    printed = set(re.findall(r"'Seed\.Seventeenth\.([\w.']+)'", report))
    assert theorems & cited, "no cited theorem found: the census is empty"
    assert not sorted((theorems & cited) - printed), sorted((theorems & cited) - printed)


def test_main_writes_the_report_and_the_manifest(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    root = lean_dir(tmp_path)
    out = tmp_path / "evidence" / "seventeenth"
    assert leanreport.main(["--lean", str(root), "--out", str(out)], runner()) == 0
    assert (out / "lean_axioms.txt").read_text(encoding="utf-8") == capsys.readouterr().out
    assert "lean_axioms.txt" in (out / "MANIFEST.sha256").read_text(encoding="utf-8")
