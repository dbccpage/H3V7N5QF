from __future__ import annotations

from collections.abc import Sequence
from pathlib import Path

import pytest

from xry import leanreport

AXIOMS = "'Seed.given_distinct' does not depend on any axioms\r\n\r\n'Seed.x' depends on axioms: [propext]\n"


def lean_dir(tmp_path: Path, body: str = "theorem t : True := trivial\n") -> Path:
    root = tmp_path / "lean4"
    (root / "H3V7N5QF").mkdir(parents=True)
    (root / "H3V7N5QF" / "Basic.lean").write_text(body, encoding="utf-8")
    hidden = root / ".lake" / "packages"
    hidden.mkdir(parents=True)
    (hidden / "Dep.lean").write_text("axiom choice : False\nsorry\n", encoding="utf-8")
    return root


def runner(build: int = 0, axioms: int = 0) -> leanreport.Runner:
    def run(cmd: Sequence[str], cwd: Path) -> tuple[int, str]:
        if list(cmd) == ["lake", "build"]:
            return build, "Build completed successfully.\n"
        assert list(cmd) == ["lake", "env", "lean", leanreport.AXIOMS_FILE]
        return axioms, AXIOMS

    return run


def test_report(tmp_path: Path) -> None:
    text = leanreport.report(lean_dir(tmp_path), runner())
    assert text.startswith("lake build: passed\n")
    assert "'Seed.given_distinct' does not depend on any axioms\n'Seed.x' depends" in text
    assert "\r" not in text and text.endswith("[propext]\n")


def test_report_fails_loudly(tmp_path: Path) -> None:
    root = lean_dir(tmp_path)
    with pytest.raises(RuntimeError, match="lake build failed"):
        leanreport.report(root, runner(build=1))
    with pytest.raises(RuntimeError, match="axiom report failed"):
        leanreport.report(root, runner(axioms=1))


def test_forbidden_words(tmp_path: Path) -> None:
    body = (
        "-- sorry, this comment is fine\n"
        "/- admit nothing,\n   axiom in a comment -/\n"
        "theorem t : True := by\n  sorry\n"
        "axiom bad : False\n"
        "  private axiom worse : False\n"
        "theorem axiomatic : True := trivial\n"
    )
    root = lean_dir(tmp_path, body)
    assert leanreport.forbidden(root) == [
        "H3V7N5QF/Basic.lean: sorry",
        "H3V7N5QF/Basic.lean: axiom",
        "H3V7N5QF/Basic.lean: private axiom",
    ]
    with pytest.raises(RuntimeError, match="forbidden"):
        leanreport.report(root, runner())


@pytest.mark.parametrize(
    "line",
    [
        "@[simp] axiom bad : (1 : Nat) = 2",
        "noncomputable axiom bad : Nat",
        "private noncomputable axiom bad : False",
        "open Nat in axiom bad : False",
        "theorem t : False := sorryAx False false",
    ],
)
def test_forbidden_sees_attributes_modifiers_and_sorryax(tmp_path: Path, line: str) -> None:
    assert leanreport.forbidden(lean_dir(tmp_path, line + "\n"))


def test_nonstandard_axioms() -> None:
    assert leanreport.nonstandard(AXIOMS) == []
    ok = "'Seed.t' depends on axioms: [propext, Classical.choice, Quot.sound]"
    assert leanreport.nonstandard(ok) == []
    user = "'Seed.t' depends on axioms: [propext, Seed.cheat]"
    sorry = "'Seed.u' depends on axioms: [sorryAx]"
    stray = "info: downloading component 'lean'"
    assert leanreport.nonstandard("\n".join([ok, user, sorry, stray])) == [user, sorry, stray]


def run_with(build_out: str, axioms: str) -> leanreport.Runner:
    def run(cmd: Sequence[str], cwd: Path) -> tuple[int, str]:
        return 0, build_out if list(cmd) == ["lake", "build"] else axioms

    return run


def test_report_refuses_sorry_and_nonstandard_axioms(tmp_path: Path) -> None:
    root = lean_dir(tmp_path)
    warned = "warning: H3V7N5QF/X.lean:1:8: declaration uses `sorry`\nBuild completed successfully.\n"
    with pytest.raises(RuntimeError, match="uses sorry"):
        leanreport.report(root, run_with(warned, AXIOMS))
    with pytest.raises(RuntimeError, match="standard axioms"):
        leanreport.report(root, run_with("ok\n", "'Seed.u' depends on axioms: [sorryAx]\n"))


def test_main_writes_the_report_and_the_manifest(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    root = lean_dir(tmp_path)
    out = tmp_path / "evidence"
    assert leanreport.main(["--lean", str(root), "--out", str(out)], runner()) == 0
    assert (out / "lean_axioms.txt").read_text(encoding="utf-8") == capsys.readouterr().out
    assert "lean_axioms.txt" in (out / "MANIFEST.sha256").read_text(encoding="utf-8")
