from __future__ import annotations

import runpy
import sys
from pathlib import Path

import pytest

CODE = Path(__file__).resolve().parent.parent / "code"

UNIQUE_FLAG = {"generate_ninth.py": "--reach-extra", "lean_report_ninth.py": "--lean"}


@pytest.mark.parametrize("name", ["generate_ninth.py", "lean_report_ninth.py"])
def test_launcher_reaches_its_command_line(
    name: str, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(sys, "argv", [name, "--help"])
    with pytest.raises(SystemExit) as stop:
        runpy.run_path(str(CODE / name), run_name="__main__")
    assert stop.value.code == 0
    out = capsys.readouterr().out
    assert "--out" in out and UNIQUE_FLAG[name] in out
    assert "ninth" in out
