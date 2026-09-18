from __future__ import annotations

import runpy
import sys
from pathlib import Path

import pytest

CODE = Path(__file__).resolve().parent.parent / "code"

#: A flag unique to each launcher's own command line: `--census-bound` belongs
#: to the evidence generator, `--lean` to the axiom-report writer.
UNIQUE_FLAG = {"generate_third.py": "--census-bound", "lean_report_third.py": "--lean"}


@pytest.mark.parametrize("name", ["generate_third.py", "lean_report_third.py"])
def test_launcher_reaches_its_command_line(
    name: str, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture[str]
) -> None:
    monkeypatch.setattr(sys, "argv", [name, "--help"])
    with pytest.raises(SystemExit) as stop:
        runpy.run_path(str(CODE / name), run_name="__main__")
    assert stop.value.code == 0
    out = capsys.readouterr().out
    assert "--out" in out and UNIQUE_FLAG[name] in out
    assert "third" in out
