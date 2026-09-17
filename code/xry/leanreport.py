"""`python -m xry.leanreport`: build `lean4/` and record what its theorems rest on.

Writes `evidence/lean_axioms.txt`: the outcome of `lake build`, the output of
`#print axioms` for every cited theorem (the file `H3V7N5QF/Axioms.lean`), and
a scan of the Lean sources for `sorry`, `admit`, and declared axioms.
"""

from __future__ import annotations

import argparse
import re
import subprocess
from collections.abc import Callable, Sequence
from pathlib import Path

from xry.evidence import write_manifest

Runner = Callable[[Sequence[str], Path], tuple[int, str]]

AXIOMS_FILE = "H3V7N5QF/Axioms.lean"
_FORBIDDEN = re.compile(r"\b(sorry|admit)\b|^\s*(?:private\s+|protected\s+)?axiom\b", re.MULTILINE)
_COMMENT = re.compile(r"/-.*?-/|--[^\n]*", re.DOTALL)


def run(cmd: Sequence[str], cwd: Path) -> tuple[int, str]:  # pragma: no cover
    """Run a command; return its exit code and combined output."""
    done = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, check=False)
    return done.returncode, done.stdout + done.stderr


def forbidden(lean_dir: Path) -> list[str]:
    """`file: word` for every `sorry`, `admit`, or declared axiom outside comments."""
    hits = []
    for path in sorted(lean_dir.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        text = _COMMENT.sub("", path.read_text(encoding="utf-8"))
        for match in _FORBIDDEN.finditer(text):
            hits.append(f"{path.relative_to(lean_dir).as_posix()}: {match.group(0).strip()}")
    return hits


def report(lean_dir: Path, runner: Runner = run) -> str:
    """The text of `lean_axioms.txt`.  Raises if the build or the scan fails."""
    code, out = runner(["lake", "build"], lean_dir)
    if code != 0:
        raise RuntimeError(f"lake build failed:\n{out}")
    code, axioms = runner(["lake", "env", "lean", AXIOMS_FILE], lean_dir)
    if code != 0:
        raise RuntimeError(f"the axiom report failed:\n{axioms}")
    hits = forbidden(lean_dir)
    if hits:
        raise RuntimeError("forbidden in lean4/: " + "; ".join(hits))
    lines = [line.rstrip() for line in axioms.replace("\r\n", "\n").split("\n")]
    body = "\n".join(line for line in lines if line)
    return (
        "lake build: passed\n"
        "sorry / admit / declared axiom in lean4/ (outside comments): none\n"
        f"#print axioms ({AXIOMS_FILE}):\n{body}\n"
    )


def main(argv: Sequence[str] | None = None, runner: Runner = run) -> int:
    """Write the report and refresh the manifest."""
    parser = argparse.ArgumentParser(prog="xry.leanreport", description=__doc__)
    parser.add_argument("--lean", type=Path, default=Path("lean4"))
    parser.add_argument("--out", type=Path, default=Path("evidence"))
    args = parser.parse_args(argv)
    text = report(args.lean, runner)
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "lean_axioms.txt").write_text(text, encoding="utf-8", newline="\n")
    write_manifest(args.out)
    print(text, end="")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
