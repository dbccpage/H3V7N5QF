"""`python -m second.leanreport`: build `lean4/` and record what the second library rests on.

Writes `evidence/second/lean_axioms.txt`: the outcome of `lake build` (both
libraries), the output of `#print axioms` for every theorem the second paper
cites (the file `Second/Axioms.lean`), and a scan of all Lean sources for
`sorry`, `admit`, and declared axioms.

Cited from the first derivation (`xry.leanreport`) and re-checked
    `run`, `forbidden` and `nonstandard` do not depend on which library is
    reported; `forbidden` scans the whole of `lean4/`.  The report is refused
    on the same grounds as the first derivation's.
"""

from __future__ import annotations

import argparse
from collections.abc import Sequence
from pathlib import Path

from xry.evidence import write_manifest
from xry.leanreport import _USES_SORRY, Runner, forbidden, nonstandard, run

AXIOMS_FILE = "Second/Axioms.lean"


def report(lean_dir: Path, runner: Runner = run) -> str:
    """The text of `lean_axioms.txt`.  Raises if the build or the scan fails."""
    code, out = runner(["lake", "build"], lean_dir)
    if code != 0:
        raise RuntimeError(f"lake build failed:\n{out}")
    if _USES_SORRY.search(out):
        raise RuntimeError(f"lake build: a declaration uses sorry:\n{out}")
    code, axioms = runner(["lake", "env", "lean", AXIOMS_FILE], lean_dir)
    if code != 0:
        raise RuntimeError(f"the axiom report failed:\n{axioms}")
    hits = forbidden(lean_dir)
    if hits:
        raise RuntimeError("forbidden in lean4/: " + "; ".join(hits))
    bad = nonstandard(axioms)
    if bad:
        raise RuntimeError("not a report within the standard axioms: " + "; ".join(bad))
    lines = [line.rstrip() for line in axioms.replace("\r\n", "\n").split("\n")]
    body = "\n".join(line for line in lines if line)
    return (
        "lake build: passed\n"
        "sorry / admit / declared axiom in lean4/ (outside comments): none\n"
        f"#print axioms ({AXIOMS_FILE}):\n{body}\n"
    )


def main(argv: Sequence[str] | None = None, runner: Runner = run) -> int:
    """Write the report and refresh the manifest."""
    parser = argparse.ArgumentParser(prog="second.leanreport", description=__doc__)
    parser.add_argument("--lean", type=Path, default=Path("lean4"))
    parser.add_argument("--out", type=Path, default=Path("evidence") / "second")
    args = parser.parse_args(argv)
    text = report(args.lean, runner)
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "lean_axioms.txt").write_text(text, encoding="utf-8", newline="\n")
    write_manifest(args.out)
    print(text, end="")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
