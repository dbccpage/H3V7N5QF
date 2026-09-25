"""Build `lean4_core/` (library `Twentyfifth`) and record the axioms of every theorem it proves.

Writes `evidence/twentyfifth/lean_axioms.txt`: the outcome of the build, a
scan of `lean4_core/` for `sorry`, `admit` and declared axioms, and the output
of `#print axioms` for every theorem of the library
(`Twentyfifth/Axioms.lean`).  The task allows only `propext` and
`Quot.sound`: the report is refused, not written, when a theorem depends on
anything else — `Classical.choice` included.

Cited from the twenty-second derivation (`twentysecond.leanreport`) and
re-checked (no change)
    `outside_allowed` (which lines of `#print axioms` fall outside the two
    allowed axioms), the allowed set and the pinned toolchain mention no
    library; `run`, `forbidden` and `_USES_SORRY` come from the first
    derivation's `xry.leanreport`.
"""

from __future__ import annotations

import argparse
from collections.abc import Sequence
from pathlib import Path

from twentysecond.leanreport import ALLOWED_AXIOMS, TOOLCHAIN, outside_allowed
from xry.evidence import write_manifest
from xry.leanreport import _USES_SORRY, Runner, forbidden, run

__all__ = ["ALLOWED_AXIOMS", "AXIOMS_FILE", "main", "outside_allowed", "report"]

AXIOMS_FILE = "Twentyfifth/Axioms.lean"


def report(lean_dir: Path, runner: Runner = run) -> str:
    """The text of `lean_axioms.txt`.  Raises if the build, the scan or the axioms fail."""
    code, out = runner(["lake", TOOLCHAIN, "build", "Twentyfifth"], lean_dir)
    if code != 0:
        raise RuntimeError(f"lake build failed:\n{out}")
    if _USES_SORRY.search(out):
        raise RuntimeError(f"lake build: a declaration uses sorry:\n{out}")
    code, axioms = runner(["lake", TOOLCHAIN, "env", "lean", AXIOMS_FILE], lean_dir)
    if code != 0:
        raise RuntimeError(f"the axiom report failed:\n{axioms}")
    hits = forbidden(lean_dir)
    if hits:
        raise RuntimeError("forbidden in lean4_core/: " + "; ".join(hits))
    bad = outside_allowed(axioms)
    if bad:
        raise RuntimeError("an axiom other than propext and Quot.sound: " + "; ".join(bad))
    lines = [line.rstrip() for line in axioms.replace("\r\n", "\n").split("\n")]
    body = "\n".join(line for line in lines if line)
    return (
        "lake build Twentyfifth (lean4_core/, no outside library): passed\n"
        "sorry / admit / declared axiom in lean4_core/ (outside comments): none\n"
        "axioms allowed: propext, Quot.sound\n"
        f"#print axioms ({AXIOMS_FILE}):\n{body}\n"
    )


def main(argv: Sequence[str] | None = None, runner: Runner = run) -> int:
    """Write the report and refresh the manifest."""
    parser = argparse.ArgumentParser(prog="twentyfifth.leanreport", description=__doc__)
    parser.add_argument("--lean", type=Path, default=Path("lean4_core"))
    parser.add_argument("--out", type=Path, default=Path("evidence") / "twentyfifth")
    args = parser.parse_args(argv)
    text = report(args.lean, runner)
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "lean_axioms.txt").write_text(text, encoding="utf-8", newline="\n")
    write_manifest(args.out)
    print(text, end="")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
