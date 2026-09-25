"""Build `lean4_core/` (library `Twentysecond`) and record the axioms of every cited theorem.

Writes `evidence/twentysecond/lean_axioms.txt`: the outcome of the build, a
scan of `lean4_core/` for `sorry`, `admit` and declared axioms, and the output
of `#print axioms` for every theorem the paper cites
(`Twentysecond/Axioms.lean`).  `lean4_core/` has no outside library, and the
task allows only `propext` and `Quot.sound`: the report is refused, not
written, when a cited theorem depends on anything else — `Classical.choice`
included, unlike the earlier derivations' reports.

Cited from the first derivation (`xry.leanreport`) and re-checked (no change)
    `run` (the command runner), `forbidden` (the source scan) and
    `_USES_SORRY` mention no library; the allowed axioms are narrowed here.
"""

from __future__ import annotations

import argparse
import re
from collections.abc import Sequence
from pathlib import Path

from xry.evidence import write_manifest
from xry.leanreport import _USES_SORRY, Runner, forbidden, run

AXIOMS_FILE = "Twentysecond/Axioms.lean"
ALLOWED_AXIOMS = frozenset({"propext", "Quot.sound"})
TOOLCHAIN = "+leanprover/lean4:v4.33.1"
_REPORT = re.compile(r"^'(.+)' (?:depends on axioms: \[(.*)\]|does not depend on any axioms)$")


def outside_allowed(axioms: str) -> list[str]:
    """Every line of `#print axioms` output that is not a report within `ALLOWED_AXIOMS`."""
    bad = []
    for raw in axioms.replace("\r\n", "\n").split("\n"):
        line = raw.rstrip()
        if not line:
            continue
        match = _REPORT.match(line)
        if match is None:
            bad.append(line)
            continue
        used = set() if match.group(2) is None else set(match.group(2).split(", "))
        if not used <= ALLOWED_AXIOMS:
            bad.append(line)
    return bad


def report(lean_dir: Path, runner: Runner = run) -> str:
    """The text of `lean_axioms.txt`.  Raises if the build, the scan or the axioms fail."""
    code, out = runner(["lake", TOOLCHAIN, "build", "Twentysecond"], lean_dir)
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
        "lake build Twentysecond (lean4_core/, no outside library): passed\n"
        "sorry / admit / declared axiom in lean4_core/ (outside comments): none\n"
        "axioms allowed: propext, Quot.sound\n"
        f"#print axioms ({AXIOMS_FILE}):\n{body}\n"
    )


def main(argv: Sequence[str] | None = None, runner: Runner = run) -> int:
    """Write the report and refresh the manifest."""
    parser = argparse.ArgumentParser(prog="twentysecond.leanreport", description=__doc__)
    parser.add_argument("--lean", type=Path, default=Path("lean4_core"))
    parser.add_argument("--out", type=Path, default=Path("evidence") / "twentysecond")
    args = parser.parse_args(argv)
    text = report(args.lean, runner)
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "lean_axioms.txt").write_text(text, encoding="utf-8", newline="\n")
    write_manifest(args.out)
    print(text, end="")
    return 0


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(main())
