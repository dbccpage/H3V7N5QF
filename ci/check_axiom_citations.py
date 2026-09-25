"""Gate: a cited Lean declaration must appear in the citing derivation's report.

This is a custody check, not a theorem census or a proof of an English claim.
It scans backticked tokens in papers and ledgers, restricts them to names of
Lean theorem/lemma declarations in this repository, then checks the *actual
Lean-generated* `#print axioms` report of that derivation. Short names can
collide: when a citation omits its namespace, the gate accepts any reported
declaration with that suffix. Fully qualified `Seed.*` citations require an
exact report name. The report generators and Lean build remain separate gates.

F001-F010 are the motivating defects. The test suite removes a real report
line in a fixture, checks the failure, restores it, and checks a clean pass.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
DERIVATIONS = (
    "base", "second", "third", "fourth", "fifth", "sixth", "seventh",
    "eighth", "ninth", "tenth", "eleventh", "twelfth", "thirteenth",
    "fourteenth", "fifteenth", "sixteenth", "seventeenth", "eighteenth",
    "nineteenth", "twentieth", "twentyfirst", "twentysecond", "twentythird",
    "twentyfourth",
    "twentyfifth",
)
#: Lean packages scanned for declarations: `lean4/` (with the outside library) and, from the
#: twenty-second derivation on, `lean4_core/` (no outside library).
LEAN_ROOTS = ("lean4", "lean4_core")
DECLARATION = re.compile(
    r"(?m)^\s*(?:@\[[^\]\n]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial|public)\s+)*"
    r"(?:theorem|lemma)\s+([A-Za-z][A-Za-z0-9_.']*)"
)
BACKTICK = re.compile(r"`([^`]+)`")
REPORT_NAME = re.compile(r"^'([^']+)' (?:depends on axioms:|does not depend)")


def declarations(root: Path) -> set[str]:
    """Names for filtering prose tokens; the Lean report resolves them."""
    out: set[str] = set()
    for name in LEAN_ROOTS:
        lean_root = root / name
        if not lean_root.is_dir():
            continue
        paths = list(lean_root.glob("*.lean"))
        paths.extend(
            path for directory in lean_root.iterdir()
            if directory.is_dir() and directory.name != ".lake"
            for path in directory.glob("*.lean")
        )
        for path in paths:
            out.update(DECLARATION.findall(path.read_text(encoding="utf-8")))
    return out


def paths(root: Path, derivation: str) -> tuple[Path, Path, Path]:
    suffix = "" if derivation == "base" else derivation
    return (
        root / "paper" / suffix / "paper.md",
        root / "paper" / suffix / "claim_ledger.md",
        root / "evidence" / suffix / "lean_axioms.txt",
    )


def cited(text: str, known: set[str]) -> set[str]:
    out: set[str] = set()
    for token in BACKTICK.findall(text):
        if token in known or (token.startswith("Seed.") and any(token.endswith("." + name) for name in known)):
            out.add(token)
    return out


def reported(text: str) -> set[str]:
    return {
        match.group(1)
        for line in text.splitlines()
        if (match := REPORT_NAME.match(line)) is not None
    }


def absent(citations: set[str], names: set[str]) -> list[str]:
    return sorted(
        citation for citation in citations
        if not (citation in names if citation.startswith("Seed.") else any(
            full == citation or full.endswith("." + citation) for full in names
        ))
    )


def check(root: Path, derivations: tuple[str, ...] = DERIVATIONS) -> list[str]:
    known = declarations(root)
    errors: list[str] = []
    for derivation in derivations:
        paper, ledger, report = paths(root, derivation)
        for path in (paper, ledger, report):
            if not path.is_file():
                errors.append(f"{derivation}: missing {path.relative_to(root)}")
        if not all(path.is_file() for path in (paper, ledger, report)):
            continue
        citation_names = cited(
            paper.read_text(encoding="utf-8") + "\n" + ledger.read_text(encoding="utf-8"), known
        )
        report_names = reported(report.read_text(encoding="utf-8"))
        if not citation_names:
            errors.append(f"{derivation}: no Lean citations identified")
        if not report_names:
            errors.append(f"{derivation}: no Lean report entries identified")
        errors.extend(f"{derivation}: {name} absent from own axiom report" for name in absent(citation_names, report_names))
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=REPO)
    parser.add_argument("--derivation", choices=DERIVATIONS, action="append")
    args = parser.parse_args(argv)
    names = tuple(args.derivation) if args.derivation else DERIVATIONS
    errors = check(args.root, names)
    if errors:
        print("\n".join(errors))
        return 1
    print(f"axiom citation/report check passed for {len(names)} derivations")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
