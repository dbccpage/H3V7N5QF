"""Gate: a claim marked *derived* must not rest on a definitional Lean theorem.

An OEWAS tripwire (see `ci/OEWAS_GATES.md`).  During the review of the
tenth-fifteenth derivations, six papers cited Lean theorems as *derivation*
evidence for a claim when the theorem was actually definitional -- proved by
`rfl` / `⟨rfl, rfl⟩`, or stating a bare self-equality `a = a` -- and so
established nothing about the claim.  Every gate was green; only a careful
reader caught it.  This gate mechanizes the catch.

What it does.  For every `paper/**/claim_ledger.md` it reads the table rows.
A row whose **Status** claims `derived` (and does not already disclose the
weakness -- see EXEMPT below) FAILS the gate when a Lean theorem it cites in
its **Evidence** cell is vacuous in one of two precise ways:

  * **self-equality** -- the theorem's statement is `EXPR = EXPR`, the two
    sides textually equal (`reaching = reaching`, `leftoverRemove x y =
    leftoverRemove x y`).  Such a theorem proves nothing, whatever its proof.
  * **notion mismatch** -- the theorem is proved by reflexivity (`rfl`,
    `Iff.rfl`, `⟨rfl, …, rfl⟩`, `by rfl`, or a one-step forward to another
    such theorem) AND the derivation's record notion (leftover / writing /
    record / coarse / admission) that the *claim* is about does not appear in
    the *theorem's* statement.  This is the `no_third_rel` case: its statement
    is about `proj`, it is cited for "the record is not a third multiplicity".

A reflexivity proof is NOT flagged on its own: "an addition leaves nothing
`:= rfl`" is true by computation and its statement names the notion, so it is
a fair (if definitional) derivation -- surfaced by `--report`, not failed.

What it is NOT.  It reads the Lean *source*, not the elaborated proof, so a
proof definitional only after elaboration (not textually `rfl`) is missed
(`#print axioms`/`whnf` would close that, at the cost of a Lean build).  The
notion-mismatch signal applies only where the derivation has a named record
notion (the tenth-fifteenth family).  Injection-proven: reverting a disclosed
row to plain `derived | Lean <self-eq or mismatched theorem>` makes it fire.

Run: `python ci/check_definitional_citations.py` (exit 1 on a hit), or
`--report` to list every `derived`-row Lean citation and its verdict.
"""

from __future__ import annotations

import argparse
import re
import sys
from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

#: Words in a row's Status/Evidence that DISCLOSE a definitional dependence,
#: so the row no longer over-claims and is not a hit.
EXEMPT = (
    "by construction",
    "definitional",
    "identity",
    "chosen",
    "rfl",
    "not cited as a proof",
    "illustrat",
)

#: A reflexivity proof term, once whitespace and newlines are collapsed.
_REFL = re.compile(r"^(rfl|Iff\.rfl|by\s+rfl|⟨\s*(rfl\s*,?\s*)+⟩)$")
#: A single forwarded reference: `name`, `name arg …`, or `Foo.name arg …`.
_FORWARD = re.compile(r"^([A-Za-z_][\w'.]*)(\s+\S.*)?$")

#: The record notion each records/readings derivation adds, as a lowercase
#: stem to look for in a claim's statement and in the cited theorem's.  A
#: reflexivity theorem cited for a claim ABOUT the notion, whose own statement
#: never NAMES the notion, is a mismatch (the `no_third_rel` case).
RECORD_NOUN = {
    "tenth": "leftover",
    "eleventh": "writing",
    "twelfth": "record",
    "thirteenth": "coars",
    "fourteenth": "leftover",
    "fifteenth": "admission",
    "sixteenth": "leftover",
    "twentyfourth": "fill",
    "twentyfifth": "balanc",
}


@dataclass(frozen=True)
class Theorem:
    """A Lean theorem as it reads in source: its statement and proof text."""

    name: str
    statement: str
    proof: str
    file: str
    line: int


def _collapse(text: str) -> str:
    """One line, single-spaced -- for matching a short proof term."""
    return re.sub(r"\s+", " ", text).strip()


class Theorems:
    """The `theorem`/`lemma` declarations under `lean4/`, resolvable per namespace.

    Short names collide across namespaces (`Seed.Tenth.leftover_swap_addTerm`
    is a real theorem; `Seed.Fourteenth`'s is `leftoverAdd = leftoverAdd`), so
    a citation is resolved to the CITING derivation's library first
    (`lean4/<Library>/…`), then to any library -- for the cross-derivation
    citations like `fewest_changes9`.
    """

    def __init__(self, by_lib: Mapping[str, dict[str, Theorem]], flat: Mapping[str, Theorem]) -> None:
        self._by_lib = by_lib
        self._flat = flat

    def merged(self, other: Theorems) -> Theorems:
        """Both packages' theorems (`lean4/` and `lean4_core/`); a library in both keeps this one's first."""
        by_lib = {lib: dict(names) for lib, names in self._by_lib.items()}
        for lib, names in other._by_lib.items():
            into = by_lib.setdefault(lib, {})
            for short, thm in names.items():
                into.setdefault(short, thm)
        flat = dict(self._flat)
        for short, thm in other._flat.items():
            flat.setdefault(short, thm)
        return Theorems(by_lib, flat)

    def resolve(self, name: str, library: str | None) -> Theorem | None:
        short = name.split(".")[-1]
        if library and library in self._by_lib:
            hit = self._by_lib[library].get(short)
            if hit is not None:
                return hit
        return self._flat.get(short)


def parse_theorems(lean_root: Path) -> Theorems:
    """Every `theorem`/`lemma` under `lean_root`, keyed by top-level library and short name."""
    by_lib: dict[str, dict[str, Theorem]] = {}
    flat: dict[str, Theorem] = {}
    starter = re.compile(r"^(?:theorem|lemma)\s+([A-Za-z_][\w'.]*)")
    stop = re.compile(r"^(?:theorem|lemma|def|abbrev|instance|namespace|end|/-|#|@\[|section|variable)")
    for path in sorted(lean_root.rglob("*.lean")):
        rel = path.relative_to(REPO).as_posix()
        library = path.relative_to(lean_root).parts[0].removesuffix(".lean")
        lines = path.read_text(encoding="utf-8").splitlines()
        i = 0
        while i < len(lines):
            m = starter.match(lines[i])
            if not m:
                i += 1
                continue
            short = m.group(1).split(".")[-1]
            block = [lines[i]]
            j = i + 1
            while j < len(lines) and not stop.match(lines[j]):
                block.append(lines[j])
                j += 1
            statement, proof = _split_signature("\n".join(block))
            thm = Theorem(short, statement, proof, rel, i + 1)
            by_lib.setdefault(library, {}).setdefault(short, thm)
            flat.setdefault(short, thm)
            i = j
    return Theorems(by_lib, flat)


def _split_signature(text: str) -> tuple[str, str]:
    """(statement, proof) split on the top-level `:=` that ends the signature."""
    depth = 0
    k = 0
    while k < len(text) - 1:
        c = text[k]
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif depth == 0 and c == ":" and text[k + 1] == "=":
            statement = text[:k]
            proof = text[k + 2 :]
            colon = statement.find(":")
            return statement[colon + 1 :].strip() if colon >= 0 else statement.strip(), proof.strip()
        k += 1
    colon = text.find(":")
    return (text[colon + 1 :].strip() if colon >= 0 else text.strip()), ""


def is_self_equality(statement: str) -> bool:
    """Does the statement read `EXPR = EXPR` (the two sides textually equal)?"""
    body = _collapse(statement)
    depth = 0
    for k in range(len(body) - 1):
        c = body[k]
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif depth == 0 and c == "=" and body[k - 1] not in "<>=!:" and body[k + 1] not in "=":
            lhs, rhs = body[:k].strip(), body[k + 1 :].strip()
            return bool(lhs) and lhs == rhs
    return False


def is_reflexivity(name: str, theorems: Theorems, library: str | None, seen: frozenset[str] = frozenset()) -> bool:
    """Is `name` proved by reflexivity, directly or through one forward step?"""
    thm = theorems.resolve(name, library)
    if thm is None or name in seen:
        return False
    proof = _collapse(thm.proof)
    if _REFL.match(proof):
        return True
    fwd = _FORWARD.match(proof)
    if fwd and fwd.group(1) != "by":
        return is_reflexivity(fwd.group(1), theorems, library, seen | {name})
    return False


def _mentions(stem: str, text: str) -> bool:
    """Does `text` contain the notion stem (case-insensitive)?"""
    return stem.lower() in text.lower()


@dataclass(frozen=True)
class Row:
    """One ledger row that claims `derived`."""

    file: str
    line: int
    claim_id: str
    statement: str
    status: str
    evidence: str

    @property
    def derivation(self) -> str:
        """The derivation name from the ledger path (`paper/<name>/claim_ledger.md`)."""
        return self.file.split("/")[1] if "/" in self.file else ""


def parse_derived_rows(ledger: Path) -> list[Row]:
    """The `derived`-claiming rows of one claim ledger."""
    rel = ledger.relative_to(REPO).as_posix()
    rows: list[Row] = []
    for n, raw in enumerate(ledger.read_text(encoding="utf-8").splitlines(), start=1):
        if not raw.lstrip().startswith("|"):
            continue
        cells = [c.strip() for c in raw.strip().strip("|").split("|")]
        if len(cells) < 4 or cells[0] in ("ID", "---") or set(cells[0]) <= set("-: "):
            continue
        claim_id, statement, status, evidence = cells[0], cells[1], cells[2], cells[3]
        if "derived" in status.lower():
            rows.append(Row(rel, n, claim_id, statement, status, evidence))
    return rows


def cited_names(evidence: str) -> list[str]:
    """Backticked identifiers in an Evidence cell that could be Lean names."""
    return [tok for tok in re.findall(r"`([^`]+)`", evidence) if re.fullmatch(r"[A-Za-z_][\w'.]*", tok)]


@dataclass(frozen=True)
class Hit:
    row: Row
    theorem: str
    reason: str


def vacuous_reason(row: Row, thm: Theorem, theorems: Theorems) -> str | None:
    """Why a cited theorem is vacuous evidence for this derived row, or None."""
    if is_self_equality(thm.statement):
        return f"self-equality statement `{_collapse(thm.statement)}` ({thm.file}:{thm.line})"
    noun = RECORD_NOUN.get(row.derivation)
    if (
        noun is not None
        and is_reflexivity(thm.name, theorems, row.derivation.capitalize())
        and _mentions(noun, row.statement)
        and not _mentions(noun, thm.statement)
    ):
        return (
            f"reflexivity proof of a statement `{_collapse(thm.statement)[:48]}` that never "
            f"names '{noun}', the notion the claim is about ({thm.file}:{thm.line})"
        )
    return None


def find_hits(ledger_files: Iterable[Path], theorems: Theorems) -> list[Hit]:
    """Every `derived` row, not disclosed, that cites a vacuous theorem."""
    hits: list[Hit] = []
    for ledger in ledger_files:
        for row in parse_derived_rows(ledger):
            disclosure = f"{row.status} {row.evidence}".lower()
            if any(word in disclosure for word in EXEMPT):
                continue
            for name in cited_names(row.evidence):
                thm = theorems.resolve(name, row.derivation.capitalize())
                if thm is None:
                    continue
                reason = vacuous_reason(row, thm, theorems)
                if reason is not None:
                    hits.append(Hit(row, name, reason))
    return hits


def ledgers(paper_root: Path) -> list[Path]:
    return sorted(paper_root.rglob("claim_ledger.md"))


def main(argv: list[str] | None = None) -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")  # Lean statements carry ∧, ⟨⟩, ℕ …
    parser = argparse.ArgumentParser(prog="check_definitional_citations", description=__doc__)
    parser.add_argument("--paper", type=Path, default=REPO / "paper")
    parser.add_argument("--lean", type=Path, default=REPO / "lean4")
    parser.add_argument("--lean-core", type=Path, default=REPO / "lean4_core", help="the package with no outside library")
    parser.add_argument("--report", action="store_true", help="list every derived-row Lean citation and its verdict")
    args = parser.parse_args(argv)

    theorems = parse_theorems(args.lean)
    if args.lean_core.is_dir():
        theorems = theorems.merged(parse_theorems(args.lean_core))
    files = ledgers(args.paper)

    if args.report:
        for ledger in files:
            for row in parse_derived_rows(ledger):
                for name in cited_names(row.evidence):
                    thm = theorems.resolve(name, row.derivation.capitalize())
                    if thm is None:
                        continue
                    if is_self_equality(thm.statement):
                        verdict = "VACUOUS: self-equality"
                    elif vacuous_reason(row, thm, theorems):
                        verdict = "VACUOUS: notion mismatch"
                    elif is_reflexivity(name, theorems, row.derivation.capitalize()):
                        verdict = "reflexivity (definitional, statement names the notion)"
                    else:
                        verdict = "substantive"
                    print(f"{row.file}:{row.line} {row.claim_id} `{name}` -> {verdict}")
        return 0

    hits = find_hits(files, theorems)
    if not hits:
        rows = sum(len(parse_derived_rows(f)) for f in files)
        print(f"definitional-citation gate clean: {rows} derived rows across {len(files)} ledgers, none rests on a definitional theorem undisclosed")
        return 0
    for hit in hits:
        print(
            f"FAIL: {hit.row.file}:{hit.row.line} {hit.row.claim_id} is marked 'derived' but cites "
            f"`{hit.theorem}`, a {hit.reason} -- mark it 'by construction'/'definitional' or cite a substantive theorem"
        )
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
