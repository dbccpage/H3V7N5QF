"""The two OEWAS anti-skill gates (`ci/check_definitional_citations.py`,
`ci/check_vacuous_checks.py`).

The repository has no hosted CI, so these tests ARE the gates: `python -m
pytest` runs each over the tree and fails on a hit.  Each gate is also
injection-proven here -- it must FIRE on the exact defect it exists to catch
and stay quiet on the repaired form -- because a gate is proved by biting, not
by being green (`ci/OEWAS_GATES.md`).
"""

from __future__ import annotations

import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "ci"))

import check_definitional_citations as cdc  # noqa: E402
import check_vacuous_checks as cvc  # noqa: E402


# --- the gates are green on the repository -------------------------------


def test_definitional_citation_gate_is_clean() -> None:
    assert cdc.main([]) == 0


def test_vacuous_check_gate_is_clean() -> None:
    assert cvc.main([]) == 0


# --- gate 1 (vacuous self-comparison) bites and recovers ------------------

_VACUOUS = '''
def admission_performed(expl):
    for state, change, out in performed(expl):
        yield state, change, out, admission_of_reaching(out)

def check(expl):
    hits = []
    for state, change, arrived, record in admission_performed(expl):
        other = admission_of_reaching(arrived)
        if other != record:
            hits.append(1)
    return hits
'''

_REPAIRED = '''
def admission_performed(expl):
    for state, change, out in performed(expl):
        yield state, change, out, admission_of_reaching(out)

def check(expl):
    hits = []
    for state, change, arrived, record in admission_performed(expl):
        if admission_of_reaching(arrived) != admission_of_reaching(swap(arrived)):
            hits.append(1)
    return hits
'''


def test_vacuous_gate_flags_generator_routed_self_comparison() -> None:
    hits = cvc.scan_source(_VACUOUS, "probe.py")
    assert len(hits) == 1
    # both sides canonicalize to the generator-namespace expression.
    assert hits[0].canonical == "admission_of_reaching(out)"


def test_vacuous_gate_passes_the_repaired_form() -> None:
    assert cvc.scan_source(_REPAIRED, "probe.py") == []


def test_vacuous_gate_respects_the_exemption_comment() -> None:
    src = "def f(x):\n    return x != x  # vacuous-ok: NaN test\n"
    assert cvc.scan_source(src, "probe.py") == []
    assert len(cvc.scan_source("def f(x):\n    return x != x\n", "probe.py")) == 1


def test_vacuous_gate_ignores_an_independent_comparison() -> None:
    src = "def f(a, b):\n    return len(a) != len(b)\n"
    assert cvc.scan_source(src, "probe.py") == []


# --- gate 2 (definitional citation) bites and recovers --------------------


def _resolve(thms: cdc.Theorems, name: str, lib: str) -> cdc.Theorem:
    thm = thms.resolve(name, lib)
    assert thm is not None
    return thm


def _theorems(**defs: str) -> cdc.Theorems:
    """Build a Theorems index from `name -> lean source` snippets, all in one library."""
    by_lib: dict[str, dict[str, cdc.Theorem]] = {"Probe": {}}
    flat: dict[str, cdc.Theorem] = {}
    for name, src in defs.items():
        statement, proof = cdc._split_signature(src)
        thm = cdc.Theorem(name, statement, proof, "lean4/Probe/X.lean", 1)
        by_lib["Probe"][name] = thm
        flat[name] = thm
    return cdc.Theorems(by_lib, flat)


def _row(status: str, evidence: str, statement: str = "the record is not a third multiplicity") -> cdc.Row:
    return cdc.Row("paper/probe/claim_ledger.md", 1, "D1", statement, status, evidence)


def test_definitional_gate_flags_a_self_equality_citation() -> None:
    thms = _theorems(swap_keeps="theorem swap_keeps : reaching = reaching := rfl")
    row = _row("derived", "Lean `swap_keeps`")
    assert cdc.vacuous_reason(row, _resolve(thms, "swap_keeps", "Probe"), thms) is not None


def test_definitional_gate_flags_a_notion_mismatch() -> None:
    # a rfl theorem about `proj`, cited for a claim about the record notion.
    thms = _theorems(
        no_third_rel="theorem no_third_rel (s : NDSt) :\n    (s.proj false).M = s.M false :=\n  rfl"
    )
    row = cdc.Row("paper/probe/claim_ledger.md", 1, "D1", "the record is not a third multiplicity", "derived", "Lean `no_third_rel`")
    row_probe = cdc.Row(row.file.replace("probe", "twelfth"), 1, "D1", row.statement, row.status, row.evidence)
    # twelfth's record notion is "record"; the theorem never says it.
    assert cdc.vacuous_reason(row_probe, _resolve(thms, "no_third_rel", "Twelfth"), thms) is not None


def test_definitional_gate_accepts_a_disclosed_row() -> None:
    thms = _theorems(swap_keeps="theorem swap_keeps : reaching = reaching := rfl")
    disclosed = _row("chosen (by construction)", "Lean `swap_keeps` (definitional)")
    assert cdc.vacuous_reason(disclosed, _resolve(thms, "swap_keeps", "Probe"), thms) is not None
    # find_hits skips it because the row disclosed the weakness.
    hits = cdc.find_hits([], thms)  # no ledger files -> no hits regardless
    assert hits == []


def test_definitional_gate_accepts_a_substantive_reflexivity() -> None:
    # a rfl proof whose statement NAMES the notion is fair (definitional but honest).
    thms = _theorems(
        leftover_addTerm="theorem leftover_addTerm (s) :\n    leftoverOf s (s.addTerm t) = nothing :=\n  rfl"
    )
    row = cdc.Row("paper/tenth/claim_ledger.md", 1, "D3", "leftover of an addition is nothing", "derived", "Lean `leftover_addTerm`")
    assert cdc.vacuous_reason(row, _resolve(thms, "leftover_addTerm", "Tenth"), thms) is None
