"""The dynamic mutation-bite gate (`ci/check_mutation_bite.py`).

No hosted CI, so this test IS the gate: every disagreement field of every
derivation's check dataclass must bite under its registered mutation, and the
panel must cover every field.  The gate is injection-proven three ways: a
reconstructed vacuous check does not bite (and is reported), removing a bite
case is reported as an uncovered field, and the whole panel is green on the
repository.  A gate is proved by biting, not by being green
(`ci/OEWAS_GATES.md`).
"""

from __future__ import annotations

import sys
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Iterator

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "ci"))
sys.path.insert(0, str(REPO / "code"))

import check_mutation_bite as cmb  # noqa: E402


def test_gate_is_clean() -> None:
    assert cmb.main([]) == 0


def test_every_field_is_covered_and_bites() -> None:
    for panel in cmb.panels():
        assert cmb.check_panel(panel) == [], panel.derivation


def test_panel_covers_exactly_the_disagreement_fields() -> None:
    for panel in cmb.panels():
        fields = cmb.disagreement_fields(panel.check_class)
        assert set(panel.cases) == set(fields), panel.derivation


def test_removing_a_bite_case_is_reported_as_uncovered() -> None:
    panel = next(p for p in cmb.panels() if p.derivation == "fifteenth")
    dropped = dict(panel.cases)
    del dropped["cross_relation_disagree"]
    crippled = cmb.Panel(panel.derivation, panel.check_class, panel.signals, dropped)
    problems = cmb.check_panel(crippled)
    assert any("cross_relation_disagree" in p and "uncovered" in p for p in problems)


def test_gate_catches_a_vacuous_check() -> None:
    """A vacuous cross-relation check -- comparing a result's admission record
    with a copy of itself -- does not bite under the mutation, and the panel
    reports it."""
    import fifteenth.explore as fexplore
    import fifteenth.invariants as finv
    from fifteenth.admission import Admission
    from fifteenth.explore import admission_performed, explore
    from fifteenth.invariants import AdmissionCheck
    from ninth.state import DState, empty

    def vacuous_signals() -> frozenset[str]:
        out = AdmissionCheck()
        for _state, _change, arrived, record in admission_performed(explore(empty(), 2, 4)):
            out.checked += 1
            if getattr(finv, "admission_of_reaching")(arrived) != record:  # a value vs a copy of itself
                out.cross_relation_disagree.append("x")
        return cmb._nonempty_lists(out)

    def relation_dependent() -> Any:
        def wrong(s: Any) -> Admission:
            return Admission(True) if isinstance(s, DState) and s.total_r > s.total_s else Admission(False)

        return cmb.everywhere("fifteenth", "admission_of_reaching", wrong)

    del fexplore  # loaded so patch_everywhere sees its binding
    panel = cmb.Panel("probe", AdmissionCheck, vacuous_signals, {"cross_relation_disagree": relation_dependent})
    problems = cmb.check_panel(panel)
    assert any("cross_relation_disagree" in p and "does not bite" in p for p in problems)


def test_repaired_check_bites_where_the_vacuous_one_does_not() -> None:
    fifteenth = next(p for p in cmb.panels() if p.derivation == "fifteenth")
    # the real fifteenth panel's cross-relation field bites (compares against the swap)
    problems = [p for p in cmb.check_panel(fifteenth) if "cross_relation_disagree" in p]
    assert problems == []
