"""The dynamic mutation-bite gate (`ci/check_mutation_bite.py`).

No hosted CI, so this test IS the gate: every registered differential check
must bite under a derivation mutation.  The gate is injection-proven by
reconstructing the ORIGINAL vacuous form of the fifteenth's cross-relation
check -- comparing a result's admission record with a copy of itself -- and
showing it survives the mutation, which the gate reports.  A gate is proved by
biting, not by being green (`ci/OEWAS_GATES.md`).
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


def test_every_registered_check_bites() -> None:
    for case in cmb.registry():
        assert cmb.run_case(case) is None, case.name


def _vacuous_fifteenth_case() -> cmb.BiteCase:
    """The fifteenth's cross-relation check as it was BEFORE the repair: it
    compared `admission_of_reaching(arrived)` with the `record` the generator
    already computed as `admission_of_reaching(out)` for the same state -- a
    value against a copy of itself."""
    import fifteenth.explore as fexplore
    import fifteenth.invariants as finv
    from fifteenth.admission import Admission
    from fifteenth.explore import admission_performed, explore
    from fifteenth.invariants import AdmissionCheck
    from ninth.state import DState, empty

    def vacuous_check(expl: Any) -> AdmissionCheck:
        out = AdmissionCheck()
        for _state, _change, arrived, record in admission_performed(expl):
            out.checked += 1
            # late-bound access, so the mutation is seen; both sides are the
            # admission of the same state, so they can never disagree.
            if getattr(finv, "admission_of_reaching")(arrived) != record:
                out.cross_relation_disagree.append("x")
        return out

    def signals() -> frozenset[str]:
        return cmb._nonempty_lists(vacuous_check(explore(empty(), 2, 4)))

    @contextmanager
    def mutate() -> Iterator[None]:
        def wrong(s: Any) -> Admission:
            return Admission(True) if isinstance(s, DState) and s.total_r > s.total_s else Admission(False)

        with cmb.patch_everywhere("fifteenth", "admission_of_reaching", wrong):
            yield

    del fexplore  # imported to ensure the module is loaded so patch_everywhere sees it
    return cmb.BiteCase("probe: vacuous cross-relation", signals, mutate, "cross_relation_disagree")


def test_gate_catches_a_vacuous_check() -> None:
    reason = cmb.run_case(_vacuous_fifteenth_case())
    assert reason is not None and "does not bite" in reason


def test_repaired_check_bites_where_the_vacuous_one_does_not() -> None:
    # same mutation, same field: the repaired check (compares against the r/s
    # swap) bites; the vacuous one (compares against itself) does not.
    repaired = next(c for c in cmb.registry() if c.field == "cross_relation_disagree" and "fifteenth" in c.name)
    assert cmb.run_case(repaired) is None
    assert cmb.run_case(_vacuous_fifteenth_case()) is not None
