"""Gate: a differential check must BITE when the derivation is mutated.

The dynamic OEWAS layer (see `ci/OEWAS_GATES.md`).  A differential check is a
*fitness assay* for a derivation: it should fail when the derivation computes
the wrong thing.  A check that cannot be made to fail by any perturbation of
the derivation is under no selective pressure -- it is vacuous, however green
it is.  This gate applies mutation testing to the checks themselves: for each
registered check it runs the derivation on a small exploration (the baseline
must be clean), then applies a one-sided mutation to a *derivation-specific*
quantity and requires the check's disagreement field to fire.  A mutation
that survives -- the check stays clean -- fails the gate and names the check.

Why one-sided and derivation-specific.  Comparing the derivation's exploration
against a fresh re-run of the SAME reference is not tested here: it is an
identity (`check_definitional_citations.py`'s prose sibling), and mutating the
shared computation moves both sides.  The mutations below hit the derivation's
own record function (`admission_of_reaching`, `leftover_of`), which the check
exists to validate; a real check sees the mutation, a vacuous one does not.

The registry is the antigen panel -- domain-specific by design, like a real
immune system, and maintained by hand.  A differential check with no
registered bite case is NOT covered; enumerating the disagreement fields and
requiring a case per field is the next tightening.  Injection-proven in
`tests/test_mutation_bite.py`: a deliberately vacuous check (comparing a value
with itself) survives every mutation, and the gate reports it.

Run: `python ci/check_mutation_bite.py` (exit 1 if a check fails to bite).
"""

from __future__ import annotations

import argparse
import sys
from collections.abc import Callable, Iterator
from contextlib import AbstractContextManager, contextmanager
from dataclasses import dataclass, fields, is_dataclass
from pathlib import Path
from typing import Any
from unittest.mock import patch

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "code"))


def _nonempty_lists(record: Any) -> frozenset[str]:
    """The names of the list-valued fields of a check dataclass that are non-empty."""
    assert is_dataclass(record)
    return frozenset(f.name for f in fields(record) if isinstance(getattr(record, f.name), list) and getattr(record, f.name))


@contextmanager
def patch_everywhere(package: str, attr: str, replacement: Callable[..., Any]) -> Iterator[None]:
    """Replace `attr` on every loaded module of `package` that binds it.

    A `from x import f` copies the reference, so the logical quantity `f`
    computes has many bindings.  A mutation-bite assay must perturb the
    quantity UNIFORMLY -- otherwise a vacuous check comparing the quantity
    against a copy of itself, computed through two different bindings, would
    spuriously disagree and look non-vacuous.  Patching every binding keeps a
    genuinely vacuous check equal (it survives, and is caught), while a check
    that uses an independent oracle or a transformed argument still bites.
    """
    patches = [
        patch(f"{name}.{attr}", replacement)
        for name, module in list(sys.modules.items())
        if name.startswith(package + ".") and hasattr(module, attr)
    ]
    for p in patches:
        p.start()
    try:
        yield
    finally:
        for p in patches:
            p.stop()


@dataclass
class BiteCase:
    """One differential check, the mutation that should make it fire, and the field that should."""

    name: str
    signals: Callable[[], frozenset[str]]
    mutate: Callable[[], "AbstractContextManager[None]"]
    field: str


def run_case(case: BiteCase) -> str | None:
    """None if the check bites under the mutation; a failure reason otherwise."""
    baseline = case.signals()
    if case.field in baseline:
        return f"baseline already reports `{case.field}` -- not a clean bite test"
    with case.mutate():
        mutated = case.signals()
    if case.field not in mutated:
        return f"the mutation did not make `{case.field}` fire -- the check does not bite (vacuous)"
    return None


# --- the antigen panel ----------------------------------------------------


def _fifteenth_cross_relation() -> BiteCase:
    from fifteenth.admission import Admission
    from fifteenth.explore import explore
    from fifteenth.invariants import check_admissions
    from ninth.state import DState, empty

    def signals() -> frozenset[str]:
        return _nonempty_lists(check_admissions(explore(empty(), 2, 4)))

    @contextmanager
    def mutate() -> Iterator[None]:
        # a relation-DEPENDENT record: an asymmetric result disagrees with its swap.
        def wrong(s: Any) -> Admission:
            return Admission(True) if isinstance(s, DState) and s.total_r > s.total_s else Admission(False)

        with patch_everywhere("fifteenth", "admission_of_reaching", wrong):
            yield

    return BiteCase("fifteenth: admission names no relation", signals, mutate, "cross_relation_disagree")


def _tenth_identify_split() -> BiteCase:
    from ninth.changes import Kind
    from ninth.state import empty
    from tenth.explore import explore
    from tenth.invariants import check_leftovers
    from tenth.leftover import LeftOver, leftover_of as real_leftover_of

    def signals() -> frozenset[str]:
        return _nonempty_lists(check_leftovers(explore(empty(), 3, 4)))

    @contextmanager
    def mutate() -> Iterator[None]:
        flip = {LeftOver.CLEARABLE: LeftOver.UNCLEARED, LeftOver.UNCLEARED: LeftOver.CLEARABLE}

        def wrong(state: Any, change: Any) -> Any:
            right = real_leftover_of(state, change)
            return flip.get(right, right) if change.kind is Kind.IDENTIFY else right

        with patch_everywhere("tenth", "leftover_of", wrong):
            yield

    return BiteCase("tenth: identification split", signals, mutate, "identify_disagreements")


def _fourteenth_cross_relation() -> BiteCase:
    from fourteenth.explore import explore
    from fourteenth.invariants import check_leftovers
    from fourteenth.leftover import leftover_of as real_leftover_of, leftover_pair
    from ninth.state import empty

    def signals() -> frozenset[str]:
        return _nonempty_lists(check_leftovers(explore(empty(), 2, 4)))

    @contextmanager
    def mutate() -> Iterator[None]:
        # a relation-DEPENDENT writing: a removal in s differs from the same in r.
        def wrong(state: Any, change: Any) -> Any:
            return leftover_pair(9, 9) if change.rel == "s" else real_leftover_of(state, change)

        with patch_everywhere("fourteenth", "leftover_of", wrong):
            yield

    return BiteCase("fourteenth: leftover names no relation", signals, mutate, "cross_relation_disagree")


def registry() -> list[BiteCase]:
    return [_fifteenth_cross_relation(), _tenth_identify_split(), _fourteenth_cross_relation()]


def main(argv: list[str] | None = None) -> int:
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    argparse.ArgumentParser(prog="check_mutation_bite", description=__doc__).parse_args(argv)

    cases = registry()
    failures = [(case, reason) for case in cases if (reason := run_case(case)) is not None]
    if not failures:
        print(f"mutation-bite gate clean: {len(cases)} differential checks, each bites under a derivation mutation")
        return 0
    for case, reason in failures:
        print(f"FAIL: {case.name} ({case.field}): {reason}")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
