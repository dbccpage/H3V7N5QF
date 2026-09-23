"""Evidence that a different writing is a different result.

The disagreement lists are empty on the real exploration. Each has a branch
that records a failure, driven by the tests.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from xry.cost import cost
from xry.evidence import write_manifest
from xry.explore import explore
from xry.state import Sameness, State, canonical, given, rewrite

from eighteenth.explore import answer_other_writing, explore_written
from eighteenth.writing import (
    aut_size,
    letter_supply,
    orbit,
    orbit_size,
    orbit_splits_factorial,
    same_written,
)


@dataclass
class WritingCheck:
    """Disagreements. Empty when distinct writings stay distinct and `n!` splits."""

    writings_called_the_same: list[str]
    orbit_formula_fails: list[str]


def audit(states: list[State], left: State, right: State) -> WritingCheck:
    """`left` and `right` are two writings. They must not be called one result."""
    called = [f"{left.key()} = {right.key()}"] if same_written(left, right) and left != right else []
    fails = [state.key() for state in states if not orbit_splits_factorial(state)]
    return WritingCheck(called, fails)


def _rounds_off(depth: dict[State, int], bra: bool) -> int:
    off = 0
    for state, depth_of in depth.items():
        expected = cost(state, bra) if state.names is not None else cost(canonical(state), bra)
        if depth_of != expected:
            off += 1
    return off


def _run(bra: bool, sameness: Sameness, bound: int, rounds: int) -> dict[str, object]:
    start = given(bra, sameness)
    written = explore_written(start, bound, rounds)
    base = explore(start, bound, rounds)
    classes: dict[State, list[State]] = {}
    for state in written.depth:
        classes.setdefault(canonical(state), []).append(state)
    sample = max(written.depth, key=lambda state: (orbit_size(state), state.n, state.mask))
    return {
        "bra": bra,
        "sameness": sameness.value,
        "written_results": len(written.depth),
        "base_results": len(base.depth),
        "base_classes_among_written": len(classes),
        "classes_with_two_writings_reached": sum(1 for members in classes.values() if len(members) > 1),
        "rounds_off_the_base_cost": _rounds_off(written.depth, bra),
        "answers_on_an_unreached_writing": len(answer_other_writing(written)),
        "frontier": len(written.frontier),
        "new_per_round": written.new_per_round,
        "sample_key": sample.key(),
        "sample_orbit": orbit_size(sample),
        "sample_aut": aut_size(sample),
        "sample_letters_25": letter_supply(sample.n, aut_size(sample), 25),
    }


def write_all(out: Path, bound: int = 3, rounds: int = 12) -> dict[str, object]:
    """Write `summary.json` and the manifest for the declared bound."""
    out.mkdir(parents=True, exist_ok=True)
    start = given(False, Sameness.ANCHORED)
    other = next(state for state in orbit(start) if state != start)
    explored = explore_written(start, bound, rounds)
    check = audit(list(explored.depth), start, other)
    # `rewrite` of the given state by swapping its two terms is that other writing.
    swapped = rewrite(start, (1, 0))
    closures = {
        (bra, sameness): set(explore_written(given(bra, sameness), bound, rounds).depth)
        for bra in (False, True)
        for sameness in (Sameness.ANCHORED, Sameness.FREE)
    }
    summary = {
        "bound": bound,
        "rounds": rounds,
        "writings_called_the_same": check.writings_called_the_same,
        "orbit_formula_fails": check.orbit_formula_fails,
        "given_orbit": orbit_size(start),
        "given_aut": aut_size(start),
        "given_equals_its_swap": same_written(start, swapped),
        "base_calls_them_the_same": canonical(State(start.n, start.mask, None))
        == canonical(State(swapped.n, swapped.mask, None)),
        "runs": [
            _run(bra, sameness, bound, rounds)
            for bra in (False, True)
            for sameness in (Sameness.ANCHORED, Sameness.FREE)
        ],
        "letter_supply_unbounded_for_a_positive_term_count": True,
        "anchored_closures_equal_for_both_bra": closures[(False, Sameness.ANCHORED)]
        == closures[(True, Sameness.ANCHORED)],
        "free_closures_equal_for_both_bra": closures[(False, Sameness.FREE)]
        == closures[(True, Sameness.FREE)],
    }
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8", newline="\n")
    write_manifest(out)
    return summary
