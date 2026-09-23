"""Evidence that a different writing is a different result.

The disagreement lists are empty on the real exploration. Each has a branch
that records a failure, driven by the tests and by the eighteenth panel of
`ci/check_mutation_bite.py`.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from xry.cost import cost
from xry.evidence import write_manifest
from xry.explore import explore, order
from xry.state import Sameness, State, canonical, given, rewrite

from eighteenth.explore import answer_other_writing, explore_written
from eighteenth.writing import (
    aut_size,
    letter_supply,
    orbit_size,
    orbit_splits_factorial,
    same_written,
)


@dataclass
class WritingCheck:
    """Disagreements. Empty when distinct writings stay distinct, `n!` splits,
    and no writing is reached in fewer changes than the base's count."""

    writings_called_the_same: list[str]
    orbit_formula_fails: list[str]
    rounds_below_the_base_cost: list[str]


def base_count(state: State, bra: bool) -> int:
    """The base's fewest changes. It reads the size and the destroyed givens,
    so it is the same for every writing of a state."""
    return cost(state, bra) if state.names is not None else cost(canonical(state), bra)


def audit(depth: dict[State, int], bra: bool, left: State, right: State) -> WritingCheck:
    """Check a written exploration from the beginning `bra`.

    `same_written` is compared with the written key of each state (an
    independent serialisation), over every pair of reached states and the two
    writings `left`, `right`. The round of each reached writing is compared
    with the base's count, which is a lower bound on every sequence.
    """
    states = sorted(depth, key=order)
    pool = states + [left, right]
    called = [
        f"{one.key()} = {other.key()}"
        for i, one in enumerate(pool)
        for other in pool[i + 1 :]
        if same_written(one, other) != (one.key() == other.key())
    ]
    fails = [state.key() for state in states if not orbit_splits_factorial(state)]
    below = [state.key() for state in states if depth[state] < base_count(state, bra)]
    return WritingCheck(called, fails, below)


def _excess(depth: dict[State, int], bra: bool) -> list[int]:
    return [depth_of - base_count(state, bra) for state, depth_of in depth.items()]


def letter_supply_grows(n: int, aut: int, span: int = 12) -> bool:
    """Every further letter raises the number of writings (`n` at least one)."""
    return all(
        letter_supply(n, aut, letters) < letter_supply(n, aut, letters + 1)
        for letters in range(n, n + span)
    )


def _run(bra: bool, sameness: Sameness, bound: int, rounds: int) -> dict[str, object]:
    start = given(bra, sameness)
    written = explore_written(start, bound, rounds)
    base = explore(start, bound, rounds)
    classes: dict[State, list[State]] = {}
    for state in written.depth:
        classes.setdefault(canonical(state), []).append(state)
    sample = max(written.depth, key=lambda state: (orbit_size(state), state.n, state.mask))
    check = audit(written.depth, bra, start, rewrite(start, (1, 0)))
    excess = _excess(written.depth, bra)
    return {
        "bra": bra,
        "sameness": sameness.value,
        "written_results": len(written.depth),
        "base_results": len(base.depth),
        "base_classes_among_written": len(classes),
        "classes_with_two_writings_reached": sum(1 for members in classes.values() if len(members) > 1),
        "rounds_above_the_base_cost": sum(1 for gap in excess if gap > 0),
        "greatest_excess_over_the_base_cost": max(excess),
        "answers_on_an_unreached_writing": len(answer_other_writing(written)),
        "frontier": len(written.frontier),
        "new_per_round": written.new_per_round,
        "sample_key": sample.key(),
        "sample_orbit": orbit_size(sample),
        "sample_aut": aut_size(sample),
        "sample_letters_25": letter_supply(sample.n, aut_size(sample), 25),
        "sample_letter_supply_grows": letter_supply_grows(sample.n, aut_size(sample)),
        "writings_called_the_same": check.writings_called_the_same,
        "orbit_formula_fails": check.orbit_formula_fails,
        "rounds_below_the_base_cost": check.rounds_below_the_base_cost,
    }


def write_all(out: Path, bound: int = 3, rounds: int = 12) -> dict[str, object]:
    """Write `summary.json` and the manifest for the declared bound."""
    out.mkdir(parents=True, exist_ok=True)
    start = given(False, Sameness.ANCHORED)
    # `rewrite` of the given state by swapping its two terms is its other writing.
    swapped = rewrite(start, (1, 0))
    closures = {
        (bra, sameness): set(explore_written(given(bra, sameness), bound, rounds).depth)
        for bra in (False, True)
        for sameness in (Sameness.ANCHORED, Sameness.FREE)
    }
    summary = {
        "bound": bound,
        "rounds": rounds,
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
        "anchored_closures_equal_for_both_bra": closures[(False, Sameness.ANCHORED)]
        == closures[(True, Sameness.ANCHORED)],
        "free_closures_equal_for_both_bra": closures[(False, Sameness.FREE)]
        == closures[(True, Sameness.FREE)],
    }
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8", newline="\n")
    write_manifest(out)
    return summary
