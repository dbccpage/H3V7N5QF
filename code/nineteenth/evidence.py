"""Evidence that a partial identification does not erase a term.

The disagreement lists are empty on the real exploration. Each has a branch
that records a failure, driven by the tests.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from xry.changes import Change, Kind, perform
from xry.evidence import write_manifest
from xry.explore import explore
from xry.state import Sameness, State, canonical, given

from nineteenth.changes import between_the_two, obstructed, partials
from nineteenth.explore import explore_partial


@dataclass
class PartialCheck:
    """Disagreements. Empty when the two readings and the base agree as stated."""

    sets_differ: list[str]
    extra_beyond_base: list[str]
    term_dropped: list[str]
    cooccur_performed: list[str]
    obstruction_not_between: list[str]
    removal_answer_outside: list[str]


def _merged(state: State) -> bool:
    return state.names is not None and state.names[0] == state.names[1]


def audit(bra: bool, sameness: Sameness, bound: int = 3, rounds: int = 12) -> PartialCheck:
    """Compare the two readings of "one chosen assertion" with the base closure."""
    start = given(bra, sameness)
    broad = explore_partial(start, bound, rounds, False)
    narrow = explore_partial(start, bound, rounds, True)
    base = explore(start, bound, rounds)
    differ = sorted(state.key() for state in set(broad.depth) ^ set(narrow.depth))
    extra = sorted(state.key() for state in broad.depth if state not in base.depth)
    dropped = sorted(state.key() for state in broad.depth if state.n < start.n)
    performed = ["cooccur performed"] if narrow.performed_partials else []
    bad_obs: list[str] = []
    bad_removal: list[str] = []
    for state in broad.depth:
        for partial in partials(state):
            loop = between_the_two(partial)
            if loop != obstructed(state, partial):
                bad_obs.append(f"{state.key()} {partial.pair[0]}-{partial.pair[1]}")
            if not loop:
                continue
            cleared = canonical(perform(state, Change(Kind.REMOVE, partial.pair[0], partial.pair[1])))
            if cleared not in broad.depth:
                bad_removal.append(state.key())
    return PartialCheck(differ, extra, dropped, performed, bad_obs, bad_removal)


def measure(bra: bool, sameness: Sameness, bound: int, rounds: int) -> dict[str, object]:
    """One beginning: the check, and the counts the paper cites."""
    start = given(bra, sameness)
    broad = explore_partial(start, bound, rounds, False)
    narrow = explore_partial(start, bound, rounds, True)
    base = explore(start, bound, rounds)
    check = audit(bra, sameness, bound, rounds)
    missing = [state for state in base.depth if state not in broad.depth]
    return {
        "bra": bra,
        "sameness": sameness.value,
        "partial_results": len(broad.depth),
        "cooccur_results": len(narrow.depth),
        "base_results": len(base.depth),
        "missing": len(missing),
        "missing_names_one_term": sum(1 for state in missing if _merged(state)),
        "missing_one_term_count": sum(1 for state in missing if state.n == 1),
        "extra": len(set(broad.depth) - set(base.depth)),
        "performed_partials": broad.performed_partials,
        "obstructed_partials": broad.obstructed_partials,
        "cooccur_performed": narrow.performed_partials,
        "cooccur_obstructed": narrow.obstructed_partials,
        "min_terms": broad.min_terms,
        "frontier": broad.frontier,
        "new_per_round": broad.new_per_round,
        "base_frontier_exits": len(base.frontier),
        "sets_differ": check.sets_differ,
        "extra_beyond_base": check.extra_beyond_base,
        "term_dropped": check.term_dropped,
        "cooccur_performed_flag": check.cooccur_performed,
        "obstruction_not_between": check.obstruction_not_between,
        "removal_answer_outside": check.removal_answer_outside,
    }


def _closure(bra: bool, sameness: Sameness, bound: int, rounds: int) -> set[State]:
    return set(explore_partial(given(bra, sameness), bound, rounds, False).depth)


def write_all(out: Path, bound: int = 3, rounds: int = 12) -> dict[str, object]:
    """Write `summary.json` and the manifest for the declared bound."""
    out.mkdir(parents=True, exist_ok=True)
    runs = [
        measure(bra, sameness, bound, rounds)
        for bra in (False, True)
        for sameness in (Sameness.ANCHORED, Sameness.FREE)
    ]
    anchored = _closure(False, Sameness.ANCHORED, bound, rounds)
    free = _closure(False, Sameness.FREE, bound, rounds)
    summary: dict[str, object] = {
        "bound": bound,
        "rounds": rounds,
        "anchored_closures_equal_for_both_bra": anchored == _closure(True, Sameness.ANCHORED, bound, rounds),
        "free_closures_equal_for_both_bra": free == _closure(True, Sameness.FREE, bound, rounds),
        "runs": runs,
    }
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8", newline="\n")
    write_manifest(out)
    return summary
