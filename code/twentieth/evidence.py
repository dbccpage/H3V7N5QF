"""Evidence that the round is the number of changes.

The disagreement lists are empty on the real exploration. Each has a branch
that records a failure, driven by the tests.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from xry.evidence import write_manifest
from xry.explore import explore, order
from xry.state import Sameness, State, added, given

from twentieth.order import _bfs, additions_priority, frontiers, rankings_differ


@dataclass
class OrderCheck:
    """Disagreements between listings, and a missing witness that the rankings differ."""

    layer_mismatch: list[str]
    frontier_mismatch: list[str]
    additions_track_rounds: list[str]
    differs_from_base: list[str]


def audit(bra: bool, bound: int = 3, rounds: int = 12, sameness: Sameness = Sameness.ANCHORED) -> OrderCheck:
    """Compare an additions-first listing with a changes-first listing, and with the base."""
    start = given(bra, sameness)
    base = explore(start, bound, rounds)
    by_add = _bfs(start, bound, rounds, True)
    by_changes = _bfs(start, bound, rounds, False)
    mismatch = sorted(
        state.key() for state in by_add.keys() | by_changes.keys() if by_add.get(state) != by_changes.get(state)
    )
    front_add = frontiers(by_add, bound)
    front_changes = frontiers(by_changes, bound)
    front_base = frontiers(base.depth, bound)
    frontier = sorted(state.key() for state in (front_add ^ front_changes) | (front_changes ^ front_base))
    differs = sorted(
        state.key()
        for state in set(base.depth) | set(by_changes)
        if base.depth.get(state) != by_changes.get(state)
    )
    tracked = [] if rankings_differ(base.depth) is not None else ["no witness"]
    return OrderCheck(mismatch, frontier, tracked, differs)


def witness(depth: dict[State, int]) -> dict[str, object] | None:
    pair = rankings_differ(depth)
    if pair is None:
        return None
    fewer, sooner = pair
    return {
        "fewer_additions": fewer.key(),
        "fewer_additions_added": list(added(fewer)),
        "fewer_additions_round": depth[fewer],
        "sooner": sooner.key(),
        "sooner_added": list(added(sooner)),
        "sooner_round": depth[sooner],
    }


def capped(bra: bool, bound: int = 3, rounds: int = 12) -> dict[str, object]:
    """Unchosen reading: stop after expanding as many results as round 2 has reached."""
    start = given(bra, Sameness.ANCHORED)
    base = explore(start, bound, rounds)
    early = {state for state, depth in base.depth.items() if depth <= 2}
    priority = additions_priority(start, bound, len(early))
    leave = sorted(early - set(priority), key=order)
    enter = sorted(set(priority) - early, key=order)
    return {
        "bra": bra,
        "expanded": len(early),
        "leave": [state.key() for state in leave],
        "enter": [state.key() for state in enter],
    }


def measure(bra: bool, sameness: Sameness, bound: int, rounds: int) -> dict[str, object]:
    """One beginning under the chosen reading."""
    start = given(bra, sameness)
    base = explore(start, bound, rounds)
    check = audit(bra, bound, rounds, sameness)
    return {
        "bra": bra,
        "sameness": sameness.value,
        "results": len(base.depth),
        "last_new_round": base.last_new_round,
        "frontier_exits": len(base.frontier),
        "states_at_bound": len(frontiers(base.depth, bound)),
        "witness": witness(base.depth),
        "layer_mismatch": check.layer_mismatch,
        "frontier_mismatch": check.frontier_mismatch,
        "additions_track_rounds": check.additions_track_rounds,
        "differs_from_base": check.differs_from_base,
    }


def write_all(out: Path, bound: int = 3, rounds: int = 12) -> dict[str, object]:
    """Write `summary.json` and the manifest for the declared bound."""
    out.mkdir(parents=True, exist_ok=True)
    summary: dict[str, object] = {
        "bound": bound,
        "rounds": rounds,
        "runs": [
            measure(bra, sameness, bound, rounds)
            for bra in (False, True)
            for sameness in (Sameness.ANCHORED, Sameness.FREE)
        ],
        "capped_by_round_2": [capped(bra, bound, rounds) for bra in (False, True)],
    }
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8", newline="\n")
    write_manifest(out)
    return summary
