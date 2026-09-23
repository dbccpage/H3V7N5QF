"""Evidence that refusal reaches the base closure.

The disagreement lists are empty on the real exploration. Each has a branch
that records a failure, driven by the tests and by the twenty-first panel of
`ci/check_mutation_bite.py`.
"""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path

from xry.changes import AnswerKind, answers, changes, obstruction
from xry.evidence import write_manifest
from xry.explore import explore
from xry.state import Sameness, State, canonical, given

from twentyfirst.refusal import explore_refusing


@dataclass
class RefusalCheck:
    """Disagreements with the base closure, and answers that buy a new result."""

    outside_the_base: list[str]
    answer_buys_a_result: list[str]
    stopped_at_the_start: list[str]


def answer_is_new(got: State, depth: dict[State, int]) -> bool:
    """An answer whose result the unobstructed changes have not reached."""
    return got not in depth


def has_unobstructed(state: State) -> bool:
    """The state has a change that is not obstructed."""
    return any(not obstruction(state, change) for change in changes(state))


def audit(bra: bool, sameness: Sameness, bound: int = 3, rounds: int = 12) -> RefusalCheck:
    """Compare the refusing exploration with the base exploration at the same bound.

    The refusing exploration performs every change and refuses an outcome that
    asserts some `xrx`; the base spreads along the changes its obstruction test
    lets through. A result reached by one and not the other, or at another
    round, is recorded. Then every base answer other than refusal is checked
    against the base closure.
    """
    start = given(bra, sameness)
    base = explore(start, bound, rounds)
    refusing = explore_refusing(start, bound, rounds).depth
    outside = sorted(
        state.key()
        for state in base.depth.keys() | refusing.keys()
        if base.depth.get(state) != refusing.get(state)
    )
    bought: list[str] = []
    for state in base.depth:
        for change in changes(state):
            if not obstruction(state, change):
                continue
            for answer in answers(state, change):
                if answer.kind is AnswerKind.REFUSE or answer.result.n > bound:
                    continue
                if answer_is_new(canonical(answer.result), base.depth):
                    bought.append(f"{state.key()} / {answer.kind.value}")
    stopped = [] if has_unobstructed(start) else [start.key()]
    return RefusalCheck(outside, bought, stopped)


def measure(bra: bool, sameness: Sameness, bound: int, rounds: int) -> dict[str, object]:
    """One beginning: the check, and how many answers were looked at."""
    start = given(bra, sameness)
    base = explore(start, bound, rounds)
    check = audit(bra, sameness, bound, rounds)
    refusing = explore_refusing(start, bound, rounds)
    looked = 0
    obstructed = 0
    for state in base.depth:
        for change in changes(state):
            if obstruction(state, change):
                obstructed += 1
                looked += len(answers(state, change))
    return {
        "bra": bra,
        "sameness": sameness.value,
        "results": len(base.depth),
        "last_new_round": base.last_new_round,
        "frontier_exits": len(base.frontier),
        "refusing_results": len(refusing.depth),
        "refusals": refusing.refusals,
        "obstructed_attempts_in_the_base": obstructed,
        "answers_checked": looked,
        "outside_the_base": check.outside_the_base,
        "answer_buys_a_result": check.answer_buys_a_result,
        "stopped_at_the_start": check.stopped_at_the_start,
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
    }
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8", newline="\n")
    write_manifest(out)
    return summary
