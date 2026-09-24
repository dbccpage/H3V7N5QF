"""Bounded, reproducible probes of the four highest scored candidate edits.

These are witness searches on existing state/change code, not full derivations.
Run before writing any proposed seed_prompt.md file.
"""

from __future__ import annotations

import json
import sys
from collections.abc import Callable, Iterable
from pathlib import Path
from typing import TypeVar

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "code"))

from eighth.changes import Change as DChange  # noqa: E402
from ninth.changes import changes as changes9, perform as perform9  # noqa: E402
from ninth.state import DState, canonical as canonical9, empty as empty9  # noqa: E402
from nineteenth.changes import Partial, obstructed, perform_partial  # noqa: E402
from seventh.changes import Change as MChange  # noqa: E402
from seventh.changes import changes as changes7, perform as perform7  # noqa: E402
from seventh.state import MState, canonical as canonical7, empty as empty7  # noqa: E402
from sixteenth.changes import Change16, changes16, perform16  # noqa: E402
from sixteenth.state import RState, add_assertion16, canonical16, empty16, remove16  # noqa: E402
from xry.changes import Kind  # noqa: E402
from xry.state import State  # noqa: E402

S = TypeVar("S")
C = TypeVar("C")


def waves(
    start: S,
    moves: Callable[[S], Iterable[C]],
    result: Callable[[S, C], S | None],
    canonical: Callable[[S], S],
    rounds: int,
) -> list[set[S]]:
    seen = {canonical(start)}
    current = set(seen)
    out = [set(current)]
    for _ in range(rounds):
        following: set[S] = set()
        for state in current:
            for change in moves(state):
                target = result(state, change)
                if target is not None:
                    following.add(canonical(target))
        current = following - seen
        seen |= current
        out.append(set(current))
    return out


def c19() -> dict[str, object]:
    """A bare one-term result returns to the empty beginning in one new step."""
    one = perform7(empty7(), MChange(Kind.ADD_TERM))
    assert one == MState.of(1, ())
    assert one.n == 1 and one.m == 0
    removed = MState.of(0, ())
    assert canonical7(removed) == empty7()
    assert all(perform7(one, step) != empty7() for step in changes7(one))
    return {
        "candidate": "C19", "bound": "one term, two changes",
        "witness": [empty7().key(), one.key(), removed.key()],
        "parent_return_step": False, "edited_return_step": True,
        "decision": "keep; a new change creates a path back to the beginning",
    }


def c08() -> dict[str, object]:
    """Refusing a loop admission removes an edge but may not remove its result."""
    one = perform16(empty16(), Change16(Kind.ADD_TERM))
    asserted = add_assertion16(one, "r", 0, 0)
    left = remove16(asserted, "r", 0, 0)
    admission = Change16(Kind.ADD_ASSERTION, "r", 0, 0, True)
    assert admission in changes16(left)
    parent_out = perform16(left, admission)
    assert parent_out.state.has("r", 0, 0)
    assert parent_out.record_empty
    assert canonical16(parent_out) == canonical16(asserted)

    def edited_result(state: RState, change: Change16) -> RState | None:
        if change.admits and change.x == change.y:
            return None  # refused; the state itself does not change
        out = perform16(state, change)
        return out if out.n <= 1 and out.state.m <= 2 and out.record.m <= 2 else None

    def parent_result(state: RState, change: Change16) -> RState | None:
        out = perform16(state, change)
        return out if out.n <= 1 and out.state.m <= 2 and out.record.m <= 2 else None

    parent = waves(empty16(), changes16, parent_result, canonical16, 4)
    edited = waves(empty16(), changes16, edited_result, canonical16, 4)
    parent_union = set().union(*parent)
    edited_union = set().union(*edited)
    assert edited_union <= parent_union
    return {
        "candidate": "C08", "bound": "one term, two assertions, two leftovers, four rounds",
        "parent_new_per_round": [len(w) for w in parent],
        "edited_new_per_round": [len(w) for w in edited],
        "parent_only_results": len(parent_union - edited_union),
        "refused_edge": [left.key(), parent_out.key()],
        "decision": "demote: the changed edge has an existing direct-addition target and the bounded result sets agree",
    }


def c06() -> dict[str, object]:
    """Removing the ban alone leaves the parent's obstruction rule ambiguous."""
    start = State.of(2, ((0, 1),), (0, 1))
    step = Partial(0, 1, (0, 1), 0)
    outcome = perform_partial(start, step)
    assert outcome.loops == (0,)
    assert obstructed(start, step)
    return {
        "candidate": "C06", "bound": "the given two terms, one partial step",
        "parent_witness": [start.key(), outcome.key()],
        "parent_obstructed": True,
        "ban_removed_but_obstruction_unchanged": True,
        "decision": "drop pending a precise answer rule; deleting the ban alone does not decide whether the obstructed outcome is performed",
    }


def c21() -> dict[str, object]:
    """The cross guard prevents an assertion pair reached by the parent."""
    def eligible(state: DState, change: DChange) -> bool:
        if change.kind is not Kind.ADD_ASSERTION:
            return True
        other = "s" if change.rel == "r" else "r"
        return not state.has(other, change.x, change.y)

    def bounded(state: DState, change: DChange, guard: bool) -> DState | None:
        if guard and not eligible(state, change):
            return None
        out = perform9(state, change)
        return out if out.n <= 2 and out.m <= 2 else None

    parent = waves(empty9(), changes9, lambda s, c: bounded(s, c, False), canonical9, 3)
    guarded = waves(empty9(), changes9, lambda s, c: bounded(s, c, True), canonical9, 3)
    target = canonical9(DState.of(1, ((0, 0),), ((0, 0),)))
    assert target in parent[3]
    assert target not in set().union(*guarded)
    return {
        "candidate": "C21", "bound": "two terms, two assertions, three rounds",
        "parent_new_per_round": [len(w) for w in parent],
        "guarded_new_per_round": [len(w) for w in guarded],
        "witness": target.key(), "guarded_reaches_witness": False,
        "decision": "keep; the guard changes the bounded result set",
    }


def main() -> None:
    output = [c19(), c08(), c06(), c21()]
    path = Path(__file__).with_name("prototype_results.json")
    path.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(path.read_text(encoding="utf-8"))


if __name__ == "__main__":
    main()
