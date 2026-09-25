"""Typed model of Problem 02: two-relation state exploration with cross-relation guard.

Seed modification:
    Adding `xry` is a change only if `xsy` is not asserted, and adding `xsy`
    is a change only if `xry` is not asserted.
"""

from __future__ import annotations

import sys
from collections import deque
from collections.abc import Iterator, Sequence
from dataclasses import dataclass, field
from pathlib import Path
from typing import Final

# Ensure repository code/ directory is available for base primitives.
_REPO_ROOT = Path(__file__).resolve().parents[4]
_CODE_DIR = _REPO_ROOT / "code"
if str(_CODE_DIR) not in sys.path:
    sys.path.insert(0, str(_CODE_DIR))

from eighth.changes import Change, Kind, perform as perform_base
from ninth.changes import changes as ninth_changes
from ninth.orbits import count_results as ninth_count_results
from ninth.state import DState, canonical, empty, same

__all__ = [
    "RELATIONS",
    "Change",
    "DState",
    "Exit",
    "GuardedExploration",
    "Kind",
    "attempt_change",
    "can_add_assertion",
    "canonical",
    "compare_with_ninth",
    "count_disjoint_results",
    "empty",
    "explore",
    "guarded_additions",
    "guarded_changes",
    "is_cross_guarded",
    "is_disjoint_support",
    "is_guarded_change",
    "other_relation",
    "perform",
    "same",
    "witness_blocked_pair",
    "witness_identification_bypass",
    "witness_two_term_bypass",
]

RELATIONS: Final[tuple[str, str]] = ("r", "s")


def other_relation(rel: str) -> str:
    """Return the complementary relation: r -> s, s -> r."""
    if rel == "r":
        return "s"
    if rel == "s":
        return "r"
    raise ValueError(f"Unknown relation: {rel}")


def is_cross_guarded(state: DState, rel: str, x: int, y: int) -> bool:
    """Check whether adding rel(x, y) is guarded by the presence of other_rel(x, y)."""
    other = other_relation(rel)
    return state.has(other, x, y)


def can_add_assertion(state: DState, rel: str, x: int, y: int) -> bool:
    """Check if assertion of rel on ordered pair (x, y) is an admitted change."""
    if not (0 <= x < state.n and 0 <= y < state.n):
        return False
    return not is_cross_guarded(state, rel, x, y)


def is_guarded_change(state: DState, change: Change) -> bool:
    """Test whether change is an admitted change on state under the guarded seed."""
    if change.kind is Kind.ADD_TERM:
        return True
    if change.kind is Kind.IDENTIFY:
        return 0 <= change.x < change.y < state.n
    if change.kind is Kind.REMOVE:
        return state.has(change.rel, change.x, change.y)
    if change.kind is Kind.ADD_ASSERTION:
        return can_add_assertion(state, change.rel, change.x, change.y)
    return False


def guarded_changes(state: DState) -> tuple[Change, ...]:
    """Every admitted change of the guarded seed on state, fewest additions first."""
    n = state.n
    if n == 0:
        return (Change(Kind.ADD_TERM),)

    out: list[Change] = []
    # 0 additions: identifications
    for x in range(n):
        for y in range(x + 1, n):
            out.append(Change(Kind.IDENTIFY, "", x, y))

    # 0 additions: removals in r then in s
    for rel in RELATIONS:
        for x, y in state.part(rel).pairs:
            out.append(Change(Kind.REMOVE, rel, x, y))

    # 1 term addition
    out.append(Change(Kind.ADD_TERM))

    # 1 assertion addition: in r then in s, respecting cross guard
    for rel in RELATIONS:
        other = other_relation(rel)
        for x in range(n):
            for y in range(n):
                if not state.has(other, x, y):
                    out.append(Change(Kind.ADD_ASSERTION, rel, x, y))

    return tuple(out)


def guarded_additions(state: DState) -> tuple[Change, ...]:
    """Return only addition changes admitted under the cross guard."""
    return tuple(c for c in guarded_changes(state) if c.kind in (Kind.ADD_TERM, Kind.ADD_ASSERTION))


def perform(state: DState, change: Change) -> DState:
    """Apply an admitted change to state. Raises ValueError if not admitted."""
    if not is_guarded_change(state, change):
        raise ValueError(f"Change {change} is not admitted on state {state}")
    return perform_base(state, change)


def is_disjoint_support(state: DState) -> bool:
    """Check whether r and s have disjoint asserted pairs (no pair asserted in both)."""
    n = state.n
    for x in range(n):
        for y in range(n):
            if state.has("r", x, y) and state.has("s", x, y):
                return False
    return True


@dataclass(frozen=True)
class Exit:
    """A change attempt that leaves the finite exploration bound."""

    state: DState
    change: Change
    reason: str


@dataclass
class GuardedExploration:
    """Exploration state and statistics for guarded relation exploration."""

    start: DState
    bound_terms: int
    bound_assertions: int
    rounds: int
    depth: dict[DState, int]
    new_per_round: list[int]
    attempts_per_round: list[int]
    blocked_attempts_per_round: list[int]
    frontier: list[Exit] = field(default_factory=list)
    shortest_paths: dict[DState, tuple[Change, ...]] = field(default_factory=dict)

    @property
    def total_results(self) -> int:
        """Total distinct results discovered within declared bounds."""
        return len(self.depth)

    @property
    def last_new_round(self) -> int:
        """Last round that produced a new result."""
        return max((r for r, count in enumerate(self.new_per_round) if count > 0), default=0)

    def results_at_round(self, round_idx: int) -> list[DState]:
        """Return results first reached in round_idx."""
        return sorted([s for s, r in self.depth.items() if r == round_idx], key=lambda s: (s.n, s.m, s.r, s.s))


def attempt_change(
    state: DState, change: Change, bound_terms: int, bound_assertions: int
) -> tuple[DState | None, bool, str]:
    """Attempt change on state within declared bounds."""
    out = perform(state, change)
    if out.n > bound_terms:
        return None, True, "terms_bound_exceeded"
    if out.m > bound_assertions:
        return None, True, "assertions_bound_exceeded"
    return canonical(out), False, "ok"


def explore(
    start: DState | None = None,
    bound_terms: int = 3,
    bound_assertions: int = 3,
    rounds: int = 6,
    additions_only: bool = False,
) -> GuardedExploration:
    """Breadth-first exploration under cross-relation guard."""
    if start is None:
        start = empty()
    root = canonical(start)

    depth: dict[DState, int] = {root: 0}
    shortest_paths: dict[DState, tuple[Change, ...]] = {root: ()}
    wave: list[DState] = [root]

    new_per_round: list[int] = [1]
    attempts_per_round: list[int] = [0]
    blocked_attempts_per_round: list[int] = [0]
    frontier: list[Exit] = []

    for _ in range(1, rounds + 1):
        nxt_wave: list[DState] = []
        attempts_this_round = 0
        blocked_this_round = 0

        for s in wave:
            # Count potential additions that were blocked by cross guard
            for rel in RELATIONS:
                other = other_relation(rel)
                for x in range(s.n):
                    for y in range(s.n):
                        if s.has(other, x, y):
                            blocked_this_round += 1

            changes_fn = guarded_additions if additions_only else guarded_changes
            for c in changes_fn(s):
                attempts_this_round += 1
                out, beyond, reason = attempt_change(s, c, bound_terms, bound_assertions)
                if beyond:
                    frontier.append(Exit(s, c, reason))
                elif out is not None and out not in depth:
                    depth[out] = len(new_per_round)
                    shortest_paths[out] = shortest_paths[s] + (c,)
                    nxt_wave.append(out)

        new_per_round.append(len(nxt_wave))
        attempts_per_round.append(attempts_this_round)
        blocked_attempts_per_round.append(blocked_this_round)
        wave = nxt_wave

    return GuardedExploration(
        start=root,
        bound_terms=bound_terms,
        bound_assertions=bound_assertions,
        rounds=rounds,
        depth=depth,
        new_per_round=new_per_round,
        attempts_per_round=attempts_per_round,
        blocked_attempts_per_round=blocked_attempts_per_round,
        frontier=frontier,
        shortest_paths=shortest_paths,
    )


def count_disjoint_results(bound_terms: int, bound_assertions: int) -> dict[str, int]:
    """Exact enumeration of canonical results whose assertion supports are disjoint."""
    counts: dict[str, int] = {}
    # Build results using BFS with guarded changes
    exp = explore(start=empty(), bound_terms=bound_terms, bound_assertions=bound_assertions, rounds=bound_terms + bound_assertions + 2)
    for state in exp.depth:
        if is_disjoint_support(state):
            key = f"{state.n}/{state.m}"
            counts[key] = counts.get(key, 0) + 1
    return counts


def compare_with_ninth(
    bound_terms: int = 3, bound_assertions: int = 3, rounds: int = 5
) -> dict[str, object]:
    """Compare round-by-round reachability between ninth and guarded systems."""
    root = canonical(empty())

    # Ninth waves
    seen_9: set[DState] = {root}
    curr_9: set[DState] = {root}
    waves_9: list[set[DState]] = [set(curr_9)]

    # Guarded waves
    seen_g: set[DState] = {root}
    curr_g: set[DState] = {root}
    waves_g: list[set[DState]] = [set(curr_g)]

    for _ in range(rounds):
        nxt_9: set[DState] = set()
        for s in curr_9:
            for c in ninth_changes(s):
                out = perform_base(s, c)
                if out.n <= bound_terms and out.m <= bound_assertions:
                    nxt_9.add(canonical(out))
        new_9 = nxt_9 - seen_9
        seen_9 |= new_9
        curr_9 = new_9
        waves_9.append(set(curr_9))

        nxt_g: set[DState] = set()
        for s in curr_g:
            for c in guarded_changes(s):
                out = perform_base(s, c)
                if out.n <= bound_terms and out.m <= bound_assertions:
                    nxt_g.add(canonical(out))
        new_g = nxt_g - seen_g
        seen_g |= new_g
        curr_g = new_g
        waves_g.append(set(curr_g))

    ninth_new = [len(w) for w in waves_9]
    guarded_new = [len(w) for w in waves_g]

    # Differences per round
    diff_per_round: list[list[str]] = []
    for r in range(len(waves_9)):
        unreached_by_guarded = sorted(s.key() for s in (waves_9[r] - waves_g[r]))
        diff_per_round.append(unreached_by_guarded)

    return {
        "ninth_new_per_round": ninth_new,
        "guarded_new_per_round": guarded_new,
        "diff_per_round": diff_per_round,
        "falsifier_satisfied": ninth_new == guarded_new,
    }


def witness_blocked_pair() -> tuple[DState, Change]:
    """Construct a concrete state and change that is blocked by the cross guard."""
    one_term = DState.of(1, ((0, 0),), ())
    blocked_change = Change(Kind.ADD_ASSERTION, "s", 0, 0)
    assert not is_guarded_change(one_term, blocked_change)
    return one_term, blocked_change


def witness_identification_bypass() -> list[tuple[Change, DState]]:
    """Produce the shortest sequence reaching 1::0-0*1|0-0*1 in 5 steps via identification."""
    s0 = canonical(empty())
    c1 = Change(Kind.ADD_TERM)
    s1 = canonical(perform(s0, c1))
    c2 = Change(Kind.ADD_TERM)
    s2 = canonical(perform(s1, c2))
    c3 = Change(Kind.ADD_ASSERTION, "r", 1, 1)
    s3 = canonical(perform(s2, c3))
    c4 = Change(Kind.ADD_ASSERTION, "s", 0, 0)
    s4 = canonical(perform(s3, c4))
    c5 = Change(Kind.IDENTIFY, "", 0, 1)
    s5 = canonical(perform(s4, c5))

    target = canonical(DState.of(1, ((0, 0),), ((0, 0),)))
    assert s5 == target
    return [(c1, s1), (c2, s2), (c3, s3), (c4, s4), (c5, s5)]


def witness_two_term_bypass() -> list[tuple[Change, DState]]:
    """Produce the 6-step sequence reaching 2::0-1*1|0-1*1 requiring 3 terms."""
    s0 = canonical(empty())
    c1 = Change(Kind.ADD_TERM)
    s1 = canonical(perform(s0, c1))
    c2 = Change(Kind.ADD_TERM)
    s2 = canonical(perform(s1, c2))
    c3 = Change(Kind.ADD_TERM)
    s3 = canonical(perform(s2, c3))
    c4 = Change(Kind.ADD_ASSERTION, "r", 2, 1)
    s4 = canonical(perform(s3, c4))
    c5 = Change(Kind.ADD_ASSERTION, "s", 0, 1)
    s5 = canonical(perform(s4, c5))
    c6 = Change(Kind.IDENTIFY, "", 0, 2)
    s6 = canonical(perform(s5, c6))

    target = canonical(DState.of(2, ((0, 1),), ((0, 1),)))
    assert s6 == target
    return [(c1, s1), (c2, s2), (c3, s3), (c4, s4), (c5, s5), (c6, s6)]

