"""Problem 10: swap-as-change derivation model.

Seed sentence diff against the ninth seed:
- A change is exactly one of: identifying two terms; removing an assertion;
  adding a term; adding an assertion. Nothing else is a change.
+ A change is exactly one of: identifying two terms; removing an assertion;
  adding a term; adding an assertion; exchanging the relations. Nothing else is a
  change. Identifying two terms replaces both by one term in every assertion.
  Exchanging the relations replaces every `xry` with `xsy` and every `xsy` with
  `xry`, preserving each multiplicity.

This module models:
1. The 5 kinds of change, including SWAP as the 5th kind.
2. Fewest additions first ordering (SWAP adds (0, 0) terms/assertions).
3. The chosen reading: swap is a change if and only if state.r != state.s (changes written state).
   The unchosen reading (allow self-swap) is parameterized via allow_self_swap=True.
4. BFS exploration from empty state up to a declared term bound and rounds.
5. All-pairs shortest path computation and comparison against ninth (without swap).
6. Exact reduction formula: dist_10(S, T) = min(dist_9(S, T), 1 + dist_9(swap(S), T)).
"""

from __future__ import annotations

import enum
import sys
from collections import deque
from pathlib import Path

_HERE = Path(__file__).resolve().parent
_REPO = _HERE.parents[3]
_CODE = _REPO / "code"
if str(_CODE) not in sys.path:
    sys.path.insert(0, str(_CODE))
from collections.abc import Iterable, Iterator, Sequence
from dataclasses import dataclass, field
from math import comb

from eighth.changes import Change as ChangeEighth
from eighth.changes import Kind as KindEighth
from eighth.changes import perform as perform_eighth
from eighth.state import RELATIONS, DState, canonical, same
from ninth.explore import count_shortest_sequences as count_shortest_sequences_ninth
from ninth.explore import explore as explore_ninth
from ninth.state import added, empty, has_term, swap

__all__ = [
    "KINDS",
    "RELATIONS",
    "Attempt",
    "Change",
    "Exit",
    "Exploration",
    "Kind",
    "added",
    "all_canonical_states",
    "all_pairs_shortest_paths",
    "attempt",
    "canonical",
    "changes",
    "compare_with_ninth",
    "count_shortest_sequences",
    "empty",
    "explore",
    "find_cost_reductions",
    "has_term",
    "is_addition",
    "is_change",
    "makes_some_loop",
    "order",
    "perform",
    "same",
    "swap",
    "transition_graph",
    "verify_swap_reduction_formula",
]


class Kind(enum.Enum):
    """The five kinds of change of the tenth seed."""

    IDENTIFY = 1
    REMOVE = 2
    ADD_TERM = 3
    ADD_ASSERTION = 4
    SWAP = 5


KINDS: tuple[Kind, ...] = (
    Kind.IDENTIFY,
    Kind.REMOVE,
    Kind.SWAP,
    Kind.ADD_TERM,
    Kind.ADD_ASSERTION,
)


@dataclass(frozen=True)
class Change:
    """One change of Problem 10.

    `rel` is 'r' or 's' for ADD_ASSERTION and REMOVE; '' otherwise.
    `x`, `y` are the terms involved for IDENTIFY, REMOVE, ADD_ASSERTION; -1 otherwise.
    """

    kind: Kind
    rel: str = ""
    x: int = -1
    y: int = -1

    def __post_init__(self) -> None:
        if self.kind in (Kind.REMOVE, Kind.ADD_ASSERTION) and self.rel not in RELATIONS:
            raise ValueError("an assertion change mentions relation 'r' or 's'")
        if self.kind in (Kind.IDENTIFY, Kind.ADD_TERM, Kind.SWAP) and self.rel:
            raise ValueError("identify, add_term, and swap mention no relation")

    @property
    def additions(self) -> tuple[int, int]:
        """(terms, assertions) added by this change."""
        if self.kind is Kind.ADD_TERM:
            return (1, 0)
        if self.kind is Kind.ADD_ASSERTION:
            return (0, 1)
        return (0, 0)

    def written(self, state: DState) -> str:
        """The change in words."""
        if self.kind is Kind.SWAP:
            return "exchange the relations"
        if self.kind is Kind.ADD_TERM:
            return "add a term"
        w = state.term_writing()
        if self.kind is Kind.IDENTIFY:
            return f"identify {w[self.x]} and {w[self.y]}"
        verb = "remove" if self.kind is Kind.REMOVE else "add"
        return f"{verb} {w[self.x]}{self.rel}{w[self.y]}"


def is_change(change: Change) -> bool:
    """Is `change` one of the five kinds?"""
    return change.kind in KINDS


def is_addition(change: Change) -> bool:
    """Does `change` add a term or an assertion?"""
    return change.kind in (Kind.ADD_TERM, Kind.ADD_ASSERTION)


def changes(state: DState, allow_self_swap: bool = False) -> tuple[Change, ...]:
    """Every change on `state`, fewest additions first.

    Fewest additions first:
    1. 0 additions:
       - Identifications (unordered pairs x < y)
       - Removals (in r then in s, each asserted pair)
       - Exchanging relations (if allow_self_swap or state.r != state.s)
    2. 1 addition:
       - Add a term
       - Add assertion (in r then in s, all ordered pairs)
    """
    n = state.n
    out: list[Change] = []
    # 0 additions:
    for x in range(n):
        for y in range(x + 1, n):
            out.append(Change(Kind.IDENTIFY, "", x, y))
    for rel in RELATIONS:
        for x, y in state.part(rel).pairs:
            out.append(Change(Kind.REMOVE, rel, x, y))
    if allow_self_swap or state.r != state.s:
        out.append(Change(Kind.SWAP))

    # 1 addition:
    out.append(Change(Kind.ADD_TERM))
    for rel in RELATIONS:
        for x in range(n):
            for y in range(n):
                out.append(Change(Kind.ADD_ASSERTION, rel, x, y))
    return tuple(out)


def perform(state: DState, change: Change) -> DState:
    """The outcome of applying `change` to `state`."""
    if change.kind is Kind.SWAP:
        return swap(state)
    if change.kind is Kind.IDENTIFY:
        eighth_change = ChangeEighth(KindEighth.IDENTIFY, "", change.x, change.y)
    elif change.kind is Kind.REMOVE:
        eighth_change = ChangeEighth(KindEighth.REMOVE, change.rel, change.x, change.y)
    elif change.kind is Kind.ADD_TERM:
        eighth_change = ChangeEighth(KindEighth.ADD_TERM, "", -1, -1)
    elif change.kind is Kind.ADD_ASSERTION:
        eighth_change = ChangeEighth(KindEighth.ADD_ASSERTION, change.rel, change.x, change.y)
    else:  # pragma: no cover
        raise ValueError(f"unknown change kind: {change.kind}")
    return perform_eighth(state, eighth_change)


def makes_some_loop(state: DState, change: Change, rel: str) -> bool:
    """Does `change` cause `rel` to transition from loop-free to having a loop?"""
    before = state.legal_r if rel == "r" else state.legal_s
    out = perform(state, change)
    after = out.legal_r if rel == "r" else out.legal_s
    return before and not after


def order(state: DState) -> tuple[int, tuple[int, ...], tuple[int, ...]]:
    """Deterministic ordering of states."""
    return (state.n, state.r, state.s)


@dataclass(frozen=True)
class Attempt:
    """Record of attempting one change."""

    state: DState
    change: Change
    outcome: DState | None
    beyond: bool
    xrx: bool
    xsx: bool


@dataclass(frozen=True)
class Exit:
    """Frontier exit leaving the bound on terms."""

    state: DState
    change: Change


@dataclass
class Exploration:
    """Complete record of BFS exploration from start state."""

    start: DState
    bound: int
    rounds: int
    depth: dict[DState, int]
    new_per_round: list[int]
    attempts_per_round: list[int]
    xrx_per_round: list[int]
    xsx_per_round: list[int]
    frontier: list[Exit] = field(default_factory=list)
    log: list[Attempt] = field(default_factory=list)

    @property
    def last_new_round(self) -> int:
        """Last round that produced a new result within the bound."""
        return max(r for r, new in enumerate(self.new_per_round) if new)

    @property
    def awaiting(self) -> list[DState]:
        """Results of the last round whose changes were not attempted."""
        return sorted((s for s, r in self.depth.items() if r >= self.rounds), key=order)


def attempt(state: DState, change: Change, bound: int) -> Attempt:
    """Attempt `change` on `state` within term bound."""
    out = perform(state, change)
    xrx = makes_some_loop(state, change, "r")
    xsx = makes_some_loop(state, change, "s")
    if out.n > bound:
        return Attempt(state, change, None, True, xrx, xsx)
    return Attempt(state, change, canonical(out), False, xrx, xsx)


def explore(
    start: DState | None = None,
    bound: int = 2,
    rounds: int = 100,
    allow_self_swap: bool = False,
    keep_log: bool = False,
) -> Exploration:
    """Breadth-first exploration from `start` (defaulting to empty())."""
    if start is None:
        start = empty()
    if start.names is not None:
        raise ValueError("state carries no names")
    if start.n > bound:
        raise ValueError("start exceeds bound")
    if bound < 1:
        raise ValueError("bound admits at least one term")
    if rounds < 0:
        raise ValueError("rounds is non-negative")

    root = canonical(start)
    depth: dict[DState, int] = {root: 0}
    wave = [root]
    new_per_round = [1]
    attempts_per_round = [0]
    xrx_per_round = [0]
    xsx_per_round = [0]
    frontier: list[Exit] = []
    log: list[Attempt] = []
    attempts_known = xrx_known = xsx_known = 0

    for r in range(1, rounds + 1):
        found: list[DState] = []
        for st in wave:
            for ch in changes(st, allow_self_swap=allow_self_swap):
                rec = attempt(st, ch, bound)
                attempts_known += 1
                xrx_known += int(rec.xrx)
                xsx_known += int(rec.xsx)
                if rec.beyond:
                    frontier.append(Exit(st, ch))
                elif rec.outcome is not None and rec.outcome not in depth:
                    depth[rec.outcome] = r
                    found.append(rec.outcome)
                if keep_log:
                    log.append(rec)
        attempts_per_round.append(attempts_known)
        xrx_per_round.append(xrx_known)
        xsx_per_round.append(xsx_known)
        wave = sorted(found, key=order)
        new_per_round.append(len(wave))

    return Exploration(
        start=root,
        bound=bound,
        rounds=rounds,
        depth=depth,
        new_per_round=new_per_round,
        attempts_per_round=attempts_per_round,
        xrx_per_round=xrx_per_round,
        xsx_per_round=xsx_per_round,
        frontier=frontier,
        log=log,
    )


def count_shortest_sequences(expl: Exploration) -> dict[DState, int]:
    """How many shortest sequences of changes reach each explored result from the start.

    Since size(t) = n + m is the shortest distance from empty(), any change
    in a shortest sequence from empty() must raise size by 1, so it must be an
    addition. A swap changes size by 0 and thus cannot be part of any shortest
    sequence from empty().
    """
    sequences: dict[DState, int] = {state: 0 for state in expl.depth}
    sequences[expl.start] = 1

    for state in sorted(expl.depth, key=lambda s: (expl.depth[s], order(s))):
        if expl.depth[state] >= expl.rounds:
            continue
        for ch in changes(state):
            out = perform(state, ch)
            if out.n > expl.bound:
                continue
            can_out = canonical(out)
            if can_out in expl.depth and expl.depth[can_out] == expl.depth[state] + 1:
                if is_addition(ch):
                    sequences[can_out] += sequences[state]

    return sequences


def compare_with_ninth(bound: int = 2, rounds: int = 4) -> dict[str, object]:
    """Compare Problem 10 exploration from empty() with Ninth exploration.

    Returns comparison statistics proving:
    1. depth_10 == depth_9 for all reachable states.
    2. new_per_round_10 == new_per_round_9.
    3. shortest sequence counts from empty() are identical.
    4. total attempts are strictly greater in Tenth due to swap attempts.
    """
    expl10 = explore(empty(), bound=bound, rounds=rounds)
    expl9 = explore_ninth(empty(), bound=bound, rounds=rounds)

    depth_match = (expl10.depth == expl9.depth)
    new_match = (expl10.new_per_round == expl9.new_per_round)

    seq10 = count_shortest_sequences(expl10)
    seq9 = count_shortest_sequences_ninth(expl9)
    seq_match = (seq10 == seq9)

    return {
        "bound": bound,
        "rounds": rounds,
        "states_count": len(expl10.depth),
        "depth_identical": depth_match,
        "new_per_round_identical": new_match,
        "sequence_counts_identical": seq_match,
        "attempts_ninth": expl9.attempts_per_round[-1],
        "attempts_tenth": expl10.attempts_per_round[-1],
        "extra_swap_attempts": expl10.attempts_per_round[-1] - expl9.attempts_per_round[-1],
    }


def all_canonical_states(bound: int = 2, max_m: int = 2) -> list[DState]:
    """Generate all canonical states with at most `bound` terms and at most `max_m` assertions."""
    expl = explore(empty(), bound=bound, rounds=bound + max_m)
    return sorted(
        [s for s in expl.depth if s.m <= max_m],
        key=lambda s: (s.n, s.m, order(s)),
    )


def transition_graph(
    states: Iterable[DState],
    include_swap: bool = True,
    allow_self_swap: bool = False,
) -> dict[DState, list[tuple[Change, DState]]]:
    """Construct transition adjacency list over canonical states."""
    state_set = set(states)
    graph: dict[DState, list[tuple[Change, DState]]] = {s: [] for s in state_set}
    for s in state_set:
        for ch in changes(s, allow_self_swap=allow_self_swap):
            if not include_swap and ch.kind is Kind.SWAP:
                continue
            out = canonical(perform(s, ch))
            if out in state_set:
                graph[s].append((ch, out))
    return graph


def all_pairs_shortest_paths(
    states: Sequence[DState],
    include_swap: bool = True,
    allow_self_swap: bool = False,
) -> dict[tuple[DState, DState], int]:
    """Compute all-pairs shortest paths on the transition graph induced by `states`."""
    graph = transition_graph(states, include_swap=include_swap, allow_self_swap=allow_self_swap)
    dist: dict[tuple[DState, DState], int] = {}

    for src in states:
        visited: dict[DState, int] = {src: 0}
        q: deque[DState] = deque([src])
        while q:
            curr = q.popleft()
            d = visited[curr]
            for _, nxt in graph[curr]:
                if nxt not in visited:
                    visited[nxt] = d + 1
                    q.append(nxt)
        for tgt in states:
            if tgt in visited:
                dist[(src, tgt)] = visited[tgt]

    return dist


def find_cost_reductions(
    states: Sequence[DState],
) -> list[tuple[DState, DState, int, int]]:
    """Find pairs (s, t) where shortest path with swap is strictly shorter than ninth.

    Returns: list of (s, t, cost_ninth, cost_tenth).
    """
    dist_9 = all_pairs_shortest_paths(states, include_swap=False)
    dist_10 = all_pairs_shortest_paths(states, include_swap=True)

    reductions: list[tuple[DState, DState, int, int]] = []
    for pair_st, d10 in dist_10.items():
        s, t = pair_st
        d9 = dist_9.get(pair_st)
        if d9 is not None and d10 < d9:
            reductions.append((s, t, d9, d10))
    return reductions


def verify_swap_reduction_formula(states: Sequence[DState]) -> bool:
    """Verify that dist_10(S, T) == min(dist_9(S, T), 1 + dist_9(swap(S), T)) for all connected pairs."""
    dist_9 = all_pairs_shortest_paths(states, include_swap=False)
    dist_10 = all_pairs_shortest_paths(states, include_swap=True)

    for (s, t), d10 in dist_10.items():
        can_swap_s = canonical(swap(s))
        d9_direct = dist_9.get((s, t))
        d9_swapped = dist_9.get((can_swap_s, t))

        candidates: list[int] = []
        if d9_direct is not None:
            candidates.append(d9_direct)
        if d9_swapped is not None and s.r != s.s:
            candidates.append(1 + d9_swapped)

        if not candidates:  # pragma: no cover
            continue
        expected = min(candidates)
        if d10 != expected:  # pragma: no cover
            return False
    return True
