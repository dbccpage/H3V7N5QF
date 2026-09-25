"""Typed Python model for Problem 03: given first change adding a term.

Seed:
    "Given: one change adding a term has been made, and its outcome is the
    beginning. Nothing else is given."

Under the parent derivation (ninth), the initial state is empty (0 terms, 0 assertions).
The only legal change from the empty state is adding a term.
In this derivation, that first change has already occurred before round zero.
The beginning state has exactly 1 term and 0 assertions.
"""

from __future__ import annotations

import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any

# Ensure repository code/ is accessible for imports
_REPO_ROOT = Path(__file__).resolve().parents[4]
_CODE_DIR = _REPO_ROOT / "code"
if str(_CODE_DIR) not in sys.path:  # pragma: no cover
    sys.path.insert(0, str(_CODE_DIR))

from eighth.changes import Change, Kind, changes, is_change, makes_some_loop, perform
from ninth.changes import attempt_counts as ninth_attempt_counts
from ninth.changes import is_addition
from ninth.explore import Attempt, Exit, Exploration, count_shortest_sequences, order, performed, sequences_exact
from ninth.orbits import count_results, layer_counts as ninth_layer_counts
from ninth.state import DState, canonical, empty, has_term, same, written

__all__ = [
    "GIVEN_ASSERTIONS",
    "GIVEN_SIZE",
    "GIVEN_TERMS",
    "ComparisonResult",
    "added",
    "attempt_counts",
    "beginning",
    "compare_with_ninth",
    "cost",
    "cost_ninth",
    "cost_shift",
    "counts_within",
    "explore",
    "is_beginning",
    "layer_counts",
    "mutual",
    "order",
    "reachable",
    "reachable_from_beginning",
    "verify_exploration_completeness",
]

#: The seed gives 1 term and 0 assertions as the outcome of the given first change.
GIVEN_TERMS: int = 1
GIVEN_ASSERTIONS: int = 0
GIVEN_SIZE: int = 1


def beginning() -> DState:
    """The beginning state: one term, 0 assertions in both relations, no names."""
    return DState(1, (0,), (0,), None)


def is_beginning(state: DState) -> bool:
    """Check if state is isomorphic to the beginning state."""
    return state.names is None and state.n == 1 and state.m == 0


def added(state: DState) -> tuple[int, int]:
    """How many terms and assertions (both relations, with multiplicity) state adds to what is given.

    Given: 1 term and 0 assertions.
    A state with n terms (n >= 1) and m assertions adds (n - 1) terms and m assertions.
    """
    if state.names is not None:
        raise ValueError("a state carries no names")
    if state.n < GIVEN_TERMS:
        raise ValueError("state has fewer terms than given beginning")
    return state.n - GIVEN_TERMS, state.m - GIVEN_ASSERTIONS


def attempt_counts(state: DState) -> tuple[int, int, int, int]:
    """How many changes state has; how many additions; how many make some xrx, some xsx asserted.

    Delegates to ninth's attempt_counts since the four change rules are unchanged.
    """
    return ninth_attempt_counts(state)


def cost(state: DState) -> int | None:
    """Fewest changes from the beginning to state: size(state) - GIVEN_SIZE.

    Returns None if state is unreachable (e.g. empty state with 0 terms).
    """
    if state.names is not None:
        raise ValueError("a state carries no names")
    if not has_term(state):
        # Empty state is never reachable from a state with a term
        return None
    return state.size - GIVEN_SIZE


def cost_ninth(state: DState) -> int:
    """Fewest changes from ninth's empty root to state: its size."""
    if state.names is not None:
        raise ValueError("a state carries no names")
    return state.size


def cost_shift(state: DState) -> int | None:
    """The shift in cost between Problem 03 and Ninth: cost_03(state) - cost_ninth(state).

    For every reachable state (n >= 1), this is exactly -1.
    For the empty state, this is None (unreachable).
    """
    c = cost(state)
    if c is None:
        return None
    return c - cost_ninth(state)


def reachable(s: DState, t: DState) -> bool:
    """Is t reachable from s by changes of the seed?

    Every change on a state with a term preserves having at least one term.
    From a state with a term, t is reachable if and only if t has at least one term.
    """
    if s.names is not None or t.names is not None:
        raise ValueError("a state carries no names")
    return (not has_term(s)) or has_term(t)


def reachable_from_beginning(t: DState) -> bool:
    """Is t reachable from the beginning state? Exactly when t has at least one term."""
    return reachable(beginning(), t)


def mutual(s: DState, t: DState) -> bool:
    """Do s and t reach each other? For states with terms, reachability is mutual."""
    return reachable(s, t) and reachable(t, s)


def explore(
    bound: int = 3,
    rounds: int = 6,
    keep_log: bool = False,
    start: DState | None = None,
) -> Exploration:
    """Explore from start (default: beginning()) for rounds rounds, keeping states with at most bound terms.

    Round r attempts every change on every result first reached in round r - 1.
    """
    if start is None:
        start = beginning()
    if start.names is not None:
        raise ValueError("a state carries no names")
    if start.n > bound:
        raise ValueError("the bound is below the start")
    if bound < 1:
        raise ValueError("the bound admits at least one term")
    if rounds < 0:
        raise ValueError("the number of rounds is not negative")

    root = canonical(start)
    depth = {root: 0}
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
        for state in wave:
            for change in changes(state):
                out = perform(state, change)
                xrx = makes_some_loop(state, change, "r")
                xsx = makes_some_loop(state, change, "s")
                attempts_known += 1
                xrx_known += int(xrx)
                xsx_known += int(xsx)
                if out.n > bound:
                    frontier.append(Exit(state, change))
                    if keep_log:
                        log.append(Attempt(state, change, None, True, xrx, xsx))
                else:
                    can_out = canonical(out)
                    if can_out not in depth:
                        depth[can_out] = r
                        found.append(can_out)
                    if keep_log:
                        log.append(Attempt(state, change, can_out, False, xrx, xsx))
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


def layer_counts(upto: int) -> list[int]:
    """Number of results at each round 0..upto from beginning() without term bound.

    Since size(beginning()) == 1, a result reached in round r has size r + 1.
    All states of size r + 1 have n >= 1, so they are all reachable from beginning().
    Therefore layer_counts(upto)[r] == ninth_layer_counts(upto + 1)[r + 1].
    """
    ninth_layers = ninth_layer_counts(upto + 1)
    return [ninth_layers[r + 1] for r in range(upto + 1)]


def counts_within(bound: int, rounds: int) -> dict[str, int]:
    """Expected results by 'terms/total' within bound terms and rounds rounds from beginning().

    A state with n terms and total t has cost (n + t) - 1.
    It is within rounds rounds if (n + t) - 1 <= rounds, i.e., t <= rounds + 1 - n.
    Here n ranges from 1 to min(bound, rounds + 1). (n=0 is never reached).
    """
    out: dict[str, int] = {}
    for n in range(1, min(bound, rounds + 1) + 1):
        deg = rounds + 1 - n
        counts = count_results(n, deg)
        for t, c in enumerate(counts):
            out[f"{n}/{t}"] = c
    return out


def verify_exploration_completeness(expl: Exploration) -> dict[str, Any]:
    """Verify that exploration from beginning() matches the independent orbit census."""
    actual_counts: Counter[str] = Counter()
    for s in expl.depth:
        actual_counts[f"{s.n}/{s.m}"] += 1

    expected_counts = counts_within(expl.bound, expl.rounds)
    disagreements = {}
    all_keys = set(actual_counts.keys()) | set(expected_counts.keys())
    for k in sorted(all_keys):
        act = actual_counts.get(k, 0)
        exp = expected_counts.get(k, 0)
        if act != exp:
            disagreements[k] = {"actual": act, "expected": exp}

    # Verify no empty state was explored
    empty_explored = any(s.n == 0 for s in expl.depth)

    return {
        "complete": len(disagreements) == 0 and not empty_explored,
        "total_explored": len(expl.depth),
        "total_expected": sum(expected_counts.values()),
        "empty_explored": empty_explored,
        "disagreements": disagreements,
    }


@dataclass(frozen=True)
class ComparisonResult:
    """Comparison between Problem 03 derivation and parent Ninth derivation."""

    root_03: DState
    root_ninth: DState
    empty_reachable_in_03: bool
    empty_reachable_in_ninth: bool
    round_03_of_one_term: int
    round_ninth_of_one_term: int
    round_03_new_per_round: list[int]
    round_ninth_new_per_round: list[int]
    cost_shifts: dict[str, int | None]
    falsifier_holds: bool
    hypothesis_supported: bool


def compare_with_ninth(bound: int = 3, rounds: int = 6) -> ComparisonResult:
    """Compare exploration from beginning() with exploration from Ninth's empty root."""
    from ninth.explore import explore as explore_ninth

    expl_03 = explore(bound=bound, rounds=rounds)
    expl_ninth = explore_ninth(start=empty(), bound=bound, rounds=rounds)

    one_term_state = canonical(beginning())
    empty_state = empty()

    empty_in_03 = empty_state in expl_03.depth
    empty_in_ninth = empty_state in expl_ninth.depth

    round_03_one_term = expl_03.depth[one_term_state]
    round_ninth_one_term = expl_ninth.depth[one_term_state]

    # Cost shifts on sampled states
    sample_shifts: dict[str, int | None] = {}
    sample_shifts["empty"] = cost_shift(empty_state)
    sample_shifts["one_term"] = cost_shift(one_term_state)

    for s in sorted(expl_03.depth.keys(), key=order)[:10]:
        sample_shifts[f"n={s.n},m={s.m}"] = cost_shift(s)

    # Falsifier: "The empty result and one-term result have the ninth's rounds after aligning beginnings."
    # In Ninth: empty is round 0, one-term is round 1.
    # In 03: one-term is round 0, empty is unreachable (not present).
    # If beginnings are aligned (round 0), in Ninth one-term is at round 1, whereas in 03 it is at round 0.
    # Furthermore empty is not in any round.
    falsifier_holds = (empty_in_03 and expl_03.depth.get(empty_state) == 0 and round_03_one_term == 1)

    hypothesis_supported = (not empty_in_03) and (round_03_one_term == 0) and (not falsifier_holds)

    return ComparisonResult(
        root_03=expl_03.start,
        root_ninth=expl_ninth.start,
        empty_reachable_in_03=empty_in_03,
        empty_reachable_in_ninth=empty_in_ninth,
        round_03_of_one_term=round_03_one_term,
        round_ninth_of_one_term=round_ninth_one_term,
        round_03_new_per_round=expl_03.new_per_round,
        round_ninth_new_per_round=expl_ninth.new_per_round,
        cost_shifts=sample_shifts,
        falsifier_holds=falsifier_holds,
        hypothesis_supported=hypothesis_supported,
    )
