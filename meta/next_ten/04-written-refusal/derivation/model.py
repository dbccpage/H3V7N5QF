"""Problem 04 (Written Refusal) Derivation Model.

Seed change from Twentyfirst seed:
"Two results that differ only in how their terms are written are different results."
(Replaces: "Two results that differ only in how their terms are written are the same result.")

Parent derivation: twentyfirst (refusal semantics: an obstructed change is refused and changes nothing).
Written comparison: eighteenth (literal written identity: different writings are different results).

This module provides:
1. Literal written state representation and equality (`same_written`).
2. Orbit computation, stabilizer calculation, and the orbit-stabilizer theorem check.
3. Refusal handling (`refused`, `refusal_result`): obstructed changes assert loops, are refused,
   and change nothing.
4. Breadth-first exploration (`explore_written_refusal`) with exact round wave tracking,
   frontier logging, and refusal accounting.
5. Independent census of written states by term count and orbit partition.
6. Differential comparisons against Eighteenth (written unobstructed closure) and
   Twentyfirst (canonical quotient closure).
"""

from __future__ import annotations

import sys
from dataclasses import dataclass, field
from itertools import permutations
from math import factorial
from pathlib import Path

# Ensure repo code/ directory is on sys.path
ROOT = Path(__file__).resolve().parents[4]
if str(ROOT / "code") not in sys.path:
    sys.path.insert(0, str(ROOT / "code"))

from xry.changes import Change, changes, perform  # noqa: E402
from xry.explore import Exit, order  # noqa: E402
from xry.state import Sameness, State, canonical, given, rewrite  # noqa: E402


def same_written(left: State, right: State) -> bool:
    """Two results are the same written result iff they have the same terms, assertions, and names."""
    return left == right


def orbit(state: State) -> frozenset[State]:
    """Every writing of `state` obtained by permuting its terms."""
    return frozenset(rewrite(state, perm) for perm in permutations(range(state.n)))


def orbit_size(state: State) -> int:
    """Number of distinct writings produced by permutations of the terms."""
    return len(orbit(state))


def aut_size(state: State) -> int:
    """Number of permutations of the terms that leave `state` identically as written."""
    return sum(1 for perm in permutations(range(state.n)) if rewrite(state, perm) == state)


def orbit_splits_factorial(state: State) -> bool:
    """Orbit-Stabilizer Theorem: n! == |orbit(state)| * |Aut(state)|."""
    return factorial(state.n) == orbit_size(state) * aut_size(state)


def to_quotient(state: State) -> State:
    """Project a literal written state into its canonical quotient class under term renaming."""
    return canonical(state)


def refusal_result(state: State) -> State:
    """A refused change is recorded and changes nothing (outcome is the state itself)."""
    return state


def refused(outcome: State) -> bool:
    """The outcome asserts some `xrx`, so the change is obstructed and refused."""
    return not outcome.legal


@dataclass(frozen=True)
class AttemptRecord:
    """One attempted change on a written state and its disposition."""

    state: State
    change: Change
    obstructed: bool
    outcome: State
    beyond_bound: bool


@dataclass
class WrittenRefusalExploration:
    """Reachable written states under refusal, and exploration metadata."""

    start: State
    bound: int
    rounds: int
    depth: dict[State, int]
    new_per_round: list[int]
    refusals_per_round: list[int]
    total_refusals: int
    frontier: list[Exit]
    log: list[AttemptRecord] = field(default_factory=list)


def explore_written_refusal(
    start: State, bound: int = 3, rounds: int = 12, keep_log: bool = False
) -> WrittenRefusalExploration:
    """Breadth-first exploration where obstructed changes are refused and literal writings are kept distinct."""
    if not start.legal:
        raise ValueError("what is given asserts no xrx")
    if start.n > bound:
        raise ValueError("the bound is below what is given")

    depth: dict[State, int] = {start: 0}
    wave: list[State] = [start]
    new_per_round: list[int] = [1]
    refusals_per_round: list[int] = [0]
    total_refusals: int = 0
    frontier: list[Exit] = []
    log: list[AttemptRecord] = []

    for _rnd in range(1, rounds + 1):
        found: list[State] = []
        round_refusals = 0
        for state in wave:
            for change in changes(state):
                out = perform(state, change)
                is_refused = refused(out)
                if is_refused:
                    round_refusals += 1
                    total_refusals += 1
                    actual_outcome = refusal_result(state)
                else:
                    actual_outcome = out

                beyond = False
                if actual_outcome.n > bound:
                    beyond = True
                    frontier.append(Exit(state, change, "the change"))
                elif actual_outcome not in depth:
                    depth[actual_outcome] = _rnd
                    found.append(actual_outcome)

                if keep_log:
                    log.append(
                        AttemptRecord(
                            state=state,
                            change=change,
                            obstructed=is_refused,
                            outcome=actual_outcome,
                            beyond_bound=beyond,
                        )
                    )

        wave = sorted(found, key=order)
        new_per_round.append(len(wave))
        refusals_per_round.append(round_refusals)
        if not wave:
            # Continue recording 0s to reach declared rounds
            pass

    return WrittenRefusalExploration(
        start=start,
        bound=bound,
        rounds=rounds,
        depth=depth,
        new_per_round=new_per_round,
        refusals_per_round=refusals_per_round,
        total_refusals=total_refusals,
        frontier=frontier,
        log=log,
    )


def independent_written_census(bound: int, sameness: Sameness) -> dict[int, int]:
    """Independent formula for the number of legal written states on n terms for 1 <= n <= bound.

    For FREE states:
      On n terms, there are n*(n-1) possible directed edges between distinct vertices.
      Each edge is independently present or absent, so there are 2^(n*(n-1)) legal written states.

    For ANCHORED states:
      Names (a, b) can be (0, 1) [distinct names] or (0, 0) [merged names].
      For n=1: only (0, 0) is valid -> 1 * 2^0 = 1 state.
      For n>=2: both (0, 1) and (0, 0) are valid -> 2 * 2^(n*(n-1)) states.
    """
    census: dict[int, int] = {}
    for n in range(1, bound + 1):
        num_relations = 1 << (n * (n - 1))
        if sameness is Sameness.FREE:
            census[n] = num_relations
        else:
            name_variants = 1 if n == 1 else 2
            census[n] = name_variants * num_relations
    return census


def total_census_count(bound: int, sameness: Sameness) -> int:
    """Total legal written states on at most `bound` terms."""
    return sum(independent_written_census(bound, sameness).values())


def verify_census(expl: WrittenRefusalExploration, sameness: Sameness) -> bool:
    """Verify that the reachable states match the census per term count."""
    expected = independent_written_census(expl.bound, sameness)
    actual: dict[int, int] = {}
    for state in expl.depth:
        actual[state.n] = actual.get(state.n, 0) + 1
    return actual == expected


def compare_with_eighteenth(
    bra: bool, sameness: Sameness, bound: int = 3, rounds: int = 12
) -> dict[str, object]:
    """Differential verification against Eighteenth's explore_written.

    Verifies whether the written refusal closure is identically Eighteenth's closure.
    """
    from eighteenth.explore import explore_written

    start = given(bra, sameness)
    written_refusal = explore_written_refusal(start, bound, rounds)
    eighteenth_expl = explore_written(start, bound, rounds)

    depth_matches = written_refusal.depth == eighteenth_expl.depth
    waves_match = written_refusal.new_per_round == eighteenth_expl.new_per_round
    frontier_matches = len(written_refusal.frontier) == len(eighteenth_expl.frontier)

    disagreements = [
        s.key()
        for s in (written_refusal.depth.keys() ^ eighteenth_expl.depth.keys())
    ]
    round_mismatches = [
        s.key()
        for s in written_refusal.depth
        if s in eighteenth_expl.depth and written_refusal.depth[s] != eighteenth_expl.depth[s]
    ]

    return {
        "depth_matches": depth_matches,
        "waves_match": waves_match,
        "frontier_matches": frontier_matches,
        "refusal_results_count": len(written_refusal.depth),
        "eighteenth_results_count": len(eighteenth_expl.depth),
        "disagreements": disagreements,
        "round_mismatches": round_mismatches,
        "total_refusals": written_refusal.total_refusals,
    }


def compare_with_twentyfirst(
    bra: bool, sameness: Sameness, bound: int = 3, rounds: int = 12
) -> dict[str, object]:
    """Differential comparison against Twentyfirst's explore_refusing.

    Verifies that the canonical projection of the written refusal closure
    equals Twentyfirst's quotient closure, and computes the splitting fiber statistics.
    """
    from twentyfirst.refusal import explore_refusing

    start = given(bra, sameness)
    written_refusal = explore_written_refusal(start, bound, rounds)
    twentyfirst_expl = explore_refusing(start, bound, rounds)

    # Group written states by canonical quotient class
    quotient_groups: dict[State, list[State]] = {}
    for state in written_refusal.depth:
        c = to_quotient(state)
        quotient_groups.setdefault(c, []).append(state)

    projected_set = set(quotient_groups.keys())
    twentyfirst_set = set(twentyfirst_expl.depth.keys())
    quotient_matches = projected_set == twentyfirst_set

    # Fibers with more than one written representative demonstrate splitting
    splitting_fibers = {c: len(states) for c, states in quotient_groups.items() if len(states) > 1}

    return {
        "quotient_matches": quotient_matches,
        "written_count": len(written_refusal.depth),
        "quotient_classes_count": len(projected_set),
        "twentyfirst_count": len(twentyfirst_set),
        "splitting_classes_count": len(splitting_fibers),
        "max_fiber_size": max(len(states) for states in quotient_groups.values()),
    }
