"""Problem 06 (Written Budget) Derivation Model.

Seed edit from Ninth seed:
"Nothing is given: to begin with there are no terms and nothing is asserted.
Each alternative begins with four changes available; each performed change uses one,
an attempt with none available changes nothing, and every result records how many remain."

This module formalizes:
1. `BudgetedState`: a pair of an underlying two-relation state without names (`DState`)
   and an integer budget in {0, 1, 2, 3, 4}.
2. Step consumption: each performed change uses one budget unit. An attempt with none
   available changes nothing (self-loop / identity).
3. Exploration: breadth-first exploration from (empty, 4) until all paths reach budget 0.
4. Independent census: orbit and parity based census of reachable states at each budget.
5. Comparison against parent Ninth derivation: exact analysis of reachable states at each
   budget vs parent round waves.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass, field
from math import comb
from pathlib import Path
from typing import Iterator

# Ensure repo code/ directory is on sys.path
ROOT = Path(__file__).resolve().parents[4]
if str(ROOT / "code") not in sys.path:  # pragma: no cover
    sys.path.insert(0, str(ROOT / "code"))

from eighth.changes import Change, Kind, perform  # noqa: E402
from ninth.changes import changes as changes9  # noqa: E402
from ninth.orbits import two_term_count  # noqa: E402
from ninth.state import DState, canonical as canonical9, empty as empty9  # noqa: E402

__all__ = [
    "INITIAL_BUDGET",
    "MAX_CHANGES",
    "AttemptRecord",
    "BudgetedState",
    "ExplorationResult",
    "attempt",
    "available_changes",
    "canonical_budgeted",
    "census_by_budget",
    "compare_with_parent",
    "explore",
    "independent_census_counts",
    "initial_state",
    "perform_change",
]

INITIAL_BUDGET: int = 4
MAX_CHANGES: int = 4


@dataclass(frozen=True, order=True)
class BudgetedState:
    """A two-relation state carrying a recorded remaining budget.

    Attributes:
        state: The underlying Ninth `DState` (canonical form).
        budget: Remaining available changes, in {0, 1, ..., 4}.
    """

    state: DState
    budget: int

    def __post_init__(self) -> None:
        if not (0 <= self.budget <= INITIAL_BUDGET):
            raise ValueError(
                f"Budget must be in 0..{INITIAL_BUDGET}, got {self.budget}"
            )
        if self.state.names is not None:
            raise ValueError("A state of this seed carries no names")

    @property
    def n(self) -> int:
        """Number of terms in the state."""
        return self.state.n

    @property
    def m(self) -> int:
        """Total multiplicity of assertions across both relations."""
        return self.state.m

    @property
    def size(self) -> int:
        """Size of the underlying state: terms + assertions."""
        return self.state.n + self.state.m

    def canonical(self) -> BudgetedState:
        """Canonical representation: least writing of state, retaining budget."""
        c_state = canonical9(self.state)
        if c_state == self.state:
            return self
        return BudgetedState(c_state, self.budget)


def canonical_budgeted(state: DState, budget: int) -> BudgetedState:
    """Construct a canonical BudgetedState from raw state and budget."""
    return BudgetedState(canonical9(state), budget)


def initial_state() -> BudgetedState:
    """The beginning: no terms, nothing asserted, four changes available."""
    return BudgetedState(empty9(), INITIAL_BUDGET)


def available_changes(bstate: BudgetedState) -> tuple[Change, ...]:
    """The changes that can be attempted on `bstate`.

    When budget > 0, the changes are those of the underlying Ninth state.
    When budget == 0, attempting any change changes nothing.
    """
    if bstate.budget == 0:
        return ()
    return changes9(bstate.state)


def perform_change(bstate: BudgetedState, change: Change) -> BudgetedState:
    """Perform `change` on `bstate`.

    'Each alternative begins with four changes available; each performed change uses one,
    an attempt with none available changes nothing, and every result records how many remain.'
    """
    if bstate.budget == 0:
        # An attempt with none available changes nothing
        return bstate
    out_state = perform(bstate.state, change)
    return canonical_budgeted(out_state, bstate.budget - 1)


@dataclass(frozen=True)
class AttemptRecord:
    """Record of an attempted change on a budgeted state."""

    source: BudgetedState
    change: Change
    outcome: BudgetedState
    performed: bool
    budget_used: int


def attempt(bstate: BudgetedState, change: Change) -> AttemptRecord:
    """Attempt `change` on `bstate` and return the complete record."""
    if bstate.budget == 0:
        return AttemptRecord(
            source=bstate,
            change=change,
            outcome=bstate,
            performed=False,
            budget_used=0,
        )
    outcome = perform_change(bstate, change)
    return AttemptRecord(
        source=bstate,
        change=change,
        outcome=outcome,
        performed=True,
        budget_used=1,
    )


@dataclass
class ExplorationResult:
    """Complete record of the budgeted state exploration."""

    start: BudgetedState
    depth: dict[BudgetedState, int]
    waves: list[list[BudgetedState]]
    by_budget: dict[int, list[BudgetedState]]
    attempts_count: int
    performed_count: int
    attempts_at_budget_zero: int
    frontier: list[tuple[BudgetedState, Change]] = field(default_factory=list)


def explore(
    start: BudgetedState | None = None,
    term_bound: int = 4,
    max_rounds: int = 100,
) -> ExplorationResult:
    """Explore all reachable budgeted states breadth-first from `start`.

    Rounds proceed until all alternatives are exhausted (budget 0 reached)
    or `max_rounds` is reached.
    """
    root = (start or initial_state()).canonical()
    depth: dict[BudgetedState, int] = {root: 0}
    waves: list[list[BudgetedState]] = [[root]]
    by_budget: dict[int, list[BudgetedState]] = {b: [] for b in range(INITIAL_BUDGET + 1)}
    by_budget[root.budget].append(root)

    attempts_count = 0
    performed_count = 0
    attempts_at_budget_zero = 0
    frontier: list[tuple[BudgetedState, Change]] = []

    wave = [root]
    for r in range(1, max_rounds + 1):
        if not wave:
            break
        next_wave: list[BudgetedState] = []
        for bstate in wave:
            if bstate.budget == 0:
                # Testing attempt when budget is 0
                for c in changes9(bstate.state):
                    attempts_count += 1
                    attempts_at_budget_zero += 1
                    rec = attempt(bstate, c)
                    assert not rec.performed
                    assert rec.outcome == bstate
                continue

            for change in changes9(bstate.state):
                attempts_count += 1
                performed_count += 1
                rec = attempt(bstate, change)
                if rec.outcome.n > term_bound:
                    frontier.append((bstate, change))
                elif rec.outcome not in depth:
                    depth[rec.outcome] = r
                    next_wave.append(rec.outcome)
                    by_budget[rec.outcome.budget].append(rec.outcome)

        next_wave.sort(key=lambda s: (s.budget, s.n, s.state.r, s.state.s))
        if next_wave:
            waves.append(next_wave)
        wave = next_wave

    return ExplorationResult(
        start=root,
        depth=depth,
        waves=waves,
        by_budget=by_budget,
        attempts_count=attempts_count,
        performed_count=performed_count,
        attempts_at_budget_zero=attempts_at_budget_zero,
        frontier=frontier,
    )


def independent_census_counts() -> dict[int, int]:
    """Independent mathematical count of reachable states by remaining budget.

    Derivation from Ninth principles:
    A state s is reachable in k steps from empty (leaving budget b = 4 - k) iff:
      1. s is well-formed
      2. s.size <= k
      3. s.size == k (mod 2)
      4. If k > 0, s.n >= 1 (non-empty)

    Counts by k:
    - k = 0 (budget 4): size 0 -> 1 state (empty)
    - k = 1 (budget 3): size 1 -> 1 state (1-term empty)
    - k = 2 (budget 2): size 2 -> 3 states:
        terms=2, mult=0: 1 state (2-term empty)
        terms=1, mult=1: 2 states (1r0, 1s0)
    - k = 3 (budget 1): sizes {1, 3} -> 1 + 8 = 9 states:
        size 1: 1 state
        size 3:
          terms=3, mult=0: 1 state
          terms=2, mult=1: 4 states (two_term_count(1))
          terms=1, mult=2: 3 states (compositions of 2 into 2 rels)
    - k = 4 (budget 0): sizes {2, 4} -> 3 + 29 = 32 states:
        size 2: 3 states
        size 4:
          terms=4, mult=0: 1 state
          terms=3, mult=1: 4 states (loop/edge in r/s)
          terms=2, mult=2: 20 states (two_term_count(2))
          terms=1, mult=3: 4 states (compositions of 3 into 2 rels)
    """
    census: dict[int, int] = {}

    # Budget 4 (k=0)
    census[4] = 1

    # Budget 3 (k=1)
    census[3] = 1

    # Budget 2 (k=2)
    # size 2 states: n=2 m=0 (1) + n=1 m=1 (2)
    census[2] = 1 + 2

    # Budget 1 (k=3)
    # size 1 states: 1
    # size 3 states: n=3 m=0 (1) + n=2 m=1 (4) + n=1 m=2 (3)
    census[1] = 1 + (1 + 4 + 3)

    # Budget 0 (k=4)
    # size 2 states: 3
    # size 4 states: n=4 m=0 (1) + n=3 m=1 (4) + n=2 m=2 (20) + n=1 m=3 (4)
    census[0] = 3 + (1 + 4 + two_term_count(2) + 4)

    return census


def census_by_budget() -> dict[int, int]:
    """Return the exact mapping of budget to expected number of states."""
    return independent_census_counts()


def compare_with_parent(expl: ExplorationResult) -> dict[str, object]:
    """Compare Problem 06 reachable states with Ninth parent exploration results.

    Key comparison points:
    1. At budget 4 (k=0): 1 state, identical to parent round 0.
    2. At budget 3 (k=1): 1 state, identical to parent round 1.
    3. At budget 2 (k=2): 3 states, identical to parent round 2.
    4. At budget 1 (k=3): 9 states. Parent's BFS discovery wave at round 3 has 8 states
       (all size 3). The 9th state in budget 1 is the 1-term empty state (size 1),
       re-reached via 2 additions followed by 1 identification or removal.
    5. At budget 0 (k=4): 32 states. Parent's BFS discovery wave at round 4 has 29 states
       (all size 4). The 3 additional states in budget 0 are the size 2 states
       (2-term empty, 1-term 0r0, 1-term 0s0), re-reached via cycles/reductions.
    6. At round >= 5: Parent Ninth reaches states of size >= 5 indefinitely.
       Problem 06 reaches NO states (0 new states), as all alternatives terminate
       at budget 0.
    """
    census = independent_census_counts()
    expl_counts = {b: len(states) for b, states in expl.by_budget.items()}

    # Parent Ninth BFS wave sizes:
    parent_bfs_wave_sizes = {
        0: 1,   # size 0
        1: 1,   # size 1
        2: 3,   # size 2
        3: 8,   # size 3
        4: 29,  # size 4
    }

    # Verify matching with independent census
    census_matches = (expl_counts == census)

    # Detect re-visited parent states at smaller sizes
    revisited: dict[int, list[tuple[int, int]]] = {}
    for b, states in expl.by_budget.items():
        k = INITIAL_BUDGET - b
        smaller = [
            (s.n, s.m) for s in states if s.size < k
        ]
        if smaller:
            revisited[b] = smaller

    return {
        "budget_counts": expl_counts,
        "census_counts": census,
        "census_matches": census_matches,
        "parent_bfs_wave_sizes": parent_bfs_wave_sizes,
        "revisited_lower_sizes": revisited,
        "total_budgeted_states": sum(expl_counts.values()),
        "max_steps": MAX_CHANGES,
        "frontier_size": len(expl.frontier),
    }
