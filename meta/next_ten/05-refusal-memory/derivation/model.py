"""Typed Python model for Problem 05: Refusal Memory.

Parent derivation: seventeenth (code/seventeenth/, lean4/Seventeenth/).

Seed change:
    "A refused change is recorded and changes nothing. Its written form is
    kept with that result; the next attempt at the same written change is
    performed even if it makes some `xrx` asserted."

Key concepts:
- `RefusalState`: carries a base seventeenth `State` and a `frozenset[Change]`
  representing the written forms of refused changes kept with that result.
- Obstruction: M1 (base obstruction: assertions that would become `xrx`) and
  M2 (outcome has `xrx`).
- Answer readings:
  - `replace` (A-replace + memory): First attempt at an obstructed change is
    refused and recorded with the state, changing no terms/assertions. The next
    attempt at that same change triggers the override and is performed even if
    it asserts some `xrx`.
  - `perform` (A-perform): Every change is performed immediately on attempt 1.
- Sameness:
  - ANCHORED: terms `a` and `b` preserved.
  - FREE: all term permutations.
  Two results differing only in term writing are the same result. Canonicalization
  minimizes over valid term permutations acting on both graph and refusal record.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass
from enum import Enum
from itertools import permutations
from pathlib import Path
from typing import Iterable, Sequence

ROOT = Path(__file__).resolve().parents[4]
if str(ROOT / "code") not in sys.path:  # pragma: no cover
    sys.path.insert(0, str(ROOT / "code"))

from seventeenth.loop import has_xrx as seventeenth_has_xrx, obstructed_m1
from xry.changes import Change, Kind, changes, obstruction, perform
from xry.state import (
    GIVEN_ASSERTIONS,
    GIVEN_TERMS,
    Sameness,
    State,
    _rewrite_mask,
    _rewritings,
    canonical as canonical_base,
    given,
    letter,
)


class RecordScope(Enum):
    """How the refusal memory behaves across transitions."""

    LOCAL = "local"  # kept strictly with that result; fresh results begin empty
    CARRIED = "carried"  # carried to successor states if still valid


@dataclass(frozen=True)
class RefusalState:
    """A result carrying a base seventeenth graph state and a refusal record."""

    state: State
    refused: frozenset[Change] = frozenset()

    def __post_init__(self) -> None:
        # Validate that all changes in refused mention valid terms of state
        for c in self.refused:
            if c.x >= self.state.n or c.y >= self.state.n:
                raise ValueError("refused change mentions term not in state")

    @property
    def n(self) -> int:
        return self.state.n

    @property
    def m(self) -> int:
        return self.state.m

    @property
    def has_loop(self) -> bool:
        return bool(self.state.loops)

    def key(self) -> str:
        """Deterministic string key for this refusal state."""
        base_key = self.state.key()
        if not self.refused:
            return base_key
        sorted_refused = sorted(c.written(self.state) for c in self.refused)
        return f"{base_key}|refused:[{'; '.join(sorted_refused)}]"

    def added(self) -> tuple[int, int]:
        """(terms added to given, assertions added to given)."""
        return self.state.n - GIVEN_TERMS, self.state.m - GIVEN_ASSERTIONS


def rewrite_change(c: Change, p: tuple[int, ...]) -> Change:
    """Map a change under term permutation `p`."""
    if c.kind is Kind.ADD_TERM:
        return c
    if c.kind is Kind.IDENTIFY:
        u, v = p[c.x], p[c.y]
        return Change(Kind.IDENTIFY, min(u, v), max(u, v))
    return Change(c.kind, p[c.x], p[c.y])


def rewrite_refusal_state(s: RefusalState, p: tuple[int, ...]) -> RefusalState:
    """Apply permutation `p` to both base state and refusal record."""
    n = s.state.n
    names = None if s.state.names is None else (p[s.state.names[0]], p[s.state.names[1]])
    new_state = State.of(n, ((p[x], p[y]) for x, y in s.state.pairs), names)
    new_refused = frozenset(rewrite_change(c, p) for c in s.refused)
    return RefusalState(new_state, new_refused)


def canonical_refusal(s: RefusalState) -> RefusalState:
    """Canonical representative under the state's sameness convention."""
    n = s.state.n
    best_tuple: tuple[int, int, int, tuple[tuple[str, int, int], ...]] | None = None
    best_state: RefusalState | None = None

    for p, tables in _rewritings(n):
        if s.state.names is not None:
            a = p[s.state.names[0]]
            b = p[s.state.names[1]]
        else:
            a, b = 0, 0
        mask = _rewrite_mask(s.state.mask, tables)
        perm_refused = tuple(
            sorted(
                (c.kind.value, c.x, c.y)
                for c in (rewrite_change(c_orig, p) for c_orig in s.refused)
            )
        )
        cand = (mask, a, b, perm_refused)
        if best_tuple is None or cand < best_tuple:
            best_tuple = cand
            names = (a, b) if s.state.names is not None else None
            rewritten_state = State(n, mask, names)
            rewritten_refused = frozenset(rewrite_change(c, p) for c in s.refused)
            best_state = RefusalState(rewritten_state, rewritten_refused)

    assert best_state is not None
    return best_state


@dataclass(frozen=True)
class StepOutcome:
    """Result of attempting a change on a RefusalState."""

    target: RefusalState
    is_refusal: bool
    is_override: bool
    obstructed: bool


def attempt_step(
    s: RefusalState,
    c: Change,
    *,
    enter_obstructed: bool = False,
    scope: RecordScope = RecordScope.LOCAL,
) -> StepOutcome:
    """Attempt change `c` on refusal state `s`.

    If `enter_obstructed` is True (A-perform reading):
        Every change is performed immediately, ignoring refusal memory.
    If `enter_obstructed` is False (A-replace with memory):
        - If unobstructed: performed normally.
        - If obstructed and `c` not in `s.refused`:
            Refused: state changes nothing, `c` is added to refusal memory.
        - If obstructed and `c` in `s.refused`:
            Override: performed even if it makes some `xrx` asserted.
    """
    blocked = obstructed_m1(s.state, c)

    if enter_obstructed:
        # A-perform: always perform immediately
        out_state = perform(s.state, c)
        return StepOutcome(
            target=canonical_refusal(RefusalState(out_state, frozenset())),
            is_refusal=False,
            is_override=False,
            obstructed=blocked,
        )

    if not blocked:
        # Unobstructed change: perform
        out_state = perform(s.state, c)
        if scope is RecordScope.LOCAL:
            next_refused: frozenset[Change] = frozenset()
        else:
            # Carry valid refused changes
            carried = set()
            for r in s.refused:
                if r.x < out_state.n and r.y < out_state.n:
                    carried.add(r)
            next_refused = frozenset(carried)
        return StepOutcome(
            target=canonical_refusal(RefusalState(out_state, next_refused)),
            is_refusal=False,
            is_override=False,
            obstructed=False,
        )

    # Obstructed change under refusal reading
    if c not in s.refused:
        # First attempt: refused! Changes nothing, kept with this result.
        new_refused = s.refused | {c}
        return StepOutcome(
            target=canonical_refusal(RefusalState(s.state, new_refused)),
            is_refusal=True,
            is_override=False,
            obstructed=True,
        )

    # Repeated attempt: override fires!
    out_state = perform(s.state, c)
    if scope is RecordScope.LOCAL:
        next_refused = frozenset()
    else:
        carried = {r for r in s.refused if r != c and r.x < out_state.n and r.y < out_state.n}
        next_refused = frozenset(carried)
    return StepOutcome(
        target=canonical_refusal(RefusalState(out_state, next_refused)),
        is_refusal=False,
        is_override=True,
        obstructed=True,
    )


@dataclass(frozen=True)
class StepRecord:
    """One logged attempted change."""

    reading: str
    round: int
    state: str
    change: str
    obstructed: bool
    outcome: str
    is_refusal: bool
    is_override: bool


@dataclass
class Closure:
    """States reached by round, exact frontier, and step log."""

    depth: dict[RefusalState, int]
    frontier: tuple[str, ...]
    log: tuple[StepRecord, ...] = ()
    unexpanded: tuple[str, ...] = ()


def closure(
    start_state: State,
    bound: int,
    rounds: int,
    *,
    enter_obstructed: bool = False,
    scope: RecordScope = RecordScope.LOCAL,
    keep_log: bool = False,
) -> Closure:
    """Breadth-first exploration of results.

    Cut when outcome terms exceed `bound` (placed in frontier).
    """
    if rounds < 0 or bound < start_state.n:
        raise ValueError("bound below start or negative rounds")

    root = canonical_refusal(RefusalState(start_state, frozenset()))
    depth: dict[RefusalState, int] = {root: 0}
    wave = [root]
    frontier: list[str] = []
    log: list[StepRecord] = []
    reading = "perform" if enter_obstructed else "replace_memory"

    for round_index in range(1, rounds + 1):
        found: list[RefusalState] = []
        for curr in wave:
            for c in changes(curr.state):
                outcome = attempt_step(curr, c, enter_obstructed=enter_obstructed, scope=scope)
                if outcome.target.n > bound:
                    frontier.append(f"{curr.key()}|{c.written(curr.state)}|terms")
                    continue
                if outcome.target not in depth:
                    depth[outcome.target] = round_index
                    found.append(outcome.target)
                if keep_log:
                    log.append(
                        StepRecord(
                            reading=reading,
                            round=round_index,
                            state=curr.key(),
                            change=c.written(curr.state),
                            obstructed=outcome.obstructed,
                            outcome=outcome.target.key(),
                            is_refusal=outcome.is_refusal,
                            is_override=outcome.is_override,
                        )
                    )
        # Sort found wave deterministically
        wave = sorted(found, key=lambda s: (s.state.n, s.state.m, s.key()))

    unexpanded = tuple(sorted(s.key() for s in wave))
    return Closure(depth, tuple(sorted(set(frontier))), tuple(log), unexpanded)


def independent_census(bound: int, sameness: Sameness) -> set[RefusalState]:
    """Independent enumeration of all canonical refusal states within `bound` terms."""
    if bound < 1:
        raise ValueError("bound must be at least 1")
    out: set[RefusalState] = set()

    for n in range(1, bound + 1):
        total_pairs = [(x, y) for x in range(n) for y in range(n)]
        name_options: tuple[tuple[int, int] | None, ...]
        if sameness is Sameness.ANCHORED:
            name_options = tuple((a, b) for a in range(n) for b in range(n))
        else:
            name_options = (None,)

        for mask in range(1 << (n * n)):
            for names in name_options:
                base = State(n, mask, names)
                # Find all possible obstructed changes on base
                obs_changes = [c for c in changes(base) if obstructed_m1(base, c)]
                # Number of subsets of obstructed changes:
                num_subsets = 1 << len(obs_changes)
                for bits in range(num_subsets):
                    subset = frozenset(
                        obs_changes[i] for i in range(len(obs_changes)) if (bits >> i) & 1
                    )
                    out.add(canonical_refusal(RefusalState(base, subset)))
    return out


def loopfree_census(bound: int, sameness: Sameness) -> set[RefusalState]:
    """Census restricted to base states asserting no `xrx` and empty refusal memory."""
    all_states = independent_census(bound, sameness)
    return {s for s in all_states if not s.has_loop and not s.refused}
