"""Problem 01 (Remove Bare Term) Derivation Model.

Seed diff from Seventh seed:
A change is exactly one of: identifying two terms; removing an assertion;
adding a term; adding an assertion; removing a term that names no assertion.
Nothing else is a change. Identifying two terms replaces both by one term in
every assertion. Removing a term that names no assertion deletes that term
and nothing asserted.

Any outcome is valid.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass, field
from enum import IntEnum
from itertools import permutations
from math import comb, factorial
from pathlib import Path
from typing import Iterable, Iterator

# Ensure repo code/ directory is on sys.path if needed
ROOT = Path(__file__).resolve().parents[4]
if str(ROOT / "code") not in sys.path:
    sys.path.insert(0, str(ROOT / "code"))

__all__ = [
    "AttemptRecord",
    "Change",
    "Exit",
    "Exploration",
    "Kind",
    "State",
    "attempt",
    "attempt_counts",
    "burnside_orbits",
    "canonical_orbits_count",
    "changes",
    "cost",
    "empty",
    "explore",
    "is_bare",
    "perform",
    "reachable",
    "two_step_cycle",
    "two_term_count",
]


class Kind(IntEnum):
    """The five kinds of change in Problem 01."""

    IDENTIFY = 0
    REMOVE = 1  # remove an assertion
    ADD_TERM = 2
    ADD_ASSERTION = 3
    REMOVE_BARE_TERM = 4

    def written(self) -> str:
        """Human-readable name of the kind."""
        if self == Kind.IDENTIFY:
            return "identify two terms"
        if self == Kind.REMOVE:
            return "remove an assertion"
        if self == Kind.ADD_TERM:
            return "add a term"
        if self == Kind.ADD_ASSERTION:
            return "add an assertion"
        return "remove a term that names no assertion"


@dataclass(frozen=True)
class Change:
    """One change of Problem 01.

    x, y are term indices involved in the change.
    - IDENTIFY: x, y with x < y
    - REMOVE: x, y of the asserted pair
    - ADD_TERM: x = -1, y = -1
    - ADD_ASSERTION: x, y of the pair to add
    - REMOVE_BARE_TERM: x is the bare term, y = -1
    """

    kind: Kind
    x: int = -1
    y: int = -1

    def __post_init__(self) -> None:
        if self.kind == Kind.IDENTIFY:
            if not (0 <= self.x < self.y):
                raise ValueError("IDENTIFY requires 0 <= x < y")
        elif self.kind == Kind.REMOVE:
            if self.x < 0 or self.y < 0:
                raise ValueError("REMOVE requires non-negative terms x, y")
        elif self.kind == Kind.ADD_TERM:
            if self.x != -1 or self.y != -1:
                raise ValueError("ADD_TERM takes no terms")
        elif self.kind == Kind.ADD_ASSERTION:
            if self.x < 0 or self.y < 0:
                raise ValueError("ADD_ASSERTION requires non-negative terms x, y")
        elif self.kind == Kind.REMOVE_BARE_TERM:
            if self.x < 0 or self.y != -1:
                raise ValueError("REMOVE_BARE_TERM requires non-negative term x and y == -1")

    @property
    def additions(self) -> tuple[int, int]:
        """How many (terms, assertions) this change adds to what is given."""
        if self.kind == Kind.ADD_TERM:
            return (1, 0)
        if self.kind == Kind.ADD_ASSERTION:
            return (0, 1)
        return (0, 0)

    @property
    def is_addition(self) -> bool:
        """Does this change add a term or an assertion?"""
        return self.kind in (Kind.ADD_TERM, Kind.ADD_ASSERTION)

    def written(self, state: State | None = None) -> str:
        """Text representation of the change."""
        if self.kind == Kind.ADD_TERM:
            return "add a term"
        if self.kind == Kind.IDENTIFY:
            return f"identify {self.x} and {self.y}"
        if self.kind == Kind.REMOVE:
            return f"remove {self.x}r{self.y}"
        if self.kind == Kind.ADD_ASSERTION:
            return f"add {self.x}r{self.y}"
        return f"remove bare term {self.x}"


@dataclass(frozen=True, order=True)
class State:
    """A state without names: n terms and multiplicities for all n*n pairs."""

    n: int
    mult: tuple[int, ...]

    def __post_init__(self) -> None:
        if self.n < 0:
            raise ValueError("number of terms cannot be negative")
        if len(self.mult) != self.n * self.n:
            raise ValueError(f"mult length {len(self.mult)} does not match n*n ({self.n * self.n})")
        if any(k < 0 for k in self.mult):
            raise ValueError("multiplicities cannot be negative")

    @property
    def m(self) -> int:
        """Total multiplicity of all assertions."""
        return sum(self.mult)

    @property
    def size(self) -> int:
        """Size of the state: terms + total multiplicity."""
        return self.n + self.m

    @property
    def distinct(self) -> int:
        """Number of pairs with multiplicity at least 1."""
        return sum(1 for k in self.mult if k > 0)

    def mult_of(self, x: int, y: int) -> int:
        """Multiplicity of assertion xry."""
        if not (0 <= x < self.n and 0 <= y < self.n):
            raise ValueError(f"term out of range: x={x}, y={y}, n={self.n}")
        return self.mult[x * self.n + y]

    def has(self, x: int, y: int) -> bool:
        """Is xry asserted (multiplicity >= 1)?"""
        return self.mult_of(x, y) > 0

    @property
    def pairs(self) -> tuple[tuple[int, int], ...]:
        """All ordered pairs (x, y) with positive multiplicity."""
        return tuple(
            (x, y)
            for x in range(self.n)
            for y in range(self.n)
            if self.has(x, y)
        )

    def is_bare(self, t: int) -> bool:
        """Does term t name no assertion in either position?"""
        if not (0 <= t < self.n):
            raise ValueError(f"term {t} not in 0..{self.n-1}")
        return all(self.mult_of(t, y) == 0 and self.mult_of(y, t) == 0 for y in range(self.n))

    @property
    def bare_terms(self) -> tuple[int, ...]:
        """All terms that name no assertion."""
        return tuple(t for t in range(self.n) if self.is_bare(t))

    def canonical(self) -> State:
        """Least writing of the state under all permutations of 0..n-1."""
        if self.n <= 1:
            return self
        n = self.n
        best = self.mult
        for p in permutations(range(n)):
            cand = [0] * (n * n)
            for x in range(n):
                px = p[x]
                for y in range(n):
                    cand[px * n + p[y]] = self.mult[x * n + y]
            cand_t = tuple(cand)
            if cand_t < best:
                best = cand_t
        if best == self.mult:
            return self
        return State(n, best)


def empty() -> State:
    """The empty beginning: no terms, nothing asserted."""
    return State(0, ())


def is_bare(state: State, t: int) -> bool:
    """Convenience predicate: does term t name no assertion?"""
    return state.is_bare(t)


def changes(state: State) -> tuple[Change, ...]:
    """Every change of Problem 01 on state, fewest additions first.

    Order:
    1. 0 additions:
       - Identifications (ordered pairs 0 <= u < v < n)
       - Assertion removals (each asserted pair)
       - Bare-term removals (each bare term)
    2. 1 addition:
       - Add a term
       - Add an assertion (each pair in range(n) x range(n))
    """
    n = state.n
    c_zero: list[Change] = []

    # 1a. Identifications
    for u in range(n):
        for v in range(u + 1, n):
            c_zero.append(Change(Kind.IDENTIFY, u, v))

    # 1b. Removals of assertions
    for x, y in state.pairs:
        c_zero.append(Change(Kind.REMOVE, x, y))

    # 1c. Removals of bare terms
    for t in state.bare_terms:
        c_zero.append(Change(Kind.REMOVE_BARE_TERM, t))

    c_one: list[Change] = []
    # 2a. Add term
    c_one.append(Change(Kind.ADD_TERM))

    # 2b. Add assertion
    for x in range(n):
        for y in range(n):
            c_one.append(Change(Kind.ADD_ASSERTION, x, y))

    return tuple(c_zero + c_one)


def attempt_counts(state: State) -> tuple[int, int]:
    """How many changes state has, and how many of them are additions.

    Total: C(n, 2) + distinct + bare_count + 1 + n^2.
    Additions: 1 + n^2.
    For empty (n=0): 1 change (add term), 1 addition.
    """
    n = state.n
    bare_count = len(state.bare_terms)
    distinct = state.distinct
    identifications = comb(n, 2)
    additions = 1 + n * n
    total = identifications + distinct + bare_count + additions
    return total, additions


def perform(state: State, change: Change) -> State:
    """The outcome of change on state.

    Any outcome is valid.
    """
    n = state.n
    if change.kind == Kind.ADD_TERM:
        # Add term: n -> n + 1, new pairs have multiplicity 0
        new_n = n + 1
        new_mult = [0] * (new_n * new_n)
        for x in range(n):
            for y in range(n):
                new_mult[x * new_n + y] = state.mult_of(x, y)
        return State(new_n, tuple(new_mult))

    if change.kind == Kind.ADD_ASSERTION:
        new_mult = list(state.mult)
        new_mult[change.x * n + change.y] += 1
        return State(n, tuple(new_mult))

    if change.kind == Kind.REMOVE:
        new_mult = list(state.mult)
        idx = change.x * n + change.y
        if new_mult[idx] <= 0:
            raise ValueError(f"cannot remove non-asserted pair ({change.x}, {change.y})")
        new_mult[idx] -= 1
        return State(n, tuple(new_mult))

    if change.kind == Kind.IDENTIFY:
        u, v = change.x, change.y
        new_n = n - 1
        new_mult = [0] * (new_n * new_n)
        # mapping: u remains u, v becomes u, w > v becomes w - 1
        def map_term(t: int) -> int:
            if t == v:
                return u
            return t if t < v else t - 1

        for x in range(n):
            mx = map_term(x)
            for y in range(n):
                my = map_term(y)
                new_mult[mx * new_n + my] += state.mult_of(x, y)
        return State(new_n, tuple(new_mult))

    if change.kind == Kind.REMOVE_BARE_TERM:
        t = change.x
        if not state.is_bare(t):
            raise ValueError(f"term {t} names an assertion and cannot be removed as bare")
        if n == 1:
            return empty()
        new_n = n - 1
        new_mult = [0] * (new_n * new_n)
        def map_down(k: int) -> int:
            return k if k < t else k - 1

        for x in range(n):
            if x == t:
                continue
            mx = map_down(x)
            for y in range(n):
                if y == t:
                    continue
                my = map_down(y)
                new_mult[mx * new_n + my] = state.mult_of(x, y)
        return State(new_n, tuple(new_mult))

    raise ValueError(f"unknown kind {change.kind}")


@dataclass(frozen=True)
class AttemptRecord:
    """Record of an attempted change."""

    source: State
    change: Change
    outcome: State | None
    beyond: bool
    disposition: str = "valid"


@dataclass(frozen=True)
class Exit:
    """Frontier exit leaving the declared bound on terms."""

    source: State
    change: Change


@dataclass
class Exploration:
    """Full breadth-first exploration record."""

    start: State
    bound: int
    rounds: int
    depth: dict[State, int]
    waves: list[list[State]]
    new_per_round: list[int]
    attempts_per_round: list[int]
    frontier: list[Exit] = field(default_factory=list)
    log: list[AttemptRecord] = field(default_factory=list)

    @property
    def total_discovered(self) -> int:
        return len(self.depth)


def attempt(state: State, change: Change, bound: int) -> AttemptRecord:
    """Attempt change on state and record outcome."""
    out = perform(state, change)
    if out.n > bound:
        return AttemptRecord(source=state, change=change, outcome=None, beyond=True)
    return AttemptRecord(source=state, change=change, outcome=out.canonical(), beyond=False)


def explore(
    start: State | None = None,
    bound: int = 3,
    rounds: int = 10,
    keep_log: bool = False,
) -> Exploration:
    """Breadth-first exploration from start up to bound terms and rounds."""
    root = (start or empty()).canonical()
    if root.n > bound:
        raise ValueError("start has more terms than bound")

    depth: dict[State, int] = {root: 0}
    waves: list[list[State]] = [[root]]
    new_per_round = [1]
    attempts_per_round = [0]
    frontier: list[Exit] = []
    log: list[AttemptRecord] = []

    wave = [root]
    total_attempts = 0

    for r in range(1, rounds + 1):
        found: list[State] = []
        for s in wave:
            for c in changes(s):
                total_attempts += 1
                rec = attempt(s, c, bound)
                if keep_log:
                    log.append(rec)
                if rec.beyond:
                    frontier.append(Exit(s, c))
                elif rec.outcome is not None and rec.outcome not in depth:
                    depth[rec.outcome] = r
                    found.append(rec.outcome)

        found.sort(key=lambda st: (st.n, st.m, st.mult))
        waves.append(found)
        wave = found
        new_per_round.append(len(found))
        attempts_per_round.append(total_attempts)
        if not wave:
            break

    return Exploration(
        start=root,
        bound=bound,
        rounds=rounds,
        depth=depth,
        waves=waves,
        new_per_round=new_per_round,
        attempts_per_round=attempts_per_round,
        frontier=frontier,
        log=log,
    )


def two_step_cycle() -> tuple[State, Change, State, Change, State]:
    """Exhibit the two-step cycle between the empty state and a one-term state.

    empty -> (add term) -> (1 term, 0 assertions) -> (remove bare term 0) -> empty.
    """
    s0 = empty()
    c1 = Change(Kind.ADD_TERM)
    s1 = perform(s0, c1).canonical()
    c2 = Change(Kind.REMOVE_BARE_TERM, 0)
    s2 = perform(s1, c2).canonical()
    return s0, c1, s1, c2, s2


def cost(state: State) -> int:
    """Fewest changes from what is given (empty) to state: exactly its size.

    size = terms + total multiplicity.
    Every change alters size by at most 1 (+1 for additions, -1 for others).
    """
    return state.size


def reachable(s: State, t: State) -> bool:
    """Is t reachable from s by changes of Problem 01?

    Every state can reach empty in s.m + s.n changes (remove all assertions,
    then remove all bare terms).
    The empty state can reach any state t in t.n + t.m changes (add terms, then
    add assertions).
    By transitivity, every state reaches every other state.
    """
    return True


def two_term_count(m: int) -> int:
    """Closed-form count of non-isomorphic states with 2 terms and total multiplicity m."""
    if m < 0:
        raise ValueError("multiplicity cannot be negative")
    fixed = m // 2 + 1 if m % 2 == 0 else 0
    return (comb(m + 3, 3) + fixed) // 2


def canonical_orbits_count(n: int, m: int) -> int:
    """Exact count of canonical states with n terms and total multiplicity m.

    Computed by Burnside's Lemma over the symmetric group S_n acting on directed pairs.
    """
    if n == 0:
        return 1 if m == 0 else 0
    if n == 1:
        return 1  # exactly one loop of multiplicity m
    if n == 2:
        return two_term_count(m)

    # General n using integer partitions of n
    return burnside_orbits(n, m)


def _integer_partitions(n: int) -> list[list[int]]:
    """Generate all integer partitions of n."""
    if n == 0:
        return [[]]
    res: list[list[int]] = []
    def helper(remaining: int, max_val: int, current: list[int]) -> None:
        if remaining == 0:
            res.append(list(current))
            return
        for v in range(min(remaining, max_val), 0, -1):
            current.append(v)
            helper(remaining - v, v, current)
            current.pop()
    helper(n, n, [])
    return res


def _conjugacy_class_size(n: int, part: list[int]) -> int:
    """Size of the conjugacy class in S_n corresponding to cycle partition."""
    counts: dict[int, int] = {}
    for c in part:
        counts[c] = counts.get(c, 0) + 1
    denom = 1
    for k, count in counts.items():
        denom *= (k ** count) * factorial(count)
    return factorial(n) // denom


def _pair_cycle_lengths(part: list[int]) -> list[int]:
    """Cycle lengths induced on the n^2 ordered pairs by a permutation with cycle partition `part`."""
    from math import gcd
    lengths: list[int] = []
    for i, c1 in enumerate(part):
        for j, c2 in enumerate(part):
            g = gcd(c1, c2)
            lcm = (c1 * c2) // g
            # gcd(c1, c2) cycles of length lcm
            lengths.extend([lcm] * g)
    return lengths


def _count_fixed_configurations(cycle_lengths: list[int], m: int) -> int:
    """Count non-negative integer solutions to sum(c * L_c) = m where c is the assignment to each cycle."""
    # Dynamic programming for change-making / coin change
    dp = [0] * (m + 1)
    dp[0] = 1
    for L in cycle_lengths:
        for val in range(L, m + 1):
            dp[val] += dp[val - L]
    return dp[m]


def burnside_orbits(n: int, m: int) -> int:
    """Burnside's lemma orbit count for directed multigraphs with loops."""
    if n == 0:
        return 1 if m == 0 else 0
    total = 0
    order_G = factorial(n)
    for part in _integer_partitions(n):
        cls_size = _conjugacy_class_size(n, part)
        cycle_lens = _pair_cycle_lengths(part)
        fixed_count = _count_fixed_configurations(cycle_lens, m)
        total += cls_size * fixed_count
    return total // order_G
