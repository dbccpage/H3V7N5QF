"""Typed Python model for Problem 08 (record-order).

Seed change from sixteenth:
    "Recorded leftovers are kept in the order they arise. Only the most
    recently recorded leftover may be admitted, adding the assertion `xry`
    or the assertion `xsy`; an unadmitted leftover is not an assertion."

Key structural properties:
1. Ordered leftover record: unadmitted leftovers form a chronological sequence (LIFO stack).
2. LIFO admission: only the top/most recent leftover `record[-1]` is admissible into `r` or `s`.
3. Renaming / Sameness: two results are the same iff their terms differ only by a permutation.
   A permutation renames term endpoints in assertions and in the leftover sequence,
   preserving sequence order.
4. Quotient refinement: forgetting sequence order projects to sixteenth's counted record.
   States with identical sixteenth counts can have different sequence orders and distinct
   canonical forms, refining the result quotient and constraining admission paths.
"""

from __future__ import annotations

from collections import defaultdict
from collections.abc import Iterable, Iterator, Sequence
from dataclasses import dataclass
from enum import Enum
import itertools
from math import comb
from typing import Any

from ninth.state import DState
from sixteenth.state import MState, RState, canonical16


class ChangeKind(Enum):
    """The four kinds of change given by the seed."""

    IDENTIFY = "identify"
    REMOVE = "remove"
    ADD_TERM = "add_term"
    ADD_ASSERTION = "add_assertion"


RELATIONS: tuple[str, str] = ("r", "s")


@dataclass(frozen=True)
class Change:
    """A change under the record-order seed.

    `admits` indicates an assertion added by admitting the most recently recorded leftover.
    """

    kind: ChangeKind
    rel: str = ""
    x: int = -1
    y: int = -1
    admits: bool = False

    def __post_init__(self) -> None:
        if self.kind in (ChangeKind.REMOVE, ChangeKind.ADD_ASSERTION) and self.rel not in RELATIONS:
            raise ValueError(f"relation must be 'r' or 's', got {self.rel!r}")
        if self.kind in (ChangeKind.IDENTIFY, ChangeKind.ADD_TERM) and self.rel:
            raise ValueError("identifications and term additions name no relation")
        if self.admits and self.kind is not ChangeKind.ADD_ASSERTION:
            raise ValueError("only an assertion addition can be an admission")

    @property
    def additions(self) -> tuple[int, int]:
        """(terms, assertions) added by this change."""
        if self.kind is ChangeKind.ADD_TERM:
            return (1, 0)
        if self.kind is ChangeKind.ADD_ASSERTION:
            return (0, 1)
        return (0, 0)

    def written(self) -> str:
        """Human-readable representation of this change."""
        if self.kind is ChangeKind.IDENTIFY:
            return f"identify {self.x} and {self.y}"
        if self.kind is ChangeKind.REMOVE:
            return f"remove {self.x}{self.rel}{self.y}"
        if self.kind is ChangeKind.ADD_TERM:
            return "add term"
        if self.admits:
            return f"admit top leftover {self.x}ℓ{self.y} into {self.rel}"
        return f"add {self.x}{self.rel}{self.y}"


@dataclass(frozen=True)
class OrderedState:
    """A state carrying two relations and an ordered sequence of unadmitted leftovers."""

    n: int
    r: tuple[int, ...]
    s: tuple[int, ...]
    record: tuple[tuple[int, int], ...] = ()

    def __post_init__(self) -> None:
        if self.n < 0:
            raise ValueError("term count cannot be negative")
        expected_len = self.n * self.n
        if len(self.r) != expected_len or len(self.s) != expected_len:
            raise ValueError(f"relation vectors must have length n^2 = {expected_len}")
        if any(m < 0 for m in self.r + self.s):
            raise ValueError("assertion multiplicities cannot be negative")
        for x, y in self.record:
            if not (0 <= x < self.n and 0 <= y < self.n):
                raise ValueError(f"leftover ({x}, {y}) out of range for n = {self.n}")

    @property
    def size(self) -> int:
        """The ninth size: terms plus sum of asserted relations (record excluded)."""
        return self.n + sum(self.r) + sum(self.s)

    @property
    def record_len(self) -> int:
        """Number of unadmitted leftovers currently in the stack."""
        return len(self.record)

    @property
    def has_leftover(self) -> bool:
        """True if there is at least one unadmitted leftover."""
        return len(self.record) > 0

    @property
    def top_leftover(self) -> tuple[int, int] | None:
        """The most recently recorded leftover (top of LIFO stack)."""
        return self.record[-1] if self.record else None

    def mult_of(self, rel: str, x: int, y: int) -> int:
        """Multiplicity of assertion x(rel)y."""
        if rel not in RELATIONS:
            raise ValueError(f"invalid relation: {rel}")
        if not (0 <= x < self.n and 0 <= y < self.n):
            return 0
        idx = x * self.n + y
        return self.r[idx] if rel == "r" else self.s[idx]

    def to_sixteenth_counts(self) -> tuple[int, ...]:
        """Project the ordered leftover sequence to a multiset count vector of length n^2."""
        counts = [0] * (self.n * self.n)
        for x, y in self.record:
            counts[x * self.n + y] += 1
        return tuple(counts)

    def to_sixteenth_state(self) -> RState:
        """Project to sixteenth's RState (forgetting order)."""
        dstate = DState(self.n, self.r, self.s)
        mstate = MState(self.n, self.to_sixteenth_counts())
        return RState(dstate, mstate)

    def key(self) -> str:
        """Compact canonical string identifier."""
        r_str = "".join(str(v) for v in self.r)
        s_str = "".join(str(v) for v in self.s)
        rec_str = ".".join(f"{x}-{y}" for x, y in self.record)
        return f"{self.n}#r:{r_str}#s:{s_str}#rec:{rec_str}"

    def written(self) -> str:
        """Notation describing terms, assertions, and ordered leftover sequence."""
        if self.n == 0:
            return "empty state"
        terms = " ".join(f"t{i}" for i in range(self.n))
        r_asserts = [f"{x}r{y}" + (f"({self.r[x*self.n+y]})" if self.r[x*self.n+y] > 1 else "")
                     for x in range(self.n) for y in range(self.n) if self.r[x*self.n+y] > 0]
        s_asserts = [f"{x}s{y}" + (f"({self.s[x*self.n+y]})" if self.s[x*self.n+y] > 1 else "")
                     for x in range(self.n) for y in range(self.n) if self.s[x*self.n+y] > 0]
        rec_parts = [f"{x}ℓ{y}" for x, y in self.record]
        asserts = " ".join(r_asserts + s_asserts) or "no assertions"
        rec = " ".join(rec_parts) if rec_parts else "none"
        return f"terms: [{terms}]; assertions: [{asserts}]; stack (bottom->top): [{rec}]"


def empty_state() -> OrderedState:
    """The initial state: no terms, no assertions, no recorded leftovers."""
    return OrderedState(0, (), (), ())


def make_state(
    n: int,
    r_pairs: Iterable[tuple[int, int]] = (),
    s_pairs: Iterable[tuple[int, int]] = (),
    record: Iterable[tuple[int, int]] = (),
) -> OrderedState:
    """Convenience constructor from lists of pairs."""
    r_vec = [0] * (n * n)
    s_vec = [0] * (n * n)
    for x, y in r_pairs:
        if not (0 <= x < n and 0 <= y < n):
            raise ValueError(f"pair ({x}, {y}) out of bounds for n={n}")
        r_vec[x * n + y] += 1
    for x, y in s_pairs:
        if not (0 <= x < n and 0 <= y < n):
            raise ValueError(f"pair ({x}, {y}) out of bounds for n={n}")
        s_vec[x * n + y] += 1
    rec_tuple = tuple(record)
    for x, y in rec_tuple:
        if not (0 <= x < n and 0 <= y < n):
            raise ValueError(f"leftover ({x}, {y}) out of bounds for n={n}")
    return OrderedState(n, tuple(r_vec), tuple(s_vec), rec_tuple)


def add_term(st: OrderedState) -> OrderedState:
    """Add a new term. Existing relations and record are preserved on terms 0..n-1."""
    n = st.n
    new_n = n + 1
    new_r = [0] * (new_n * new_n)
    new_s = [0] * (new_n * new_n)
    for x in range(n):
        for y in range(n):
            new_r[x * new_n + y] = st.r[x * n + y]
            new_s[x * new_n + y] = st.s[x * n + y]
    return OrderedState(new_n, tuple(new_r), tuple(new_s), st.record)


def add_assertion(st: OrderedState, rel: str, x: int, y: int) -> OrderedState:
    """Directly add assertion x(rel)y. Leftover record is unchanged."""
    if not (0 <= x < st.n and 0 <= y < st.n):
        raise ValueError(f"terms ({x}, {y}) out of bounds for n={st.n}")
    if rel not in RELATIONS:
        raise ValueError(f"invalid relation: {rel}")
    idx = x * st.n + y
    if rel == "r":
        new_r = list(st.r)
        new_r[idx] += 1
        return OrderedState(st.n, tuple(new_r), st.s, st.record)
    else:
        new_s = list(st.s)
        new_s[idx] += 1
        return OrderedState(st.n, st.r, tuple(new_s), st.record)


def remove_assertion(st: OrderedState, rel: str, x: int, y: int) -> OrderedState:
    """Remove assertion x(rel)y and append (x, y) to the leftover record."""
    if not (0 <= x < st.n and 0 <= y < st.n):
        raise ValueError(f"terms ({x}, {y}) out of bounds for n={st.n}")
    if rel not in RELATIONS:
        raise ValueError(f"invalid relation: {rel}")
    idx = x * st.n + y
    if rel == "r":
        if st.r[idx] == 0:
            raise ValueError(f"cannot remove non-asserted pair ({x}, {y}) in r")
        new_r = list(st.r)
        new_r[idx] -= 1
        return OrderedState(st.n, tuple(new_r), st.s, st.record + ((x, y),))
    else:
        if st.s[idx] == 0:
            raise ValueError(f"cannot remove non-asserted pair ({x}, {y}) in s")
        new_s = list(st.s)
        new_s[idx] -= 1
        return OrderedState(st.n, st.r, tuple(new_s), st.record + ((x, y),))


def admit_top(st: OrderedState, rel: str) -> OrderedState:
    """Admit the most recently recorded leftover (top of stack) into `rel`.

    Removes the last leftover from record and adds the assertion into `rel`.
    """
    if not st.record:
        raise ValueError("no leftover available to admit")
    if rel not in RELATIONS:
        raise ValueError(f"invalid relation: {rel}")
    x, y = st.record[-1]
    popped_record = st.record[:-1]
    idx = x * st.n + y
    if rel == "r":
        new_r = list(st.r)
        new_r[idx] += 1
        return OrderedState(st.n, tuple(new_r), st.s, popped_record)
    else:
        new_s = list(st.s)
        new_s[idx] += 1
        return OrderedState(st.n, st.r, tuple(new_s), popped_record)


def identify_terms(st: OrderedState, u: int, v: int) -> OrderedState:
    """Identify terms u and v where 0 <= u < v < n.

    Replaces v by u in assertions and in the leftover record, shifting terms > v down by 1.
    The order of leftovers in the record is preserved.
    """
    if not (0 <= u < v < st.n):
        raise ValueError(f"invalid identification pair: {u}, {v} for n={st.n}")

    def remap(t: int) -> int:
        if t == v:
            return u
        return t - 1 if t > v else t

    new_n = st.n - 1
    new_r = [0] * (new_n * new_n)
    new_s = [0] * (new_n * new_n)
    n = st.n
    for x in range(n):
        for y in range(n):
            nx = remap(x)
            ny = remap(y)
            new_r[nx * new_n + ny] += st.r[x * n + y]
            new_s[nx * new_n + ny] += st.s[x * n + y]

    new_record = tuple((remap(x), remap(y)) for x, y in st.record)
    return OrderedState(new_n, tuple(new_r), tuple(new_s), new_record)


def perform(st: OrderedState, change: Change) -> OrderedState:
    """Apply a change to `st`."""
    if change.kind is ChangeKind.IDENTIFY:
        return identify_terms(st, change.x, change.y)
    if change.kind is ChangeKind.REMOVE:
        return remove_assertion(st, change.rel, change.x, change.y)
    if change.kind is ChangeKind.ADD_TERM:
        return add_term(st)
    if change.admits:
        return admit_top(st, change.rel)
    return add_assertion(st, change.rel, change.x, change.y)


def rewrite(st: OrderedState, p: Sequence[int]) -> OrderedState:
    """Permute term names according to bijection p: range(n) -> range(n).

    p[i] is the new name of term i.
    Assertions and the ordered leftover sequence have their endpoints renamed.
    The leftover sequence order is unchanged.
    """
    n = st.n
    if len(p) != n:
        raise ValueError("permutation length must match n")
    new_r = [0] * (n * n)
    new_s = [0] * (n * n)
    for x in range(n):
        for y in range(n):
            new_r[p[x] * n + p[y]] = st.r[x * n + y]
            new_s[p[x] * n + p[y]] = st.s[x * n + y]
    new_rec = tuple((p[x], p[y]) for x, y in st.record)
    return OrderedState(n, tuple(new_r), tuple(new_s), new_rec)


_CANONICAL_CACHE: dict[OrderedState, OrderedState] = {}


def canonical(st: OrderedState) -> OrderedState:
    """The canonical (least) writing of `st` under all permutations of its terms."""
    if st in _CANONICAL_CACHE:
        return _CANONICAL_CACHE[st]
    if st.n <= 1:
        _CANONICAL_CACHE[st] = st
        return st

    n = st.n
    best: tuple[tuple[int, ...], tuple[int, ...], tuple[tuple[int, int], ...]] | None = None
    best_state: OrderedState | None = None

    for p in itertools.permutations(range(n)):
        cand = rewrite(st, p)
        rep = (cand.r, cand.s, cand.record)
        if best is None or rep < best:
            best = rep
            best_state = cand

    assert best_state is not None
    _CANONICAL_CACHE[st] = best_state
    return best_state


def same(a: OrderedState, b: OrderedState) -> bool:
    """Check if states a and b differ only in how their terms are written."""
    return a.n == b.n and canonical(a) == canonical(b)


def clear_canonical_cache() -> None:
    """Clear the canonicalization cache."""
    _CANONICAL_CACHE.clear()


def changes(st: OrderedState) -> tuple[Change, ...]:
    """Enumerate every legal change on `st`, fewest additions first.

    Order:
    1. Identifications: (0 additions)
    2. Removals: in r, then s (0 additions)
    3. Add term: (1 addition: 1 term)
    4. Direct additions: in r, then s (1 addition: 1 assertion)
    5. Admissions: admit top leftover into r, then s (1 addition: 1 assertion)
    """
    out: list[Change] = []
    n = st.n

    # 1. Identifications
    for x in range(n):
        for y in range(x + 1, n):
            out.append(Change(ChangeKind.IDENTIFY, "", x, y))

    # 2. Removals
    for x in range(n):
        for y in range(n):
            if st.r[x * n + y] > 0:
                out.append(Change(ChangeKind.REMOVE, "r", x, y))
    for x in range(n):
        for y in range(n):
            if st.s[x * n + y] > 0:
                out.append(Change(ChangeKind.REMOVE, "s", x, y))

    # 3. Add term
    out.append(Change(ChangeKind.ADD_TERM))

    # 4. Direct additions
    for x in range(n):
        for y in range(n):
            out.append(Change(ChangeKind.ADD_ASSERTION, "r", x, y, False))
    for x in range(n):
        for y in range(n):
            out.append(Change(ChangeKind.ADD_ASSERTION, "s", x, y, False))

    # 5. Admissions: ONLY the most recently recorded leftover (top of stack)
    if st.record:
        top_x, top_y = st.record[-1]
        out.append(Change(ChangeKind.ADD_ASSERTION, "r", top_x, top_y, True))
        out.append(Change(ChangeKind.ADD_ASSERTION, "s", top_x, top_y, True))

    return tuple(out)


def attempt_counts(st: OrderedState) -> tuple[int, int, int]:
    """Count (total_changes, direct_additions, admissions).

    Total = C(n, 2) + asserted_r + asserted_s + 1 + 2*n^2 + (2 if record else 0).
    """
    n = st.n
    distinct_r = sum(1 for v in st.r if v > 0)
    distinct_s = sum(1 for v in st.s if v > 0)
    adm_count = 2 if st.record else 0
    direct_adds = 1 + 2 * n * n
    total = comb(n, 2) + distinct_r + distinct_s + direct_adds + adm_count
    return total, direct_adds, adm_count


@dataclass
class ExplorationResult:
    """Summary of exploration from empty state."""

    start: OrderedState
    bound: int
    rounds: int
    depth: dict[OrderedState, int]
    new_per_round: list[int]
    attempts_per_round: list[int]
    admissions_per_round: list[int]
    frontier: list[tuple[OrderedState, Change]]


def explore(start: OrderedState, bound: int, rounds: int = 6) -> ExplorationResult:
    """Breadth-first exploration from `start`, bounding term count to `bound`."""
    root = canonical(start)
    depth: dict[OrderedState, int] = {root: 0}
    wave = [root]
    new_per_round = [1]
    attempts_per_round = [0]
    admissions_per_round = [0]
    frontier: list[tuple[OrderedState, Change]] = []
    total_attempts = 0
    total_admissions = 0

    for _ in range(1, rounds + 1):
        found: list[OrderedState] = []
        for st in wave:
            for ch in changes(st):
                total_attempts += 1
                if ch.admits:
                    total_admissions += 1
                out = perform(st, ch)
                if out.n > bound:
                    frontier.append((st, ch))
                else:
                    c_out = canonical(out)
                    if c_out not in depth:
                        depth[c_out] = len(new_per_round)
                        found.append(c_out)
        attempts_per_round.append(total_attempts)
        admissions_per_round.append(total_admissions)
        # Canonical sort for deterministic progression
        wave = sorted(found, key=lambda s: (s.n, s.r, s.s, s.record))
        new_per_round.append(len(wave))

    return ExplorationResult(
        start=root,
        bound=bound,
        rounds=rounds,
        depth=depth,
        new_per_round=new_per_round,
        attempts_per_round=attempts_per_round,
        admissions_per_round=admissions_per_round,
        frontier=frontier,
    )


def compare_quotients(ordered_states: Iterable[OrderedState]) -> dict[str, Any]:
    """Compare the ordered state quotient with sixteenth's quotient.

    Groups ordered canonical states by their sixteenth canonical form.
    Returns:
    - total_ordered: number of distinct ordered canonical states
    - total_sixteenth: number of distinct sixteenth canonical states
    - split_classes: mapping of sixteenth canonical states to the list of distinct
      ordered states that project to them
    - num_split_classes: count of sixteenth states having > 1 ordered preimage
    """
    groups: dict[RState, list[OrderedState]] = defaultdict(list)
    for st in ordered_states:
        c_st = canonical(st)
        sixteenth_equiv = canonical16(c_st.to_sixteenth_state())
        groups[sixteenth_equiv].append(c_st)

    # Filter to split classes
    splits = {k: v for k, v in groups.items() if len(v) > 1}

    return {
        "total_ordered": len(list(ordered_states)),
        "total_sixteenth": len(groups),
        "split_classes": splits,
        "num_split_classes": len(splits),
    }


def find_minimal_quotient_witness() -> tuple[OrderedState, OrderedState]:
    """Return the minimal pair of reachable states demonstrating quotient refinement.

    Both states have:
    - 2 terms
    - 0 assertions
    - 2 recorded leftovers: (0, 0) and (0, 1)
    - State A record: ((0, 0), (0, 1)) -> top is (0, 1)
    - State B record: ((0, 1), (0, 0)) -> top is (0, 0)
    They have identical sixteenth count projection {(0,0):1, (0,1):1},
    identical sixteenth canonical forms, but distinct ordered canonical forms
    and disjoint admissible admission pairs.
    """
    st_a = make_state(2, (), (), record=((0, 0), (0, 1)))
    st_b = make_state(2, (), (), record=((0, 1), (0, 0)))
    return canonical(st_a), canonical(st_b)
