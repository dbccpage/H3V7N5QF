"""Problem 07 (Two-Term Readings) Derivation Model.

Seed edit from Eighteenth seed:
"A reading names at most two terms and records the assertions between them.
Two results are the same if every such reading gives the same record."

This module formalizes:
1. Sub-readings: extraction of all 0-, 1-, and 2-term sub-readings from a state.
2. Record sets: the set of induced assertion records across all choices of <= 2 terms.
3. Local sameness: equivalence relation where s1 ~ s2 iff their record sets agree.
4. Unchosen alternative: multiset of local records (recording multiplicity of subgraphs).
5. Quotient exploration: exploring reachable states under local reading equivalence.
6. Comparison against eighteenth (written equality) and base (FREE canonical rewriting).
7. Smallest colliding pairs (witnesses of coarseness):
   - At n=2: arb and bra have identical local records but are distinct written states.
   - At n=3: non-isomorphic states (e.g. 2 edges vs 4 edges) share identical local records.
8. Step congruence check: demonstrating that the one-step transition system does NOT
   descend to the local reading quotient.
"""

from __future__ import annotations

import sys
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable, Sequence

# Ensure repo code/ directory is on sys.path
ROOT = Path(__file__).resolve().parents[4]
if str(ROOT / "code") not in sys.path:  # pragma: no cover
    sys.path.insert(0, str(ROOT / "code"))

from eighteenth.explore import WrittenExploration, explore_written  # noqa: E402
from eighteenth.writing import same_written  # noqa: E402
from xry.changes import Change, changes, obstruction, perform  # noqa: E402
from xry.explore import Exit, order  # noqa: E402
from xry.state import Sameness, State, canonical, given, rewrite  # noqa: E402

__all__ = [
    "LocalRecord",
    "Record0",
    "Record1",
    "Record2",
    "Subreadings",
    "extract_records",
    "record_set",
    "record_multiset",
    "same_local",
    "same_local_multiset",
    "explore_quotient",
    "find_smallest_written_collision",
    "find_smallest_free_collision",
    "check_step_congruence",
    "QuotientExploration",
    "StepCongruenceFailure",
]

# Record types:
# Record0: (0, ()) representing the unique 0-term reading.
# Record1: (1, loop) where loop is ((0, 0),) if loop is present, else ().
# Record2: (2, pairs) where pairs is a sorted tuple of induced edges among {(0, 1), (1, 0)}.
Pair = tuple[int, int]
Record0 = tuple[int, tuple[()]]
Record1 = tuple[int, tuple[Pair, ...]]
Record2 = tuple[int, tuple[Pair, ...]]
LocalRecord = tuple[int, tuple[Pair, ...]]


def extract_records(state: State) -> list[LocalRecord]:
    """Extract all 0-, 1-, and 2-term sub-readings in order.

    For each choice of at most two terms:
    - 0 terms: choice () -> (0, ())
    - 1 term: choice (u,) -> (1, ((0, 0),)) if loop else (1, ())
    - 2 terms: ordered choice (u, v) with u != v ->
      (2, edges) where edges is the sorted tuple of relations between term 0 (u)
      and term 1 (v).
    """
    records: list[LocalRecord] = []

    # 0 terms: exactly one choice
    records.append((0, ()))

    # 1 term: n choices
    for u in range(state.n):
        loop: tuple[Pair, ...] = ((0, 0),) if state.has(u, u) else ()
        records.append((1, loop))

    # 2 terms: n * (n - 1) ordered choices with u != v
    for u in range(state.n):
        for v in range(state.n):
            if u != v:
                pairs: list[Pair] = []
                if state.has(u, v):
                    pairs.append((0, 1))
                if state.has(v, u):
                    pairs.append((1, 0))
                records.append((2, tuple(pairs)))

    return records


def record_set(state: State) -> frozenset[LocalRecord]:
    """The set of all local reading records (the chosen reading)."""
    return frozenset(extract_records(state))


def record_multiset(state: State) -> tuple[tuple[LocalRecord, int], ...]:
    """The multiset of all local reading records (the unchosen reading)."""
    counts = Counter(extract_records(state))
    return tuple(sorted(counts.items()))


def same_local(left: State, right: State) -> bool:
    """The chosen sameness: two results are the same if every reading gives the same record.

    In the chosen set reading, this corresponds to equality of record sets.
    """
    return record_set(left) == record_set(right)


def same_local_multiset(left: State, right: State) -> bool:
    """The unchosen alternative: two results are the same if multiset of readings agree."""
    return record_multiset(left) == record_multiset(right)


@dataclass(frozen=True)
class StepCongruenceFailure:
    """Witness that step transitions do not descend to equivalence classes.

    Attributes:
        state_a: First state in equivalence class.
        state_b: Second state in equivalence class (same_local(state_a, state_b) is True).
        reachable_classes_a: Equivalence classes reachable in one step from state_a.
        reachable_classes_b: Equivalence classes reachable in one step from state_b.
    """

    state_a: State
    state_b: State
    reachable_classes_a: frozenset[frozenset[LocalRecord]]
    reachable_classes_b: frozenset[frozenset[LocalRecord]]


def check_step_congruence(
    states: Iterable[State],
    max_terms: int = 3,
) -> tuple[bool, list[StepCongruenceFailure]]:
    """Test whether the one-step transition system descends to the local reading quotient.

    For any pair s1 ~ s2 in the same local equivalence class, their sets of
    one-step reachable equivalence classes must coincide.
    """
    by_rec: dict[frozenset[LocalRecord], list[State]] = {}
    for s in states:
        by_rec.setdefault(record_set(s), []).append(s)

    failures: list[StepCongruenceFailure] = []
    for rec, group in by_rec.items():
        if len(group) <= 1:
            continue
        # Map each state in the group to its set of reachable quotient classes
        out_per_state: list[tuple[State, frozenset[frozenset[LocalRecord]]]] = []
        for s in group:
            reachable_recs = set()
            for ch in changes(s):
                if not obstruction(s, ch):
                    out = perform(s, ch)
                    if out.legal and out.n <= max_terms:
                        reachable_recs.add(record_set(out))
            out_per_state.append((s, frozenset(reachable_recs)))

        first_s, first_out = out_per_state[0]
        for other_s, other_out in out_per_state[1:]:
            if first_out != other_out:
                failures.append(
                    StepCongruenceFailure(first_s, other_s, first_out, other_out)
                )

    return (len(failures) == 0, failures)


@dataclass
class QuotientExploration:
    """Results explored under local reading quotient."""

    start: State
    bound: int
    rounds: int
    total_written_states: int
    distinct_quotient_classes: int
    new_classes_per_round: list[int]
    class_members: dict[frozenset[LocalRecord], list[State]]
    canonical_forms_per_class: dict[frozenset[LocalRecord], set[State]]


def explore_quotient(
    start: State,
    bound: int = 3,
    rounds: int = 12,
) -> QuotientExploration:
    """Explore reachable states and compute the quotient partition by local readings."""
    expl = explore_written(start, bound=bound, rounds=rounds)
    class_members: dict[frozenset[LocalRecord], list[State]] = {}
    canonicals_per_class: dict[frozenset[LocalRecord], set[State]] = {}

    for s in sorted(expl.depth, key=order):
        rec = record_set(s)
        class_members.setdefault(rec, []).append(s)
        canonicals_per_class.setdefault(rec, set()).add(canonical(s))

    # Track discovery round of each quotient class
    class_first_round: dict[frozenset[LocalRecord], int] = {}
    for s, rnd in expl.depth.items():
        rec = record_set(s)
        if rec not in class_first_round or rnd < class_first_round[rec]:
            class_first_round[rec] = rnd

    max_round = max(expl.depth.values()) if expl.depth else 0
    new_per_round = [0] * (max_round + 1)
    for rnd in class_first_round.values():
        new_per_round[rnd] += 1

    return QuotientExploration(
        start=start,
        bound=bound,
        rounds=rounds,
        total_written_states=len(expl.depth),
        distinct_quotient_classes=len(class_members),
        new_classes_per_round=new_per_round,
        class_members=class_members,
        canonical_forms_per_class=canonicals_per_class,
    )


def find_smallest_written_collision(
    states: Iterable[State],
) -> tuple[State, State] | None:
    """Find the smallest pair of distinct written states that have identical local records."""
    by_rec: dict[tuple[int, frozenset[LocalRecord]], list[State]] = {}
    for s in states:
        by_rec.setdefault((s.n, record_set(s)), []).append(s)

    for (n, rec), group in sorted(by_rec.items(), key=lambda item: (item[0][0], len(item[1]))):
        for i in range(len(group)):
            for j in range(i + 1, len(group)):
                if not same_written(group[i], group[j]):
                    return (group[i], group[j])
    return None


def find_smallest_free_collision(
    states: Iterable[State],
) -> tuple[State, State] | None:
    """Find the smallest pair of states that have identical local records but different canonical forms."""
    by_rec: dict[tuple[int, frozenset[LocalRecord]], list[State]] = {}
    for s in states:
        by_rec.setdefault((s.n, record_set(s)), []).append(s)

    for (n, rec), group in sorted(by_rec.items(), key=lambda item: (item[0][0], len(item[1]))):
        for i in range(len(group)):
            for j in range(i + 1, len(group)):
                if canonical(group[i]) != canonical(group[j]):
                    return (group[i], group[j])
    return None
