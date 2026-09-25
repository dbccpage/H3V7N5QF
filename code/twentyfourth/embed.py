"""The twenty-third seed mapped in, the two maps back, and the twenty-third's record question.

Derived (paper, D9–D11; `lean4_core/Twentyfourth/Map.lean`)
    * The twenty-third's results map one to one into this seed's results: a
      twenty-third state is read as a state with no term filled (`of_state`),
      two such are one result here exactly when they are one result there, and
      each of the twenty-third's changes is a change here of the same kind (an
      identification of two unfilled terms fills nothing).  So no two
      twenty-third results become one: the merge loses nothing.
    * The map back (`read_back`): a result with no filled term goes to its
      twenty-third result, any other to "none".  It returns the original on
      every mapped result; the smallest result answered "none" is one term,
      filled, nothing asserted, at cost 2, and it is the only one at that cost
      (`smallest_none`).
    * The forgetting map (`forget_key`): every result to the twenty-third
      result of its states; it answers every result, returns the original on
      mapped results, carries each change to a change of the same kind or,
      for a filling, to no change; it loses the filled terms and with them
      the record of which balance.
    * The twenty-third's record (terms, assertions in `r` and in `s`) records
      no assertion exactly for the result asserting nothing, but does not show
      which terms keep a result from being it: results with one record are
      kept by one term, by two, or only by three (`record_question`).

Cited from the twenty-third derivation (`twentythird.explore`) and re-checked
(computed again)
    Its grouped exploration is run at the same bounds: its results must be
    this seed's results with no filled term, at the same rounds, with the same
    numbers of shortest sequences (`compare_with_twentythird`).
"""

from __future__ import annotations

from dataclasses import dataclass

from twentythird.explore import Grouped as Grouped23
from twentythird.explore import explore as explore23
from twentythird.explore import shortest_sequences as shortest23
from twentythird.state import Key

from twentyfourth.cost import record23
from twentyfourth.explore import Grouped, shortest_sequences
from twentyfourth.state import DState, Key24, keeping_size, keeping_terms, of_state, result_key

__all__ = [
    "Comparison",
    "RecordQuestion",
    "compare_with_twentythird",
    "forget_key",
    "lift_key",
    "read_back",
    "record_question",
    "record_witnesses",
    "smallest_none",
    "unfilled_key",
]


def lift_key(key: Key) -> Key24:
    """The mark here of a twenty-third result read with no term filled."""
    n, table = key
    return (n, table, (0,) * n)


def read_back(key: Key24) -> Key | None:
    """The map back: the twenty-third result of a result with no filled term, "none" (`None`) otherwise."""
    n, table, fills = key
    return None if any(fills) else (n, table)


def forget_key(key: Key24) -> Key:
    """The forgetting map: the twenty-third result of the states of a result (the least table comes first)."""
    return (key[0], key[1])


def smallest_none(grouped: Grouped) -> Key24 | None:
    """The first result, in round then fixed order, that the map back answers "none" on."""
    for key in grouped.ordered_keys():
        if read_back(key) is None:
            return key
    return None


@dataclass(frozen=True)
class Comparison:
    """This seed's results with no filled term against the twenty-third's run at the same bounds."""

    twentythird: Grouped23
    missing: tuple[Key24, ...]
    extra: tuple[Key24, ...]
    round_differs: tuple[Key24, ...]
    sequences_differ: tuple[Key24, ...]
    forgotten_onto: int
    largest_fibre: int


def compare_with_twentythird(grouped: Grouped) -> Comparison:
    """The twenty-third's results, lifted, against the results here with no filled term."""
    theirs = explore23(grouped.bound, grouped.rounds)
    lifted = {lift_key(k): r for k, r in theirs.round_of.items()}
    ours = {k: r for k, r in grouped.round_of.items() if not any(k[2])}
    ours_seq = shortest_sequences(grouped)
    theirs_seq = {lift_key(k): v for k, v in shortest23(theirs).items()}
    fibres: dict[Key, int] = {}
    for k in grouped.round_of:
        fibres[forget_key(k)] = fibres.get(forget_key(k), 0) + 1
    return Comparison(
        twentythird=theirs,
        missing=tuple(sorted(set(lifted) - set(ours))),
        extra=tuple(sorted(set(ours) - set(lifted))),
        round_differs=tuple(sorted(k for k in set(ours) & set(lifted) if ours[k] != lifted[k])),
        sequences_differ=tuple(sorted(k for k in set(ours) & set(lifted) if ours_seq[k] != theirs_seq[k])),
        forgotten_onto=len(fibres),
        largest_fibre=max(fibres.values(), default=0),
    )


def record_witnesses() -> tuple[tuple[DState, DState], tuple[DState, DState]]:
    """`a b; ara` with `a b; arb`, and `a b c; ara asb` with `a b c; arb bsa`: one record each, kept by
    different numbers of terms."""
    return (
        (DState.of(2, [(0, 0)]), DState.of(2, [(0, 1)])),
        (DState.of(3, [(0, 0)], [(0, 1)]), DState.of(3, [(0, 1)], [(1, 0)])),
    )


@dataclass(frozen=True)
class RecordQuestion:
    """The twenty-third's results grouped by their record, and how many terms keep each from nothing."""

    records: int
    records_with_several_sizes: int
    records_with_several_term_counts: int
    first: tuple[tuple[int, int, int], tuple[str, ...]] | None
    whether_shown: bool


def record_question(theirs: Grouped23) -> RecordQuestion:
    """Does the twenty-third's record show which terms keep a result from being the one asserting nothing?"""
    sizes: dict[tuple[int, int, int], set[int]] = {}
    counts: dict[tuple[int, int, int], set[int]] = {}
    firsts: dict[tuple[int, int, int], dict[int, str]] = {}
    whether = True
    for key in theirs.ordered_keys():
        rep = theirs.representative(key)
        rec = record23(rep)
        size = keeping_size(rep)
        sizes.setdefault(rec, set()).add(size)
        counts.setdefault(rec, set()).add(keeping_terms(rep))
        firsts.setdefault(rec, {}).setdefault(size, rep.written())
        whether &= (rec[1] + rec[2] == 0) == (size == 0)
    several = [rec for rec in sizes if len(sizes[rec]) > 1]
    first = None
    if several:
        rec = min(several, key=lambda x: (x[0] + x[1] + x[2], x))
        first = (rec, tuple(firsts[rec][s] for s in sorted(firsts[rec])))
    return RecordQuestion(
        records=len(sizes),
        records_with_several_sizes=len(several),
        records_with_several_term_counts=sum(1 for rec in counts if len(counts[rec]) > 1),
        first=first,
        whether_shown=whether,
    )


def unfilled_key(base: DState) -> Key24:
    """The mark of a twenty-third state read with no term filled (equal to `lift_key` of its mark there)."""
    return result_key(of_state(base))
