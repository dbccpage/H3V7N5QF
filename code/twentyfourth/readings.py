"""The unchosen readings, and the sameness the seed's clauses generate on states with filled terms.

Derived (paper, D1 and D16)
    * The sameness (C-S): rewriting (carrying the filled terms), one more pair
      asserted together, and raising one term generate exactly the classes of
      `result_key`.  Checked by search (`generated_classes`) on one and two
      terms, every pattern of filled terms, as the twenty-third checked its
      own (23:D1).
    * C-F1′ (filling a filled term is a change with its start as outcome):
      it reaches nothing, so the results and rounds are C-F1's (no search
      needed; `moves` under C-F1 simply leaves it out).
    * C-F2 (a count per term): different results; its rounds are
      `cost_counted`.
    * C-F3 (filling also asserts `xrx` and `xsx` once): the pair asserted
      together is taken out, so every outcome is C-F1's result.
    * C-F4 (filling adds the missing loops until the term balances): other
      outcomes (the loop's excess set to zero), the same results and rounds.
    * C-I2, C-I3 (the one term of an identification filled only when both
      were, never): the same results and rounds; other outcomes of some
      identifications (`identification_outcomes`).
    * C-E′ (the ninth's states, not plain, with filled terms): the same
      results and rounds.
"""

from __future__ import annotations

from collections.abc import Iterator
from itertools import permutations, product

from ninth.changes import Kind
from twentythird.readings import box_states
from twentythird.state import raise_term

from twentyfourth.changes import Fill, Reading, perform24
from twentyfourth.cost import cost
from twentyfourth.explore import Grouped, performed
from twentyfourth.state import DState, FState, result_key, rewrite

__all__ = ["box_fstates", "fill_steps", "generated_classes", "identification_outcomes"]


def box_fstates(n: int, total: int) -> list[FState]:
    """Every state on `n` terms with at most `total` assertions per relation, and every set of filled terms."""
    return [FState(b, f) for b in box_states(n, total) for f in product((0, 1), repeat=n)]


def fill_steps(state: FState) -> Iterator[FState]:
    """The states one step of the seed's clauses away: a rewriting (filled terms carried), one more pair
    asserted together, one term raised."""
    n = state.n
    for p in permutations(range(n)):
        yield rewrite(state, p)
    for i in range(n * n):
        r = list(state.base.r)
        s = list(state.base.s)
        r[i] += 1
        s[i] += 1
        yield FState(DState(n, tuple(r), tuple(s)), state.fills)
    for x in range(n):
        yield FState(raise_term(state.base, x), state.fills)


def generated_classes(n: int, small: int, large: int) -> dict[FState, FState]:
    """For every state with at most `small` assertions per relation, the root of its class under the joins
    the clauses make among the states with at most `large` per relation."""
    states = box_fstates(n, large)
    parent = {s: s for s in states}

    def find(s: FState) -> FState:
        while parent[s] != s:
            parent[s] = parent[parent[s]]
            s = parent[s]
        return s

    for s in states:
        for t in fill_steps(s):
            if t in parent:
                a, b = find(s), find(t)
                if a != b:
                    parent[a] = b
    return {s: find(s) for s in states if s.base.total_r <= small and s.base.total_s <= small}


def identification_outcomes(grouped: Grouped, other: Reading) -> dict[str, int]:
    """Every identification performed in the chosen exploration, performed again under `other`: how many
    reach another result, and how each reading moves the cost (odd or even)."""
    out = {"identifications": 0, "other_result": 0, "even_move_chosen": 0, "even_move_other": 0}
    for state, change, raw, _ in performed(grouped.states):
        if isinstance(change, Fill) or change.kind is not Kind.IDENTIFY:
            continue
        alt = perform24(state, change, other)
        out["identifications"] += 1
        out["other_result"] += result_key(alt) != result_key(raw)
        out["even_move_chosen"] += (cost(raw) - cost(state)) % 2 == 0
        out["even_move_other"] += (cost(alt) - cost(state)) % 2 == 0
    return out
