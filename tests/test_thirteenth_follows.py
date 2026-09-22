from __future__ import annotations

from ninth.state import DState, empty
from thirteenth.explore import explore
from thirteenth.follows import (
    both_relations,
    coarse_verdicts,
    determines_finer,
    unique_split,
    swap_same_coarse,
    verdicts,
)


def test_coarse_statements_do_not_follow() -> None:
    expl = explore(empty(), 2, 4)
    found = coarse_verdicts(expl)
    names = {v.name for v in found}
    assert names == {"determines_finer", "unique_split", "swap_same_coarse", "both_relations"}
    by_name = {v.name: v for v in found}
    assert by_name["determines_finer"].holds_at is not None and by_name["determines_finer"].fails_at is not None
    assert by_name["swap_same_coarse"].holds_at is not None
    assert not by_name["determines_finer"].follows
    two = DState.of(2, [], [])
    between = DState.of(2, [(0, 1)], [])
    both = DState.of(2, [(0, 1)], [(0, 1)])
    assert determines_finer(two) and unique_split(two)
    assert not determines_finer(between)
    assert swap_same_coarse(between)
    assert both_relations(both)
    state_v = verdicts(expl)
    assert state_v and any(not v.follows_within_bound for v in state_v)


def test_swap_same_coarse_excludes_a_result_equal_to_its_own_exchange() -> None:
    """A state whose exchange is the same result up to renaming is not a
    'different finer result with the same coarser writing', though its written
    r and s tuples differ (regression for the r != s test)."""
    from ninth.state import same, swap
    from thirteenth.coarse import same_coarser
    from thirteenth.invariants import check_coarses

    # r asserts 1 r 1, s asserts 0 s 0: exchanging and renaming term 0 <-> 1
    # gives the same result, so it is not a swap-collapse.
    self_sym = DState.of(2, [(1, 1)], [(0, 0)])
    assert self_sym.r != self_sym.s
    assert same(self_sym, swap(self_sym)) and same_coarser(self_sym, swap(self_sym))
    assert not swap_same_coarse(self_sym)
    # It reaches such a state within the bound and does not count it.
    expl = explore(empty(), 3, 6)
    assert any(same(s, swap(s)) and s.r != s.s for s in expl.depth)
    counted = sum(1 for s in expl.depth if swap_same_coarse(s))
    check = check_coarses(expl)
    assert check.swap_collapses == counted
    assert check.swap_collapses == sum(
        1 for s in expl.depth if not same(s, swap(s)) and same_coarser(s, swap(s))
    )
