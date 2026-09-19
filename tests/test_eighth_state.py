from __future__ import annotations

import pytest

from eighth.state import (
    GIVEN_ASSERTIONS,
    GIVEN_TERMS,
    RELATIONS,
    DState,
    MState,
    added,
    canonical,
    forget_canonical_forms,
    given,
    identify,
    names_one_term,
    of_r,
    pair,
    remove,
    rewrite,
    same,
)
from xry.state import Sameness


def test_a_two_relation_state_and_its_parts() -> None:
    s = DState.of(2, [(0, 1), (0, 1)], [(1, 0), (0, 0)], (0, 1))
    assert s.r_part() == MState.of(2, [(0, 1), (0, 1)], (0, 1)) and s.s_part() == MState.of(2, [(1, 0), (0, 0)], (0, 1))
    assert s.part("r") == s.r_part() and s.part("s") == s.s_part()
    assert s.total_r == 2 and s.total_s == 2 and s.m == 4 and s.size == 6 and s.distinct == 3 and s.most == 2
    assert s.mult_of("r", 0, 1) == 2 and s.has("s", 0, 0) and not s.has("s", 0, 1)
    assert s.legal_r and not s.legal_s and not s.simple and not s.nothing_in_s
    assert s.key() == "2:01:0-1*2|0-0*1.1-0*1" and s.written() == "terms a b; asserted arb(2) asa bsa"
    assert RELATIONS == ("r", "s") and (GIVEN_TERMS, GIVEN_ASSERTIONS) == (2, 1)
    assert added(s) == (0, 3)
    with pytest.raises(ValueError):
        s.part("t")
    with pytest.raises(ValueError):
        DState(2, (0,) * 4, (0,) * 3)
    with pytest.raises(ValueError):
        DState(1, (-1,), (0,))
    with pytest.raises(ValueError):
        DState(1, (0,), (0,), (0, 1))
    with pytest.raises(ValueError):
        DState(-1, (), ())
    with pytest.raises(ValueError):
        pair(MState.of(2, []), MState.of(1, []))
    with pytest.raises(ValueError):
        pair(MState.of(2, [], (0, 1)), MState.of(2, []))
    merged = DState.of(1, [(0, 0)], [(0, 0), (0, 0)], (0, 0))
    assert names_one_term(merged) and merged.written() == "terms a (a and b are one term); asserted ara asa(2)"
    assert not names_one_term(given(False, Sameness.FREE))


def test_what_is_given_and_the_embedding() -> None:
    g = given(False, Sameness.ANCHORED)
    assert g == of_r(MState.of(2, [(0, 1)], (0, 1))) and g.nothing_in_s and g.written() == "terms a b; asserted arb"
    assert given(True, Sameness.FREE) == DState.of(2, [(0, 1), (1, 0)]) and given(True, Sameness.FREE).names is None
    assert of_r(MState.of(1, [(0, 0)])).s == (0,)


def test_sameness_rewrites_both_relations_at_once() -> None:
    s = DState.of(2, [(0, 1)], [(1, 1)])
    t = DState.of(2, [(1, 0)], [(0, 0)])
    u = DState.of(2, [(1, 0)], [(1, 1)])
    assert same(s, t) and not same(s, u)  # the parts of s and u are the same up to separate rewritings only
    assert canonical(s) == canonical(t) and canonical(s) != canonical(u)
    assert rewrite(s, (1, 0)) == t
    assert not same(s, DState.of(3, [(0, 1)], [(1, 1)])) and not same(s, DState.of(2, [(0, 1)], [(1, 1)], (0, 1)))
    assert canonical(DState.of(2, [(1, 1)], [], (1, 0))) == DState.of(2, [(0, 0)], [], (0, 1))
    assert forget_canonical_forms() >= 1 and forget_canonical_forms() == 0


def test_removal_and_identification_act_on_the_named_relation() -> None:
    s = DState.of(2, [(0, 1)], [(0, 1), (1, 0)], (0, 1))
    assert remove(s, "s", 0, 1) == DState.of(2, [(0, 1)], [(1, 0)], (0, 1))
    assert remove(s, "r", 0, 1) == DState.of(2, [], [(0, 1), (1, 0)], (0, 1))
    with pytest.raises(ValueError):
        remove(s, "t", 0, 1)
    with pytest.raises(ValueError):
        remove(s, "r", 1, 0)
    assert identify(s, 0, 1) == DState.of(1, [(0, 0)], [(0, 0), (0, 0)], (0, 0))
