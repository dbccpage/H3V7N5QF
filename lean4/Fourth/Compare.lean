import Fourth.Answers

/-!
# What survives the assertion being counted

The task's rule 5 asks, for every result of an earlier derivation that is used,
whether its proof still holds from the fourth seed.  This file states the answer
in Lean for the results the fourth paper cites: on the states asserting nothing
twice, the third derivation's results, reachability criterion, cost and one-way
reachability are exactly the fourth seed's, through the support map `toSt` and
the indicator map `ofSt`; and the fourth seed's statements on all counted states
(`Fourth/Cost.lean`) are their extensions.

* `reach4_iff_reach2`: between two well-formed states asserting nothing twice,
  reachability under the fourth seed is reachability of the supports under the
  third — in the same number of changes.
* `reach4_givenA_iff`, `reach4_givenB_iff`: from what is given, a well-formed
  state asserting nothing twice is reached under the fourth seed exactly when
  its support is reached under the third, in the same number of changes: the
  results asserting nothing twice, their rounds and their costs are the third's.
* `contains4_iff_contains`: the reachability criterion, containment, agrees
  with the third's on those states.
* `results_extend`: every result of the third seed is a result of the fourth
  (its indicator); `arb_twice_result`: the fourth seed has results the third
  does not have — the state with `arb` twice, reached in one change, asserts
  something twice.
* `size_ofSt`: the size of an indicator state is the size of the earlier state,
  so the third's cost formula is the fourth's on those states.
-/

namespace Seed.Fourth

open Seed Seed.Second Seed.Third MSt

/-- Between well-formed states asserting nothing twice, reachability under the fourth
seed is reachability of the supports under the third seed, in the same number of
changes. -/
theorem reach4_iff_reach2 {s t : MSt} (hw : s.WF) (hs : s.Simple) (htw : t.WF) (ht : t.Simple)
    (n : ℕ) : Reach4 s t n ↔ Reach2 (toSt s) (toSt t) n := by
  constructor
  · intro h
    exact h.toReach2 hw ht
  · intro h
    have := h.toReach4
    rwa [ofSt_toSt hw hs, ofSt_toSt htw ht] at this

/-- From what is given (`bra` not asserted), a well-formed state asserting nothing
twice is reached under the fourth seed exactly when its support is reached under the
third seed, in the same number of changes. -/
theorem reach4_givenA_iff {t : MSt} (htw : t.WF) (ht : t.Simple) (n : ℕ) :
    Reach4 givenA4 t n ↔ Reach2 givenA (toSt t) n := by
  rw [reach4_iff_reach2 givenA4_wf (ofSt_simple _) htw ht, toSt_givenA4]

theorem reach4_givenB_iff {t : MSt} (htw : t.WF) (ht : t.Simple) (n : ℕ) :
    Reach4 givenB4 t n ↔ Reach2 givenB (toSt t) n := by
  rw [reach4_iff_reach2 givenB4_wf (ofSt_simple _) htw ht, toSt_givenB4]

/-- The reachability criterion agrees with the third's on states asserting nothing
twice: counted containment is containment of the supports. -/
theorem contains4_iff_contains {s t : MSt} (hw : s.WF) (hs : s.Simple) (htw : t.WF) :
    Contains4 s t ↔ Contains (toSt s) (toSt t) :=
  ⟨fun h => h.toSt hw, fun h => contains4_of_toSt h hw hs htw⟩

/-- Every result of the third seed is a result of the fourth: its indicator, reached in
the same number of changes. -/
theorem results_extend {g : St} {n : ℕ} (h : Reach2 givenA g n) : Reach4 givenA4 (ofSt g) n :=
  h.toReach4

theorem results_extend_B {g : St} {n : ℕ} (h : Reach2 givenB g n) : Reach4 givenB4 (ofSt g) n :=
  h.toReach4

/-- The fourth seed has results the third does not have: `arb` twice is reached in one
change and asserts something twice. -/
theorem arb_twice_result :
    Reach4 givenA4 (givenA4.addAssertion 0 1) 1 ∧ ¬ (givenA4.addAssertion 0 1).Simple := by
  obtain ⟨st, h2⟩ := arb_twice
  refine ⟨Reach4.step (Reach4.refl _) st, fun hs => ?_⟩
  have := hs (0, 1)
  omega

/-- The size of an indicator state is the size of the earlier state: the third's cost
formula is the fourth's on states asserting nothing twice. -/
theorem size_ofSt {s : St} (hw : s.WF) : (ofSt s).size = s.size := by
  have := size_toSt (ofSt_simple s)
  rw [toSt_ofSt hw] at this
  exact this.symm

/-- One-way reachability survives and extends: on states asserting nothing twice it is
the third's `Reach2.antisymm`, and `Reach4.antisymm` holds for all counted states. -/
theorem antisymm_survives {s t : MSt} {n m : ℕ} (hw : s.WF) (hs : s.Simple) (htw : t.WF)
    (ht : t.Simple) (h1 : Reach4 s t n) (h2 : Reach4 t s m) :
    (n = 0 ∧ m = 0 ∧ toSt s = toSt t) ∧ (n = 0 ∧ m = 0 ∧ s = t) :=
  ⟨Reach2.antisymm ((reach4_iff_reach2 hw hs htw ht n).1 h1)
      ((reach4_iff_reach2 htw ht hw hs m).1 h2),
    h1.antisymm h2 hw⟩

end Seed.Fourth
