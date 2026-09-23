import Seventeenth.Embed

/-!
# Performing an obstructed change

Identifying `a` with `b` in what is given is one change. The outcome asserts
`ara`, the two names are one term, and the base cost of that outcome is not
the length. Adding `ara` is one change whose outcome asserts `ara`.
-/

namespace Seed.Seventeenth

open Seed St

/-- The one-term state asserting `ara`, names on that term. -/
def oneLoop : St := ⟨{0}, {(0, 0)}, 0, 0⟩

theorem identify_givenA_eq : givenA.identify 0 1 = oneLoop := by
  decide

theorem identify_givenB_eq : givenB.identify 0 1 = oneLoop := by
  decide

def identify_givenA_step : Step17 givenA (givenA.identify 0 1) :=
  Step17.identify givenA 0 1 (by simp [givenA]) (by simp [givenA]) (by decide)

def identify_givenB_step : Step17 givenB (givenB.identify 0 1) :=
  Step17.identify givenB 0 1 (by simp [givenB]) (by simp [givenB]) (by decide)

theorem identify_givenA_reach : ReachAll givenA (givenA.identify 0 1) 1 :=
  ReachAll.step (ReachAll.refl _) identify_givenA_step

theorem identify_givenB_reach : ReachAll givenB (givenB.identify 0 1) 1 :=
  ReachAll.step (ReachAll.refl _) identify_givenB_step

theorem oneLoop_hasXrx : HasXrx oneLoop := ⟨0, by simp [oneLoop]⟩

theorem mergedA_hasXrx : HasXrx (givenA.identify 0 1) := by
  rw [identify_givenA_eq]
  exact oneLoop_hasXrx

theorem mergedB_hasXrx : HasXrx (givenB.identify 0 1) := by
  rw [identify_givenB_eq]
  exact oneLoop_hasXrx

theorem oneLoop_names : oneLoop.a = oneLoop.b := by simp [oneLoop]

theorem names_merged_with_loop : (givenA.identify 0 1).a = (givenA.identify 0 1).b ∧
    HasXrx (givenA.identify 0 1) := by
  rw [identify_givenA_eq]
  exact ⟨oneLoop_names, oneLoop_hasXrx⟩

theorem costA_oneLoop : costA oneLoop = 6 := by decide

theorem costB_oneLoop : costB oneLoop = 8 := by decide

theorem costA_mergedA : costA (givenA.identify 0 1) = 6 := by
  rw [identify_givenA_eq]
  exact costA_oneLoop

theorem costB_mergedB : costB (givenB.identify 0 1) = 8 := by
  rw [identify_givenB_eq]
  exact costB_oneLoop

/-- The base lower bound does not hold of this one change: the formula gives 6,
the length is 1, and `6 ≰ 1 + 3`. -/
theorem cost_not_lower_bound_A : ReachAll givenA (givenA.identify 0 1) 1 ∧
    costA (givenA.identify 0 1) = 6 ∧ ¬ costA (givenA.identify 0 1) ≤ 1 + 3 := by
  refine ⟨identify_givenA_reach, costA_mergedA, ?_⟩
  rw [costA_mergedA]
  omega

theorem cost_not_lower_bound_B : ReachAll givenB (givenB.identify 0 1) 1 ∧
    costB (givenB.identify 0 1) = 8 ∧ ¬ costB (givenB.identify 0 1) ≤ 1 + 4 := by
  refine ⟨identify_givenB_reach, costB_mergedB, ?_⟩
  rw [costB_mergedB]
  omega

/-- Once the names are one term, `ara` is asserted, so "`arb` is never asserted
again" fails if `ara` is what `arb` became. -/
theorem arb_not_gone : (givenA.identify 0 1).a = (givenA.identify 0 1).b ∧
    ((givenA.identify 0 1).a, (givenA.identify 0 1).b) ∈ (givenA.identify 0 1).A := by
  rw [identify_givenA_eq]
  exact ⟨oneLoop_names, by simp [oneLoop]⟩

def add_ara_step : Step17 givenA (givenA.addAssertion 0 0) :=
  Step17.addAssertion givenA 0 0 (by simp [givenA]) (by simp [givenA]) (by simp [givenA])

theorem add_ara_reach : ReachAll givenA (givenA.addAssertion 0 0) 1 :=
  ReachAll.step (ReachAll.refl _) add_ara_step

theorem add_ara_hasXrx : HasXrx (givenA.addAssertion 0 0) :=
  adding_xrx_obstructed givenA 0

/-- The outcome of adding `ara` is not reached by unobstructed steps. -/
theorem add_ara_not_unobstructed {n : ℕ} : ¬ Reach17 givenA (givenA.addAssertion 0 0) n := by
  intro h
  exact h.loopFree givenA_legal 0 (by simp [St.addAssertion])

end Seed.Seventeenth
