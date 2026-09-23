import Seventeenth.Step
import H3V7N5QF.Paths

/-!
# The base's unobstructed steps are these steps

Every base `Step` is an unobstructed `Step17`, and every unobstructed
`Step17` is a base `Step`, with no hypothesis on the state: the base's
side-conditions are exactly M1. Sequences match, and the base cost is the
fewest changes along those sequences.
-/

namespace Seed.Seventeenth

open Seed St

theorem Step.toStep17 {s s' : St} (h : Step s s') : Nonempty (Step17 s s') := by
  cases h with
  | addTerm t ht => exact ⟨Step17.addTerm s t ht⟩
  | addAssertion x y hx hy _ hnew => exact ⟨Step17.addAssertion s x y hx hy hnew⟩
  | remove p hp => exact ⟨Step17.remove s p hp⟩
  | identify u v hu hv huv _ _ => exact ⟨Step17.identify s u v hu hv huv⟩

theorem Step.unobstructed17 {s s' : St} (h : Step s s') :
    ∃ st : Step17 s s', st.unobstructed := by
  cases h with
  | addTerm t ht =>
    refine ⟨Step17.addTerm s t ht, ?_⟩
    simp [Step17.unobstructed, Step17.obstructedM1]
  | addAssertion x y hx hy hxy hnew =>
    refine ⟨Step17.addAssertion s x y hx hy hnew, ?_⟩
    simpa [Step17.unobstructed, Step17.obstructedM1] using hxy
  | remove p hp =>
    refine ⟨Step17.remove s p hp, ?_⟩
    simp [Step17.unobstructed, Step17.obstructedM1]
  | identify u v hu hv huv h1 h2 =>
    refine ⟨Step17.identify s u v hu hv huv, ?_⟩
    intro hmem
    simp only [Step17.obstructedM1] at hmem
    rcases hmem with hmem | hmem
    · exact h1 hmem
    · exact h2 hmem

theorem Step17.toStep {s s' : St} (h : Step17 s s') (hu : h.unobstructed) :
    Step s s' := by
  cases h with
  | addTerm t ht => exact Step.addTerm s t ht
  | addAssertion x y hx hy hnew =>
    have hxy : x ≠ y := by
      intro heq
      exact hu (by simpa [Step17.obstructedM1] using heq)
    exact Step.addAssertion s x y hx hy hxy hnew
  | remove p hp => exact Step.remove s p hp
  | identify u v hu' hv huv =>
    have hnot : ¬ ((u, v) ∈ s.A ∨ (v, u) ∈ s.A) := by
      simpa [Step17.unobstructed, Step17.obstructedM1] using hu
    exact Step.identify s u v hu' hv huv
      (fun h => hnot (Or.inl h)) (fun h => hnot (Or.inr h))

theorem Reach.toReach17 {s t : St} {n : ℕ} (h : Reach s t n) : Reach17 s t n := by
  induction h with
  | refl => exact Reach17.refl _
  | step _ st ih =>
    obtain ⟨st17, hu⟩ := Step.unobstructed17 st
    exact Reach17.step ih st17 hu

theorem Reach17.toReach {s t : St} {n : ℕ} (h : Reach17 s t n) : Reach s t n := by
  induction h with
  | refl => exact Reach.refl _
  | step _ st hu ih => exact Reach.step ih (st.toStep hu)

/-- Along unobstructed steps from what is given (`bra` not asserted), the base
cost is a lower bound. It is the base's `fewest_changes_lower_A`, re-checked
by the embedding. -/
theorem fewest_changes17_lower_A {t : St} {n : ℕ} (h : Reach17 givenA t n) :
    costA t ≤ n + 3 :=
  fewest_changes_lower_A h.toReach

theorem fewest_changes17_lower_B {t : St} {n : ℕ} (h : Reach17 givenB t n) :
    costB t ≤ n + 4 :=
  fewest_changes_lower_B h.toReach

/-- The base cost is the fewest changes along unobstructed steps, for a
loop-free well-formed state written with `a = 0` and `b ∈ {0, 1}`. -/
theorem fewest_changes17_A {g : St} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0)
    (hb : g.b = 1 ∨ g.b = 0) :
    (∃ n, Reach17 givenA g n ∧ n + 3 = costA g) ∧
      ∀ n, Reach17 givenA g n → costA g ≤ n + 3 := by
  obtain ⟨⟨n, hR, hn⟩, hlow⟩ := fewest_changes_A hg hgw ha hb
  refine ⟨⟨n, Reach.toReach17 hR, hn⟩, ?_⟩
  intro m hm
  exact hlow m hm.toReach

theorem fewest_changes17_B {g : St} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0)
    (hb : g.b = 1 ∨ g.b = 0) :
    (∃ n, Reach17 givenB g n ∧ n + 4 = costB g) ∧
      ∀ n, Reach17 givenB g n → costB g ≤ n + 4 := by
  obtain ⟨⟨n, hR, hn⟩, hlow⟩ := fewest_changes_B hg hgw ha hb
  refine ⟨⟨n, Reach.toReach17 hR, hn⟩, ?_⟩
  intro m hm
  exact hlow m hm.toReach

end Seed.Seventeenth
