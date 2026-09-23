import Seventeenth.Step
import H3V7N5QF.Paths

/-!
# The base's unobstructed steps are these steps

Every base `Step` is an unobstructed `Step17`. On a loop-free state, an
unobstructed `Step17` is a base `Step`. Sequences match, and the base cost
is the fewest changes along those sequences.
-/

namespace Seed.Seventeenth

open Seed St

theorem Step.toStep17 {s s' : St} : Step s s' → Step17 s s'
  | .addTerm s t ht => .addTerm s t ht
  | .addAssertion s x y hx hy _ hnew => .addAssertion s x y hx hy hnew
  | .remove s p hp => .remove s p hp
  | .identify s u v hu hv huv _ _ => .identify s u v hu hv huv

theorem Step.unobstructed17 {s s' : St} (h : Step s s') : h.toStep17.unobstructed := by
  cases h with
  | addTerm t ht =>
    simp [Step.toStep17, Step17.unobstructed, Step17.obstructedM1]
  | addAssertion x y hx hy hxy hnew =>
    simpa [Step.toStep17, Step17.unobstructed, Step17.obstructedM1] using hxy
  | remove p hp =>
    simp [Step.toStep17, Step17.unobstructed, Step17.obstructedM1]
  | identify u v hu hv huv h1 h2 =>
    intro hmem
    simp only [Step.toStep17, Step17.obstructedM1] at hmem
    rcases hmem with hmem | hmem
    · exact h1 hmem
    · exact h2 hmem

theorem Step17.toStep {s s' : St} (h : Step17 s s') (hs : LoopFree s) (hu : h.unobstructed) :
    Step s s' := by
  cases h with
  | addTerm t ht => exact Step.addTerm s t ht
  | addAssertion x y hx hy hnew =>
    have hxy : x ≠ y := by
      intro hxy
      exact hu (by simpa [Step17.obstructedM1] using hxy)
    exact Step.addAssertion s x y hx hy hxy hnew
  | remove p hp => exact Step.remove s p hp
  | identify u v hu' hv huv =>
    have hnot : ¬ ((u, v) ∈ s.A ∨ (v, u) ∈ s.A) := by
      simpa [Step17.obstructedM1] using hu
    exact Step.identify s u v hu' hv huv (by tauto) (by tauto)

theorem Reach.toReach17 {s t : St} {n : ℕ} (h : Reach s t n) (hs : LoopFree s) :
    Reach17 s t n := by
  induction h with
  | refl => exact Reach17.refl _
  | step r st ih => exact Reach17.step ih st.toStep17 st.unobstructed17

theorem Reach17.toReach {s t : St} {n : ℕ} (h : Reach17 s t n) (hs : LoopFree s) :
    Reach s t n := by
  induction h with
  | refl => exact Reach.refl _
  | step r st hu ih => exact Reach.step ih (st.toStep (r.loopFree hs) hu)

/-- Along unobstructed steps from what is given (`bra` not asserted), the base
cost is a lower bound. It is the base's `fewest_changes_lower_A`, re-checked
by the embedding. -/
theorem fewest_changes17_lower_A {t : St} {n : ℕ} (h : Reach17 givenA t n) :
    costA t ≤ n + 3 :=
  fewest_changes_lower_A (h.toReach givenA_legal)

theorem fewest_changes17_lower_B {t : St} {n : ℕ} (h : Reach17 givenB t n) :
    costB t ≤ n + 4 :=
  fewest_changes_lower_B (h.toReach givenB_legal)

/-- The base cost is the fewest changes along unobstructed steps, for a
loop-free well-formed state written with `a = 0` and `b ∈ {0, 1}`. -/
theorem fewest_changes17_A {g : St} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0)
    (hb : g.b = 1 ∨ g.b = 0) :
    (∃ n, Reach17 givenA g n ∧ n + 3 = costA g) ∧
      ∀ n, Reach17 givenA g n → costA g ≤ n + 3 := by
  obtain ⟨⟨n, hR, hn⟩, hlow⟩ := fewest_changes_A hg hgw ha hb
  refine ⟨⟨n, hR.toReach17 givenA_legal, hn⟩, ?_⟩
  intro m hm
  exact hlow m (hm.toReach givenA_legal)

theorem fewest_changes17_B {g : St} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0)
    (hb : g.b = 1 ∨ g.b = 0) :
    (∃ n, Reach17 givenB g n ∧ n + 4 = costB g) ∧
      ∀ n, Reach17 givenB g n → costB g ≤ n + 4 := by
  obtain ⟨⟨n, hR, hn⟩, hlow⟩ := fewest_changes_B hg hgw ha hb
  refine ⟨⟨n, hR.toReach17 givenB_legal, hn⟩, ?_⟩
  intro m hm
  exact hlow m (hm.toReach givenB_legal)

end Seed.Seventeenth
