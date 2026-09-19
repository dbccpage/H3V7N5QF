import Fifth.Rename

/-!
# The sixth seed: nothing is forbidden

`prompt/sixth/seed_prompt.md` is the fifth seed without the sentence "For no
term `x` may `xrx` be asserted" and without the paragraph on obstruction,
answers and refusal.  The state is the fifth's `MSt` (terms, a multiplicity for
each ordered pair, the two names) and `MSt.Legal` ("no `xrx` asserted") is now a
property a state may or may not have, no longer a condition on results.  The
operations `MSt.addTerm`, `MSt.addAssertion`, `MSt.remove`, `MSt.identify` are
the fourth's and fifth's, unchanged: none of them looked at legality.

Derived here, about identification with something asserted between or at the
merged terms (which the fifth seed never performed):
* the multiplicity of `uru` after identifying `u`, `v` is at least
  `M(u,v) + M(v,u)` (`identify_M_ge_pair`) — the given assertions survive the
  merge of `a` and `b` as `ara`;
* every other pair of the outcome has multiplicity zero when every term is merged
  into `u` (`identify_M_eq_zero_of_all_merged`);
* the one-term state asserting `0r0` `k` times (`loopState k`): its size, its
  well-formedness, and that it is contained in every well-formed state written
  with `a = b = 0` and `0r0` at least `k` times (`loopState_contains`).
-/

namespace Seed.Sixth

open Seed Seed.Fourth Seed.Fifth MSt

/-- After identifying `u` and `v`, `uru` is asserted at least `M(u,v) + M(v,u)` times:
both pairs lie in the fibre of `(u, u)`. -/
theorem identify_M_ge_pair (s : MSt) {u v : ℕ} (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v) :
    s.M (u, v) + s.M (v, u) ≤ (s.identify u v).M (u, u) := by
  rw [identify_M]
  have h1 : ((u, v) : ℕ × ℕ) ∈ (s.T ×ˢ s.T).filter (fun q => (merge u v q.1, merge u v q.2) = (u, u)) :=
    mem_fiber.2 ⟨⟨hu, hv⟩, by simp [merge_left, merge_right]⟩
  have h2 : ((v, u) : ℕ × ℕ) ∈ (s.T ×ˢ s.T).filter (fun q => (merge u v q.1, merge u v q.2) = (u, u)) :=
    mem_fiber.2 ⟨⟨hv, hu⟩, by simp [merge_left, merge_right]⟩
  have hne : ((u, v) : ℕ × ℕ) ≠ (v, u) := fun h => huv (Prod.mk.inj h).1
  have hsub : ({(u, v), (v, u)} : Finset (ℕ × ℕ)) ⊆
      (s.T ×ˢ s.T).filter (fun q => (merge u v q.1, merge u v q.2) = (u, u)) := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact h1
    · exact h2
  calc s.M (u, v) + s.M (v, u) = ∑ q ∈ ({(u, v), (v, u)} : Finset (ℕ × ℕ)), s.M q := by
        rw [Finset.sum_pair hne]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

/-- When every term is merged into `u`, every pair of the outcome but `(u, u)` has
multiplicity zero. -/
theorem identify_M_eq_zero_of_all_merged (s : MSt) (u v : ℕ) (hall : ∀ x ∈ s.T, merge u v x = u)
    {p : ℕ × ℕ} (hp : p ≠ (u, u)) : (s.identify u v).M p = 0 := by
  rw [identify_M_eq_zero_iff]
  intro x y hx hy hxy
  exfalso
  apply hp
  rw [← hxy, hall x hx, hall y hy]

/-- The one-term state (term `0`, both names on it) asserting `0r0` `k` times. -/
def loopState (k : ℕ) : MSt := ⟨{0}, fun p => if p = (0, 0) then k else 0, 0, 0⟩

theorem loopState_T (k : ℕ) : (loopState k).T = {0} := rfl
theorem loopState_a (k : ℕ) : (loopState k).a = 0 := rfl
theorem loopState_b (k : ℕ) : (loopState k).b = 0 := rfl
theorem loopState_M_self (k : ℕ) : (loopState k).M (0, 0) = k := by simp [loopState]
theorem loopState_M_of_ne (k : ℕ) {p : ℕ × ℕ} (hp : p ≠ (0, 0)) : (loopState k).M p = 0 := by
  simp [loopState, hp]

theorem loopState_wf (k : ℕ) : (loopState k).WF := by
  refine ⟨fun p hp => ?_, by simp [loopState], by simp [loopState]⟩
  by_cases h : p = (0, 0)
  · subst h
    simp [loopState]
  · exact absurd (loopState_M_of_ne k h) hp

theorem loopState_zero : loopState 0 = oneTerm4 := by
  apply MSt.ext
  · rfl
  · funext p
    show (if p = (0, 0) then 0 else 0) = (if p ∈ oneTerm.A then 1 else 0)
    simp [oneTerm]
  · rfl
  · rfl

theorem total_loopState (k : ℕ) : (loopState k).total = k := by
  unfold MSt.total
  rw [loopState_T]
  simp [loopState]

theorem size_loopState (k : ℕ) : (loopState k).size = k + 1 := by
  unfold MSt.size
  rw [total_loopState, loopState_T]
  simp [Nat.add_comm]

/-- The one-term state with `0r0` `k` times is contained in every well-formed state written
with `a = b = 0` asserting `0r0` at least `k` times. -/
theorem loopState_contains {g : MSt} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 0) {k : ℕ}
    (hk : k ≤ g.M (0, 0)) : Contains4 (loopState k) g := by
  refine ⟨fun t ht => ?_, fun p => ?_, ha, hb⟩
  · rw [loopState_T, Finset.mem_singleton] at ht
    subst ht
    exact ha ▸ hgw.2.1
  · by_cases hp : p = (0, 0)
    · subst hp
      rw [loopState_M_self]
      exact hk
    · rw [loopState_M_of_ne k hp]
      exact Nat.zero_le _

end Seed.Sixth
