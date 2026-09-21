import Twelfth.Rename

/-!
# Coarser writings, and the unchosen coarser reading

`prompt/thirteenth/seed_prompt.md` is the ninth seed with one passage added:
a coarser writing of an assertion forgets whether it was written with `r` or
with `s`, every result is recorded also in that coarser writing, and two
results that differ only in which relation wrote their assertions may be the
same coarser result.

The state of the thirteenth seed under the chosen reading C-C1 is the ninth's
`NDSt`.  The coarser writing is the one-relation state whose multiplicity at
each pair is the sum of the two (`coarse`).  The unchosen reading C-C2 takes
that coarser writing as the result.
-/

namespace Seed.Thirteenth

open Seed Seed.Ninth Seed.Seventh Seed.Eighth Seed.Eleventh NDSt

/-- The coarser writing: one multiplicity, the sum of `r` and `s`. -/
def coarse (s : NDSt) : NSt := ⟨s.T, fun p => s.M false p + s.M true p⟩

/-- The coarser writing determines the finer one: unique preimage. -/
def determines (s : NDSt) : Prop := ∀ t : NDSt, coarse t = coarse s → t = s

theorem coarse_eq_sum (s : NDSt) (p : ℕ × ℕ) :
    (coarse s).M p = s.M false p + s.M true p :=
  rfl

theorem coarse_T (s : NDSt) : (coarse s).T = s.T := rfl

theorem coarse_swap (s : NDSt) : coarse s.swap = coarse s := by
  apply NSt.ext
  · rfl
  · funext p
    simp [coarse, NDSt.swap, add_comm]

theorem size_coarse (s : NDSt) : (coarse s).size = s.size := by
  unfold coarse NSt.size
  rw [size9_eq]
  simp [NSt.total, NDSt.proj]
  rw [Finset.sum_add_distrib, add_assoc]

theorem coarse_wf {s : NDSt} (h : s.WF) : (coarse s).WF := by
  intro p hp
  have : s.M false p ≠ 0 ∨ s.M true p ≠ 0 := by
    have : s.M false p + s.M true p ≠ 0 := hp
    omega
  cases this with
  | inl hr => exact h.1 p hr
  | inr hs => exact h.2 p hs

theorem coarse_not_assertion (s : NDSt) :
    (s.proj false).M = s.M false ∧ (s.proj true).M = s.M true :=
  ⟨rfl, rfl⟩

theorem determines_of_nothing (s : NDSt) (h : ∀ q p, s.M q p = 0) :
    determines s := by
  intro t ht
  apply NDSt.ext
  · simpa [coarse] using congrArg NSt.T ht
  · funext q p
    have hsum : t.M false p + t.M true p = s.M false p + s.M true p := by
      simpa [coarse] using congrFun (congrArg NSt.M ht) p
    have : t.M false p + t.M true p = 0 := by simp [hsum, h]
    have tf : t.M false p = 0 := by omega
    have tt' : t.M true p = 0 := by omega
    cases q <;> simp [tf, tt', h]

theorem empty_determines : determines empty9 :=
  determines_of_nothing empty9 (by intro q p; rfl)

theorem twoBetween_ne_swap : twoBetween.swap ≠ twoBetween := by
  intro h
  have := congrFun (congrFun (congrArg NDSt.M h) false) (0, 1)
  simp [NDSt.swap, twoBetween] at this

theorem not_determines_twoBetween : ¬ determines twoBetween := by
  intro h
  exact twoBetween_ne_swap (h twoBetween.swap (coarse_swap twoBetween))

theorem r_and_s_same_coarse :
    coarse twoBetween = coarse twoBetween.swap ∧ twoBetween ≠ twoBetween.swap :=
  ⟨(coarse_swap twoBetween).symm, twoBetween_ne_swap.symm⟩

end Seed.Thirteenth
