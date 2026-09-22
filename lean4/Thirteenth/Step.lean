import Thirteenth.State

/-!
# Coarser writings of a change of the ninth seed

A change of the thirteenth seed is a change of the ninth (`Step13` as `Step9`).
The coarser writing is computed from the state (C-C1), not a fifth kind of
change.  Adding in `r` and adding in `s` land on the same coarser writing.
-/

namespace Seed.Thirteenth

open Seed Seed.Ninth Seed.Seventh Seed.Eighth Seed.Eleventh NDSt

abbrev Step13 : NDSt → NDSt → Prop := Step9
abbrev Reach13 : NDSt → NDSt → ℕ → Prop := Reach9

theorem Step9.toStep13 {s t : NDSt} (h : Step9 s t) : Step13 s t := h
theorem Step13.toStep9 {s t : NDSt} (h : Step13 s t) : Step9 s t := h

theorem first_change_adds_term13 {t : NDSt} (h : Step13 empty9 t) :
    ∃ x, t = empty9.addTerm x :=
  first_change_adds_term9 h

theorem coarse_addAssertion_r_s (s : NDSt) (x y : ℕ) :
    coarse (s.addAssertion false x y) = coarse (s.addAssertion true x y) := by
  apply NSt.ext
  · rfl
  · funext p
    unfold coarse NDSt.addAssertion
    simp
    by_cases hp : p = (x, y)
    · subst hp
      simp
      omega
    · simp [hp]

theorem coarse_addTerm (s : NDSt) (x : ℕ) : coarse (s.addTerm x) = (coarse s).addTerm x :=
  rfl

end Seed.Thirteenth
