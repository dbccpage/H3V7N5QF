import Twentyfourth

open Twentysecond Twentythird Twentyfourth

theorem v1 (F : Nat → Bool) : (∃ x, x < 0 + 1 ∧ F x = true) → F 0 = true := by
  rintro ⟨x, hx, h⟩
  have : x = 0 := by omega
  rw [this] at h
  exact h

theorem v2 (F : Nat → Bool) : F 0 = true → ∃ x, x < 0 + 1 ∧ F x = true := fun h => ⟨0, by omega, h⟩

theorem v3 (F : Nat → Bool) : F 0 = true → ∃ x, x < 0 + 1 ∧ F x = true := fun h => ⟨0, Nat.zero_lt_one, h⟩

theorem v4 (F : Nat → Bool) : (∃ x, x < 0 + 1 ∧ F x = true) → F 0 = true := fun ⟨x, hx, h⟩ => by
  have : x = 0 := by omega
  subst this
  exact h

theorem v5 (F : Nat → Bool) : Reach24 ⟨⟨0 + 1, []⟩, F⟩ ⟨⟨1, []⟩, F⟩ 0 := Reach24.refl _

#print axioms v1
#print axioms v2
#print axioms v3
#print axioms v4
#print axioms v5
