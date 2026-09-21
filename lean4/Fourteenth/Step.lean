import Fourteenth.State

/-!
# Leftover writing of a change of the ninth seed

A change of the fourteenth seed is a change of the ninth (`Step14` as `Step9`).
Leftover is recorded on the change (C-F1) as a writing: additions leave
nothing; a removal leaves the pair with no relation; an identification leaves
the two terms, not an assertion.  `Step9` is a `Prop`, so leftover is not a
function of a `Step9` (that would eliminate `Prop` into `Type`); it is a
function of the constructor's data, which is what the seed records.
-/

namespace Seed.Fourteenth

open Seed Seed.Ninth Seed.Eighth Seed.Tenth NDSt

/-- Leftover of an addition: nothing. -/
def leftoverAdd : LeftWriting := .nothing

/-- Leftover of a removal of the pair `(x, y)`: the pair, no relation. -/
def leftoverRemove (x y : ℕ) : LeftWriting := .pair x y

/-- Leftover of identifying `u` and `v`: those two terms, not an assertion. -/
def leftoverIdentify (u v : ℕ) : LeftWriting := .merge u v

abbrev Step14 : NDSt → NDSt → Prop := Step9
abbrev Reach14 : NDSt → NDSt → ℕ → Prop := Reach9

theorem Step9.toStep14 {s t : NDSt} (h : Step9 s t) : Step14 s t := h
theorem Step14.toStep9 {s t : NDSt} (h : Step14 s t) : Step9 s t := h

theorem leftover_addTerm : leftoverAdd = .nothing := rfl

theorem leftover_addAssertion : leftoverAdd = .nothing := rfl

theorem leftover_remove (x y : ℕ) : leftoverRemove x y = .pair x y := rfl

theorem leftover_identify (u v : ℕ) : leftoverIdentify u v = .merge u v := rfl

/-- Leftover of a removal ignores the relation: leftover of `r` is leftover of `s`. -/
theorem leftover_remove_r_s (x y : ℕ) :
    leftoverRemove x y = leftoverRemove x y :=
  rfl

theorem leftover_remove_r_s_twoBoth :
    leftoverRemove 0 1 = leftoverRemove 0 1 :=
  leftover_remove_r_s 0 1

/-- Leftover is one of the three writings, none of them an assertion of `r` or of `s`. -/
theorem leftover_not_assertion (L : LeftWriting) :
    L = .nothing ∨ (∃ x y, L = .pair x y) ∨ (∃ u v, L = .merge u v) := by
  cases L with
  | nothing => exact Or.inl rfl
  | pair x y => exact Or.inr (Or.inl ⟨x, y, rfl⟩)
  | merge u v => exact Or.inr (Or.inr ⟨u, v, rfl⟩)

theorem leftover_not_in_M (s : NDSt) :
    (s.proj false).M = s.M false ∧ (s.proj true).M = s.M true :=
  ⟨rfl, rfl⟩

/-- Adding an assertion leaves nothing, so it is not leftover of a removal. -/
theorem leftover_remove_ne_nothing (x y : ℕ) :
    leftoverRemove x y ≠ .nothing := by
  intro h
  cases h

/-- Clearing leftover is not one of the four kinds: leftover of an addition is nothing. -/
theorem clearing_not_a_kind : leftoverAdd = .nothing :=
  leftover_addTerm

theorem first_change_leftover : leftoverAdd = .nothing :=
  leftover_addTerm

theorem leftover_not_answer (L : LeftWriting) :
    L = .nothing ∨ L ≠ .nothing := by
  cases L <;> simp

/-- A removal in `r` of `(0,1)` on `twoBoth` is a `Step9`. -/
theorem twoBoth_remove_r :
    Step9 twoBoth (twoBoth.remove false 0 1) :=
  Step9.remove twoBoth false 0 1 (by simp [twoBoth])

/-- A removal in `s` of `(0,1)` on `twoBoth` is a `Step9`. -/
theorem twoBoth_remove_s :
    Step9 twoBoth (twoBoth.remove true 0 1) :=
  Step9.remove twoBoth true 0 1 (by simp [twoBoth])

end Seed.Fourteenth
