import Eleventh.State

/-!
# Writings of a change of the ninth seed

A change of the eleventh seed is a change of the ninth (`Step11` as `Step9`).
A writing is a reading of a result (C-W1), not a fifth kind of change.
Injective writings determine the assertions; a collision forbids every
coarser writing from determining; identifying two terms drops a term, a
colliding writing does not.
-/

namespace Seed.Eleventh

open Seed Seed.Ninth Seed.Eighth NDSt

abbrev Step11 : NDSt → NDSt → Prop := Step9
abbrev Reach11 : NDSt → NDSt → ℕ → Prop := Reach9

theorem Step9.toStep11 {s t : NDSt} (h : Step9 s t) : Step11 s t := h
theorem Step11.toStep9 {s t : NDSt} (h : Step11 s t) : Step9 s t := h

theorem inj_determines (s : NDSt) (w : ℕ → ℕ) (h : injOn w s.T) :
    determines s w := by
  intro q L K x y x' y' hx hy hx' hy' hL hK hL' hK'
  have hxeq : x = x' := h hx hx' (hL.trans hL'.symm)
  have hyeq : y = y' := h hy hy' (hK.trans hK'.symm)
  subst hxeq
  subst hyeq
  rfl

theorem coarser_of_not_determines {s : NDSt} {w w' : ℕ → ℕ}
    (hc : coarser w w' s.T) (h : ¬ determines s w) : ¬ determines s w' := by
  intro hd
  apply h
  intro q L K x y x' y' hx hy hx' hy' hL hK hL' hK'
  have hxw' : w' x' = w' x := (hc hx hx' (hL.trans hL'.symm)).symm
  have hyw' : w' y' = w' y := (hc hy hy' (hK.trans hK'.symm)).symm
  exact hd q (w' x) (w' y) x y x' y' hx hy hx' hy' rfl rfl hxw' hyw'

theorem writing_not_assertion (s : NDSt) :
    (s.proj false).M = s.M false ∧ (s.proj true).M = s.M true :=
  ⟨rfl, rfl⟩

theorem twoBetween_not_determines_r : ¬ determinesRel twoBetween collide false := by
  intro h
  have hx : (0 : ℕ) ∈ twoBetween.T := by simp [twoBetween]
  have hy : (1 : ℕ) ∈ twoBetween.T := by simp [twoBetween]
  have h01 := h 0 0 0 1 0 0 hx hy hx hx rfl rfl rfl rfl
  simp [twoBetween] at h01

theorem twoBetween_determines_s : determinesRel twoBetween collide true := by
  intro L K x y x' y' hx hy hx' hy' hL hK hL' hK'
  simp [twoBetween]

theorem r_collision_not_s :
    ¬ determinesRel twoBetween collide false ∧ determinesRel twoBetween collide true :=
  ⟨twoBetween_not_determines_r, twoBetween_determines_s⟩

theorem apart_injOn_twoBetween : injOn apart twoBetween.T := by
  intro x y hx hy hw
  simpa [apart] using hw

theorem apart_determines_twoBetween : determines twoBetween apart :=
  inj_determines twoBetween apart apart_injOn_twoBetween

theorem collide_keeps_terms : twoTerms9.T.card = 2 := by
  simp [twoTerms9, oneTerm9, NDSt.addTerm, empty9]

theorem identify_drops_a_term :
    (twoTerms9.identify 0 1).T.card + 1 = twoTerms9.T.card := by
  have hv : (1 : ℕ) ∈ twoTerms9.T := by simp [mem_twoTerms9_T]
  simp [NDSt.identify]
  rw [Finset.card_erase_of_mem hv]
  have : twoTerms9.T.card = 2 := collide_keeps_terms
  omega

theorem first_change_adds_term11 {t : NDSt} (h : Step11 empty9 t) :
    ∃ x, t = empty9.addTerm x :=
  first_change_adds_term9 h

end Seed.Eleventh
