import Twelfth.State

/-!
# Identification records of a change of the ninth seed

A change of the twelfth seed is a change of the ninth (`Step12` as `Step9`).
The record of an identification is computed from the start (C-M1), not a
fifth kind of change.  The record of one relation is determined by that
relation; the two records can differ; a non-empty record is not restored
by any one later change; an empty record of two isolated terms is restored
by adding a term.
-/

namespace Seed.Twelfth

open Seed Seed.Ninth Seed.Eighth Seed.Eleventh NDSt

abbrev Step12 : NDSt → NDSt → Prop := Step9
abbrev Reach12 : NDSt → NDSt → ℕ → Prop := Reach9

theorem Step9.toStep12 {s t : NDSt} (h : Step9 s t) : Step12 s t := h
theorem Step12.toStep9 {s t : NDSt} (h : Step12 s t) : Step9 s t := h

theorem first_change_adds_term12 {t : NDSt} (h : Step12 empty9 t) :
    ∃ x, t = empty9.addTerm x :=
  first_change_adds_term9 h

theorem identify_drops_a_term :
    (twoTerms9.identify 0 1).T.card + 1 = twoTerms9.T.card := by
  have hv : (1 : ℕ) ∈ twoTerms9.T := by simp [mem_twoTerms9_T]
  simp [NDSt.identify]
  rw [Finset.card_erase_of_mem hv]
  have : twoTerms9.T.card = 2 := by
    simp [twoTerms9, oneTerm9, NDSt.addTerm, empty9]
  omega

theorem empty_record_restored_by_addTerm :
    twoTerms9.identify 0 1 = oneTerm9 ∧ oneTerm9.addTerm 1 = twoTerms9 :=
  ⟨identify_twoTerms9, rfl⟩

theorem identify_twoBetween_T :
    (twoBetween.identify 0 1).T = {0} := by
  change ({0, 1} : Finset ℕ).erase 1 = ({0} : Finset ℕ)
  decide

theorem identify_twoBetween_card :
    (twoBetween.identify 0 1).T.card = 1 := by
  rw [identify_twoBetween_T]
  simp

theorem twoBetween_card : twoBetween.T.card = 2 := by
  simp [twoBetween]

theorem twoBetween_M00 : twoBetween.M false (0, 0) = 0 :=
  twoBetween_M_r_00

theorem identify_twoBetween_M00 :
    (twoBetween.identify 0 1).M false (0, 0) ≠ 0 := by
  simp [NDSt.identify, twoBetween, Seed.merge]

theorem step9_card {s t : NDSt} (h : Step9 s t) :
    t.T.card = s.T.card + 1 ∨ t.T.card = s.T.card ∨ t.T.card + 1 = s.T.card := by
  cases h with
  | addTerm x hx =>
    left
    simp [NDSt.addTerm, Finset.card_insert_of_notMem hx]
  | addAssertion q a b ha hb =>
    right; left
    simp [NDSt.addAssertion]
  | remove q a b hp =>
    right; left
    simp [NDSt.remove]
  | identify u v hu hv huv =>
    right; right
    have hpos : 1 ≤ s.T.card := Finset.one_le_card.mpr ⟨v, hv⟩
    simp [NDSt.identify, Finset.card_erase_of_mem hv]
    omega

theorem step9_M_of_card_succ {s t : NDSt} (h : Step9 s t)
    (hc : t.T.card = s.T.card + 1) : t.M = s.M := by
  cases h with
  | addTerm x hx =>
    rfl
  | addAssertion q a b ha hb =>
    simp [NDSt.addAssertion] at hc
  | remove q a b hp =>
    simp [NDSt.remove] at hc
  | identify u v hu hv huv =>
    have hpos : 1 ≤ s.T.card := Finset.one_le_card.mpr ⟨v, hv⟩
    simp [NDSt.identify, Finset.card_erase_of_mem hv] at hc

theorem nonempty_not_restored :
    ¬ Step9 (twoBetween.identify 0 1) twoBetween := by
  intro h
  have h1 : (twoBetween.identify 0 1).T.card = 1 := identify_twoBetween_card
  have h2 : twoBetween.T.card = 2 := twoBetween_card
  have hs : twoBetween.T.card = (twoBetween.identify 0 1).T.card + 1 := by omega
  have hM := step9_M_of_card_succ h hs
  have h00 : twoBetween.M false (0, 0) = (twoBetween.identify 0 1).M false (0, 0) :=
    congrFun (congrFun hM false) (0, 0)
  rw [twoBetween_M00] at h00
  exact identify_twoBetween_M00 h00.symm

end Seed.Twelfth
