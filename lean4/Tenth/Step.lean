import Tenth.State

/-!
# Leftover of a change of the ninth seed

A change of the tenth seed is a change of the ninth (`Step10` as `Step9`).
Leftover is recorded on the change (C-L1) as a function of the start and the
outcome: additions raise the size and leave nothing; a removal keeps the
terms and leaves a leftover cleared by adding that assertion; an
identification drops a term and leaves a leftover that a later change can
clear exactly when some one `Step9` restores the start up to writing: to
some rewriting `rename9 π s` of it, since two results that differ only in how
their terms are written are the same result.  (An earlier version asked for
`Step9 t s` exactly, which made the outcome depend on which of the two terms
the identification kept, and disagreed with `code/tenth/leftover.py`, which
compares up to writing; see `paper/tenth/change_log.md`.)
-/

namespace Seed.Tenth

open Seed Seed.Ninth Seed.Eighth NDSt
open Classical

/-- Rewriting by the permutation that moves nothing leaves a state as it was. -/
theorem rename9_refl (s : NDSt) : rename9 (Equiv.refl ℕ) s = s := by
  apply NDSt.ext
  · simp [rename9]
  · funext q p
    simp [rename9]

/-- Which leftover outcome the change from `s` to `t` has (C-L1). -/
noncomputable def leftoverOf (s t : NDSt) : LeftOver :=
  if t.size = s.size + 1 then .nothingLeft
  else if t.T.card = s.T.card then .clearable
  else if ∃ π : Equiv.Perm ℕ, ∃ _ : Step9 t (rename9 π s), True then .clearable
  else .uncleared

abbrev Step10 : NDSt → NDSt → Prop := Step9
abbrev Reach10 : NDSt → NDSt → ℕ → Prop := Reach9

theorem Step9.toStep10 {s t : NDSt} (h : Step9 s t) : Step10 s t := h
theorem Step10.toStep9 {s t : NDSt} (h : Step10 s t) : Step9 s t := h

theorem leftover_addTerm {s : NDSt} {u : ℕ} (hw : s.WF) (ht : u ∉ s.T) :
    leftoverOf s (s.addTerm u) = .nothingLeft := by
  simp [leftoverOf, size_addTerm9 hw ht]

theorem leftover_addAssertion (s : NDSt) (q : Rel) (x y : ℕ)
    (hx : x ∈ s.T) (hy : y ∈ s.T) :
    leftoverOf s (s.addAssertion q x y) = .nothingLeft := by
  simp [leftoverOf, size_addAssertion9 q hx hy]

theorem leftover_remove {s : NDSt} (hw : s.WF) (q : Rel) (x y : ℕ)
    (hp : s.M q (x, y) ≠ 0) :
    leftoverOf s (s.remove q x y) = .clearable := by
  have hne : ¬ (s.remove q x y).size = s.size + 1 := by
    have := size_remove9 hw q hp
    omega
  have hT : (s.remove q x y).T.card = s.T.card := by simp [NDSt.remove]
  simp [leftoverOf, hne, hT]

/-- Adding the removed assertion restores the start. -/
theorem clears_remove (s : NDSt) (q : Rel) (x y : ℕ)
    (hx : x ∈ s.T) (hy : y ∈ s.T) (hp : s.M q (x, y) ≠ 0) :
    Step9 (s.remove q x y) s := by
  have hT : x ∈ (s.remove q x y).T := by simpa [NDSt.remove] using hx
  have hT' : y ∈ (s.remove q x y).T := by simpa [NDSt.remove] using hy
  have := Step9.addAssertion (s.remove q x y) q x y hT hT'
  rwa [remove_add_of_pos s q x y hp] at this

theorem leftover_not_assertion (s t : NDSt) :
    leftoverOf s t = .nothingLeft ∨ leftoverOf s t = .clearable ∨ leftoverOf s t = .uncleared := by
  cases leftoverOf s t <;> simp

theorem first_change_leftover :
    leftoverOf empty9 (empty9.addTerm 0) = .nothingLeft :=
  leftover_addTerm empty9_wf (by simp [empty9])

theorem identify_twoEmpty_restored :
    Step9 (twoEmpty.identify 0 1) twoEmpty := by
  have h1 : 1 ∉ (twoEmpty.identify 0 1).T := by
    simp [identify_twoEmpty]
  have := Step9.addTerm (twoEmpty.identify 0 1) 1 h1
  rwa [addTerm_identify_twoEmpty] at this

theorem leftover_identify_twoEmpty :
    leftoverOf twoEmpty (twoEmpty.identify 0 1) = .clearable := by
  have hsize : ¬ (twoEmpty.identify 0 1).size = twoEmpty.size + 1 := by
    have := size_identify9
      (by simp [twoEmpty, empty9, NDSt.addTerm] : 0 ∈ twoEmpty.T)
      (by simp [twoEmpty, empty9, NDSt.addTerm] : 1 ∈ twoEmpty.T)
      (by decide : 0 ≠ 1)
    omega
  have hT : ¬ (twoEmpty.identify 0 1).T.card = twoEmpty.T.card := by
    simp [identify_twoEmpty, twoEmpty_T]
  have hex : ∃ π : Equiv.Perm ℕ, ∃ _ : Step9 (twoEmpty.identify 0 1) (rename9 π twoEmpty), True :=
    ⟨Equiv.refl ℕ, by rw [rename9_refl]; exact identify_twoEmpty_restored, trivial⟩
  simp only [leftoverOf, hsize, hT, if_false]
  rw [if_pos hex]

end Seed.Tenth
