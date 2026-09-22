import Tenth.Rename

/-!
# Writings of terms, and the unchosen labeled reading

`prompt/eleventh/seed_prompt.md` is the ninth seed with one passage added: a
writing of terms may give two terms the same letter while they remain two
terms, and assertions are read from the writing.  If two terms are written
the same and their assertions differ, the writing does not determine the
assertions.

The state of the eleventh seed under the chosen reading C-W1 is the ninth's
`NDSt`.  A writing is a function from terms to letters (`Writing`).  The
unchosen reading C-W2 tags a ninth state with a writing (`Labeled`).
-/

namespace Seed.Eleventh

open Seed Seed.Ninth Seed.Eighth NDSt

/-- A writing of terms: a letter for each natural, read on the state's terms. -/
def Writing := ℕ → ℕ

/-- The writing gives two terms of `T` the same letter only when they are one term. -/
def injOn (w : ℕ → ℕ) (T : Finset ℕ) : Prop :=
  ∀ ⦃x y⦄, x ∈ T → y ∈ T → w x = w y → x = y

/-- The multiplicity of relation `q` is constant on every letter-pair rectangle. -/
def determinesRel (s : NDSt) (w : ℕ → ℕ) (q : Rel) : Prop :=
  ∀ L K x y x' y',
    x ∈ s.T → y ∈ s.T → x' ∈ s.T → y' ∈ s.T →
    w x = L → w y = K → w x' = L → w y' = K →
    s.M q (x, y) = s.M q (x', y')

/-- The writing determines the assertions of both relations. -/
def determines (s : NDSt) (w : ℕ → ℕ) : Prop := ∀ q, determinesRel s w q

/-- `w'` writes together every pair `w` writes together (and possibly more). -/
def coarser (w w' : ℕ → ℕ) (T : Finset ℕ) : Prop :=
  ∀ ⦃x y⦄, x ∈ T → y ∈ T → w x = w y → w' x = w' y

/-- Unchosen reading C-W2: a ninth state together with a writing of its terms. -/
structure Labeled where
  state : NDSt
  letter : ℕ → ℕ

namespace Labeled

/-- The ninth's size: a writing is not an assertion and is not counted. -/
def size (t : Labeled) : ℕ := t.state.size

/-- The empty beginning, with any writing (no terms to write). -/
def start : Labeled := ⟨empty9, fun _ => 0⟩

end Labeled

/-- Every term the same letter. -/
def collide : ℕ → ℕ := fun _ => 0

/-- Each term its own letter. -/
def apart : ℕ → ℕ := id

/-- Two terms with `0 r 1` asserted once, nothing with `s`. -/
def twoBetween : NDSt :=
  ⟨{0, 1}, fun q p => if q = false ∧ p = (0, 1) then 1 else 0⟩

theorem twoBetween_wf : twoBetween.WF := by
  refine ⟨?_, ?_⟩
  · intro p hp
    have : (if false = false ∧ p = (0, 1) then (1 : ℕ) else 0) ≠ 0 := by
      simpa [NDSt.proj, twoBetween] using hp
    have hp01 : p = (0, 1) := by
      by_cases h : p = (0, 1)
      · exact h
      · simp [h] at this
    subst hp01
    simp [twoBetween]
  · intro p hp
    have : (if true = false ∧ p = (0, 1) then (1 : ℕ) else 0) ≠ 0 := by
      simpa [NDSt.proj, twoBetween] using hp
    simp at this

theorem mem_twoBetween_T (x : ℕ) : x ∈ twoBetween.T ↔ x = 0 ∨ x = 1 := by
  simp [twoBetween, Finset.mem_insert, Finset.mem_singleton]

theorem twoBetween_M_r_01 : twoBetween.M false (0, 1) = 1 := by simp [twoBetween]
theorem twoBetween_M_r_00 : twoBetween.M false (0, 0) = 0 := by simp [twoBetween]
theorem twoBetween_M_s (p : ℕ × ℕ) : twoBetween.M true p = 0 := by simp [twoBetween]

end Seed.Eleventh
