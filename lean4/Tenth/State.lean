import Ninth.Rename

/-!
# Leftover outcomes, and the unchosen tagged reading

`prompt/tenth/seed_prompt.md` is the ninth seed with one passage added: after
every change, record what that change leaves.  A leftover is not an
assertion.  Three outcomes: nothing left; a leftover that a later change of
the four kinds can clear; a leftover that none of them can.

The state of the tenth seed under the chosen reading C-L1 is the ninth's
`NDSt`.  Leftover is recorded on the change (`Tenth/Step.lean`).  The
unchosen reading C-L2 tags a ninth state with a leftover (`Tagged`).
-/

namespace Seed.Tenth

open Seed Seed.Ninth Seed.Eighth

/-- The three leftover outcomes the seed names. -/
inductive LeftOver
  | nothingLeft
  | clearable
  | uncleared
deriving DecidableEq, Repr

/-- Unchosen reading C-L2: a ninth state together with leftover status. -/
structure Tagged where
  state : NDSt
  leftover : LeftOver

namespace Tagged

/-- The ninth's size: leftover is not an assertion and is not counted. -/
def size (t : Tagged) : ℕ := t.state.size

/-- The empty beginning, tagged nothing left (no incoming change). -/
def start : Tagged := ⟨empty9, .nothingLeft⟩

end Tagged

/-- Removing an assertion and adding it back restores the state, when it was asserted. -/
theorem remove_add_of_pos (s : NDSt) (q : Rel) (x y : ℕ)
    (hp : s.M q (x, y) ≠ 0) :
    (s.remove q x y).addAssertion q x y = s := by
  apply NDSt.ext
  · rfl
  · funext q' p
    by_cases hq : q' = q
    · subst hq
      by_cases he : p = (x, y)
      · subst he
        simp [NDSt.remove, NDSt.addAssertion, Function.update_apply]
        exact Nat.succ_pred_eq_of_ne_zero hp
      · have hne : p ≠ (x, y) := he
        simp [NDSt.remove, NDSt.addAssertion, Function.update_of_ne hne]
    · simp [NDSt.remove, NDSt.addAssertion, Function.update_of_ne hq]

/-- Two terms, nothing asserted. -/
def twoEmpty : NDSt := empty9.addTerm 0 |>.addTerm 1

theorem twoEmpty_M (q : Rel) (p : ℕ × ℕ) : twoEmpty.M q p = 0 := by
  simp [twoEmpty, empty9, NDSt.addTerm]

theorem twoEmpty_T : twoEmpty.T = {0, 1} := by
  ext n
  simp [twoEmpty, empty9, NDSt.addTerm, Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- Identifying the two empty terms leaves the one-term state. -/
theorem identify_twoEmpty : (twoEmpty.identify 0 1).T = {0} := by
  simp [twoEmpty, empty9, NDSt.identify, NDSt.addTerm]

theorem identify_twoEmpty_M (q : Rel) (p : ℕ × ℕ) : (twoEmpty.identify 0 1).M q p = 0 := by
  simp [NDSt.identify, twoEmpty_M]

theorem addTerm_identify_twoEmpty : (twoEmpty.identify 0 1).addTerm 1 = twoEmpty := by
  apply NDSt.ext
  · simp [NDSt.addTerm, identify_twoEmpty, twoEmpty_T]
    ext n
    simp [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl) <;> simp [twoEmpty, empty9, NDSt.addTerm]
    · intro h
      have : n = 0 ∨ n = 1 := by
        simpa [twoEmpty, empty9, NDSt.addTerm] using h
      exact this.symm
  · funext q p
    simp [NDSt.addTerm, identify_twoEmpty_M, twoEmpty_M]

/-- Two terms with `0 r 1` asserted once. -/
def twoBetween : NDSt :=
  ⟨{0, 1}, fun q p => if q = false ∧ p = (0, 1) then 1 else 0⟩

end Seed.Tenth
