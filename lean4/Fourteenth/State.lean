import Thirteenth.Rename

/-!
# Leftover writings, and the unchosen tagged reading

`prompt/fourteenth/seed_prompt.md` is the ninth seed with one passage added:
after every change, record what that change leaves.  A leftover is written
neither `xry` nor `xsy`.  A leftover is not an assertion and is not an answer.

The state of the fourteenth seed under the chosen reading C-F1 is the ninth's
`NDSt`.  Leftover is a writing of the change (`Fourteenth/Step.lean`).  The
unchosen reading C-F2 tags a ninth state with a leftover writing (`Tagged`).
-/

namespace Seed.Fourteenth

open Seed Seed.Ninth Seed.Eighth Seed.Tenth

/-- A leftover writing: neither `xry` nor `xsy`. -/
inductive LeftWriting
  | nothing
  | pair (x y : ℕ)
  | merge (u v : ℕ)
deriving DecidableEq, Repr

/-- Unchosen reading C-F2: a ninth state together with leftover writing. -/
structure Tagged where
  state : NDSt
  leftover : LeftWriting

namespace Tagged

/-- The ninth's size: leftover is not an assertion and is not counted. -/
def size (t : Tagged) : ℕ := t.state.size

/-- The empty beginning, tagged nothing (no incoming change). -/
def start : Tagged := ⟨empty9, .nothing⟩

end Tagged

/-- Two terms with `0 r 1` and `0 s 1` each once. -/
def twoBoth : NDSt :=
  ⟨{0, 1}, fun _q p => if p = (0, 1) then 1 else 0⟩

theorem twoBoth_M_r : twoBoth.M false (0, 1) = 1 := by simp [twoBoth]
theorem twoBoth_M_s : twoBoth.M true (0, 1) = 1 := by simp [twoBoth]

theorem twoBoth_T : twoBoth.T = {0, 1} := rfl

end Seed.Fourteenth
