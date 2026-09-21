import Fourteenth.Rename

/-!
# Admission records, and the unchosen tagged reading

`prompt/fifteenth/seed_prompt.md` is the ninth seed with one passage added:
a result of the changes is reached; whether it is admitted is not given by
the reaching; record for every result whether it is admitted; reaching a
result does not make it admitted.

The state of the fifteenth seed under the chosen reading C-A1 is the ninth's
`NDSt`.  Admission is a record of a result (`Fifteenth/Step.lean`).  The
unchosen reading C-A2 tags a ninth state with an admission record (`Tagged`).
-/

namespace Seed.Fifteenth

open Seed Seed.Ninth Seed.Eighth

/-- Whether a result is admitted: neither `xry` nor `xsy`. -/
inductive Admission
  | notAdmitted
  | admitted
deriving DecidableEq, Repr

/-- Unchosen reading C-A2: a ninth state together with an admission record. -/
structure Tagged where
  state : NDSt
  admission : Admission

namespace Tagged

/-- The ninth's size: admission is not an assertion and is not counted. -/
def size (t : Tagged) : ℕ := t.state.size

/-- The empty beginning, not admitted (no reaching has admitted it). -/
def start : Tagged := ⟨empty9, .notAdmitted⟩

end Tagged

/-- Two terms with `0 r 1` and `0 s 1` each once. -/
def twoBoth : NDSt :=
  ⟨{0, 1}, fun _q p => if p = (0, 1) then 1 else 0⟩

theorem twoBoth_M_r : twoBoth.M false (0, 1) = 1 := by simp [twoBoth]
theorem twoBoth_M_s : twoBoth.M true (0, 1) = 1 := by simp [twoBoth]

theorem twoBoth_T : twoBoth.T = {0, 1} := rfl

end Seed.Fifteenth
