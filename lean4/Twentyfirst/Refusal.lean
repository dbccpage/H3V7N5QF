import H3V7N5QF.Paths

/-!
# An obstructed change is refused

Identifying `a` with `b` in what is given asserts `ara`. That change is not a
performed step. Adding a term, and removing `arb`, are performed steps, so
the alternative does not stop at the identification.
-/

namespace Seed.Twentyfirst

open Seed

theorem no_step_to_illegal {s t : St} (hs : s.Legal) (ht : ¬ t.Legal) : ¬ Step s t :=
  fun h => ht (h.legal hs)

theorem identify_given_illegal : ¬ (givenA.identify 0 1).Legal := by
  intro h
  exact h 0 (by decide : (0, 0) ∈ (givenA.identify 0 1).A)

theorem identify_given_refused : ¬ Step givenA (givenA.identify 0 1) :=
  no_step_to_illegal givenA_legal identify_given_illegal

theorem refusal_continues_by_a_term : Step givenA (givenA.addTerm 2) :=
  Step.addTerm givenA 2 (by decide)

theorem refusal_continues_by_removal : Step givenA (givenA.remove (0, 1)) :=
  Step.remove givenA (0, 1) (by decide)

end Seed.Twentyfirst
