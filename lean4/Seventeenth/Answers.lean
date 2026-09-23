import Seventeenth.Perform
import H3V7N5QF.Answers

/-!
# Answers, re-checked once an obstructed change may be performed

Removing the assertions between two terms and then identifying them ends at
the same state as identifying them and then removing the `xrx` that results.
The base proves the equality (`remove_obstruction_first_or_last`). The
intermediate of the second path asserts `xrx`, so the equality does not show
that intermediate is not a result. A refused addition of `xrx` is not an
unobstructed step, and its outcome is not reached by unobstructed steps.
-/

namespace Seed.Seventeenth

open Seed St

theorem remove_first_eq_perform_first {s : St} (hs : s.Legal) (u v : ℕ) :
    ((s.remove (u, v)).remove (v, u)).identify u v = (s.identify u v).remove (u, u) :=
  remove_obstruction_first_or_last hs u v

theorem perform_first_givenA :
    ReachAll givenA ((givenA.identify 0 1).remove (0, 0)) 2 := by
  have hmem : (0, 0) ∈ (givenA.identify 0 1).A := by
    rw [identify_givenA_eq]
    simp [oneLoop]
  have st : Step17 (givenA.identify 0 1) ((givenA.identify 0 1).remove (0, 0)) :=
    Step17.remove _ (0, 0) hmem
  exact ReachAll.step identify_givenA_reach st

theorem perform_first_intermediate_has_xrx : HasXrx (givenA.identify 0 1) :=
  mergedA_hasXrx

theorem perform_first_not_a_base_step :
    ¬ (Step17.identify givenA 0 1 (by simp [givenA]) (by simp [givenA]) (by decide)).unobstructed := by
  intro hu
  exact hu (by simp [Step17.obstructedM1, givenA])

/-- Refusal does not enter the addition of `ara`: that step is obstructed, and
no unobstructed sequence from what is given reaches its outcome. -/
theorem refusal_does_not_enter {n : ℕ} :
    ¬ (Step17.addAssertion givenA 0 0 (by simp [givenA]) (by simp [givenA])
        (by simp [givenA])).unobstructed ∧
      ¬ Reach17 givenA (givenA.addAssertion 0 0) n :=
  ⟨fun hu => hu rfl, add_ara_not_unobstructed⟩

end Seed.Seventeenth
