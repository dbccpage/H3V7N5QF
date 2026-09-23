import H3V7N5QF.Paths

/-!
# The round counts changes

Removing `arb` is one change and adds fewer assertions than it removes.
Reaching the one-term state takes a further identification. That state adds
still less, and it is reached later. The number of terms and assertions added
is not the round.
-/

namespace Seed.Twentieth

open Seed

/-- Terms and assertions added to what is given, as a difference of sizes. -/
def addedCount (s : St) : Int :=
  (s.T.card + s.A.card : Int) - (givenA.T.card + givenA.A.card : Int)

/-- What is given with `arb` removed. -/
def cleared : St := ⟨{0, 1}, ∅, 0, 1⟩

theorem remove_eq_cleared : givenA.remove (0, 1) = cleared := by decide

theorem cleared_step : Step givenA cleared :=
  remove_eq_cleared ▸ Step.remove givenA (0, 1) (by decide)

theorem reach_cleared : Reach givenA cleared 1 :=
  Reach.step (Reach.refl givenA) cleared_step

theorem added_oneTerm : addedCount oneTerm = -2 := by decide

theorem added_cleared : addedCount cleared = -1 := by decide

/-- Fewer additions, and more changes. -/
theorem additions_diverge :
    addedCount oneTerm < addedCount cleared ∧ Reach givenA cleared 1 ∧ Reach givenA oneTerm 2 := by
  refine ⟨?_, reach_cleared, givenA_to_oneTerm⟩
  rw [added_oneTerm, added_cleared]
  omega

end Seed.Twentieth
