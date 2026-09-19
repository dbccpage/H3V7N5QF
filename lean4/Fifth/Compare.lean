import Fifth.Answers

/-!
# What survives removal and identification

The task's rule 5 asks, for every result of an earlier derivation that is used,
whether its proof still holds from the fifth seed.  This file states the answer in
Lean for the fourth derivation's four headline results, on the fourth's own results
(the states containing what is given):

* **the results extend**: every sequence of the fourth seed is a sequence of the
  fifth (`Reach4.toReach5`), so every result of the fourth is a result of the fifth
  at the same round (`results_extend_A`, `_B`); and the fifth has results the fourth
  does not — the given terms with nothing asserted, reached in one change
  (`results_grow`);
* **the cost survives only on the fourth's results**: there the fewest changes is
  the size difference (`fewest_changes5_of_contains_A`, `_B`), while in general it is
  the size difference plus twice the destroyed givens (`fewest_changes5_A`, `_B`) and
  the size can fall (`size_can_fall`);
* **the reachability criterion does not survive**: containment is still sufficient
  (`contains4_reach5`) but no longer necessary — the beginning with `bra` reaches the
  one without, which it does not contain (`criterion_fails`); the criterion is now
  the names (`reach5_iff`);
* **one-way reachability does not survive**: the two beginnings reach each other
  (`no_return_fails`, `antisymm_fails`), and a result is reached by sequences of
  different lengths (`length_not_unique`).
-/

namespace Seed.Fifth

open Seed Seed.Fourth MSt

/-- Every result of the fourth seed is a result of the fifth, at the same round. -/
theorem results_extend_A {g : MSt} {n : ℕ} (h : Reach4 givenA4 g n) : Reach5 givenA4 g n :=
  h.toReach5

theorem results_extend_B {g : MSt} {n : ℕ} (h : Reach4 givenB4 g n) : Reach5 givenB4 g n :=
  h.toReach5

/-- The fifth seed has results the fourth does not: the given terms with nothing
asserted, one change away, is no result of the fourth seed. -/
theorem results_grow :
    Reach5 givenA4 (givenA4.remove 0 1) 1 ∧ ∀ n, ¬ Reach4 givenA4 (givenA4.remove 0 1) n :=
  ⟨Reach5.single step_remove_arb, fun _ h => contains_fails h.contains⟩

/-- Containment is still sufficient for reachability (the fourth's additions are changes
of the fifth). -/
theorem contains4_reach5 {s g : MSt} (hs : s.WF) (hg : g.Legal) (hgw : g.WF)
    (h : Contains4 s g) : ∃ n, Reach5 s g n :=
  let ⟨n, hn, _⟩ := reach4_of_contains hs hg hgw h
  ⟨n, hn.toReach5⟩

/-- Containment is no longer necessary: the beginning with `bra` reaches the beginning
without it, which it does not contain. -/
theorem criterion_fails : ¬ Contains4 givenB4 givenA4 ∧ Reach5 givenB4 givenA4 1 :=
  ⟨fun h => by
      have := h.mult (1, 0)
      rw [givenB4_bra, givenA4_bra] at this
      omega,
    no_return_fails.2⟩

/-- On the fourth's results the fewest changes agree with the fourth's, but the fourth's
"every sequence has that length" fails on those very results. -/
theorem cost_survives_length_does_not :
    (∀ g : MSt, g.Legal → g.WF → Contains4 givenA4 g →
      (∃ n, Reach5 givenA4 g n ∧ n + 3 = g.size) ∧ ∀ n, Reach5 givenA4 g n → g.size ≤ n + 3) ∧
    (Reach5 givenA4 givenA4 0 ∧ Reach5 givenA4 givenA4 2) :=
  ⟨fun _ hg hgw h => fewest_changes5_of_contains_A hg hgw h, length_not_unique⟩

end Seed.Fifth
