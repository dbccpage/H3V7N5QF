import Sixth.Reach

/-!
# What survives once nothing is forbidden

The task's rule 5 asks, for every result of an earlier derivation that is used,
whether its proof still holds from the sixth seed.  This file states the answer in
Lean for the fifth derivation's headline results, and for the obstruction and answer
notions the sixth seed drops:

* **the results extend**: every sequence of the fifth seed is a sequence of the sixth
  (`Reach5.toReach6`), so every result of the fifth is a result of the sixth at the
  same round (`results_extend_A`, `_B`); the sixth has results the fifth has not
  (`results_grow`: `ara` added to what is given); the results are now every
  well-formed state (`results_are_every_wf_state`), and among the states asserting
  no `xrx` the two seeds have the same results (`legal_results_are_the_fifths`);
* **the reachability criterion survives** as it stands, without the legality
  hypothesis (`criterion_survives`);
* **the cost survives on the fifth's results and on every state with the names
  apart** (`cost_survives_on_legal`, `cost_survives_names_apart`) and fails with the
  names one term and `crc` asserted (`cost_fails_names_merged`: one change where the
  fifth's potential says three);
* **the obstruction notion is empty**: every attempt of the fifth seed is a change of
  the sixth and conversely (`nothing_obstructed`); the fifth's characterisation of
  the obstructed attempts survives as "which changes make some `xrx` asserted"
  (`Step6.not_legal_iff`, in `Sixth/Step.lean`);
* **the answer notion is gone**: the fifth's answer "remove the obstruction" for
  identifying `a` and `b` (remove the givens, then identify) and the direct
  identification are two sequences to two *different* results
  (`remove_answer_differs`); the fifth's `remove_obstruction_first_or_last5` fails
  without its legality hypothesis (`first_or_last_fails`).
-/

namespace Seed.Sixth

open Seed Seed.Fourth Seed.Fifth MSt

/-- Every result of the fifth seed is a result of the sixth, at the same round. -/
theorem results_extend_A {g : MSt} {n : ℕ} (h : Reach5 givenA4 g n) : Reach6 givenA4 g n :=
  h.toReach6

theorem results_extend_B {g : MSt} {n : ℕ} (h : Reach5 givenB4 g n) : Reach6 givenB4 g n :=
  h.toReach6

/-- The sixth seed has results the fifth has not: `ara` added to what is given, one
change away, is no result of the fifth seed. -/
theorem results_grow :
    Reach6 givenA4 (givenA4.addAssertion 0 0) 1 ∧ ∀ n, ¬ Reach5 givenA4 (givenA4.addAssertion 0 0) n :=
  ⟨xrx_is_a_result.1, fun _ h => adding_xrx_always_obstructed4 givenA4 0 (h.legal givenA4_legal)⟩

/-- The results are every well-formed state, with the names anywhere. -/
theorem results_are_every_wf_state (g : MSt) : (∃ n, Reach6 givenA4 g n) ↔ g.WF :=
  result6_iff_A g

/-- Among the states asserting no `xrx`, the results of the two seeds are the same. -/
theorem legal_results_are_the_fifths (g : MSt) (hg : g.Legal) :
    (∃ n, Reach6 givenA4 g n) ↔ ∃ n, Reach5 givenA4 g n := by
  rw [result6_iff_A, result5_iff_A]
  exact ⟨fun hw => ⟨hg, hw⟩, fun h => h.2⟩

/-- The reachability criterion survives: the names decide, for every well-formed target. -/
theorem criterion_survives {s g : MSt} (hs : s.WF) (hgw : g.WF) :
    (∃ n, Reach6 s g n) ↔ (s.a = s.b → g.a = g.b) :=
  reach6_iff hs hgw

/-- On the fifth's results the fifth's fewest changes survive. -/
theorem cost_survives_on_legal {g : MSt} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0)
    (hb : g.b = 1 ∨ g.b = 0) :
    (∃ n, Reach6 givenA4 g n ∧ n + 3 = costA5 g) ∧ ∀ n, Reach6 givenA4 g n → costA5 g ≤ n + 3 :=
  fewest_changes6_of_legal_A hg hgw ha hb

/-- With the names apart the fifth's fewest changes survive, `xrx` or not. -/
theorem cost_survives_names_apart {g : MSt} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1) :
    (∃ n, Reach6 givenA4 g n ∧ n + 3 = costA5 g) ∧ ∀ n, Reach6 givenA4 g n → costA5 g ≤ n + 3 :=
  fewest_changes6_apart_A hgw ha hb

/-- With the names one term and `crc` asserted the fifth's cost fails: one change where its
potential says three. -/
theorem cost_fails_names_merged :
    Reach6 givenA4 (givenA4.identify 0 1) 1 ∧ costA5 (givenA4.identify 0 1) = 6 ∧
      costA6 (givenA4.identify 0 1) = 4 :=
  fifth_potential_fails

/-- Nothing is obstructed: the attempts of the fifth seed are exactly the changes of the
sixth. -/
theorem nothing_obstructed (s t : MSt) : Try5 s t ↔ Step6 s t :=
  try5_iff_step6 s t

/-- The fifth's answer "remove the obstruction" (remove `arb` and `bra`, then identify:
the one-term state asserting nothing) and the direct identification (the one-term
state asserting `0r0` twice) are two sequences to two different results. -/
theorem remove_answer_differs :
    Reach6 givenB4 oneTerm4 3 ∧ Reach6 givenB4 (givenB4.identify 0 1) 1 ∧
      givenB4.identify 0 1 ≠ oneTerm4 := by
  refine ⟨givenB4_to_oneTerm4.toReach6, ?_, ?_⟩
  · exact Reach6.single (Step6.identify _ 0 1 ((mem_givenB4_T 0).2 (Or.inl rfl))
      ((mem_givenB4_T 1).2 (Or.inr rfl)) (by omega))
  · rw [identify_givenB4_eq]
    intro h
    have e := congrArg (fun s : MSt => s.M (0, 0)) h
    rw [loopState_M_self] at e
    simp [oneTerm4, ofSt_M, oneTerm] at e

/-- Two terms with `0r0` and `0r1` asserted once each, the names apart. -/
def witnessW : MSt := ⟨{0, 1}, fun p => if p = (0, 0) then 1 else if p = (0, 1) then 1 else 0, 0, 1⟩

/-- Removing the obstruction first, or identifying first and then lowering the resulting
`0r0` to zero, no longer give the same state: the second path also destroys the `0r0`
that was there before.  The fifth's `remove_obstruction_first_or_last5` needed
legality. -/
theorem first_or_last_fails :
    (lowered (lowered witnessW (0, 1)) (1, 0)).identify 0 1 ≠ lowered (witnessW.identify 0 1) (0, 0) := by
  intro h
  have e := congrArg (fun s : MSt => s.M (0, 0)) h
  rw [lowered_M_self] at e
  have h0 : (0 : ℕ) ∈ (lowered (lowered witnessW (0, 1)) (1, 0)).T := by simp [lowered, witnessW]
  have hge := identify_M_ge (lowered (lowered witnessW (0, 1)) (1, 0)) 0 1 h0 h0
  rw [merge_left, lowered_M_of_ne (lowered witnessW (0, 1)) (p := (1, 0)) (q := (0, 0)) (by decide),
    lowered_M_of_ne witnessW (p := (0, 1)) (q := (0, 0)) (by decide)] at hge
  have hw : witnessW.M (0, 0) = 1 := by simp [witnessW]
  omega

end Seed.Sixth
