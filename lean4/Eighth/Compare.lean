import Eighth.Reach

/-!
# What survives the second relation

The task's rule 5 asks, for every result of an earlier derivation that is used,
whether its proof still holds from the eighth seed — in particular whether it
survives the second relation, per relation, jointly, or not.  This file states
the answer in Lean for the sixth derivation's headline results, through the
embedding `MSt.ofR` and the projections `DSt.proj`:

* **the results extend**: every result of the sixth seed is a result of the
  eighth asserting nothing with `s`, at the same round (`results_ofR_A`,
  `_B`); the results asserting nothing with `s` are exactly the sixth's
  (`results_r_iff`); the eighth has results the sixth has not (`results_grow`);
  the `r` part and the `s` part of every result are each a result of the sixth
  (`proj_results`), and any two such parts on the same terms make a result
  (`results_pair`, in `Eighth/Reach.lean`): **jointly free**;
* **the reachability criterion survives** as a statement about the `r` part's
  names (`criterion_survives`, `reach8_iff_r`): the `s` part imposes nothing;
* **the cost survives per relation and adds up** (`cost_survives`,
  `costA8_eq`): the sixth's fewest changes to the `r` part plus the `s` total;
  on the results asserting nothing with `s` it is the sixth's as it stands
  (`fewest_changes8_of_r_A`), and a state whose `r` part is what is given
  costs exactly its `s` total (`s_costs_its_total`);
* **the interaction** is through the terms and the names alone: an
  identification merges both relations (`proj_identify`), a rewriting rewrites
  both (`Eighth/Rename.lean`); an assertion of one relation leaves the other
  part as it is (`Step8.proj_self`); the sixth's one irreversible change (the
  merge of the names) is the eighth's (`Reach8.names_stay_merged`).
-/

namespace Seed.Eighth

open Seed Seed.Fourth Seed.Fifth Seed.Sixth DSt

/-- Every result of the sixth seed is a result of the eighth, with nothing in `s`, at the same round. -/
theorem results_ofR_A {g : MSt} {n : ℕ} (h : Reach6 givenA4 g n) : Reach8 givenA8 g.ofR n := h.ofR

theorem results_ofR_B {g : MSt} {n : ℕ} (h : Reach6 givenB4 g n) : Reach8 givenB8 g.ofR n := h.ofR

/-- Among the states asserting nothing with `s`, the results of the eighth seed are the sixth's. -/
theorem results_r_iff (g : DSt) (hs : g.NothingInS) :
    (∃ n, Reach8 givenA8 g n) ↔ ∃ n, Reach6 givenA4 (g.proj false) n := by
  rw [result8_iff_A, result6_iff_A]
  constructor
  · exact fun hw => hw.1
  · intro hw
    refine ⟨hw, ?_⟩
    have e : g.proj true = ⟨g.T, fun _ => 0, g.a, g.b⟩ := by
      apply MSt.ext
      · rfl
      · funext p
        exact hs p
      · rfl
      · rfl
    rw [e]
    exact ⟨fun _ h => absurd rfl h, hw.2.1, hw.2.2⟩

/-- The eighth seed has results the sixth has not: `asb` added to what is given. -/
theorem results_grow :
    Reach8 givenA8 (givenA8.addAssertion true 0 1) 1 ∧
      ∀ (m : MSt) (n : ℕ), Reach6 givenA4 m n → m.ofR ≠ givenA8.addAssertion true 0 1 := by
  refine ⟨s_is_a_result.1, fun m _ _ e => s_is_a_result.2 ?_⟩
  rw [← e]
  exact ofR_nothing_in_s m

/-- The `r` part and the `s` part of every result are each a result of the sixth seed. -/
theorem proj_results {g : DSt} {n : ℕ} (h : Reach8 givenA8 g n) (q : Rel) :
    ∃ m, Reach6 givenA4 (g.proj q) m :=
  (result6_iff_A _).2 (wf_proj (h.wf givenA8_wf) q)

/-- The reachability criterion survives: the names of the `r` part decide, and reachability of
two-relation states is reachability of their `r` parts. -/
theorem criterion_survives {s g : DSt} (hs : s.WF) (hgw : g.WF) :
    ((∃ n, Reach8 s g n) ↔ (s.a = s.b → g.a = g.b)) ∧
      ((∃ n, Reach8 s g n) ↔ ∃ n, Reach6 (s.proj false) (g.proj false) n) :=
  ⟨reach8_iff hs hgw, reach8_iff_r hs hgw⟩

/-- The cost survives per relation and adds up: the fewest changes to a result is the sixth's
fewest changes to its `r` part plus its `s` total. -/
theorem cost_survives {g : DSt} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1 ∨ g.b = 0) :
    (∃ n, Reach8 givenA8 g n ∧ n + 3 = costA6 (g.proj false) + (g.proj true).total) ∧
      ∀ n, Reach8 givenA8 g n → costA6 (g.proj false) + (g.proj true).total ≤ n + 3 := by
  rw [← costA8_eq]
  exact fewest_changes8_A hgw ha hb

/-- Two results with the same `r` part reach each other, whatever their `s` parts. -/
theorem same_r_part_mutual {s g : DSt} (hs : s.WF) (hgw : g.WF) (h : s.proj false = g.proj false) :
    (∃ n, Reach8 s g n) ∧ ∃ n, Reach8 g s n := by
  have ha : s.a = g.a := congrArg MSt.a h
  have hb : s.b = g.b := congrArg MSt.b h
  exact ⟨reach8_of_names hs hgw (fun e => by rw [← ha, ← hb]; exact e),
    reach8_of_names hgw hs (fun e => by rw [ha, hb]; exact e)⟩

/-- The interaction: an identification merges both relations, and an assertion of one relation
leaves the other part as it is. -/
theorem interaction (s : DSt) (u v x y : ℕ) (q : Rel) :
    (s.identify u v).proj false = (s.proj false).identify u v ∧
      (s.identify u v).proj true = (s.proj true).identify u v ∧
      (s.addAssertion q x y).proj (!q) = s.proj (!q) :=
  ⟨rfl, rfl, proj_addAssertion_other s (not_ne q) x y⟩

end Seed.Eighth
