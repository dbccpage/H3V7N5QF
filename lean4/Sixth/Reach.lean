import Sixth.Cost

/-!
# Reachability under the sixth seed: the names still decide

Derived here:
* **the criterion survives**: a well-formed state `g` is reachable from a well-formed
  state `s` exactly when the names, if one term in `s`, are one term in `g`
  (`reach6_iff`) — the fifth's `reach5_iff` with "legal" dropped from `g`.  The
  proof is the fifth's path (remove everything, identify every other term into `a`,
  move the names, then add), whose pieces `reach5_clear`, `reach5_collapse`,
  `move_a_pair`, `move_b_pair`, `two_names_to`, `merge_names`, `move_one` mention no
  legality and are used through the embedding, with the addition path replaced by
  `reach6_of_contains`;
* **the results are every well-formed state** (`result6_iff_A`, `result6_iff_B`):
  the states asserting some `xrx` are results like the others (`xrx_is_a_result`,
  `loopState_is_a_result`);
* reachability is mutual within the two classes (`reach6_symm`), one-way between them
  (`merged_never_apart6`, `loopState_never_apart`); every result with `a ≠ b`
  reaches what is given (`reach6_back_A`, `_B`); any two results are comparable
  (`reach6_total`); every result reaches itself in two changes (`cycle2_6`), so the
  lengths of the sequences reaching it are unbounded (`Reach6.unbounded`);
* the fifth's refutations of one-way reachability survive through the embedding
  (`no_return_fails6`, `antisymm_fails6`, `length_not_unique6`); containment is still
  sufficient and still not necessary (`contains4_reach6`, `criterion_not_containment`).
-/

namespace Seed.Sixth

open Seed Seed.Fourth Seed.Fifth MSt

/-- **Sufficiency.**  From a well-formed state whose names, if one term, are one term in
the target: remove everything, identify every other term into `a`, move the names,
then add what the target has — `xrx` like any pair. -/
theorem reach6_of_names {s g : MSt} (hs : s.WF) (hgw : g.WF) (h : s.a = s.b → g.a = g.b) :
    ∃ n, Reach6 s g n := by
  have r1 := (reach5_clear s.total s hs rfl).toReach6
  have hK : ({s.a, s.b} : Finset ℕ) ⊆ (cleared s).T := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hs.2.1
    · exact hs.2.2
  have r2 := (reach5_collapse _ (cleared s) {s.a, s.b} (cleared_wf hs) (fun _ => rfl) hK
    (by simp [cleared]) (by simp [cleared]) rfl).toReach6
  have r3 : ∃ m, Reach6 ⟨{s.a, s.b}, fun _ => 0, s.a, s.b⟩ ⟨{g.a, g.b}, fun _ => 0, g.a, g.b⟩ m := by
    by_cases hab : s.a = s.b
    · have hgab := h hab
      rw [hab, hgab]
      obtain ⟨m, hm⟩ := move_one s.b g.b
      exact ⟨m, hm.toReach6⟩
    · by_cases hgab : g.a = g.b
      · rw [hgab]
        obtain ⟨m, hm⟩ := move_one s.a g.b
        exact ⟨1 + m, ((merge_names hab).trans hm).toReach6⟩
      · exact ⟨8, (two_names_to hab hgab).toReach6⟩
  obtain ⟨m, r3⟩ := r3
  have hc : Contains4 ⟨{g.a, g.b}, fun _ => 0, g.a, g.b⟩ g := by
    refine ⟨fun t ht => ?_, fun _ => Nat.zero_le _, rfl, rfl⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hgw.2.1
    · exact hgw.2.2
  obtain ⟨k, r4, _⟩ := reach6_of_contains (pair_wf g.a g.b) hgw hc
  exact ⟨_, ((r1.trans r2).trans r3).trans r4⟩

/-- **Reachability is decided by the names.**  A well-formed state is reachable from a
well-formed state exactly when the names, if one term at the start, are one term at
the end. -/
theorem reach6_iff {s g : MSt} (hs : s.WF) (hgw : g.WF) :
    (∃ n, Reach6 s g n) ↔ (s.a = s.b → g.a = g.b) :=
  ⟨fun ⟨_, h⟩ hab => h.names_stay_merged hab, reach6_of_names hs hgw⟩

/-- **The results, `bra` not asserted to begin with:** every well-formed state. -/
theorem result6_iff_A (g : MSt) : (∃ n, Reach6 givenA4 g n) ↔ g.WF :=
  ⟨fun ⟨_, h⟩ => h.wf givenA4_wf,
    fun hgw => reach6_of_names givenA4_wf hgw (fun h => absurd h (by rw [givenA4_a, givenA4_b]; omega))⟩

/-- **The results, `bra` asserted to begin with:** the same. -/
theorem result6_iff_B (g : MSt) : (∃ n, Reach6 givenB4 g n) ↔ g.WF :=
  ⟨fun ⟨_, h⟩ => h.wf givenB4_wf,
    fun hgw => reach6_of_names givenB4_wf hgw (fun h => absurd h (by rw [givenB4_a, givenB4_b]; omega))⟩

/-- A state asserting some `xrx` is a result: `ara` added to what is given, one change. -/
theorem xrx_is_a_result :
    Reach6 givenA4 (givenA4.addAssertion 0 0) 1 ∧ ¬ (givenA4.addAssertion 0 0).Legal :=
  ⟨Reach6.single (Step6.addAssertion _ 0 0 ((mem_givenA4_T 0).2 (Or.inl rfl)) ((mem_givenA4_T 0).2 (Or.inl rfl))),
    adding_xrx_always_obstructed4 givenA4 0⟩

/-- The one-term state asserting `0r0` `k` times is a result, for every `k`. -/
theorem loopState_is_a_result (k : ℕ) : ∃ n, Reach6 givenA4 (loopState k) n :=
  (result6_iff_A _).2 (loopState_wf k)

/-- Reachability is mutual within the two classes. -/
theorem reach6_symm {s g : MSt} (hsw : s.WF) (hgw : g.WF) (h : g.a = g.b → s.a = s.b) :
    ∃ n, Reach6 g s n :=
  reach6_of_names hgw hsw h

/-- Every result with `a` and `b` two terms reaches what is given. -/
theorem reach6_back_A {g : MSt} (hgw : g.WF) (hne : g.a ≠ g.b) : ∃ n, Reach6 g givenA4 n :=
  reach6_of_names hgw givenA4_wf (fun h => absurd h hne)

theorem reach6_back_B {g : MSt} (hgw : g.WF) (hne : g.a ≠ g.b) : ∃ n, Reach6 g givenB4 n :=
  reach6_of_names hgw givenB4_wf (fun h => absurd h hne)

/-- Any two results are comparable: one of them reaches the other. -/
theorem reach6_total {s g : MSt} (hsw : s.WF) (hgw : g.WF) :
    (∃ n, Reach6 s g n) ∨ ∃ n, Reach6 g s n := by
  by_cases hab : s.a = s.b
  · by_cases hgab : g.a = g.b
    · exact Or.inl (reach6_of_names hsw hgw (fun _ => hgab))
    · exact Or.inr (reach6_of_names hgw hsw (fun h => absurd h hgab))
  · exact Or.inl (reach6_of_names hsw hgw (fun h => absurd h hab))

/-- One-way between the classes: from the one-term state, what is given is never reached. -/
theorem merged_never_apart6 (n : ℕ) : ¬ Reach6 oneTerm4 givenA4 n := by
  intro h
  have := h.names_stay_merged rfl
  rw [givenA4_a, givenA4_b] at this
  omega

/-- Nor from the one-term state asserting `0r0` however often. -/
theorem loopState_never_apart (k n : ℕ) : ¬ Reach6 (loopState k) givenA4 n := by
  intro h
  have := h.names_stay_merged rfl
  rw [givenA4_a, givenA4_b] at this
  omega

/-! ## Every state reaches itself in two changes -/

theorem cycle2_6 {s : MSt} (hw : s.WF) (hne : s.T.Nonempty) : Reach6 s s 2 := (cycle2 hw hne).toReach6

theorem Reach6.cycles {s : MSt} (hw : s.WF) (hne : s.T.Nonempty) (k : ℕ) : Reach6 s s (2 * k) := by
  induction k with
  | zero => exact Reach6.refl s
  | succ k ih =>
    have := ih.trans (cycle2_6 hw hne)
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    exact this

/-- The lengths of the sequences reaching a result are unbounded. -/
theorem Reach6.unbounded {s t : MSt} {n : ℕ} (h : Reach6 s t n) (hw : s.WF) (hne : s.T.Nonempty)
    (k : ℕ) : Reach6 s t (2 * k + n) :=
  (Reach6.cycles hw hne k).trans h

/-! ## One-way reachability stays refuted; containment stays sufficient, not necessary -/

theorem no_return_fails6 : Reach6 givenA4 givenB4 1 ∧ Reach6 givenB4 givenA4 1 :=
  ⟨no_return_fails.1.toReach6, no_return_fails.2.toReach6⟩

theorem antisymm_fails6 :
    givenA4 ≠ givenB4 ∧ (∃ n, Reach6 givenA4 givenB4 n) ∧ ∃ m, Reach6 givenB4 givenA4 m :=
  ⟨antisymm_fails.1, ⟨1, no_return_fails6.1⟩, ⟨1, no_return_fails6.2⟩⟩

theorem length_not_unique6 : Reach6 givenA4 givenA4 0 ∧ Reach6 givenA4 givenA4 2 :=
  ⟨Reach6.refl _, no_return_fails6.1.trans no_return_fails6.2⟩

theorem contains4_reach6 {s g : MSt} (hs : s.WF) (hgw : g.WF) (h : Contains4 s g) :
    ∃ n, Reach6 s g n :=
  let ⟨n, hn, _⟩ := reach6_of_contains hs hgw h
  ⟨n, hn⟩

theorem criterion_not_containment : ¬ Contains4 givenB4 givenA4 ∧ Reach6 givenB4 givenA4 1 :=
  ⟨criterion_fails.1, no_return_fails6.2⟩

end Seed.Sixth
