import Seventh.Cost

/-!
# Reachability from nothing: a term decides

Derived here:
* **sufficiency**: from a well-formed state with a term every well-formed state
  with a term is reached (`reach7_of_nonempty`): the sixth's path
  (`reach6_of_names` — remove everything, identify every other term into one,
  add what the target has) through `name`, with both names on one term of the
  start and one term of the target, so that the sixth's condition on the names
  holds trivially; from the empty state every well-formed state is reached by
  additions (`reach7_by_additions`);
* **the criterion**: a well-formed state is reachable from a well-formed state
  exactly when it has a term or the start is empty (`reach7_iff`) — the
  sixth's names criterion with the names gone and the empty state added;
* **the results are every well-formed state**, the empty one included
  (`result7_iff`, `empty_is_a_result`);
* reachability is mutual among the states with a term (`reach7_symm`), one-way
  out of the empty state (`empty_never_returned`, `no_cycle_at_empty`); any two
  results are comparable (`reach7_total`); every state with a term reaches
  itself in two changes (`cycle2_7`, the sixth's through `name`), so the
  lengths of the sequences reaching it are unbounded (`Reach7.unbounded`);
* one-way reachability among the states with a term is refuted by witnesses
  (`no_return_fails7`, `antisymm_fails7`, `length_not_unique7`).
-/

namespace Seed.Seventh

open Seed Seed.Fourth Seed.Fifth Seed.Sixth NSt

/-- **Sufficiency among the states with a term**: the sixth's `reach6_of_names` through `name`. -/
theorem reach7_of_nonempty {s g : NSt} (hs : s.WF) (hg : g.WF) (hsne : s.T.Nonempty)
    (hgne : g.T.Nonempty) : ∃ n, Reach7 s g n := by
  obtain ⟨c, hc⟩ := hsne
  obtain ⟨c', hc'⟩ := hgne
  obtain ⟨n, hn⟩ := reach6_of_names (name_wf hs hc) (name_wf hg hc') (fun _ => rfl)
  exact ⟨n, hn.forget⟩

/-- **Reachability is decided by having a term.**  A well-formed state is reachable from a
well-formed state exactly when it has a term, or the start is empty. -/
theorem reach7_iff {s g : NSt} (hs : s.WF) (hg : g.WF) :
    (∃ n, Reach7 s g n) ↔ (s.T.Nonempty → g.T.Nonempty) := by
  constructor
  · rintro ⟨n, h⟩ hsne
    exact h.nonempty hsne
  · intro h
    by_cases hsne : s.T.Nonempty
    · exact reach7_of_nonempty hs hg hsne (h hsne)
    · rw [eq_empty_of_wf hs hsne]
      exact ⟨_, reach7_by_additions hg⟩

/-- **The results are every well-formed state.** -/
theorem result7_iff (g : NSt) : (∃ n, Reach7 empty g n) ↔ g.WF :=
  ⟨fun ⟨_, h⟩ => h.wf empty_wf, fun hw => ⟨_, reach7_by_additions hw⟩⟩

/-- The empty state is a result: round 0. -/
theorem empty_is_a_result : Reach7 empty empty 0 := Reach7.refl _

/-- Reachability is mutual among the states with a term. -/
theorem reach7_symm {s g : NSt} (hs : s.WF) (hg : g.WF) (hsne : s.T.Nonempty) (hgne : g.T.Nonempty) :
    (∃ n, Reach7 s g n) ∧ ∃ n, Reach7 g s n :=
  ⟨reach7_of_nonempty hs hg hsne hgne, reach7_of_nonempty hg hs hgne hsne⟩

/-- Any two results are comparable: one of them reaches the other. -/
theorem reach7_total {s g : NSt} (hs : s.WF) (hg : g.WF) :
    (∃ n, Reach7 s g n) ∨ ∃ n, Reach7 g s n := by
  by_cases hsne : s.T.Nonempty
  · by_cases hgne : g.T.Nonempty
    · exact Or.inl (reach7_of_nonempty hs hg hsne hgne)
    · exact Or.inr ((reach7_iff hg hs).2 (fun h => absurd h hgne))
  · exact Or.inl ((reach7_iff hs hg).2 (fun h => absurd h hsne))

/-- One-way out of the empty state: no state with a term reaches it. -/
theorem empty_never_returned {s : NSt} (hs : s.WF) (hne : s.T.Nonempty) (n : ℕ) :
    ¬ Reach7 s empty n := by
  intro h
  obtain ⟨rfl, _⟩ := (reach7_empty_iff hs).1 h
  exact empty_not_nonempty hne

/-- The empty state has no cycle: the only sequence from it to itself is the empty one. -/
theorem no_cycle_at_empty {n : ℕ} (h : Reach7 empty empty n) : n = 0 :=
  ((reach7_empty_iff empty_wf).1 h).2

/-! ## Every state with a term reaches itself in two changes -/

theorem cycle2_7 {s : NSt} (hw : s.WF) (hne : s.T.Nonempty) : Reach7 s s 2 := by
  obtain ⟨c, hc⟩ := hne
  exact (cycle2_6 (name_wf hw hc) ⟨c, hc⟩).forget

theorem Reach7.cycles {s : NSt} (hw : s.WF) (hne : s.T.Nonempty) (k : ℕ) : Reach7 s s (2 * k) := by
  induction k with
  | zero => exact Reach7.refl s
  | succ k ih =>
    have := ih.trans (cycle2_7 hw hne)
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    exact this

/-- The lengths of the sequences reaching a result from a state with a term are unbounded. -/
theorem Reach7.unbounded {s t : NSt} {n : ℕ} (h : Reach7 s t n) (hw : s.WF) (hne : s.T.Nonempty)
    (k : ℕ) : Reach7 s t (2 * k + n) :=
  (Reach7.cycles hw hne k).trans h

/-! ## One-way reachability among the states with a term is refuted -/

/-- The one-term state: a term added to the empty state. -/
def oneTerm7 : NSt := empty.addTerm 0

/-- The two-term state asserting nothing. -/
def twoTerms7 : NSt := oneTerm7.addTerm 1

theorem mem_oneTerm7_T (x : ℕ) : x ∈ oneTerm7.T ↔ x = 0 := by simp [oneTerm7, NSt.addTerm, empty]

theorem mem_twoTerms7_T (x : ℕ) : x ∈ twoTerms7.T ↔ x = 1 ∨ x = 0 := by
  simp [twoTerms7, oneTerm7, NSt.addTerm, empty]

theorem oneTerm7_wf : oneTerm7.WF := addTerm_wf empty_wf 0

/-- Identifying the two terms of the two-term state gives the one-term state back. -/
theorem identify_twoTerms7 : twoTerms7.identify 0 1 = oneTerm7 := by
  apply NSt.ext
  · show (insert 1 (insert 0 ∅) : Finset ℕ).erase 1 = insert 0 ∅
    decide
  · funext p
    simp [NSt.identify, twoTerms7, oneTerm7, NSt.addTerm, empty]

theorem no_return_fails7 : Reach7 oneTerm7 twoTerms7 1 ∧ Reach7 twoTerms7 oneTerm7 1 := by
  constructor
  · exact Reach7.single (Step7.addTerm oneTerm7 1 (by simp [mem_oneTerm7_T]))
  · have st : Step7 twoTerms7 (twoTerms7.identify 0 1) :=
      Step7.identify twoTerms7 0 1 ((mem_twoTerms7_T 0).2 (Or.inr rfl)) ((mem_twoTerms7_T 1).2 (Or.inl rfl))
        (by omega)
    rw [identify_twoTerms7] at st
    exact Reach7.single st

theorem antisymm_fails7 :
    oneTerm7 ≠ twoTerms7 ∧ (∃ n, Reach7 oneTerm7 twoTerms7 n) ∧ ∃ n, Reach7 twoTerms7 oneTerm7 n := by
  refine ⟨?_, ⟨1, no_return_fails7.1⟩, ⟨1, no_return_fails7.2⟩⟩
  intro h
  have h1 : (1 : ℕ) ∉ oneTerm7.T := by simp [mem_oneTerm7_T]
  have h2 : (1 : ℕ) ∈ twoTerms7.T := (mem_twoTerms7_T 1).2 (Or.inl rfl)
  rw [h] at h1
  exact h1 h2

theorem length_not_unique7 : Reach7 oneTerm7 oneTerm7 0 ∧ Reach7 oneTerm7 oneTerm7 2 :=
  ⟨Reach7.refl _, no_return_fails7.1.trans no_return_fails7.2⟩

end Seed.Seventh
