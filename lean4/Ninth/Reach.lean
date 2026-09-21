import Ninth.Cost

/-!
# Reachability from nothing with two relations: a term decides

Derived here:
* **sufficiency**: from a well-formed state with a term every well-formed state
  with a term is reached (`reach9_of_nonempty`): the eighth's path
  (`reach8_of_names` — clear `s`, the sixth's path on the `r` part, add the
  target's `s` assertions) through the naming map, with both names on one term
  of the start and one term of the target, so that the eighth's condition on
  the names holds trivially; from the empty state every well-formed state is
  reached by additions (`reach9_by_additions`);
* **the criterion**: a well-formed state is reachable from a well-formed state
  exactly when it has a term or the start is empty (`reach9_iff`) — the
  seventh's criterion on the terms the two relations share; the eighth's "the
  `s` part imposes nothing" survives, and so does its mirror: the `r` part
  imposes nothing either;
* **the results are every well-formed two-relation state**, the empty one
  included (`result9_iff`, `empty9_is_a_result`), and they are **jointly
  free**: any two well-formed parts on the same terms make a result
  (`results_pair9`);
* reachability is mutual among the states with a term (`reach9_symm`), one-way
  out of the empty state (`empty9_never_returned`, `no_cycle_at_empty9`); any
  two results are comparable (`reach9_total`); every state with a term reaches
  itself in two changes (`cycle2_9`, the eighth's through the naming map), so
  the lengths of the sequences reaching it are unbounded (`Reach9.unbounded`);
* the exchange of the relations keeps reachability (`reach9_swap`) and carries
  results to results (`result9_swap`);
* one-way reachability among the states with a term is refuted by witnesses
  (`no_return_fails9`, `antisymm_fails9`, `length_not_unique9`).
-/

namespace Seed.Ninth

open Seed Seed.Fourth Seed.Fifth Seed.Sixth Seed.Seventh Seed.Eighth NDSt

/-- **Sufficiency among the states with a term**: the eighth's `reach8_of_names` through the
naming map. -/
theorem reach9_of_nonempty {s g : NDSt} (hs : s.WF) (hg : g.WF) (hsne : s.T.Nonempty)
    (hgne : g.T.Nonempty) : ∃ n, Reach9 s g n := by
  obtain ⟨c, hc⟩ := hsne
  obtain ⟨c', hc'⟩ := hgne
  obtain ⟨n, hn⟩ := reach8_of_names (name9_wf hs hc) (name9_wf hg hc') (fun _ => rfl)
  exact ⟨n, hn.forget⟩

/-- **Reachability is decided by having a term.**  A well-formed state is reachable from a
well-formed state exactly when it has a term, or the start is empty. -/
theorem reach9_iff {s g : NDSt} (hs : s.WF) (hg : g.WF) :
    (∃ n, Reach9 s g n) ↔ (s.T.Nonempty → g.T.Nonempty) := by
  constructor
  · rintro ⟨n, h⟩ hsne
    exact h.nonempty hsne
  · intro h
    by_cases hsne : s.T.Nonempty
    · exact reach9_of_nonempty hs hg hsne (h hsne)
    · rw [eq_empty9_of_wf hs hsne]
      exact ⟨_, reach9_by_additions hg⟩

/-- **The results are every well-formed state.** -/
theorem result9_iff (g : NDSt) : (∃ n, Reach9 empty9 g n) ↔ g.WF :=
  ⟨fun ⟨_, h⟩ => h.wf empty9_wf, fun hw => ⟨_, reach9_by_additions hw⟩⟩

/-- The empty state is a result: round 0. -/
theorem empty9_is_a_result : Reach9 empty9 empty9 0 := Reach9.refl _

/-- **The results are jointly free**: any well-formed `r` part and `s` part on the same terms
make a result. -/
theorem results_pair9 {m m' : NSt} (hm : m.WF) (hm' : m'.WF) (hT : m'.T = m.T) :
    ∃ n, Reach9 empty9 ⟨m.T, fun q => match q with | false => m.M | true => m'.M⟩ n := by
  apply (result9_iff _).2
  refine ⟨hm, ?_⟩
  show (⟨m.T, m'.M⟩ : NSt).WF
  rw [← hT]
  exact hm'

/-- Reachability is mutual among the states with a term. -/
theorem reach9_symm {s g : NDSt} (hs : s.WF) (hg : g.WF) (hsne : s.T.Nonempty) (hgne : g.T.Nonempty) :
    (∃ n, Reach9 s g n) ∧ ∃ n, Reach9 g s n :=
  ⟨reach9_of_nonempty hs hg hsne hgne, reach9_of_nonempty hg hs hgne hsne⟩

/-- Any two results are comparable: one of them reaches the other. -/
theorem reach9_total {s g : NDSt} (hs : s.WF) (hg : g.WF) :
    (∃ n, Reach9 s g n) ∨ ∃ n, Reach9 g s n := by
  by_cases hsne : s.T.Nonempty
  · by_cases hgne : g.T.Nonempty
    · exact Or.inl (reach9_of_nonempty hs hg hsne hgne)
    · exact Or.inr ((reach9_iff hg hs).2 (fun h => absurd h hgne))
  · exact Or.inl ((reach9_iff hs hg).2 (fun h => absurd h hsne))

/-- One-way out of the empty state: no state with a term reaches it. -/
theorem empty9_never_returned {s : NDSt} (hs : s.WF) (hne : s.T.Nonempty) (n : ℕ) :
    ¬ Reach9 s empty9 n := by
  intro h
  obtain ⟨rfl, _⟩ := (reach9_empty_iff hs).1 h
  exact empty9_not_nonempty hne

/-- The empty state has no cycle: the only sequence from it to itself is the empty one. -/
theorem no_cycle_at_empty9 {n : ℕ} (h : Reach9 empty9 empty9 n) : n = 0 :=
  ((reach9_empty_iff empty9_wf).1 h).2

/-! ## The exchange of the relations keeps reachability -/

theorem reach9_swap {s g : NDSt} {n : ℕ} (h : Reach9 s g n) : Reach9 s.swap g.swap n := h.swap

/-- The exchange carries results to results, at the same round. -/
theorem result9_swap {g : NDSt} {n : ℕ} (h : Reach9 empty9 g n) : Reach9 empty9 g.swap n := by
  have := h.swap
  rwa [swap9_empty] at this

/-! ## Every state with a term reaches itself in two changes -/

theorem cycle2_9 {s : NDSt} (hne : s.T.Nonempty) : Reach9 s s 2 := by
  obtain ⟨c, hc⟩ := hne
  exact (cycle2_8 (s := s.name c) ⟨c, hc⟩).forget

theorem Reach9.cycles {s : NDSt} (hne : s.T.Nonempty) (k : ℕ) : Reach9 s s (2 * k) := by
  induction k with
  | zero => exact Reach9.refl s
  | succ k ih =>
    have := ih.trans (cycle2_9 hne)
    rw [show 2 * (k + 1) = 2 * k + 2 by omega]
    exact this

/-- The lengths of the sequences reaching a result from a state with a term are unbounded. -/
theorem Reach9.unbounded {s t : NDSt} {n : ℕ} (h : Reach9 s t n) (hne : s.T.Nonempty) (k : ℕ) :
    Reach9 s t (2 * k + n) :=
  (Reach9.cycles hne k).trans h

/-! ## One-way reachability among the states with a term is refuted -/

/-- The two-term state asserting nothing. -/
def twoTerms9 : NDSt := oneTerm9.addTerm 1

theorem mem_twoTerms9_T (x : ℕ) : x ∈ twoTerms9.T ↔ x = 1 ∨ x = 0 := by
  simp [twoTerms9, oneTerm9, NDSt.addTerm, empty9]

/-- Identifying the two terms of the two-term state gives the one-term state back. -/
theorem identify_twoTerms9 : twoTerms9.identify 0 1 = oneTerm9 := by
  apply NDSt.ext
  · show (insert 1 (insert 0 ∅) : Finset ℕ).erase 1 = insert 0 ∅
    decide
  · funext q p
    simp [NDSt.identify, twoTerms9, oneTerm9, NDSt.addTerm, empty9]

theorem no_return_fails9 : Reach9 oneTerm9 twoTerms9 1 ∧ Reach9 twoTerms9 oneTerm9 1 := by
  constructor
  · exact Reach9.single (Step9.addTerm oneTerm9 1 (by simp [mem_oneTerm9_T]))
  · have st : Step9 twoTerms9 (twoTerms9.identify 0 1) :=
      Step9.identify twoTerms9 0 1 ((mem_twoTerms9_T 0).2 (Or.inr rfl)) ((mem_twoTerms9_T 1).2 (Or.inl rfl))
        (by omega)
    rw [identify_twoTerms9] at st
    exact Reach9.single st

theorem antisymm_fails9 :
    oneTerm9 ≠ twoTerms9 ∧ (∃ n, Reach9 oneTerm9 twoTerms9 n) ∧ ∃ n, Reach9 twoTerms9 oneTerm9 n := by
  refine ⟨?_, ⟨1, no_return_fails9.1⟩, ⟨1, no_return_fails9.2⟩⟩
  intro h
  have h1 : (1 : ℕ) ∉ oneTerm9.T := by simp [mem_oneTerm9_T]
  have h2 : (1 : ℕ) ∈ twoTerms9.T := (mem_twoTerms9_T 1).2 (Or.inl rfl)
  rw [h] at h1
  exact h1 h2

theorem length_not_unique9 : Reach9 oneTerm9 oneTerm9 0 ∧ Reach9 oneTerm9 oneTerm9 2 :=
  ⟨Reach9.refl _, no_return_fails9.1.trans no_return_fails9.2⟩

end Seed.Ninth
