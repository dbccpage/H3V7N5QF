import Seventh.Reach

/-!
# What survives with nothing given

The task's rule 5 asks, for every result of an earlier derivation that is used,
whether its proof still holds from the seventh seed — in particular once there
is no given datum and no names.  This file states the answer in Lean for the
sixth derivation's headline results, through the two maps `forget` and `name`:

* **the results**: every result of the sixth seed (either beginning) is a
  result of the seventh with its names forgotten (`results_forget_A`, `_B`);
  every result of the seventh with a term is a result of the sixth once its
  names are placed (`results_name`); the seventh has one result no sixth
  sequence reaches — the empty state (`empty_is_new`, `sixth_never_empty`);
* **the reachability criterion**: on states with a term the sixth's criterion
  says "always" through `name` and so does the seventh's
  (`criterion_survives`); the seventh adds the one-way exit from the empty
  state (`Seventh/Reach.lean`);
* **the cost does not survive**: the one-term state is one change from the
  empty state, while the sixth's potential on its named form is 5, two changes
  from `arb` (`sixth_cost_fails`); what survives is the size difference with
  nothing given (`size_difference_survives`);
* **the names and their one-way merge have no object**: through `name` the
  names of every state are one term, so the sixth's `Reach6.names_stay_merged`
  is vacuous (`names_merged_vacuous`); what replaces it is that a term stays
  (`Reach7.nonempty`).
-/

namespace Seed.Seventh

open Seed Seed.Fourth Seed.Fifth Seed.Sixth NSt

/-- Every result of the sixth seed (`bra` not given) is a result of the seventh, names forgotten. -/
theorem results_forget_A {g : MSt} {n : ℕ} (h : Reach6 givenA4 g n) : ∃ m, Reach7 empty g.forget m :=
  (result7_iff _).2 (wf_forget (h.wf givenA4_wf))

theorem results_forget_B {g : MSt} {n : ℕ} (h : Reach6 givenB4 g n) : ∃ m, Reach7 empty g.forget m :=
  (result7_iff _).2 (wf_forget (h.wf givenB4_wf))

/-- Every result of the seventh seed with a term is a result of the sixth once named. -/
theorem results_name {g : NSt} (hg : g.WF) {c : ℕ} (hc : c ∈ g.T) :
    (∃ n, Reach6 givenA4 (g.name c) n) ∧ ∃ n, Reach6 givenB4 (g.name c) n :=
  ⟨(result6_iff_A _).2 (name_wf hg hc), (result6_iff_B _).2 (name_wf hg hc)⟩

/-- No sequence of the sixth seed ends without a term. -/
theorem sixth_never_empty {g : MSt} {n : ℕ} (h : Reach6 givenA4 g n) : g.forget ≠ empty := by
  intro e
  have hne : g.forget.T.Nonempty := h.nonempty ⟨0, (mem_givenA4_T 0).2 (Or.inl rfl)⟩
  rw [e] at hne
  exact empty_not_nonempty hne

/-- The seventh seed has a result no earlier seed has: the empty state. -/
theorem empty_is_new :
    Reach7 empty empty 0 ∧ ∀ (g : MSt) (n : ℕ), Reach6 givenA4 g n → g.forget ≠ empty :=
  ⟨Reach7.refl _, fun _ _ h => sixth_never_empty h⟩

/-- On states with a term, the sixth's criterion (through `name`) and the seventh's both say
"reachable": the criterion survives there; the empty-state clause is new. -/
theorem criterion_survives {s g : NSt} (hs : s.WF) (hg : g.WF) {c c' : ℕ} (hc : c ∈ s.T)
    (hc' : c' ∈ g.T) : (∃ n, Reach7 s g n) ∧ ∃ n, Reach6 (s.name c) (g.name c') n :=
  ⟨reach7_of_nonempty hs hg ⟨c, hc⟩ ⟨c', hc'⟩,
    reach6_of_names (name_wf hs hc) (name_wf hg hc') (fun _ => rfl)⟩

/-- The sixth's potential on the named one-term state: size 1, two destroyed givens. -/
theorem costA6_oneTerm7 : costA6 (oneTerm7.name 0) = 5 := by
  unfold costA6
  have h1 : (oneTerm7.name 0).size = 1 := size_oneTerm7 0
  have h2 : lostA6 (oneTerm7.name 0) = 2 := by
    rw [lostA6_of_eq rfl]
    rfl
  rw [h1, h2]

/-- **The sixth's cost does not survive.**  The one-term state is one change from the empty
state; under the sixth seed its named form costs two changes from `arb`. -/
theorem sixth_cost_fails :
    Reach7 empty oneTerm7 1 ∧ costA6 (oneTerm7.name 0) = 5 ∧
      ∀ n, Reach6 givenA4 (oneTerm7.name 0) n → 2 ≤ n := by
  refine ⟨(cost_oneTerm 0).1, costA6_oneTerm7, fun n h => ?_⟩
  have := fewest_changes6_lower_A h
  rw [costA6_oneTerm7] at this
  omega

/-- **The size difference survives** with nothing given: the fewest changes to a result is its
size minus the size of what is given, which is 0. -/
theorem size_difference_survives {g : NSt} (hgw : g.WF) :
    Reach7 empty g (g.size - empty.size) ∧ ∀ n, Reach7 empty g n → g.size - empty.size ≤ n := by
  rw [empty_size, Nat.sub_zero]
  exact fewest_changes7 hgw

/-- Through `name` the names of every state are one term, so the sixth's one-way merge of the
names holds vacuously along every sequence from a state with a term. -/
theorem names_merged_vacuous {s t : NSt} {n : ℕ} (h : Reach7 s t n) {c : ℕ} (hc : c ∈ s.T) :
    ∃ c', c' ∈ t.T ∧ (t.name c').a = (t.name c').b ∧ Reach6 (s.name c) (t.name c') n := by
  obtain ⟨c', hc', r⟩ := h.name hc
  exact ⟨c', hc', rfl, r⟩

end Seed.Seventh
