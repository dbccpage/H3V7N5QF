import Ninth.Reach

/-!
# What survives with nothing given and two relations

The task's rule 5 asks, for every result of an earlier derivation that is used,
whether its proof still holds from the ninth seed — in particular whether the
seventh's collapses (cost = size, reachability = has a term, one sameness) and
the eighth's independence (results a product, cost a sum, count not a product)
survive together, and where they interfere.  This file states the answer in
Lean for the headline results of both, through the four maps `forget`, `name`,
`proj` and `ofR`:

From the seventh —
* **the results**: every result of the seventh is a result of the ninth with
  nothing in `s` at the same round (`results_ofR7`); the results asserting
  nothing with `s` are exactly the seventh's (`results_r_iff9`), and by the
  exchange of the relations so are those asserting nothing with `r`
  (`results_s_iff9`); both parts of every result are results of the seventh
  (`proj_results9`);
* **the cost**: the size, which is the seventh's cost of the `r` part plus the
  `s` total (`cost_survives7`) — the eighth's additivity with the seventh's
  cost; the sum of the two parts' costs overcounts the terms
  (`cost_not_sum_of_parts9`, in `Ninth/Cost.lean`);
* **the criterion** survives on each part: reachability of two-relation states
  is reachability of either part under the seventh seed
  (`criterion_survives7`).

From the eighth —
* **the results**: every result of the eighth (either beginning) is a result of
  the ninth with its names forgotten (`results_forget8_A`, `_B`); every result
  of the ninth with a term is a result of the eighth once named
  (`results_name8`); the ninth has one result no eighth sequence reaches — the
  empty state (`empty9_is_new`, `eighth_never_empty`);
* **the criterion**: on states with a term the eighth's criterion says "always"
  through the naming map and so does the ninth's (`criterion_survives8`); the
  ninth adds the one-way exit from the empty state (`Ninth/Reach.lean`);
* **the cost does not survive**: the one-term state is one change from the
  empty state, while the eighth's potential on its named form is 5, two changes
  from `arb` (`eighth_cost_fails`); what survives is the size difference with
  nothing given (`size_difference_survives9`);
* **the names and their one-way merge have no object**: through the naming map
  the names of every state are one term, so the eighth's
  `Reach8.names_stay_merged` is vacuous (`names_merged_vacuous9`); what
  replaces it is that a term stays (`Reach9.nonempty`);
* **the interaction** of the two relations is still through the terms alone:
  an identification merges both, an assertion of one relation leaves the other
  part as it is (`interaction9`).

Where the two dials interfere, in Lean: the shared terms in the cost
(`cost_not_sum_of_parts9`, `one_term_parts9`) and the exchange symmetry
(`exchange_symmetry9`, `Step9.swap`, `Reach9.swap`), which the eighth's given
broke.
-/

namespace Seed.Ninth

open Seed Seed.Fourth Seed.Fifth Seed.Sixth Seed.Seventh Seed.Eighth NDSt

/-! ## From the seventh -/

/-- Every result of the seventh seed is a result of the ninth, with nothing in `s`, at the same
round. -/
theorem results_ofR7 {g : NSt} {n : ℕ} (h : Reach7 Seed.Seventh.empty g n) : Reach9 empty9 g.ofR n := by
  have := h.ofR
  rwa [ofR9_empty] at this

/-- Among the states asserting nothing with `s`, the results of the ninth seed are the seventh's. -/
theorem results_r_iff9 (g : NDSt) (hs : g.NothingIn true) :
    (∃ n, Reach9 empty9 g n) ↔ ∃ n, Reach7 Seed.Seventh.empty (g.proj false) n := by
  rw [result9_iff, result7_iff]
  constructor
  · exact fun hw => hw.1
  · intro hw
    refine ⟨hw, ?_⟩
    intro p hp
    exact absurd (hs p) hp

/-- By the exchange: among the states asserting nothing with `r`, the results are the seventh's. -/
theorem results_s_iff9 (g : NDSt) (hr : g.NothingIn false) :
    (∃ n, Reach9 empty9 g n) ↔ ∃ n, Reach7 Seed.Seventh.empty (g.proj true) n := by
  rw [result9_iff, result7_iff]
  exact ⟨fun hw => hw.2, fun hw => ⟨fun p hp => absurd (hr p) hp, hw⟩⟩

/-- The `r` part and the `s` part of every result are each a result of the seventh seed. -/
theorem proj_results9 {g : NDSt} {n : ℕ} (h : Reach9 empty9 g n) (q : Rel) :
    ∃ m, Reach7 Seed.Seventh.empty (g.proj q) m :=
  (result7_iff _).2 (wf_proj9 (h.wf empty9_wf) q)

/-- **The cost survives as the size**, and adds up as the eighth's did: the seventh's cost of
the `r` part plus the `s` total, the `r` part being reached under the seventh seed in exactly
its size. -/
theorem cost_survives7 {g : NDSt} (hgw : g.WF) :
    (Reach9 empty9 g g.size ∧ ∀ n, Reach9 empty9 g n → g.size ≤ n) ∧
      g.size = (g.proj false).size + (g.proj true).total ∧
      Reach7 Seed.Seventh.empty (g.proj false) (g.proj false).size :=
  ⟨fewest_changes9 hgw, rfl, (fewest_changes7 hgw.1).1⟩

/-- The criterion survives on each part: reachability of two-relation states is reachability of
either part under the seventh seed (the parts share the terms). -/
theorem criterion_survives7 {s g : NDSt} (hs : s.WF) (hg : g.WF) (q : Rel) :
    (∃ n, Reach9 s g n) ↔ ∃ n, Reach7 (s.proj q) (g.proj q) n := by
  rw [reach9_iff hs hg, reach7_iff (wf_proj9 hs q) (wf_proj9 hg q)]
  rfl

/-! ## From the eighth -/

/-- Every result of the eighth seed (`bra` not given) is a result of the ninth, names forgotten. -/
theorem results_forget8_A {g : DSt} {n : ℕ} (h : Reach8 givenA8 g n) : ∃ m, Reach9 empty9 g.forget m :=
  (result9_iff _).2 (wf_forget9 (h.wf givenA8_wf))

theorem results_forget8_B {g : DSt} {n : ℕ} (h : Reach8 givenB8 g n) : ∃ m, Reach9 empty9 g.forget m :=
  (result9_iff _).2 (wf_forget9 (h.wf givenB8_wf))

/-- Every result of the ninth seed with a term is a result of the eighth once named. -/
theorem results_name8 {g : NDSt} (hg : g.WF) {c : ℕ} (hc : c ∈ g.T) :
    (∃ n, Reach8 givenA8 (g.name c) n) ∧ ∃ n, Reach8 givenB8 (g.name c) n :=
  ⟨(result8_iff_A _).2 (name9_wf hg hc), (result8_iff_B _).2 (name9_wf hg hc)⟩

/-- No sequence of the eighth seed ends without a term. -/
theorem eighth_never_empty {g : DSt} {n : ℕ} (h : Reach8 givenA8 g n) : g.forget ≠ empty9 := by
  intro e
  have hne : g.forget.T.Nonempty := h.nonempty givenA8_nonempty
  rw [e] at hne
  exact empty9_not_nonempty hne

/-- The ninth seed has a result no eighth sequence reaches: the empty state. -/
theorem empty9_is_new :
    Reach9 empty9 empty9 0 ∧ ∀ (g : DSt) (n : ℕ), Reach8 givenA8 g n → g.forget ≠ empty9 :=
  ⟨Reach9.refl _, fun _ _ h => eighth_never_empty h⟩

/-- On states with a term, the eighth's criterion (through the naming map) and the ninth's both
say "reachable": the criterion survives there; the empty-state clause is new. -/
theorem criterion_survives8 {s g : NDSt} (hs : s.WF) (hg : g.WF) {c c' : ℕ} (hc : c ∈ s.T)
    (hc' : c' ∈ g.T) : (∃ n, Reach9 s g n) ∧ ∃ n, Reach8 (s.name c) (g.name c') n :=
  ⟨reach9_of_nonempty hs hg ⟨c, hc⟩ ⟨c', hc'⟩,
    reach8_of_names (name9_wf hs hc) (name9_wf hg hc') (fun _ => rfl)⟩

/-- The eighth's potential on the named one-term state: size 1, two destroyed givens, nothing in
`s`. -/
theorem costA8_oneTerm9 : costA8 (oneTerm9.name 0) = 5 := by
  rw [costA8_eq]
  have h1 : (oneTerm9.name 0).proj false = oneTerm7.name 0 := rfl
  have h2 : ((oneTerm9.name 0).proj true).total = 0 := by
    show (⟨insert 0 ∅, fun _ => 0, 0, 0⟩ : MSt).total = 0
    simp [MSt.total]
  rw [h1, h2, costA6_oneTerm7]

/-- **The eighth's cost does not survive.**  The one-term state is one change from the empty
state; under the eighth seed its named form costs two changes from `arb`. -/
theorem eighth_cost_fails :
    Reach9 empty9 oneTerm9 1 ∧ costA8 (oneTerm9.name 0) = 5 ∧
      ∀ n, Reach8 givenA8 (oneTerm9.name 0) n → 2 ≤ n := by
  refine ⟨(cost_oneTerm9 0).1, costA8_oneTerm9, fun n h => ?_⟩
  have := fewest_changes8_lower_A h
  rw [costA8_oneTerm9] at this
  omega

/-- **The size difference survives** with nothing given: the fewest changes to a result is its
size minus the size of what is given, which is 0. -/
theorem size_difference_survives9 {g : NDSt} (hgw : g.WF) :
    Reach9 empty9 g (g.size - empty9.size) ∧ ∀ n, Reach9 empty9 g n → g.size - empty9.size ≤ n := by
  rw [empty9_size, Nat.sub_zero]
  exact fewest_changes9 hgw

/-- Through the naming map the names of every state are one term, so the eighth's one-way merge
of the names holds vacuously along every sequence from a state with a term. -/
theorem names_merged_vacuous9 {s t : NDSt} {n : ℕ} (h : Reach9 s t n) {c : ℕ} (hc : c ∈ s.T) :
    ∃ c', c' ∈ t.T ∧ (t.name c').a = (t.name c').b ∧ Reach8 (s.name c) (t.name c') n := by
  obtain ⟨c', hc', r⟩ := h.name hc
  exact ⟨c', hc', rfl, r⟩

/-- The interaction: an identification merges both relations, and an assertion of one relation
leaves the other part as it is — through the terms alone, there being no names. -/
theorem interaction9 (s : NDSt) (u v x y : ℕ) (q : Rel) :
    (s.identify u v).proj false = (s.proj false).identify u v ∧
      (s.identify u v).proj true = (s.proj true).identify u v ∧
      (s.addAssertion q x y).proj (!q) = s.proj (!q) :=
  ⟨rfl, rfl, proj9_addAssertion_other s (not_ne q) x y⟩

/-! ## Where the dials interfere: the exchange symmetry -/

/-- **The exchange of the relations is a symmetry of the results, the cost and reachability.** -/
theorem exchange_symmetry9 {g : NDSt} {n : ℕ} (h : Reach9 empty9 g n) :
    Reach9 empty9 g.swap n ∧ g.swap.size = g.size ∧ (g.swap.T.Nonempty ↔ g.T.Nonempty) :=
  ⟨result9_swap h, size9_swap g, Iff.rfl⟩

end Seed.Ninth
