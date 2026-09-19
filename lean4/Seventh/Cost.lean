import Seventh.Step

/-!
# Fewest changes from nothing

Nothing is given, so nothing can be destroyed: the sixth's potential
`size + 2·lost` loses its second term, and the cost of a result is its **size**
(terms plus the sum of the multiplicities).

Derived here:
* every change moves the size by exactly one (`Step7.size_step`: the sixth's
  `Step6.size_step` through `name` for the three kinds that need a term, and
  `size_addTerm7` for the term), so a state reached from the empty state in `n`
  changes has size at most `n` (`Reach7.size_le`, `fewest_changes7_lower`), and
  the size and the length of a sequence have a fixed parity
  (`Reach7.size_parity`);
* additions reach every well-formed state from the empty one in exactly its
  size (`reach7_by_additions`): the first term is added, then the sixth's
  addition path (`reach6_of_contains`) through `name` does the rest
  (`reach7_of_contains`);
* so the fewest changes to a result is its size (`fewest_changes7`), and every
  shortest sequence is additions only (`shortest_are_additions`): a removal or
  an identification in a sequence of length the size would leave the size
  below the length.
-/

namespace Seed.Seventh

open Seed Seed.Fourth Seed.Fifth Seed.Sixth NSt

/-! ## Every change moves the size by one -/

theorem Step7.size_step {s t : NSt} (h : Step7 s t) (hw : s.WF) :
    t.size = s.size + 1 ∨ t.size + 1 = s.size := by
  cases h with
  | addTerm t ht => exact Or.inl (size_addTerm7 hw ht)
  | addAssertion x y hx hy => exact Or.inl (Seed.Fourth.size_addAssertion (s := s.name x) hx hy)
  | remove x y hp =>
    exact Or.inr (Seed.Fifth.size_remove (s.name x) (hw (x, y) hp).1 (hw (x, y) hp).2 hp)
  | identify u v hu hv huv => exact Or.inr (Seed.Fifth.size_identify (s.name u) hu hv huv)

theorem Reach7.size_le {s t : NSt} {n : ℕ} (h : Reach7 s t n) (hw : s.WF) : t.size ≤ s.size + n := by
  induction h with
  | refl => omega
  | step r st ih =>
    rcases st.size_step (r.wf hw) with e | e <;> omega

theorem Reach7.size_parity {s t : NSt} {n : ℕ} (h : Reach7 s t n) (hw : s.WF) :
    (s.size + t.size + n) % 2 = 0 := by
  induction h with
  | refl => omega
  | step r st ih =>
    rcases st.size_step (r.wf hw) with e | e <;> omega

/-- **Lower bound.**  A result reached in `n` changes has size at most `n`. -/
theorem fewest_changes7_lower {g : NSt} {n : ℕ} (h : Reach7 empty g n) : g.size ≤ n := by
  have := h.size_le empty_wf
  rw [empty_size] at this
  omega

/-! ## Additions reach everything -/

/-- Containment without names: every term and every multiplicity of `s` is in `t`. -/
structure Contains7 (s t : NSt) : Prop where
  terms : s.T ⊆ t.T
  mult : ∀ p, s.M p ≤ t.M p

theorem Contains7.name {s t : NSt} (h : Contains7 s t) (c : ℕ) : Contains4 (s.name c) (t.name c) :=
  ⟨h.terms, h.mult, rfl, rfl⟩

/-- Additions reach everything that contains the state, once a term is there: the sixth's
`reach6_of_contains` through `name`. -/
theorem reach7_of_contains {s g : NSt} (hs : s.WF) (hgw : g.WF) {c : ℕ} (hc : c ∈ s.T)
    (h : Contains7 s g) : ∃ n, Reach7 s g n ∧ n + s.size = g.size := by
  obtain ⟨n, hn, e⟩ := reach6_of_contains (name_wf hs hc) (name_wf hgw (h.terms hc)) (h.name c)
  exact ⟨n, hn.forget, e⟩

theorem step_first_term (c : ℕ) : Step7 empty (empty.addTerm c) :=
  Step7.addTerm empty c (Finset.notMem_empty c)

/-- **Upper bound.**  From the empty state, additions reach every well-formed state in exactly
its size: the first term, then the rest. -/
theorem reach7_by_additions {g : NSt} (hgw : g.WF) : Reach7 empty g g.size := by
  by_cases hne : g.T.Nonempty
  · obtain ⟨c, hc⟩ := hne
    have hw1 : (empty.addTerm c).WF := addTerm_wf empty_wf c
    have hcont : Contains7 (empty.addTerm c) g := by
      refine ⟨fun x hx => ?_, fun p => Nat.zero_le _⟩
      have hx' : x = c := by simpa [NSt.addTerm, empty] using hx
      rw [hx']
      exact hc
    obtain ⟨n, hn, e⟩ := reach7_of_contains hw1 hgw (Finset.mem_insert_self c _) hcont
    rw [size_oneTerm7] at e
    have r : Reach7 empty g (1 + n) := (Reach7.single (step_first_term c)).trans hn
    rw [show g.size = 1 + n by omega]
    exact r
  · rw [eq_empty_of_wf hgw hne, empty_size]
    exact Reach7.refl _

/-- **Fewest changes.**  Every well-formed state is reached from the empty state in exactly its
size and in no fewer changes. -/
theorem fewest_changes7 {g : NSt} (hgw : g.WF) :
    Reach7 empty g g.size ∧ ∀ n, Reach7 empty g n → g.size ≤ n :=
  ⟨reach7_by_additions hgw, fun _ h => fewest_changes7_lower h⟩

/-- The one-term state costs one change. -/
theorem cost_oneTerm (t : ℕ) :
    Reach7 empty (empty.addTerm t) 1 ∧ ∀ n, Reach7 empty (empty.addTerm t) n → 1 ≤ n := by
  have := fewest_changes7 (addTerm_wf empty_wf t)
  rw [size_oneTerm7] at this
  exact this

/-! ## Every shortest sequence is additions only -/

/-- One addition: a term, or an assertion. -/
inductive Add7 : NSt → NSt → Prop
  | addTerm (s : NSt) (t : ℕ) (ht : t ∉ s.T) : Add7 s (s.addTerm t)
  | addAssertion (s : NSt) (x y : ℕ) (hx : x ∈ s.T) (hy : y ∈ s.T) : Add7 s (s.addAssertion x y)

/-- `AddReach7 s t n`: `t` is reached from `s` by `n` additions. -/
inductive AddReach7 : NSt → NSt → ℕ → Prop
  | refl (s : NSt) : AddReach7 s s 0
  | step {s t u : NSt} {n : ℕ} : AddReach7 s t n → Add7 t u → AddReach7 s u (n + 1)

theorem Add7.toStep7 {s t : NSt} (h : Add7 s t) : Step7 s t := by
  cases h with
  | addTerm t ht => exact Step7.addTerm s t ht
  | addAssertion x y hx hy => exact Step7.addAssertion s x y hx hy

theorem AddReach7.toReach7 {s t : NSt} {n : ℕ} (h : AddReach7 s t n) : Reach7 s t n := by
  induction h with
  | refl => exact Reach7.refl _
  | step _ st ih => exact Reach7.step ih st.toStep7

/-- A change either lowers the size by one or is an addition. -/
theorem Step7.lowers_or_adds {s t : NSt} (h : Step7 s t) (hw : s.WF) :
    t.size + 1 = s.size ∨ Add7 s t := by
  cases h with
  | addTerm t ht => exact Or.inr (Add7.addTerm s t ht)
  | addAssertion x y hx hy => exact Or.inr (Add7.addAssertion s x y hx hy)
  | remove x y hp =>
    exact Or.inl (Seed.Fifth.size_remove (s.name x) (hw (x, y) hp).1 (hw (x, y) hp).2 hp)
  | identify u v hu hv huv => exact Or.inl (Seed.Fifth.size_identify (s.name u) hu hv huv)

/-- **Every shortest sequence is additions only.**  A sequence from the empty state whose length
is the size of its end uses no removal and no identification. -/
theorem shortest_are_additions {g : NSt} {n : ℕ} (h : Reach7 empty g n) :
    n = g.size → AddReach7 empty g n := by
  induction h with
  | refl =>
    intro _
    exact AddReach7.refl _
  | @step t u m r st ih =>
    intro hn
    have ht := fewest_changes7_lower r
    rcases st.lowers_or_adds (r.wf empty_wf) with e | add
    · omega
    · have hm : m = t.size := by
        rcases st.size_step (r.wf empty_wf) with e | e <;> omega
      exact AddReach7.step (ih hm) add

end Seed.Seventh
