import Ninth.Step

/-!
# Fewest changes from nothing, with two relations

Nothing is given, so nothing can be destroyed: the eighth's potential
`size + 2·lost` loses its second term, and the cost of a result is its **size**
(terms plus the sum of the multiplicities of both relations).  The seventh's
collapse survives with both totals counted.

Derived here:
* every change moves the size by exactly one (`Step9.size_step`: the fourth's
  and fifth's lemmas on a part through the naming map, and `size_addTerm9` for
  the term), so a state reached from the empty state in `n` changes has size at
  most `n` (`Reach9.size_le`, `fewest_changes9_lower`), and the size and the
  length of a sequence have a fixed parity (`Reach9.size_parity`);
* additions reach every well-formed state from the empty one in exactly its
  size (`reach9_by_additions`): the terms one by one (`reach9_addTerms`), then
  the `r` multiplicities, then the `s` multiplicities — the eighth's
  `reach8_raise` through the naming map once a term is there (`reach9_raise`);
* so the fewest changes to a result is its size (`fewest_changes9`), and every
  shortest sequence is additions only (`shortest_are_additions9`);
* **the eighth's additivity survives in the seventh's shape and no other**: the
  size is the seventh's size of the `r` part plus the `s` total (`size9_eq`,
  `cost_adds_up9`), and by the exchange the seventh's size of the `s` part plus
  the `r` total (`cost_adds_up9_swapped`); but the sum of the two parts' sizes
  is the size plus the terms (`cost_not_sum_of_parts9`): the two relations
  share the terms, which a per-relation cost counts twice.  The one-term state
  is the witness: each part costs 1, the state costs 1, not 2
  (`one_term_parts9`).
-/

namespace Seed.Ninth

open Seed Seed.Fourth Seed.Fifth Seed.Sixth Seed.Seventh Seed.Eighth NDSt

/-! ## Every change moves the size by one -/

theorem Step9.size_step {s t : NDSt} (h : Step9 s t) (hw : s.WF) :
    t.size = s.size + 1 ∨ t.size + 1 = s.size := by
  cases h with
  | addTerm t ht => exact Or.inl (size_addTerm9 hw ht)
  | addAssertion q x y hx hy => exact Or.inl (size_addAssertion9 q hx hy)
  | remove q x y hp => exact Or.inr (size_remove9 hw q hp)
  | identify u v hu hv huv => exact Or.inr (size_identify9 hu hv huv)

theorem Reach9.size_le {s t : NDSt} {n : ℕ} (h : Reach9 s t n) (hw : s.WF) : t.size ≤ s.size + n := by
  induction h with
  | refl => omega
  | step r st ih =>
    rcases st.size_step (r.wf hw) with e | e <;> omega

theorem Reach9.size_parity {s t : NDSt} {n : ℕ} (h : Reach9 s t n) (hw : s.WF) :
    (s.size + t.size + n) % 2 = 0 := by
  induction h with
  | refl => omega
  | step r st ih =>
    rcases st.size_step (r.wf hw) with e | e <;> omega

/-- **Lower bound.**  A result reached in `n` changes has size at most `n`. -/
theorem fewest_changes9_lower {g : NDSt} {n : ℕ} (h : Reach9 empty9 g n) : g.size ≤ n := by
  have := h.size_le empty9_wf
  rw [empty9_size] at this
  omega

/-! ## Additions reach everything -/

/-- The state with terms `T` and nothing asserted. -/
def bare9 (T : Finset ℕ) : NDSt := ⟨T, fun _ _ => 0⟩

theorem bare9_wf (T : Finset ℕ) : (bare9 T).WF := ⟨fun _ h => absurd rfl h, fun _ h => absurd rfl h⟩

theorem bare9_empty : bare9 ∅ = empty9 := rfl

/-- The terms are added one by one: `T.card` changes from the empty state. -/
theorem reach9_addTerms (T : Finset ℕ) : Reach9 empty9 (bare9 T) T.card := by
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.card_empty]
    exact Reach9.refl _
  | insert a S haS ih =>
    rw [Finset.card_insert_of_notMem haS]
    exact Reach9.step ih (Step9.addTerm (bare9 S) a haS)

/-- Raising the multiplicities of relation `q` one at a time: the eighth's `reach8_raise`
through the naming map, once a term is there. -/
theorem reach9_raise {g : NDSt} (hgw : g.WF) {c : ℕ} (hc : c ∈ g.T) (q : Rel) (d : ℕ) (s : NDSt)
    (hT : s.T = g.T) (hother : s.M (!q) = g.M (!q)) (hw : s.WF) (hle : ∀ p, s.M q p ≤ g.M q p)
    (htot : (g.proj q).total = (s.proj q).total + d) : Reach9 s g d := by
  have hc' : c ∈ s.T := by rw [hT]; exact hc
  have r := reach8_raise (g.name c) (name9_wf hgw hc) q d (s.name c) hT rfl rfl hother
    (name9_wf hw hc') hle htot
  exact r.forget

/-- The `r` part filled in, nothing in `s`. -/
def halfway9 (g : NDSt) : NDSt :=
  ⟨g.T, fun q => match q with
    | false => g.M false
    | true => fun _ => 0⟩

theorem halfway9_wf {g : NDSt} (hgw : g.WF) : (halfway9 g).WF := ⟨hgw.1, fun _ h => absurd rfl h⟩

/-- **Upper bound.**  From the empty state, additions reach every well-formed state in exactly
its size: the terms, then the `r` assertions, then the `s` assertions. -/
theorem reach9_by_additions {g : NDSt} (hgw : g.WF) : Reach9 empty9 g g.size := by
  by_cases hne : g.T.Nonempty
  · obtain ⟨c, hc⟩ := hne
    have r1 : Reach9 empty9 (bare9 g.T) g.T.card := reach9_addTerms g.T
    have r2 : Reach9 (bare9 g.T) (halfway9 g) (g.proj false).total :=
      reach9_raise (halfway9_wf hgw) hc false _ (bare9 g.T) rfl rfl (bare9_wf _) (fun _ => Nat.zero_le _)
        (by
          show (g.proj false).total = (⟨g.T, fun _ => 0⟩ : NSt).total + (g.proj false).total
          rw [total_zero9]
          omega)
    have r3 : Reach9 (halfway9 g) g (g.proj true).total :=
      reach9_raise hgw hc true _ (halfway9 g) rfl rfl (halfway9_wf hgw) (fun _ => Nat.zero_le _)
        (by
          show (g.proj true).total = (⟨g.T, fun _ => 0⟩ : NSt).total + (g.proj true).total
          rw [total_zero9]
          omega)
    have r := (r1.trans r2).trans r3
    rw [size9_eq]
    exact r
  · rw [eq_empty9_of_wf hgw hne, empty9_size]
    exact Reach9.refl _

/-- **Fewest changes.**  Every well-formed state is reached from the empty state in exactly its
size and in no fewer changes. -/
theorem fewest_changes9 {g : NDSt} (hgw : g.WF) :
    Reach9 empty9 g g.size ∧ ∀ n, Reach9 empty9 g n → g.size ≤ n :=
  ⟨reach9_by_additions hgw, fun _ h => fewest_changes9_lower h⟩

/-- The one-term state costs one change. -/
theorem cost_oneTerm9 (t : ℕ) :
    Reach9 empty9 (empty9.addTerm t) 1 ∧ ∀ n, Reach9 empty9 (empty9.addTerm t) n → 1 ≤ n := by
  have := fewest_changes9 (addTerm9_wf empty9_wf t)
  rw [size_oneTerm9] at this
  exact this

/-! ## The cost adds up per relation, with the terms counted once -/

/-- The cost is the seventh's cost of the `r` part (its size) plus the `s` total. -/
theorem cost_adds_up9 (g : NDSt) : g.size = (g.proj false).size + (g.proj true).total := rfl

/-- By the exchange: the seventh's cost of the `s` part plus the `r` total. -/
theorem cost_adds_up9_swapped (g : NDSt) : g.size = (g.proj true).size + (g.proj false).total := by
  rw [← size9_swap]
  rfl

/-- **The per-relation costs do not add up**: their sum counts the shared terms twice. -/
theorem cost_not_sum_of_parts9 (g : NDSt) :
    (g.proj false).size + (g.proj true).size = g.size + g.T.card := by
  rw [size9_eq]
  unfold NSt.size
  simp only [proj9_T]
  omega

/-- The witness: each part of the one-term state costs one change under the seventh seed, and
so does the state — not two. -/
theorem one_term_parts9 :
    (oneTerm9.proj false).size = 1 ∧ (oneTerm9.proj true).size = 1 ∧ oneTerm9.size = 1 :=
  ⟨size_oneTerm7 0, size_oneTerm7 0, size_oneTerm9 0⟩

/-! ## Every shortest sequence is additions only -/

/-- One addition: a term, or an assertion of either relation. -/
inductive Add9 : NDSt → NDSt → Prop
  | addTerm (s : NDSt) (t : ℕ) (ht : t ∉ s.T) : Add9 s (s.addTerm t)
  | addAssertion (s : NDSt) (q : Rel) (x y : ℕ) (hx : x ∈ s.T) (hy : y ∈ s.T) : Add9 s (s.addAssertion q x y)

/-- `AddReach9 s t n`: `t` is reached from `s` by `n` additions. -/
inductive AddReach9 : NDSt → NDSt → ℕ → Prop
  | refl (s : NDSt) : AddReach9 s s 0
  | step {s t u : NDSt} {n : ℕ} : AddReach9 s t n → Add9 t u → AddReach9 s u (n + 1)

theorem Add9.toStep9 {s t : NDSt} (h : Add9 s t) : Step9 s t := by
  cases h with
  | addTerm t ht => exact Step9.addTerm s t ht
  | addAssertion q x y hx hy => exact Step9.addAssertion s q x y hx hy

theorem AddReach9.toReach9 {s t : NDSt} {n : ℕ} (h : AddReach9 s t n) : Reach9 s t n := by
  induction h with
  | refl => exact Reach9.refl _
  | step _ st ih => exact Reach9.step ih st.toStep9

/-- A change either lowers the size by one or is an addition. -/
theorem Step9.lowers_or_adds {s t : NDSt} (h : Step9 s t) (hw : s.WF) :
    t.size + 1 = s.size ∨ Add9 s t := by
  cases h with
  | addTerm t ht => exact Or.inr (Add9.addTerm s t ht)
  | addAssertion q x y hx hy => exact Or.inr (Add9.addAssertion s q x y hx hy)
  | remove q x y hp => exact Or.inl (size_remove9 hw q hp)
  | identify u v hu hv huv => exact Or.inl (size_identify9 hu hv huv)

/-- **Every shortest sequence is additions only.**  A sequence from the empty state whose length
is the size of its end uses no removal and no identification. -/
theorem shortest_are_additions9 {g : NDSt} {n : ℕ} (h : Reach9 empty9 g n) :
    n = g.size → AddReach9 empty9 g n := by
  induction h with
  | refl =>
    intro _
    exact AddReach9.refl _
  | @step t u m r st ih =>
    intro hn
    have ht := fewest_changes9_lower r
    rcases st.lowers_or_adds (r.wf empty9_wf) with e | add
    · omega
    · have hm : m = t.size := by
        rcases st.size_step (r.wf empty9_wf) with e | e <;> omega
      exact AddReach9.step (ih hm) add

end Seed.Ninth
