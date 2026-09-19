import Eighth.Step

/-!
# Fewest changes with two relations

The potential is the sixth's on the `r` part with the `s` total added: `size`
(terms plus both totals) plus twice the destroyed givens read on the `r` part
(the given lives in `r` alone).

Derived here:
* one change raises the potential by at most one (`Step8.costA_le`,
  `Step8.costB_le`): an `s` change moves the `s` total by one and leaves the
  `r` part — hence the destroyed givens — as it is; a term, an `r` change and
  an identification are the sixth's on the `r` part (`Seed.Sixth.Step6.costA_le`
  through `Step8.proj`) with the `s` total kept (`Seed.Fourth.total_addTerm`,
  `Seed.Fifth.total_identify` on the `s` part); so a state reached from what is
  given in `n` changes has cost at most `n` plus the cost of what is given
  (`fewest_changes8_lower_A`, `_B`);
* raising the multiplicities of one relation is a sequence of additions of that
  relation (`reach8_raise`, the sixth's `reach6_raise` with a relation tag);
* the bound is attained: the sixth's sequence to the `r` part, lifted to the
  states asserting nothing with `s` (`Reach6.ofR`), then the `s` additions
  (`fewest_changes8_upper_A`, `_B`; `fewest_changes8_A`, `_B`);
* **the cost is additive per relation** (`costA8_eq`): the sixth's cost of
  the `r` part plus the `s` total; on states asserting nothing with `s` the
  sixth's fewest changes survive as they stand (`fewest_changes8_of_r_A`,
  `_B`); the `s` part costs exactly its total (`s_costs_its_total`);
* every change moves the size by exactly one (`Step8.size_step`,
  `Reach8.size_parity`).
-/

namespace Seed.Eighth

open Seed Seed.Fourth Seed.Fifth Seed.Sixth DSt

/-- Destroyed givens, `bra` not given: the sixth's, read on the `r` part. -/
def lostA8 (s : DSt) : ℕ := lostA6 (s.proj false)

/-- Destroyed givens, `bra` given. -/
def lostB8 (s : DSt) : ℕ := lostB6 (s.proj false)

/-- Size (both relations) plus two for each destroyed given (`bra` not given). -/
def costA8 (s : DSt) : ℕ := s.size + 2 * lostA8 s

/-- Size plus two for each destroyed given (`bra` given). -/
def costB8 (s : DSt) : ℕ := s.size + 2 * lostB8 s

/-- **The cost is additive per relation**: the sixth's cost of the `r` part plus the `s` total. -/
theorem costA8_eq (s : DSt) : costA8 s = costA6 (s.proj false) + (s.proj true).total := by
  unfold costA8 costA6 lostA8 DSt.size
  omega

theorem costB8_eq (s : DSt) : costB8 s = costB6 (s.proj false) + (s.proj true).total := by
  unfold costB8 costB6 lostB8 DSt.size
  omega

theorem costA8_ofR (m : MSt) : costA8 m.ofR = costA6 m := by
  rw [costA8_eq, proj_ofR_false, proj_ofR_true]
  unfold MSt.total
  simp

theorem costB8_ofR (m : MSt) : costB8 m.ofR = costB6 m := by
  rw [costB8_eq, proj_ofR_false, proj_ofR_true]
  unfold MSt.total
  simp

/-! ## The `r` part and the `s` total never both move -/

/-- An `s` change keeps the `r` part and moves the `s` total by one; every other change is a
change of the sixth on the `r` part and keeps the `s` total. -/
theorem Step8.split {s t : DSt} (h : Step8 s t) (hw : s.WF) :
    (t.proj false = s.proj false ∧ ((t.proj true).total = (s.proj true).total + 1 ∨ (t.proj true).total + 1 = (s.proj true).total)) ∨
      (Step6 (s.proj false) (t.proj false) ∧ (t.proj true).total = (s.proj true).total) := by
  cases h with
  | addTerm t ht =>
    refine Or.inr ⟨by rw [proj_addTerm]; exact Step6.addTerm _ t ht, ?_⟩
    rw [proj_addTerm]
    exact Seed.Fourth.total_addTerm hw.2 t
  | addAssertion q x y hx hy =>
    cases q
    · refine Or.inr ⟨by rw [proj_addAssertion_self]; exact Step6.addAssertion _ x y hx hy, ?_⟩
      rw [proj_addAssertion_other s (by decide) x y]
    · refine Or.inl ⟨proj_addAssertion_other s (by decide) x y, Or.inl ?_⟩
      rw [proj_addAssertion_self]
      exact Seed.Fourth.total_addAssertion (s := s.proj true) hx hy
  | remove q x y hp =>
    have hxy := (wf_proj hw q).1 (x, y) hp
    cases q
    · refine Or.inr ⟨by rw [proj_remove_self]; exact Step6.remove _ x y hp, ?_⟩
      rw [proj_remove_other s (by decide) x y]
    · refine Or.inl ⟨proj_remove_other s (by decide) x y, Or.inr ?_⟩
      rw [proj_remove_self]
      exact Seed.Fifth.total_remove (s.proj true) hxy.1 hxy.2 hp
  | identify u v hu hv huv =>
    refine Or.inr ⟨by rw [proj_identify]; exact Step6.identify _ u v hu hv huv, ?_⟩
    rw [proj_identify]
    exact Seed.Fifth.total_identify (s.proj true) hu huv

/-- Every change moves the size by exactly one. -/
theorem Step8.size_step {s t : DSt} (h : Step8 s t) (hw : s.WF) :
    t.size = s.size + 1 ∨ t.size + 1 = s.size := by
  unfold DSt.size
  rcases h.split hw with ⟨e, hs⟩ | ⟨st, hs⟩
  · rw [e]
    omega
  · rcases st.size_step hw.1 with e | e <;> omega

theorem Reach8.size_parity {s t : DSt} {n : ℕ} (h : Reach8 s t n) (hw : s.WF) :
    (s.size + t.size + n) % 2 = 0 := by
  induction h with
  | refl => omega
  | step r st ih =>
    rcases st.size_step (r.wf hw) with e | e <;> omega

/-! ## One change raises the cost by at most one -/

/-- The sixth's potential on the `r` part rises by at most one, or the `r` part is unchanged. -/
theorem lostA8_step {s t : DSt} (h : Step8 s t) (hw : s.WF) :
    costA6 (t.proj false) ≤ costA6 (s.proj false) + 1 := by
  rcases h.proj false with st | e
  · exact st.costA_le hw.1
  · rw [e]
    omega

theorem lostB8_step {s t : DSt} (h : Step8 s t) (hw : s.WF) :
    costB6 (t.proj false) ≤ costB6 (s.proj false) + 1 := by
  rcases h.proj false with st | e
  · exact st.costB_le hw.1
  · rw [e]
    omega

theorem Step8.costA_le {s t : DSt} (h : Step8 s t) (hw : s.WF) : costA8 t ≤ costA8 s + 1 := by
  rw [costA8_eq, costA8_eq]
  rcases h.split hw with ⟨e, hs⟩ | ⟨st, hs⟩
  · rw [e]
    omega
  · have := st.costA_le hw.1
    omega

theorem Step8.costB_le {s t : DSt} (h : Step8 s t) (hw : s.WF) : costB8 t ≤ costB8 s + 1 := by
  rw [costB8_eq, costB8_eq]
  rcases h.split hw with ⟨e, hs⟩ | ⟨st, hs⟩
  · rw [e]
    omega
  · have := st.costB_le hw.1
    omega

theorem Reach8.costA_le {s t : DSt} {n : ℕ} (h : Reach8 s t n) (hw : s.WF) : costA8 t ≤ costA8 s + n := by
  induction h with
  | refl => omega
  | step r st ih =>
    have := st.costA_le (r.wf hw)
    omega

theorem Reach8.costB_le {s t : DSt} {n : ℕ} (h : Reach8 s t n) (hw : s.WF) : costB8 t ≤ costB8 s + n := by
  induction h with
  | refl => omega
  | step r st ih =>
    have := st.costB_le (r.wf hw)
    omega

theorem costA8_givenA8 : costA8 givenA8 = 3 := by rw [givenA8, costA8_ofR, costA6_givenA4]
theorem costB8_givenB8 : costB8 givenB8 = 4 := by rw [givenB8, costB8_ofR, costB6_givenB4]

/-- **Lower bound, `bra` not asserted to begin with.** -/
theorem fewest_changes8_lower_A {t : DSt} {n : ℕ} (h : Reach8 givenA8 t n) : costA8 t ≤ n + 3 := by
  have := h.costA_le givenA8_wf
  rw [costA8_givenA8] at this
  omega

theorem fewest_changes8_lower_B {t : DSt} {n : ℕ} (h : Reach8 givenB8 t n) : costB8 t ≤ n + 4 := by
  have := h.costB_le givenB8_wf
  rw [costB8_givenB8] at this
  omega

/-! ## Raising one relation's multiplicities -/

/-- Raising the multiplicities of relation `q` one at a time (the sixth's `reach6_raise` with a
relation tag): from a well-formed state with the same terms, names and other relation as the
target and multiplicities below the target's, the target is reached in the difference of the
`q` totals. -/
theorem reach8_raise (g : DSt) (hgw : g.WF) (q : Rel) :
    ∀ (d : ℕ) (s : DSt), s.T = g.T → s.a = g.a → s.b = g.b → s.M (!q) = g.M (!q) → s.WF →
      (∀ p, s.M q p ≤ g.M q p) → (g.proj q).total = (s.proj q).total + d → Reach8 s g d := by
  intro d
  induction d with
  | zero =>
    intro s hT ha hb hother hw hle htot
    have e : s = g := by
      apply DSt.ext
      · exact hT
      · funext q' p
        by_cases hq : q' = q
        · subst hq
          by_cases hp : p ∈ g.T ×ˢ g.T
          · by_contra hne
            have hlt : s.M q' p < g.M q' p := lt_of_le_of_ne (hle p) hne
            have : ∑ w ∈ g.T ×ˢ g.T, s.M q' w < ∑ w ∈ g.T ×ˢ g.T, g.M q' w :=
              Finset.sum_lt_sum (fun w _ => hle w) ⟨p, hp, hlt⟩
            unfold MSt.total at htot
            simp only [proj_T, proj_M] at htot
            rw [hT] at htot
            omega
          · have h1 : g.M q' p = 0 := by
              by_contra h
              exact hp (Finset.mem_product.2 ((wf_proj hgw q').1 p h))
            have h2 : s.M q' p = 0 := by
              by_contra h
              have := (wf_proj hw q').1 p h
              simp only [proj_T] at this
              rw [hT] at this
              exact hp (Finset.mem_product.2 this)
            rw [h1, h2]
        · have : q' = !q := by cases q <;> cases q' <;> simp_all
          rw [this, hother]
      · exact ha
      · exact hb
    rw [e]
    exact Reach8.refl g
  | succ d ih =>
    intro s hT ha hb hother hw hle htot
    have hlt : ∑ w ∈ g.T ×ˢ g.T, s.M q w < ∑ w ∈ g.T ×ˢ g.T, g.M q w := by
      unfold MSt.total at htot
      simp only [proj_T, proj_M] at htot
      rw [hT] at htot
      omega
    obtain ⟨p, hp, hplt⟩ := Finset.exists_lt_of_sum_lt hlt
    obtain ⟨x, y⟩ := p
    have hxT : x ∈ s.T := by rw [hT]; exact (Finset.mem_product.1 hp).1
    have hyT : y ∈ s.T := by rw [hT]; exact (Finset.mem_product.1 hp).2
    have st := Step8.addAssertion s q x y hxT hyT
    have hw' := st.wf hw
    have hle' : ∀ w, (s.addAssertion q x y).M q w ≤ g.M q w := by
      intro w
      show Function.update s.M q (Function.update (s.M q) (x, y) (s.M q (x, y) + 1)) q w ≤ g.M q w
      rw [Function.update_self, Function.update_apply]
      split_ifs with hw
      · subst hw
        omega
      · exact hle w
    have hother' : (s.addAssertion q x y).M (!q) = g.M (!q) := by
      show Function.update s.M q _ (!q) = g.M (!q)
      rw [Function.update_of_ne (not_ne q), hother]
    have htot' : (g.proj q).total = ((s.addAssertion q x y).proj q).total + d := by
      rw [proj_addAssertion_self, Seed.Fourth.total_addAssertion (s := s.proj q) hxT hyT]
      omega
    have r := ih (s.addAssertion q x y) hT ha hb hother' hw' hle' htot'
    have : Reach8 s g (1 + d) := Reach8.trans (Reach8.single st) r
    rw [Nat.add_comm] at this
    exact this

/-- From the embedding of the `r` part, the `s` additions reach the state. -/
theorem reach8_from_ofR {g : DSt} (hgw : g.WF) : Reach8 (g.proj false).ofR g (g.proj true).total := by
  refine reach8_raise g hgw true (g.proj true).total (g.proj false).ofR rfl rfl rfl rfl (ofR_wf hgw.1)
    (fun _ => Nat.zero_le _) ?_
  rw [proj_ofR_true]
  unfold MSt.total
  simp

/-! ## Upper bounds -/

/-- **Fewest changes, `bra` not asserted to begin with.**  A well-formed two-relation state written
with `a = 0` and `b ∈ {0, 1}` is reached in exactly `costA8 − 3` changes and no fewer: the sixth's
sequence to the `r` part, with nothing in `s`, then the `s` additions. -/
theorem fewest_changes8_A {g : DSt} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1 ∨ g.b = 0) :
    (∃ n, Reach8 givenA8 g n ∧ n + 3 = costA8 g) ∧ ∀ n, Reach8 givenA8 g n → costA8 g ≤ n + 3 := by
  constructor
  · obtain ⟨n, hn, hc⟩ := (fewest_changes6_A (g := g.proj false) hgw.1 ha hb).1
    refine ⟨n + (g.proj true).total, hn.ofR.trans (reach8_from_ofR hgw), ?_⟩
    rw [costA8_eq]
    omega
  · exact fun _ h => fewest_changes8_lower_A h

/-- **Fewest changes, `bra` asserted to begin with.** -/
theorem fewest_changes8_B {g : DSt} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1 ∨ g.b = 0) :
    (∃ n, Reach8 givenB8 g n ∧ n + 4 = costB8 g) ∧ ∀ n, Reach8 givenB8 g n → costB8 g ≤ n + 4 := by
  constructor
  · obtain ⟨n, hn, hc⟩ := (fewest_changes6_B (g := g.proj false) hgw.1 ha hb).1
    refine ⟨n + (g.proj true).total, hn.ofR.trans (reach8_from_ofR hgw), ?_⟩
    rw [costB8_eq]
    omega
  · exact fun _ h => fewest_changes8_lower_B h

/-- On states asserting nothing with `s` the sixth's fewest changes survive as they stand. -/
theorem fewest_changes8_of_r_A {g : DSt} (hgw : g.WF) (hs : g.NothingInS) (ha : g.a = 0)
    (hb : g.b = 1 ∨ g.b = 0) :
    (∃ n, Reach8 givenA8 g n ∧ n + 3 = costA6 (g.proj false)) ∧
      ∀ n, Reach8 givenA8 g n → costA6 (g.proj false) ≤ n + 3 := by
  have e : costA8 g = costA6 (g.proj false) := by
    rw [costA8_eq]
    have : (g.proj true).total = 0 := by
      unfold MSt.total
      apply Finset.sum_eq_zero
      intro p _
      exact hs p
    omega
  rw [← e]
  exact fewest_changes8_A hgw ha hb

theorem fewest_changes8_of_r_B {g : DSt} (hgw : g.WF) (hs : g.NothingInS) (ha : g.a = 0)
    (hb : g.b = 1 ∨ g.b = 0) :
    (∃ n, Reach8 givenB8 g n ∧ n + 4 = costB6 (g.proj false)) ∧
      ∀ n, Reach8 givenB8 g n → costB6 (g.proj false) ≤ n + 4 := by
  have e : costB8 g = costB6 (g.proj false) := by
    rw [costB8_eq]
    have : (g.proj true).total = 0 := by
      unfold MSt.total
      apply Finset.sum_eq_zero
      intro p _
      exact hs p
    omega
  rw [← e]
  exact fewest_changes8_B hgw ha hb

/-- **The `s` part costs exactly its total.**  A state whose `r` part is what is given is reached
in exactly its `s` total, and no fewer. -/
theorem s_costs_its_total {g : DSt} (hgw : g.WF) (hr : g.proj false = givenA4) :
    Reach8 givenA8 g (g.proj true).total ∧ ∀ n, Reach8 givenA8 g n → (g.proj true).total ≤ n := by
  constructor
  · have := reach8_from_ofR hgw
    rw [hr] at this
    exact this
  · intro n h
    have := fewest_changes8_lower_A h
    rw [costA8_eq, hr, costA6_givenA4] at this
    omega

end Seed.Eighth
