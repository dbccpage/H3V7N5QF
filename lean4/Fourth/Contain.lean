import Fourth.Step

/-!
# Containment with multiplicities: nothing is ever taken away

Every change of the fourth seed adds one term or raises one multiplicity by one
and takes nothing away, so a state is contained in its outcome: every term and
both names are in place and every multiplicity is the same or higher
(`Step4.contains`).  Containment composes, so every sequence of changes leaves
its start contained in its end (`Reach4.contains`).

Cited from the third derivation and re-checked: the third's containment
(terms, asserted pairs, names in place) is containment of the supports; a
counted containment gives a containment of the supports (`Contains4.toSt`) and
a containment of earlier states gives a counted containment of the indicators
(`Contains.ofSt`).  So what the third derivation derived from containment
survives on the supports, and is derived here again for all counted states:
* every term, every asserted assertion and both names persist, and no
  multiplicity ever decreases (`Reach4.term_persists`, `Reach4.mult_le`,
  `Reach4.asserted_persists`, `Reach4.name_a`, `Reach4.name_b`);
* `a`, `b` stay two terms; `arb` (and `bra`, if asserted) stays asserted; every
  result has at least two terms (`Reach4.names_apart`, `Reach4.arb_persists`,
  `Reach4.bra_persists`, `Reach4.two_terms`);
* the number of terms and the total multiplicity never decrease
  (`Reach4.card_T_le`, `Reach4.total_le`);
* an obstruction is never cleared (`Reach4.obstruction_persists`,
  `Reach4.xrx_still_obstructed`);
* the fewest classes of a split of the support never decreases
  (`Reach4.split_mono`, through `Contains4.toSt` and the second derivation's
  `Carries.split`);
* containment is one-way (`Contains4.antisymm`).

New to the counted seed: a multiplicity can rise — the multiplicity of `arb` is
not kept at one (`arb_twice`).
-/

namespace Seed.Fourth

open Seed Seed.Second Seed.Third MSt

/-- `s` is contained in `t`: terms and names in place, every multiplicity the same or
higher. -/
structure Contains4 (s t : MSt) : Prop where
  terms : s.T ⊆ t.T
  mult : ∀ p, s.M p ≤ t.M p
  name_a : t.a = s.a
  name_b : t.b = s.b

theorem Contains4.refl (s : MSt) : Contains4 s s :=
  ⟨Finset.Subset.refl _, fun _ => le_refl _, rfl, rfl⟩

theorem Contains4.trans {s t u : MSt} (h : Contains4 s t) (h' : Contains4 t u) : Contains4 s u :=
  ⟨h.terms.trans h'.terms, fun p => (h.mult p).trans (h'.mult p), h'.name_a.trans h.name_a,
    h'.name_b.trans h.name_b⟩

/-- Containment is one-way: two states contained in each other are the same state. -/
theorem Contains4.antisymm {s t : MSt} (h : Contains4 s t) (h' : Contains4 t s) : s = t := by
  apply MSt.ext
  · exact Finset.Subset.antisymm h.terms h'.terms
  · funext p
    exact le_antisymm (h.mult p) (h'.mult p)
  · exact h.name_a.symm
  · exact h.name_b.symm

/-- One change leaves its state contained in its outcome. -/
theorem Step4.contains {s t : MSt} (h : Step4 s t) : Contains4 s t := by
  cases h with
  | addTerm t ht => exact ⟨Finset.subset_insert _ _, fun _ => le_refl _, rfl, rfl⟩
  | addAssertion x y hx hy hxy =>
    refine ⟨Finset.Subset.refl _, fun p => ?_, rfl, rfl⟩
    show s.M p ≤ Function.update s.M (x, y) (s.M (x, y) + 1) p
    rw [Function.update_apply]
    split_ifs with hp
    · subst hp
      omega
    · exact le_refl _

/-- A sequence of changes leaves its start contained in its end. -/
theorem Reach4.contains {s t : MSt} {n : ℕ} (h : Reach4 s t n) : Contains4 s t := by
  induction h with
  | refl => exact Contains4.refl _
  | step _ st ih => exact ih.trans st.contains

/-! ## The two containments, through the maps -/

/-- A counted containment is a containment of the supports (third derivation's
`Contains`). -/
theorem Contains4.toSt {s t : MSt} (h : Contains4 s t) (hw : s.WF) : Contains (toSt s) (toSt t) := by
  refine ⟨h.terms, fun p hp => ?_, h.name_a, h.name_b⟩
  rw [mem_toSt_A_of_wf hw] at hp
  rw [mem_toSt_A]
  have hm := h.mult p
  exact ⟨⟨h.terms (hw.1 p hp).1, h.terms (hw.1 p hp).2⟩, by omega⟩

/-- A containment of earlier states is a counted containment of the indicators. -/
theorem _root_.Seed.Third.Contains.ofSt {s t : St} (h : Contains s t) : Contains4 (ofSt s) (ofSt t) := by
  refine ⟨h.terms, fun p => ?_, h.name_a, h.name_b⟩
  rw [ofSt_M, ofSt_M]
  by_cases hp : p ∈ s.A
  · simp [hp, h.asserted hp]
  · simp [hp]

/-- On states asserting nothing twice, a containment of the supports is a counted
containment. -/
theorem contains4_of_toSt {s t : MSt} (h : Contains (toSt s) (toSt t)) (hw : s.WF) (hs : s.Simple)
    (htw : t.WF) : Contains4 s t := by
  refine ⟨h.terms, fun p => ?_, h.name_a, h.name_b⟩
  by_cases hp : s.M p = 0
  · omega
  · have := h.asserted ((mem_toSt_A_of_wf hw).2 hp)
    rw [mem_toSt_A_of_wf htw] at this
    have := hs p
    omega

/-! ## What is given survives -/

theorem Reach4.term_persists {s t : MSt} {n : ℕ} (h : Reach4 s t n) {x : ℕ} (hx : x ∈ s.T) :
    x ∈ t.T := h.contains.terms hx

/-- No multiplicity ever decreases. -/
theorem Reach4.mult_le {s t : MSt} {n : ℕ} (h : Reach4 s t n) (p : ℕ × ℕ) : s.M p ≤ t.M p :=
  h.contains.mult p

theorem Reach4.asserted_persists {s t : MSt} {n : ℕ} (h : Reach4 s t n) {p : ℕ × ℕ}
    (hp : s.M p ≠ 0) : t.M p ≠ 0 := by
  have := h.mult_le p
  omega

theorem Reach4.name_a {s t : MSt} {n : ℕ} (h : Reach4 s t n) : t.a = s.a := h.contains.name_a

theorem Reach4.name_b {s t : MSt} {n : ℕ} (h : Reach4 s t n) : t.b = s.b := h.contains.name_b

/-- `arb`, once asserted, is asserted after every sequence of changes, with a
multiplicity at least what it was. -/
theorem Reach4.arb_persists {s t : MSt} {n : ℕ} (h : Reach4 s t n) (hab : s.M (s.a, s.b) ≠ 0) :
    t.M (t.a, t.b) ≠ 0 := by
  rw [h.name_a, h.name_b]
  exact h.asserted_persists hab

theorem Reach4.arb_mult_le {s t : MSt} {n : ℕ} (h : Reach4 s t n) :
    s.M (s.a, s.b) ≤ t.M (t.a, t.b) := by
  rw [h.name_a, h.name_b]
  exact h.mult_le _

/-- `bra`, once asserted, is asserted after every sequence of changes. -/
theorem Reach4.bra_persists {s t : MSt} {n : ℕ} (h : Reach4 s t n) (hba : s.M (s.b, s.a) ≠ 0) :
    t.M (t.b, t.a) ≠ 0 := by
  rw [h.name_a, h.name_b]
  exact h.asserted_persists hba

/-- `a` and `b` are never one term. -/
theorem Reach4.names_apart {s t : MSt} {n : ℕ} (h : Reach4 s t n) (hs : s.Legal)
    (hab : s.M (s.a, s.b) ≠ 0) : t.a ≠ t.b := by
  rw [h.name_a, h.name_b]
  exact names_apart_of_legal hs hab

/-- Every result has at least two terms. -/
theorem Reach4.two_terms {s t : MSt} {n : ℕ} (h : Reach4 s t n) (hs : s.Legal) (hw : s.WF)
    (hab : s.M (s.a, s.b) ≠ 0) : 2 ≤ t.T.card := by
  have htw := h.wf hw
  have hne := h.names_apart hs hab
  have hsub : ({t.a, t.b} : Finset ℕ) ⊆ t.T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact htw.2.1
    · exact htw.2.2
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at this
  exact this

/-! ## Counts never decrease -/

theorem Reach4.card_T_le {s t : MSt} {n : ℕ} (h : Reach4 s t n) : s.T.card ≤ t.T.card :=
  Finset.card_le_card h.contains.terms

/-- The total multiplicity never decreases. -/
theorem Contains4.total_le {s t : MSt} (h : Contains4 s t) : s.total ≤ t.total := by
  unfold MSt.total
  calc ∑ p ∈ s.T ×ˢ s.T, s.M p ≤ ∑ p ∈ s.T ×ˢ s.T, t.M p :=
        Finset.sum_le_sum (fun p _ => h.mult p)
    _ ≤ ∑ p ∈ t.T ×ˢ t.T, t.M p :=
        Finset.sum_le_sum_of_subset (Finset.product_subset_product h.terms h.terms)

theorem Reach4.total_le {s t : MSt} {n : ℕ} (h : Reach4 s t n) : s.total ≤ t.total :=
  h.contains.total_le

/-! ## An obstruction is never cleared -/

/-- Whatever is asserted stays asserted: an assertion that obstructs is still there
after any sequence of changes. -/
theorem Reach4.obstruction_persists {s t : MSt} {n : ℕ} (h : Reach4 s t n) {u v : ℕ}
    (huv : s.M (u, v) ≠ 0) : t.M (u, v) ≠ 0 :=
  h.asserted_persists huv

/-- Adding `xrx` makes `xrx` asserted in every state. -/
theorem adding_xrx_always_obstructed4 (s : MSt) (x : ℕ) : ¬ (s.addAssertion x x).Legal := by
  intro h
  have := h x
  change Function.update s.M (x, x) (s.M (x, x) + 1) (x, x) = 0 at this
  rw [Function.update_self] at this
  omega

/-- Adding `xrx` is obstructed after every sequence of changes: no further changes
make it performable. -/
theorem Reach4.xrx_still_obstructed {s t : MSt} {n : ℕ} (_h : Reach4 s t n) (x : ℕ) :
    ¬ (t.addAssertion x x).Legal :=
  adding_xrx_always_obstructed4 t x

/-- The fewest classes of a split of the support never decreases (second derivation's
`Carries.split` on the containment of the supports). -/
theorem Reach4.split_mono {s t : MSt} {n : ℕ} (h : Reach4 s t n) (hw : s.WF) {k : ℕ}
    (ht : Split (toSt t) k) : Split (toSt s) k :=
  (h.contains.toSt hw).carries.split ht

/-! ## A multiplicity can rise -/

/-- Adding `arb` again is a performed change of the beginning without `bra`, and
afterwards `arb` has multiplicity two: the multiplicity of `arb` is not kept at one. -/
theorem arb_twice :
    Step4 givenA4 (givenA4.addAssertion 0 1) ∧ (givenA4.addAssertion 0 1).M (0, 1) = 2 := by
  refine ⟨Step4.addAssertion givenA4 0 1 (by simp [givenA4, ofSt, givenA])
    (by simp [givenA4, ofSt, givenA]) (by omega), ?_⟩
  change Function.update givenA4.M (0, 1) (givenA4.M (0, 1) + 1) (0, 1) = 2
  rw [Function.update_self, givenA4_arb]

end Seed.Fourth
