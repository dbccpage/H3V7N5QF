import Third.Step

/-!
# Containment: nothing is ever taken away

Every change of the third seed adds one term or one assertion and takes nothing
away, so a state is contained in its outcome: every term, every asserted `xry`
and both names are in place (`Step2.contains`).  Containment composes, so every
sequence of changes leaves its start contained in its end (`Reach2.contains`).

Cited from the second derivation and re-checked: containment is a carrying map
with the identity as the map (`Contains.carries`), and every sequence of the
third seed is a sequence of the second (`Reach2.toReach3`); so what the second
derivation derived from the carrying map restricts to this seed.  It is also
derived here directly from containment, which is stronger: the assertions
themselves persist, not only their images.

Derived here from containment:
* every term and every assertion persists (`Reach2.term_persists`,
  `Reach2.asserted_persists`); `a` and `b` are never one term, and `arb` (and
  `bra`, if asserted) is never lost (`Reach2.names_apart`,
  `Reach2.arb_persists`, `Reach2.bra_persists`); every result has at least two
  terms (`Reach2.two_terms`);
* the numbers of terms and of assertions never decrease (`Reach2.card_T_le`,
  `Reach2.card_A_le`);
* an obstruction is never cleared: an assertion that obstructs stays asserted
  (`Reach2.obstruction_persists`), and adding `xrx` stays obstructed after any
  sequence of changes (`Reach2.xrx_still_obstructed`);
* the fewest classes of a split never decreases (`Reach2.split_mono`, through the
  embedding);
* containment is one-way (`Contains.antisymm`).
-/

namespace Seed.Third

open Seed Seed.Second St

/-- `s` is contained in `t`: terms, assertions and names in place. -/
structure Contains (s t : St) : Prop where
  terms : s.T ⊆ t.T
  asserted : s.A ⊆ t.A
  name_a : t.a = s.a
  name_b : t.b = s.b

theorem Contains.refl (s : St) : Contains s s :=
  ⟨Finset.Subset.refl _, Finset.Subset.refl _, rfl, rfl⟩

theorem Contains.trans {s t u : St} (h : Contains s t) (h' : Contains t u) : Contains s u :=
  ⟨h.terms.trans h'.terms, h.asserted.trans h'.asserted, h'.name_a.trans h.name_a,
    h'.name_b.trans h.name_b⟩

/-- Containment is one-way: two states contained in each other are the same state. -/
theorem Contains.antisymm {s t : St} (h : Contains s t) (h' : Contains t s) : s = t := by
  apply St.ext
  · exact Finset.Subset.antisymm h.terms h'.terms
  · exact Finset.Subset.antisymm h.asserted h'.asserted
  · exact h.name_a.symm
  · exact h.name_b.symm

/-- One change leaves its state contained in its outcome. -/
theorem Step2.contains {s t : St} (h : Step2 s t) : Contains s t := by
  cases h with
  | addTerm t ht => exact ⟨Finset.subset_insert _ _, Finset.Subset.refl _, rfl, rfl⟩
  | addAssertion x y hx hy hxy hnew => exact ⟨Finset.Subset.refl _, Finset.subset_insert _ _, rfl, rfl⟩

/-- A sequence of changes leaves its start contained in its end. -/
theorem Reach2.contains {s t : St} {n : ℕ} (h : Reach2 s t n) : Contains s t := by
  induction h with
  | refl => exact Contains.refl _
  | step _ st ih => exact ih.trans st.contains

/-- Containment is a carrying map (second derivation's `Carries`) with the identity. -/
theorem Contains.carries {s t : St} (h : Contains s t) : Carries id s t :=
  ⟨fun _ hx => h.terms hx, fun _ hp => by simpa using h.asserted hp, h.name_a.symm,
    h.name_b.symm⟩

/-! ## What is given survives -/

theorem Reach2.term_persists {s t : St} {n : ℕ} (h : Reach2 s t n) {x : ℕ} (hx : x ∈ s.T) :
    x ∈ t.T := h.contains.terms hx

theorem Reach2.asserted_persists {s t : St} {n : ℕ} (h : Reach2 s t n) {p : ℕ × ℕ}
    (hp : p ∈ s.A) : p ∈ t.A := h.contains.asserted hp

theorem Reach2.name_a {s t : St} {n : ℕ} (h : Reach2 s t n) : t.a = s.a := h.contains.name_a

theorem Reach2.name_b {s t : St} {n : ℕ} (h : Reach2 s t n) : t.b = s.b := h.contains.name_b

/-- `arb`, once asserted, is asserted after every sequence of changes (second
derivation's `Reach3.arb_persists`, through the embedding). -/
theorem Reach2.arb_persists {s t : St} {n : ℕ} (h : Reach2 s t n) (hab : (s.a, s.b) ∈ s.A) :
    (t.a, t.b) ∈ t.A :=
  h.toReach3.arb_persists hab

/-- `bra`, once asserted, is asserted after every sequence of changes. -/
theorem Reach2.bra_persists {s t : St} {n : ℕ} (h : Reach2 s t n) (hba : (s.b, s.a) ∈ s.A) :
    (t.b, t.a) ∈ t.A :=
  h.toReach3.bra_persists hba

/-- `a` and `b` are never one term. -/
theorem Reach2.names_apart {s t : St} {n : ℕ} (h : Reach2 s t n) (hs : s.Legal)
    (hab : (s.a, s.b) ∈ s.A) : t.a ≠ t.b :=
  h.toReach3.names_apart hs hab

/-- Every result has at least two terms. -/
theorem Reach2.two_terms {s t : St} {n : ℕ} (h : Reach2 s t n) (hs : s.Legal) (hw : s.WF)
    (hab : (s.a, s.b) ∈ s.A) : 2 ≤ t.T.card :=
  h.toReach3.two_terms hs hw hab

/-! ## Counts never decrease -/

theorem Reach2.card_T_le {s t : St} {n : ℕ} (h : Reach2 s t n) : s.T.card ≤ t.T.card :=
  Finset.card_le_card h.contains.terms

theorem Reach2.card_A_le {s t : St} {n : ℕ} (h : Reach2 s t n) : s.A.card ≤ t.A.card :=
  Finset.card_le_card h.contains.asserted

/-! ## An obstruction is never cleared -/

/-- Whatever is asserted stays asserted: in particular an assertion that obstructs
(the second seed's `urv`) is still there after any sequence of changes.  Stronger
than the second derivation's `Reach3.obstruction_persists`, which has it for the
images of `u`, `v`. -/
theorem Reach2.obstruction_persists {s t : St} {n : ℕ} (h : Reach2 s t n) {u v : ℕ}
    (huv : (u, v) ∈ s.A) : (u, v) ∈ t.A :=
  h.asserted_persists huv

/-- Adding `xrx` is obstructed after every sequence of changes: no further changes
make it performable (first derivation's `adding_xrx_always_obstructed`, on the
state reached). -/
theorem Reach2.xrx_still_obstructed {s t : St} {n : ℕ} (_h : Reach2 s t n) (x : ℕ) :
    ¬ (t.addAssertion x x).Legal :=
  adding_xrx_always_obstructed t x

/-- The fewest classes of a split never decreases (second derivation's
`Reach3.split_mono`, through the embedding). -/
theorem Reach2.split_mono {s t : St} {n : ℕ} (h : Reach2 s t n) {k : ℕ} (ht : Split t k) :
    Split s k :=
  h.toReach3.split_mono ht

end Seed.Third
