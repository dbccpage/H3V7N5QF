import Third.Answers

/-!
# The fourth seed: assertions are counted

`prompt/fourth/seed_prompt.md` differs from the third seed in two sentences: an
assertion is asserted a number of times, its multiplicity, and adding an
assertion raises its multiplicity by one; `arb` is asserted with multiplicity
one.  So the state changes: a counted state `MSt` has terms, a multiplicity for
each ordered pair of terms, and the two names.  "Asserted" means multiplicity
at least one.

Two maps connect the counted states with the earlier derivations' states
`Seed.St`, both needed to cite earlier results and to say whether they survive
the counting:
* `ofSt`: an earlier state read as a counted state asserting everything once
  (the *indicator*);
* `toSt`: the earlier state asserting exactly what a counted state asserts
  (the *support*).
The support of the indicator is the state itself (`toSt_ofSt`); the indicator
of the support is the counted state exactly when nothing is asserted twice
(`ofSt_toSt`, `Simple`).

Derived here: `a ≠ b` in every legal counted state asserting `arb`
(`names_apart_of_legal`, the first derivation's `given_distinct` on the
relation "multiplicity positive"); the two beginnings `givenA4`, `givenB4` are
legal and well formed; the size (terms plus the sum of the multiplicities)
rises by exactly one when a term is added or a multiplicity raised
(`size_addTerm`, `size_addAssertion`).
-/

namespace Seed.Fourth

open Seed Seed.Second Seed.Third

/-- Terms, a multiplicity for each ordered pair of terms, and the terms named `a`, `b`. -/
@[ext]
structure MSt where
  T : Finset ℕ
  M : ℕ × ℕ → ℕ
  a : ℕ
  b : ℕ

namespace MSt

/-- No `xrx` is asserted: every `xrx` has multiplicity zero. -/
def Legal (s : MSt) : Prop := ∀ x, s.M (x, x) = 0

/-- Only pairs of terms that are there have a positive multiplicity, and the names
are carried by terms. -/
def WF (s : MSt) : Prop := (∀ p, s.M p ≠ 0 → p.1 ∈ s.T ∧ p.2 ∈ s.T) ∧ s.a ∈ s.T ∧ s.b ∈ s.T

/-- Nothing is asserted more than once. -/
def Simple (s : MSt) : Prop := ∀ p, s.M p ≤ 1

/-- Adding a term. -/
def addTerm (s : MSt) (t : ℕ) : MSt := ⟨insert t s.T, s.M, s.a, s.b⟩

/-- Adding an assertion: its multiplicity rises by one. -/
def addAssertion (s : MSt) (x y : ℕ) : MSt :=
  ⟨s.T, Function.update s.M (x, y) (s.M (x, y) + 1), s.a, s.b⟩

/-- The sum of the multiplicities over the pairs of terms. -/
def total (s : MSt) : ℕ := ∑ p ∈ s.T ×ˢ s.T, s.M p

/-- Terms plus assertions, counted with multiplicity. -/
def size (s : MSt) : ℕ := s.T.card + s.total

end MSt

open MSt

/-! ## The two maps to and from the earlier states -/

/-- An earlier state read as a counted state: everything it asserts, once. -/
def ofSt (s : St) : MSt := ⟨s.T, fun p => if p ∈ s.A then 1 else 0, s.a, s.b⟩

/-- The support of a counted state: the earlier state asserting what has positive
multiplicity. -/
def toSt (s : MSt) : St := ⟨s.T, (s.T ×ˢ s.T).filter (fun p => s.M p ≠ 0), s.a, s.b⟩

@[simp] theorem ofSt_T (s : St) : (ofSt s).T = s.T := rfl
@[simp] theorem ofSt_a (s : St) : (ofSt s).a = s.a := rfl
@[simp] theorem ofSt_b (s : St) : (ofSt s).b = s.b := rfl
@[simp] theorem toSt_T (s : MSt) : (toSt s).T = s.T := rfl
@[simp] theorem toSt_a (s : MSt) : (toSt s).a = s.a := rfl
@[simp] theorem toSt_b (s : MSt) : (toSt s).b = s.b := rfl

theorem ofSt_M (s : St) (p : ℕ × ℕ) : (ofSt s).M p = if p ∈ s.A then 1 else 0 := rfl

theorem mem_toSt_A {s : MSt} {p : ℕ × ℕ} :
    p ∈ (toSt s).A ↔ (p.1 ∈ s.T ∧ p.2 ∈ s.T) ∧ s.M p ≠ 0 := by
  simp [toSt, Finset.mem_filter, Finset.mem_product]

/-- With well-formedness the support asserts exactly what has positive multiplicity. -/
theorem mem_toSt_A_of_wf {s : MSt} (hw : s.WF) {p : ℕ × ℕ} : p ∈ (toSt s).A ↔ s.M p ≠ 0 := by
  rw [mem_toSt_A]
  exact ⟨fun h => h.2, fun h => ⟨hw.1 p h, h⟩⟩

/-- The support of the indicator is the state itself. -/
theorem toSt_ofSt {s : St} (hw : s.WF) : toSt (ofSt s) = s := by
  apply St.ext
  · rfl
  · ext p
    rw [mem_toSt_A, ofSt_M]
    constructor
    · rintro ⟨_, h⟩
      by_contra hp
      simp [hp] at h
    · intro hp
      exact ⟨hw.1 p hp, by simp [hp]⟩
  · rfl
  · rfl

/-- The indicator of the support is the counted state, when nothing is asserted twice. -/
theorem ofSt_toSt {s : MSt} (hw : s.WF) (hs : s.Simple) : ofSt (toSt s) = s := by
  apply MSt.ext
  · rfl
  · funext p
    rw [ofSt_M]
    by_cases h : p ∈ (toSt s).A
    · rw [if_pos h]
      have h1 := (mem_toSt_A_of_wf hw).1 h
      have h2 := hs p
      omega
    · rw [if_neg h]
      have h1 : ¬ s.M p ≠ 0 := fun h' => h ((mem_toSt_A_of_wf hw).2 h')
      omega
  · rfl
  · rfl

theorem ofSt_simple (s : St) : (ofSt s).Simple := by
  intro p
  rw [ofSt_M]
  split_ifs <;> omega

theorem ofSt_legal {s : St} (hs : s.Legal) : (ofSt s).Legal := by
  intro x
  rw [ofSt_M]
  simp [hs x]

theorem ofSt_wf {s : St} (hw : s.WF) : (ofSt s).WF := by
  refine ⟨fun p hp => ?_, hw.2.1, hw.2.2⟩
  rw [ofSt_M] at hp
  by_contra hcon
  by_cases h : p ∈ s.A
  · exact hcon (hw.1 p h)
  · simp [h] at hp

theorem toSt_legal {s : MSt} (hs : s.Legal) : (toSt s).Legal := by
  intro x hx
  rw [mem_toSt_A] at hx
  exact hx.2 (hs x)

theorem toSt_wf {s : MSt} (hw : s.WF) : (toSt s).WF :=
  ⟨fun _ hp => (mem_toSt_A.1 hp).1, hw.2.1, hw.2.2⟩

/-! ## What is given -/

/-- What is given, `bra` not asserted: `arb` once. -/
def givenA4 : MSt := ofSt givenA

/-- What is given, `bra` asserted: `arb` once and `bra` once. -/
def givenB4 : MSt := ofSt givenB

theorem givenA4_legal : givenA4.Legal := ofSt_legal givenA_legal
theorem givenB4_legal : givenB4.Legal := ofSt_legal givenB_legal
theorem givenA4_wf : givenA4.WF := ofSt_wf givenA_wf
theorem givenB4_wf : givenB4.WF := ofSt_wf givenB_wf

theorem givenA4_arb : givenA4.M (0, 1) = 1 := by simp [givenA4, ofSt_M, givenA]
theorem givenA4_bra : givenA4.M (1, 0) = 0 := by simp [givenA4, ofSt_M, givenA]
theorem givenB4_arb : givenB4.M (0, 1) = 1 := by simp [givenB4, ofSt_M, givenB]
theorem givenB4_bra : givenB4.M (1, 0) = 1 := by simp [givenB4, ofSt_M, givenB]
theorem toSt_givenA4 : toSt givenA4 = givenA := toSt_ofSt givenA_wf
theorem toSt_givenB4 : toSt givenB4 = givenB := toSt_ofSt givenB_wf
theorem givenA4_a : givenA4.a = 0 := rfl
theorem givenA4_b : givenA4.b = 1 := rfl
theorem givenB4_a : givenB4.a = 0 := rfl
theorem givenB4_b : givenB4.b = 1 := rfl

theorem givenA4_arb_ne : givenA4.M (givenA4.a, givenA4.b) ≠ 0 := by
  rw [givenA4_a, givenA4_b, givenA4_arb]
  omega

theorem givenB4_arb_ne : givenB4.M (givenB4.a, givenB4.b) ≠ 0 := by
  rw [givenB4_a, givenB4_b, givenB4_arb]
  omega

theorem givenB4_bra_ne : givenB4.M (givenB4.b, givenB4.a) ≠ 0 := by
  rw [givenB4_a, givenB4_b, givenB4_bra]
  omega

/-- The two given terms are two terms: in a legal counted state with `arb` asserted,
`a ≠ b` (the first derivation's `given_distinct`, on the relation "positive
multiplicity"). -/
theorem names_apart_of_legal {s : MSt} (hs : s.Legal) (hab : s.M (s.a, s.b) ≠ 0) : s.a ≠ s.b :=
  given_distinct (R := fun x y => s.M (x, y) ≠ 0) (fun x h => h (hs x)) hab

/-! ## Size rises by exactly one -/

theorem total_addTerm {s : MSt} (hw : s.WF) (t : ℕ) : (s.addTerm t).total = s.total := by
  unfold MSt.total MSt.addTerm
  symm
  apply Finset.sum_subset
  · exact Finset.product_subset_product (Finset.subset_insert _ _) (Finset.subset_insert _ _)
  · intro p _ hp
    by_contra h
    exact hp (Finset.mem_product.2 (hw.1 p h))

theorem size_addTerm {s : MSt} (hw : s.WF) {t : ℕ} (ht : t ∉ s.T) :
    (s.addTerm t).size = s.size + 1 := by
  unfold MSt.size
  rw [total_addTerm hw]
  show (insert t s.T).card + s.total = s.T.card + s.total + 1
  rw [Finset.card_insert_of_notMem ht]
  omega

theorem total_addAssertion {s : MSt} {x y : ℕ} (hx : x ∈ s.T) (hy : y ∈ s.T) :
    (s.addAssertion x y).total = s.total + 1 := by
  unfold MSt.total MSt.addAssertion
  have hp : (x, y) ∈ s.T ×ˢ s.T := Finset.mem_product.2 ⟨hx, hy⟩
  rw [Finset.sum_update_of_mem hp, Finset.sdiff_singleton_eq_erase,
    ← Finset.sum_erase_add _ _ hp]
  omega

theorem size_addAssertion {s : MSt} {x y : ℕ} (hx : x ∈ s.T) (hy : y ∈ s.T) :
    (s.addAssertion x y).size = s.size + 1 := by
  unfold MSt.size
  rw [total_addAssertion hx hy]
  show s.T.card + (s.total + 1) = s.T.card + s.total + 1
  omega

theorem size_givenA4 : givenA4.size = 3 := by decide
theorem size_givenB4 : givenB4.size = 4 := by decide

/-- The size of a counted state asserting nothing twice is the size of its support. -/
theorem size_toSt {s : MSt} (hs : s.Simple) : (toSt s).size = s.size := by
  unfold St.size MSt.size MSt.total
  congr 1
  show ((s.T ×ˢ s.T).filter (fun p => s.M p ≠ 0)).card = ∑ p ∈ s.T ×ˢ s.T, s.M p
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro p _
  have := hs p
  split_ifs with h <;> omega

end Seed.Fourth
