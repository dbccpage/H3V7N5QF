import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

/-!
# What is given, and what an identification does to the asserting

Terms are the elements of a type `T`.  `R x y` reads "`xry` is asserted".
Nothing about `R` is assumed beyond what the seed gives.

* given: `R a b`; for no `x` is `R x x` allowed (`Legal`).
* derived here: `a ≠ b`; `bra` is neither refuted nor derived; on the two given
  terms there are exactly two legal ways of asserting that contain `arb`;
  an identification makes some `xrx` asserted exactly when it merges the two
  terms of an asserted `xry`; once asserted, `xrx` survives every
  identification and every addition.
-/

namespace Seed

variable {T U : Type*}

/-- For no term `x` is `xrx` asserted. -/
def Legal (R : T → T → Prop) : Prop := ∀ x, ¬ R x x

/-- The two given terms are two terms. -/
theorem given_distinct {R : T → T → Prop} (h : Legal R) {a b : T} (hab : R a b) : a ≠ b := by
  rintro rfl
  exact h _ hab

/-- `bra` is not refuted: what is given holds in a legal asserting with `bra`. -/
theorem bra_not_refuted :
    ∃ R : Bool → Bool → Prop, Legal R ∧ R false true ∧ R true false :=
  ⟨fun x y => x ≠ y, fun _ h => h rfl, by decide, by decide⟩

/-- `bra` is not derived: what is given holds in a legal asserting without `bra`. -/
theorem bra_not_derived :
    ∃ R : Bool → Bool → Prop, Legal R ∧ R false true ∧ ¬ R true false :=
  ⟨fun x y => x = false ∧ y = true, fun x h => by cases x <;> simp_all, ⟨rfl, rfl⟩, by simp⟩

/-- On the two given terms alone, a legal asserting that contains `arb` is one of
exactly two: `arb` only, or `arb` and `bra`. -/
theorem two_states_on_given_terms (R : Bool → Bool → Prop) (h : Legal R)
    (hab : R false true) :
    (∀ x y, R x y ↔ (x = false ∧ y = true)) ∨ (∀ x y, R x y ↔ x ≠ y) := by
  have h0 := h false
  have h1 := h true
  by_cases hba : R true false
  · right
    intro x y
    cases x <;> cases y <;> simp [hab, hba, h0, h1]
  · left
    intro x y
    cases x <;> cases y <;> simp [hab, hba, h0, h1]

/-- The two alternatives really differ. -/
theorem two_states_differ :
    ¬ ((∀ x y : Bool, (x = false ∧ y = true) ↔ x ≠ y)) := by
  intro h
  have := (h true false).2 (by decide)
  simp at this

/-- Not given, and it would decide `bra`: if asserting passed on (`xry`, `yrz` give
`xrz`) then `bra` could not be asserted.  Since passing on is not given, nothing
follows about `bra` from this. -/
theorem passing_on_refutes_bra {R : T → T → Prop} (h : Legal R)
    (pass : ∀ x y z, R x y → R y z → R x z) {a b : T} (hab : R a b) : ¬ R b a :=
  fun hba => h a (pass a b a hab hba)

/-- What is asserted after every term `x` is replaced by `q x` in every assertion. -/
def Image (q : T → U) (R : T → T → Prop) : U → U → Prop :=
  fun x' y' => ∃ x y, q x = x' ∧ q y = y' ∧ R x y

/-- A replacement makes some `xrx` asserted exactly when it merges the two terms
of something asserted. -/
theorem image_loop_iff (q : T → U) (R : T → T → Prop) :
    (∃ w, Image q R w w) ↔ ∃ x y, R x y ∧ q x = q y := by
  constructor
  · rintro ⟨w, x, y, hx, hy, hR⟩
    exact ⟨x, y, hR, hx.trans hy.symm⟩
  · rintro ⟨x, y, hR, hq⟩
    exact ⟨q x, x, y, rfl, hq.symm, hR⟩

/-- Identifying `u` and `v`: both are replaced by one term (written `u`). -/
def merge [DecidableEq T] (u v : T) (x : T) : T := if x = v then u else x

@[simp] theorem merge_left [DecidableEq T] (u v : T) : merge u v u = u := by
  unfold merge; split <;> rfl

@[simp] theorem merge_right [DecidableEq T] (u v : T) : merge u v v = u := by
  unfold merge; simp

theorem merge_of_ne [DecidableEq T] {u v x : T} (h : x ≠ v) : merge u v x = x := by
  unfold merge; simp [h]

/-- If an identification merges two different terms, they are the two identified. -/
theorem merge_eq_merge [DecidableEq T] {u v x y : T} (hxy : x ≠ y)
    (h : merge u v x = merge u v y) : (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  unfold merge at h
  split_ifs at h with hx hy hy
  · exact absurd (hx.trans hy.symm) hxy
  · exact Or.inr ⟨hx, h.symm⟩
  · exact Or.inl ⟨h, hy⟩
  · exact absurd h hxy

/-- **Obstruction of an identification.**  Identifying `u` and `v` in a legal
asserting makes some `xrx` asserted exactly when `urv` or `vru` is asserted. -/
theorem identification_obstructed_iff [DecidableEq T] {R : T → T → Prop} (h : Legal R)
    (u v : T) : (∃ w, Image (merge u v) R w w) ↔ (R u v ∨ R v u) := by
  rw [image_loop_iff]
  constructor
  · rintro ⟨x, y, hR, hq⟩
    have hxy : x ≠ y := by
      rintro rfl
      exact h _ hR
    rcases merge_eq_merge hxy hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hR
    · exact Or.inr hR
  · rintro (hR | hR)
    · exact ⟨u, v, hR, by simp⟩
    · exact ⟨v, u, hR, by simp⟩

/-- Once `xrx` is asserted, every replacement of terms leaves some `xrx` asserted. -/
theorem loop_survives_replacement (q : T → U) {R : T → T → Prop} {x : T} (hx : R x x) :
    Image q R (q x) (q x) :=
  ⟨x, x, rfl, rfl, hx⟩

/-- Once `xrx` is asserted, asserting more leaves it asserted. -/
theorem loop_survives_additions {R R' : T → T → Prop} (hsub : ∀ x y, R x y → R' x y)
    {x : T} (hx : R x x) : R' x x :=
  hsub x x hx

/-- So an illegal asserting becomes legal only by un-asserting: if `R'` is legal and
`R` is not, some assertion of `R` is missing from `R'`. -/
theorem only_removal_restores {R R' : T → T → Prop} (hR : ¬ Legal R) (hR' : Legal R') :
    ∃ x y, R x y ∧ ¬ R' x y := by
  by_contra hcon
  exact hR fun x hx => hcon ⟨x, x, hx, hR' x⟩

end Seed
