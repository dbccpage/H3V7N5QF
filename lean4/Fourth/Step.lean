import Fourth.State

/-!
# The two kinds of change on counted states

`Step4` is one performed (unobstructed) change of the fourth seed: a new term, or
an assertion between two terms that are there — asserted already or not: its
multiplicity rises by one.  `Reach4 s t n`: `t` is reached from `s` by `n`
changes.

Cited from the third derivation and re-checked through the two maps:
* every change of the third seed is a change of the fourth on the indicator
  states (`Step2.toStep4`, `Reach2.toReach4`);
* a change of the fourth seed whose outcome asserts nothing twice is a change
  of the third seed on the supports (`Step4.toStep2`, `Reach4.toReach2`).
So the third derivation's theorems about changes apply to the counted seed
exactly on the states asserting nothing twice, and the statements proved
afresh here for all counted states are their extensions.

Derived here: legality, well-formedness and "at least one term" are preserved
(`Step4.legal`, `Step4.wf`, `Step4.nonempty`, and for sequences).
-/

namespace Seed.Fourth

open Seed Seed.Second Seed.Third MSt

/-- One performed (unobstructed) change of the fourth seed.  "Nothing else is a
change": the new term is new; the added assertion is between two terms that are
there, whether or not it is asserted already. -/
inductive Step4 : MSt → MSt → Prop
  | addTerm (s : MSt) (t : ℕ) (ht : t ∉ s.T) : Step4 s (s.addTerm t)
  | addAssertion (s : MSt) (x y : ℕ) (hx : x ∈ s.T) (hy : y ∈ s.T) (hxy : x ≠ y) :
      Step4 s (s.addAssertion x y)

/-! ## Invariants of one change -/

theorem Step4.legal {s t : MSt} (h : Step4 s t) (hs : s.Legal) : t.Legal := by
  cases h with
  | addTerm t ht => exact hs
  | addAssertion x y hx hy hxy =>
    intro z
    show Function.update s.M (x, y) (s.M (x, y) + 1) (z, z) = 0
    rw [Function.update_apply]
    split_ifs with h
    · exact absurd ((Prod.mk.inj h).1.symm.trans (Prod.mk.inj h).2) hxy
    · exact hs z

theorem Step4.wf {s t : MSt} (h : Step4 s t) (hs : s.WF) : t.WF := by
  cases h with
  | addTerm t ht =>
    refine ⟨fun p hp => ?_, Finset.mem_insert_of_mem hs.2.1, Finset.mem_insert_of_mem hs.2.2⟩
    exact ⟨Finset.mem_insert_of_mem (hs.1 p hp).1, Finset.mem_insert_of_mem (hs.1 p hp).2⟩
  | addAssertion x y hx hy hxy =>
    refine ⟨fun p hp => ?_, hs.2.1, hs.2.2⟩
    show p.1 ∈ s.T ∧ p.2 ∈ s.T
    change Function.update s.M (x, y) (s.M (x, y) + 1) p ≠ 0 at hp
    rw [Function.update_apply] at hp
    split_ifs at hp with h
    · subst h
      exact ⟨hx, hy⟩
    · exact hs.1 p hp

theorem Step4.nonempty {s t : MSt} (h : Step4 s t) (hs : s.T.Nonempty) : t.T.Nonempty := by
  cases h with
  | addTerm t ht => exact Finset.insert_nonempty _ _
  | addAssertion x y hx hy hxy => exact hs

/-! ## Sequences of changes -/

/-- `Reach4 s t n`: `t` is reached from `s` by `n` performed changes of the fourth seed. -/
inductive Reach4 : MSt → MSt → ℕ → Prop
  | refl (s : MSt) : Reach4 s s 0
  | step {s t u : MSt} {n : ℕ} : Reach4 s t n → Step4 t u → Reach4 s u (n + 1)

theorem Reach4.trans {s t u : MSt} {n m : ℕ} (h1 : Reach4 s t n) (h2 : Reach4 t u m) :
    Reach4 s u (n + m) := by
  induction h2 with
  | refl => exact h1
  | step _ st ih => exact Reach4.step ih st

/-- No change at all: the state is the same. -/
theorem Reach4.eq_of_zero {s t : MSt} (h : Reach4 s t 0) : s = t := by
  cases h
  rfl

theorem Reach4.legal {s t : MSt} {n : ℕ} (h : Reach4 s t n) (hs : s.Legal) : t.Legal := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.legal ih

theorem Reach4.wf {s t : MSt} {n : ℕ} (h : Reach4 s t n) (hs : s.WF) : t.WF := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.wf ih

theorem Reach4.nonempty {s t : MSt} {n : ℕ} (h : Reach4 s t n) (hs : s.T.Nonempty) :
    t.T.Nonempty := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.nonempty ih

/-! ## The third seed's changes are changes of the fourth, on indicator states -/

theorem ofSt_addTerm (s : St) (t : ℕ) : ofSt (s.addTerm t) = (ofSt s).addTerm t := rfl

theorem ofSt_addAssertion {s : St} {x y : ℕ} (hnew : (x, y) ∉ s.A) :
    ofSt (s.addAssertion x y) = (ofSt s).addAssertion x y := by
  apply MSt.ext
  · rfl
  · funext p
    show (if p ∈ insert (x, y) s.A then 1 else 0) =
      Function.update (fun q => if q ∈ s.A then 1 else 0) (x, y)
        ((if (x, y) ∈ s.A then 1 else 0) + 1) p
    rw [Function.update_apply]
    by_cases hp : p = (x, y)
    · subst hp
      simp [hnew]
    · simp [Finset.mem_insert, hp]
  · rfl
  · rfl

/-- Every change of the third seed is a change of the fourth on the indicator states. -/
theorem _root_.Seed.Third.Step2.toStep4 {s t : St} (h : Step2 s t) : Step4 (ofSt s) (ofSt t) := by
  cases h with
  | addTerm t ht =>
    rw [ofSt_addTerm]
    exact Step4.addTerm _ t ht
  | addAssertion x y hx hy hxy hnew =>
    rw [ofSt_addAssertion hnew]
    exact Step4.addAssertion _ x y hx hy hxy

theorem _root_.Seed.Third.Reach2.toReach4 {s t : St} {n : ℕ} (h : Reach2 s t n) : Reach4 (ofSt s) (ofSt t) n := by
  induction h with
  | refl => exact Reach4.refl _
  | step _ st ih => exact Reach4.step ih st.toStep4

/-! ## A change of the fourth seed whose outcome asserts nothing twice is a change of the third -/

theorem toSt_addTerm {s : MSt} (hw : s.WF) (t : ℕ) : toSt (s.addTerm t) = (toSt s).addTerm t := by
  apply St.ext
  · rfl
  · ext p
    rw [mem_toSt_A]
    show _ ↔ p ∈ (toSt s).A
    rw [mem_toSt_A]
    constructor
    · rintro ⟨_, h⟩
      exact ⟨hw.1 p h, h⟩
    · rintro ⟨⟨h1, h2⟩, h⟩
      exact ⟨⟨Finset.mem_insert_of_mem h1, Finset.mem_insert_of_mem h2⟩, h⟩
  · rfl
  · rfl

theorem toSt_addAssertion {s : MSt} {x y : ℕ} (hx : x ∈ s.T) (hy : y ∈ s.T) :
    toSt (s.addAssertion x y) = (toSt s).addAssertion x y := by
  apply St.ext
  · rfl
  · ext p
    rw [mem_toSt_A]
    show ((p.1 ∈ s.T ∧ p.2 ∈ s.T) ∧ Function.update s.M (x, y) (s.M (x, y) + 1) p ≠ 0) ↔
      p ∈ insert (x, y) (toSt s).A
    rw [Finset.mem_insert, mem_toSt_A, Function.update_apply]
    by_cases hp : p = (x, y)
    · subst hp
      simp [hx, hy]
    · simp [hp]
  · rfl
  · rfl

/-- The multiplicity of the added assertion was zero if the outcome asserts nothing twice. -/
theorem Step4.mult_zero_of_simple {s : MSt} {x y : ℕ} (hs : (s.addAssertion x y).Simple) :
    s.M (x, y) = 0 := by
  have := hs (x, y)
  change Function.update s.M (x, y) (s.M (x, y) + 1) (x, y) ≤ 1 at this
  rw [Function.update_self] at this
  omega

/-- A change of the fourth seed whose outcome asserts nothing twice is a change of the
third seed on the supports. -/
theorem Step4.toStep2 {s t : MSt} (h : Step4 s t) (hw : s.WF) (ht : t.Simple) :
    Step2 (toSt s) (toSt t) := by
  cases h with
  | addTerm t ht' =>
    rw [toSt_addTerm hw]
    exact Step2.addTerm _ t ht'
  | addAssertion x y hx hy hxy =>
    rw [toSt_addAssertion hx hy]
    refine Step2.addAssertion _ x y hx hy hxy ?_
    rw [mem_toSt_A_of_wf hw]
    simp [Step4.mult_zero_of_simple ht]

/-- A state whose outcome asserts nothing twice asserts nothing twice itself. -/
theorem Step4.simple_of_simple {s t : MSt} (h : Step4 s t) (ht : t.Simple) : s.Simple := by
  cases h with
  | addTerm t ht' => exact ht
  | addAssertion x y hx hy hxy =>
    intro p
    have := ht p
    change Function.update s.M (x, y) (s.M (x, y) + 1) p ≤ 1 at this
    rw [Function.update_apply] at this
    split_ifs at this with hp
    · subst hp
      omega
    · exact this

theorem Reach4.toReach2 {s t : MSt} {n : ℕ} (h : Reach4 s t n) (hw : s.WF) (ht : t.Simple) :
    Reach2 (toSt s) (toSt t) n := by
  induction h with
  | refl => exact Reach2.refl _
  | step r st ih => exact Reach2.step (ih (st.simple_of_simple ht)) (st.toStep2 (r.wf hw) ht)

/-- Every state along a sequence ending in a state asserting nothing twice asserts
nothing twice. -/
theorem Reach4.simple_of_simple {s t : MSt} {n : ℕ} (h : Reach4 s t n) (ht : t.Simple) :
    s.Simple := by
  induction h with
  | refl => exact ht
  | step _ st ih => exact ih (st.simple_of_simple ht)

end Seed.Fourth
