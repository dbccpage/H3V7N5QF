import Fifth.State

/-!
# The four kinds of change on counted states

`Step5` is one performed (unobstructed) change of the fifth seed: a new term; an
assertion between two terms that are there, asserted already or not; the
removal of an asserted assertion (its multiplicity falls by one); the
identification of two terms that are there with nothing asserted between them.
`Reach5 s t n`: `t` is reached from `s` by `n` changes.

Cited from the fourth derivation and re-checked: every change of the fourth seed
is a change of the fifth (`Step4.toStep5`, `Reach4.toReach5`), and a change of
the fifth is a removal, an identification, or a change of the fourth
(`Step5.cases4`).  So what the fourth derivation proved for *every* sequence of
its changes holds for the fifth's sequences of additions, and what it proved
from "a change only adds" must be re-examined on removals and identifications.

Cited from the first derivation and re-checked: between states asserting nothing
twice, a change of the fifth seed is a change of the first seed on the supports
(`Step5.toStep`); the first's `Step.names_stay_merged` and
`Reach.arb_gone_for_good` are re-proved on counted states
(`Step5.names_stay_merged`, `Reach5.names_stay_merged`,
`Reach5.arb_gone_for_good`).

Derived here: which changes are obstructed (`remove_legal`, `identify_legal_iff`);
legality, well-formedness and "at least one term" are preserved (`Step5.legal`,
`Step5.wf`, `Step5.nonempty`, and for sequences).
-/

namespace Seed.Fifth

open Seed Seed.Fourth MSt

/-- One performed (unobstructed) change of the fifth seed.  "Nothing else is a
change": the new term is new; the added assertion is between two terms that are
there; the removed assertion is asserted; the identified terms are two terms that
are there with nothing asserted between them. -/
inductive Step5 : MSt → MSt → Prop
  | addTerm (s : MSt) (t : ℕ) (ht : t ∉ s.T) : Step5 s (s.addTerm t)
  | addAssertion (s : MSt) (x y : ℕ) (hx : x ∈ s.T) (hy : y ∈ s.T) (hxy : x ≠ y) :
      Step5 s (s.addAssertion x y)
  | remove (s : MSt) (x y : ℕ) (hp : s.M (x, y) ≠ 0) : Step5 s (s.remove x y)
  | identify (s : MSt) (u v : ℕ) (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v)
      (h1 : s.M (u, v) = 0) (h2 : s.M (v, u) = 0) : Step5 s (s.identify u v)

/-- Every change of the fourth seed is a change of the fifth. -/
theorem _root_.Seed.Fourth.Step4.toStep5 {s t : MSt} (h : Step4 s t) : Step5 s t := by
  cases h with
  | addTerm t ht => exact Step5.addTerm s t ht
  | addAssertion x y hx hy hxy => exact Step5.addAssertion s x y hx hy hxy

/-- A change of the fifth seed is a removal, an identification, or a change of the
fourth seed. -/
theorem Step5.cases4 {s t : MSt} (h : Step5 s t) :
    (∃ x y, s.M (x, y) ≠ 0 ∧ t = s.remove x y) ∨
      (∃ u v, u ∈ s.T ∧ v ∈ s.T ∧ u ≠ v ∧ t = s.identify u v) ∨ Step4 s t := by
  cases h with
  | addTerm t ht => exact Or.inr (Or.inr (Step4.addTerm s t ht))
  | addAssertion x y hx hy hxy => exact Or.inr (Or.inr (Step4.addAssertion s x y hx hy hxy))
  | remove x y hp => exact Or.inl ⟨x, y, hp, rfl⟩
  | identify u v hu hv huv h1 h2 => exact Or.inr (Or.inl ⟨u, v, hu, hv, huv, rfl⟩)

/-! ## Which changes are obstructed -/

/-- Removing an assertion is never obstructed. -/
theorem remove_legal {s : MSt} (hs : s.Legal) (x y : ℕ) : (s.remove x y).Legal := by
  intro z
  rw [remove_M, Function.update_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    rw [hs z]
  · exact hs z

/-- Identifying `u` and `v` in a legal state is unobstructed exactly when neither `urv`
nor `vru` is asserted (the first derivation's `identify_legal_iff`, with
multiplicities). -/
theorem identify_legal_iff {s : MSt} (hs : s.Legal) {u v : ℕ} (hu : u ∈ s.T) (hv : v ∈ s.T)
    (huv : u ≠ v) : (s.identify u v).Legal ↔ s.M (u, v) = 0 ∧ s.M (v, u) = 0 := by
  constructor
  · intro h
    have h1 := (identify_M_eq_zero_iff s u v (u, u)).1 (h u) u v hu hv (by simp)
    have h2 := (identify_M_eq_zero_iff s u v (u, u)).1 (h u) v u hv hu (by simp)
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩ z
    rw [identify_M_eq_zero_iff]
    intro x y hx hy hp
    simp only [Prod.mk.injEq] at hp
    by_cases hxy : x = y
    · subst hxy
      exact hs x
    · rcases merge_eq_merge hxy (hp.1.trans hp.2.symm) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h1
      · exact h2

/-! ## Invariants of one change -/

theorem Step5.legal {s t : MSt} (h : Step5 s t) (hs : s.Legal) : t.Legal := by
  cases h with
  | addTerm t ht => exact (Step4.addTerm s t ht).legal hs
  | addAssertion x y hx hy hxy => exact (Step4.addAssertion s x y hx hy hxy).legal hs
  | remove x y hp => exact remove_legal hs x y
  | identify u v hu hv huv h1 h2 => exact (identify_legal_iff hs hu hv huv).2 ⟨h1, h2⟩

theorem Step5.wf {s t : MSt} (h : Step5 s t) (hw : s.WF) : t.WF := by
  cases h with
  | addTerm t ht => exact (Step4.addTerm s t ht).wf hw
  | addAssertion x y hx hy hxy => exact (Step4.addAssertion s x y hx hy hxy).wf hw
  | remove x y hp =>
    refine ⟨fun p hne => ?_, hw.2.1, hw.2.2⟩
    rw [remove_M, Function.update_apply] at hne
    split_ifs at hne with h
    · subst h
      exact hw.1 _ hp
    · exact hw.1 p hne
  | identify u v hu hv huv h1 h2 =>
    refine ⟨fun p hne => ?_, merge_mem_erase hu huv hw.2.1, merge_mem_erase hu huv hw.2.2⟩
    obtain ⟨x, y, hx, hy, hp, _⟩ := identify_M_ne_zero s u v hne
    rw [← hp]
    exact ⟨merge_mem_erase hu huv hx, merge_mem_erase hu huv hy⟩

theorem Step5.nonempty {s t : MSt} (h : Step5 s t) (hs : s.T.Nonempty) : t.T.Nonempty := by
  cases h with
  | addTerm t ht => exact Finset.insert_nonempty _ _
  | addAssertion x y hx hy hxy => exact hs
  | remove x y hp => exact hs
  | identify u v hu hv huv h1 h2 => exact ⟨u, Finset.mem_erase.2 ⟨huv, hu⟩⟩

/-- Once `a` and `b` are one term they stay one term (the first derivation's
`Step.names_stay_merged`, re-proved). -/
theorem Step5.names_stay_merged {s t : MSt} (h : Step5 s t) (hab : s.a = s.b) : t.a = t.b := by
  cases h with
  | addTerm t ht => exact hab
  | addAssertion x y hx hy hxy => exact hab
  | remove x y hp => exact hab
  | identify u v hu hv huv h1 h2 =>
    show merge u v s.a = merge u v s.b
    rw [hab]

/-! ## Sequences of changes -/

/-- `Reach5 s t n`: `t` is reached from `s` by `n` performed changes of the fifth seed. -/
inductive Reach5 : MSt → MSt → ℕ → Prop
  | refl (s : MSt) : Reach5 s s 0
  | step {s t u : MSt} {n : ℕ} : Reach5 s t n → Step5 t u → Reach5 s u (n + 1)

theorem Reach5.trans {s t u : MSt} {n m : ℕ} (h1 : Reach5 s t n) (h2 : Reach5 t u m) :
    Reach5 s u (n + m) := by
  induction h2 with
  | refl => exact h1
  | step _ st ih => exact Reach5.step ih st

theorem Reach5.single {s t : MSt} (h : Step5 s t) : Reach5 s t 1 := Reach5.step (Reach5.refl s) h

theorem Reach5.eq_of_zero {s t : MSt} (h : Reach5 s t 0) : s = t := by
  cases h
  rfl

theorem Reach5.legal {s t : MSt} {n : ℕ} (h : Reach5 s t n) (hs : s.Legal) : t.Legal := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.legal ih

theorem Reach5.wf {s t : MSt} {n : ℕ} (h : Reach5 s t n) (hs : s.WF) : t.WF := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.wf ih

theorem Reach5.nonempty {s t : MSt} {n : ℕ} (h : Reach5 s t n) (hs : s.T.Nonempty) :
    t.T.Nonempty := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.nonempty ih

/-- Every sequence of changes of the fourth seed is a sequence of the fifth. -/
theorem _root_.Seed.Fourth.Reach4.toReach5 {s t : MSt} {n : ℕ} (h : Reach4 s t n) :
    Reach5 s t n := by
  induction h with
  | refl => exact Reach5.refl _
  | step _ st ih => exact Reach5.step ih st.toStep5

/-- Identifying `a` and `b` cannot be undone by any sequence of changes (the first
derivation's `Reach.names_stay_merged`, re-proved). -/
theorem Reach5.names_stay_merged {s t : MSt} {n : ℕ} (h : Reach5 s t n) (hab : s.a = s.b) :
    t.a = t.b := by
  induction h with
  | refl => exact hab
  | step _ st ih => exact st.names_stay_merged ih

/-- After `a` and `b` are identified, `arb` is never asserted again. -/
theorem Reach5.arb_gone_for_good {s t : MSt} {n : ℕ} (h : Reach5 s t n) (hs : s.Legal)
    (hab : s.a = s.b) : t.M (t.a, t.b) = 0 := by
  rw [h.names_stay_merged hab]
  exact h.legal hs _

/-! ## On states asserting nothing twice, a change of the fifth seed is a change of the first -/

/-- Between well-formed states asserting nothing twice, a change of the fifth seed is a
change of the first seed on the supports. -/
theorem Step5.toStep {s t : MSt} (h : Step5 s t) (hw : s.WF) (hs : s.Simple) (ht : t.Simple) :
    Step (toSt s) (toSt t) := by
  cases h with
  | addTerm t ht' => exact ((Step4.addTerm s t ht').toStep2 hw ht).toStep
  | addAssertion x y hx hy hxy => exact ((Step4.addAssertion s x y hx hy hxy).toStep2 hw ht).toStep
  | remove x y hp =>
    have h1 : s.M (x, y) = 1 := by
      have := hs (x, y)
      omega
    rw [toSt_remove h1]
    exact Step.remove _ (x, y) ((mem_toSt_A_of_wf hw).2 hp)
  | identify u v hu hv huv h1 h2 =>
    rw [toSt_identify hw hu huv]
    refine Step.identify _ u v hu hv huv ?_ ?_
    · rw [mem_toSt_A_of_wf hw]
      simp [h1]
    · rw [mem_toSt_A_of_wf hw]
      simp [h2]

end Seed.Fifth
