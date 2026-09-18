import Second.Answers

/-!
# The third seed: two kinds of change

`prompt/third/seed_prompt.md` differs from the second seed in one sentence:
identifying two terms is not a change.  The states are those of the first
derivation (`Seed.St`, with its `addTerm` and `addAssertion`); the changes are a
new inductive `Step2` with two constructors.

Cited from the earlier derivations and re-checked here: every `Step2` is a
`Step3` of the second seed (`Step2.toStep3`) and hence a `Step` of the first
(`Step2.toStep`), so the earlier theorems about one change and about sequences
of changes restrict to the third seed.  Through this embedding legality,
well-formedness and "at least one term" are inherited (`Step2.legal`,
`Step2.wf`, `Step2.nonempty`, `Reach2.legal`, `Reach2.wf`, `Reach2.nonempty`),
and so are the earlier lower bounds on the number of changes
(`Reach2.size_le_inherited`, `Reach2.costA_le_inherited`).  Conversely a change
of the second seed is an identification or a change of the third
(`Step3.identify_or_step2`), and no change of the third seed has the outcome of
an identification or of a removal (`Step2.ne_identify`, `Step2.ne_remove`).
-/

namespace Seed.Third

open Seed Seed.Second St

/-- One performed (unobstructed) change of the third seed.  "Nothing else is a
change": the new term is new, the added assertion is new and between two terms
that are there. -/
inductive Step2 : St → St → Prop
  | addTerm (s : St) (t : ℕ) (ht : t ∉ s.T) : Step2 s (s.addTerm t)
  | addAssertion (s : St) (x y : ℕ) (hx : x ∈ s.T) (hy : y ∈ s.T) (hxy : x ≠ y)
      (hnew : (x, y) ∉ s.A) : Step2 s (s.addAssertion x y)

/-- Every change of the third seed is a change of the second. -/
theorem Step2.toStep3 {s t : St} (h : Step2 s t) : Step3 s t := by
  cases h with
  | addTerm t ht => exact Step3.addTerm s t ht
  | addAssertion x y hx hy hxy hnew => exact Step3.addAssertion s x y hx hy hxy hnew

/-- Every change of the third seed is a change of the first. -/
theorem Step2.toStep {s t : St} (h : Step2 s t) : Step s t := h.toStep3.toStep

/-- A change of the second seed is an identification, or a change of the third seed. -/
theorem Step3.identify_or_step2 {s t : St} (h : Step3 s t) :
    (∃ u v, u ∈ s.T ∧ v ∈ s.T ∧ u ≠ v ∧ t = s.identify u v) ∨ Step2 s t := by
  cases h with
  | addTerm t ht => exact Or.inr (Step2.addTerm s t ht)
  | addAssertion x y hx hy hxy hnew => exact Or.inr (Step2.addAssertion s x y hx hy hxy hnew)
  | identify u v hu hv huv h1 h2 => exact Or.inl ⟨u, v, hu, hv, huv, rfl⟩

/-- No change of the third seed has the outcome of identifying a term `v` that is
there with another. -/
theorem Step2.ne_identify {s t : St} (h : Step2 s t) {u v : ℕ} (hv : v ∈ s.T) :
    t ≠ s.identify u v := by
  cases h with
  | addTerm t ht =>
    intro he
    have hm : t ∈ (s.addTerm t).T := Finset.mem_insert_self t s.T
    rw [he] at hm
    simp only [St.identify, Finset.mem_erase] at hm
    exact ht hm.2
  | addAssertion x y hx hy hxy hnew =>
    intro he
    have hm : v ∈ (s.addAssertion x y).T := hv
    rw [he] at hm
    simp only [St.identify, Finset.mem_erase] at hm
    exact hm.1 rfl

/-- No change of the third seed has the outcome of removing an assertion. -/
theorem Step2.ne_remove {s t : St} (h : Step2 s t) (p : ℕ × ℕ) : t ≠ s.remove p :=
  h.toStep3.ne_remove p

/-! ## Inherited invariants (earlier derivations, re-checked through the embedding) -/

theorem Step2.legal {s t : St} (h : Step2 s t) (hs : s.Legal) : t.Legal := h.toStep3.legal hs

theorem Step2.wf {s t : St} (h : Step2 s t) (hs : s.WF) : t.WF := h.toStep3.wf hs

theorem Step2.nonempty {s t : St} (h : Step2 s t) (hs : s.T.Nonempty) : t.T.Nonempty :=
  h.toStep3.nonempty hs

/-- `Reach2 s t n`: `t` is reached from `s` by `n` performed changes of the third seed. -/
inductive Reach2 : St → St → ℕ → Prop
  | refl (s : St) : Reach2 s s 0
  | step {s t u : St} {n : ℕ} : Reach2 s t n → Step2 t u → Reach2 s u (n + 1)

theorem Reach2.toReach3 {s t : St} {n : ℕ} (h : Reach2 s t n) : Reach3 s t n := by
  induction h with
  | refl => exact Reach3.refl _
  | step _ st ih => exact Reach3.step ih st.toStep3

theorem Reach2.toReach {s t : St} {n : ℕ} (h : Reach2 s t n) : Reach s t n := h.toReach3.toReach

theorem Reach2.trans {s t u : St} {n m : ℕ} (h1 : Reach2 s t n) (h2 : Reach2 t u m) :
    Reach2 s u (n + m) := by
  induction h2 with
  | refl => exact h1
  | step _ st ih => exact Reach2.step ih st

/-- No change at all: the state is the same. -/
theorem Reach2.eq_of_zero {s t : St} (h : Reach2 s t 0) : s = t := by
  cases h
  rfl

theorem Reach2.legal {s t : St} {n : ℕ} (h : Reach2 s t n) (hs : s.Legal) : t.Legal :=
  h.toReach3.legal hs

theorem Reach2.wf {s t : St} {n : ℕ} (h : Reach2 s t n) (hs : s.WF) : t.WF := h.toReach3.wf hs

theorem Reach2.nonempty {s t : St} {n : ℕ} (h : Reach2 s t n) (hs : s.T.Nonempty) :
    t.T.Nonempty := h.toReach3.nonempty hs

/-- The second derivation's lower bound, inherited: size rises by at most one per change. -/
theorem Reach2.size_le_inherited {s t : St} {n : ℕ} (h : Reach2 s t n) : t.size ≤ s.size + n :=
  h.toReach3.size_le

/-- The first derivation's lower bound, inherited through both embeddings. -/
theorem Reach2.costA_le_inherited {t : St} {n : ℕ} (h : Reach2 givenA t n) : costA t ≤ n + 3 :=
  h.toReach3.costA_le_inherited

theorem Reach2.costB_le_inherited {t : St} {n : ℕ} (h : Reach2 givenB t n) : costB t ≤ n + 4 :=
  h.toReach3.costB_le_inherited

end Seed.Third
