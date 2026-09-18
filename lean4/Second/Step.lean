import H3V7N5QF.Answers

/-!
# The second seed: three kinds of change

`prompt/second/seed_prompt.md` differs from the first seed in one sentence:
removing an assertion is not a change.  The states are those of the first
derivation (`Seed.St`, with its `addTerm`, `addAssertion`, `identify`); the
changes are a new inductive `Step3` with three constructors.

Cited from the first derivation and re-checked here: every `Step3` is a `Step`
(`Step3.toStep`), so the first derivation's theorems about one change and about
sequences of changes restrict to the second seed.  Through this embedding
legality, well-formedness and "at least one term" are inherited (`Step3.legal`,
`Step3.wf`, `Step3.nonempty`, `Reach3.legal`, `Reach3.wf`, `Reach3.nonempty`),
and so is the first derivation's lower bound on the number of changes
(`Reach3.costA_le_inherited`).  Conversely a change of the first seed is a
removal or a change of the second (`Step.remove_or_step3`), and no change of the
second seed has the outcome of a removal (`Step3.ne_remove`).
-/

namespace Seed.Second

open Seed St

/-- One performed (unobstructed) change of the second seed.  "Nothing else is a
change": the new term is new, the added assertion is new and between terms that are
there, the identified terms are two terms that are there and nothing is asserted
between them. -/
inductive Step3 : St → St → Prop
  | addTerm (s : St) (t : ℕ) (ht : t ∉ s.T) : Step3 s (s.addTerm t)
  | addAssertion (s : St) (x y : ℕ) (hx : x ∈ s.T) (hy : y ∈ s.T) (hxy : x ≠ y)
      (hnew : (x, y) ∉ s.A) : Step3 s (s.addAssertion x y)
  | identify (s : St) (u v : ℕ) (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v)
      (h1 : (u, v) ∉ s.A) (h2 : (v, u) ∉ s.A) : Step3 s (s.identify u v)

/-- Every change of the second seed is a change of the first. -/
theorem Step3.toStep {s t : St} (h : Step3 s t) : Step s t := by
  cases h with
  | addTerm t ht => exact Step.addTerm s t ht
  | addAssertion x y hx hy hxy hnew => exact Step.addAssertion s x y hx hy hxy hnew
  | identify u v hu hv huv h1 h2 => exact Step.identify s u v hu hv huv h1 h2

/-- A change of the first seed is a removal, or a change of the second seed. -/
theorem Step.remove_or_step3 {s t : St} (h : Step s t) :
    (∃ p ∈ s.A, t = s.remove p) ∨ Step3 s t := by
  cases h with
  | addTerm t ht => exact Or.inr (Step3.addTerm s t ht)
  | addAssertion x y hx hy hxy hnew => exact Or.inr (Step3.addAssertion s x y hx hy hxy hnew)
  | remove p hp => exact Or.inl ⟨p, hp, rfl⟩
  | identify u v hu hv huv h1 h2 => exact Or.inr (Step3.identify s u v hu hv huv h1 h2)

/-- No change of the second seed has the outcome of removing an assertion. -/
theorem Step3.ne_remove {s t : St} (h : Step3 s t) (p : ℕ × ℕ) : t ≠ s.remove p := by
  cases h with
  | addTerm t ht =>
    intro he
    have hm : t ∈ (s.addTerm t).T := Finset.mem_insert_self t s.T
    rw [he] at hm
    exact ht hm
  | addAssertion x y hx hy hxy hnew =>
    intro he
    have hm : (x, y) ∈ (s.addAssertion x y).A := Finset.mem_insert_self _ _
    rw [he] at hm
    exact hnew (Finset.mem_of_mem_erase hm)
  | identify u v hu hv huv h1 h2 =>
    intro he
    have hm : v ∉ (s.identify u v).T := Finset.notMem_erase v s.T
    rw [he] at hm
    exact hm hv

/-! ## Inherited invariants (first derivation, re-checked through the embedding) -/

theorem Step3.legal {s t : St} (h : Step3 s t) (hs : s.Legal) : t.Legal := h.toStep.legal hs

theorem Step3.wf {s t : St} (h : Step3 s t) (hs : s.WF) : t.WF := h.toStep.wf hs

theorem Step3.nonempty {s t : St} (h : Step3 s t) (hs : s.T.Nonempty) : t.T.Nonempty :=
  h.toStep.nonempty hs

/-- `Reach3 s t n`: `t` is reached from `s` by `n` performed changes of the second seed. -/
inductive Reach3 : St → St → ℕ → Prop
  | refl (s : St) : Reach3 s s 0
  | step {s t u : St} {n : ℕ} : Reach3 s t n → Step3 t u → Reach3 s u (n + 1)

theorem Reach3.toReach {s t : St} {n : ℕ} (h : Reach3 s t n) : Reach s t n := by
  induction h with
  | refl => exact Reach.refl _
  | step _ st ih => exact Reach.step ih st.toStep

theorem Reach3.trans {s t u : St} {n m : ℕ} (h1 : Reach3 s t n) (h2 : Reach3 t u m) :
    Reach3 s u (n + m) := by
  induction h2 with
  | refl => exact h1
  | step _ st ih => exact Reach3.step ih st

theorem Reach3.legal {s t : St} {n : ℕ} (h : Reach3 s t n) (hs : s.Legal) : t.Legal :=
  h.toReach.legal hs

theorem Reach3.wf {s t : St} {n : ℕ} (h : Reach3 s t n) (hs : s.WF) : t.WF := h.toReach.wf hs

theorem Reach3.nonempty {s t : St} {n : ℕ} (h : Reach3 s t n) (hs : s.T.Nonempty) :
    t.T.Nonempty := h.toReach.nonempty hs

/-- The first derivation's lower bound, inherited: a state reached from what is given
(`bra` not asserted) in `n` changes has `costA ≤ n + 3`. -/
theorem Reach3.costA_le_inherited {t : St} {n : ℕ} (h : Reach3 givenA t n) : costA t ≤ n + 3 :=
  fewest_changes_lower_A h.toReach

theorem Reach3.costB_le_inherited {t : St} {n : ℕ} (h : Reach3 givenB t n) : costB t ≤ n + 4 :=
  fewest_changes_lower_B h.toReach

end Seed.Second
