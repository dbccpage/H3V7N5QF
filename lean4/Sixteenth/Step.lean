import Sixteenth.State

/-!
# The five changes on a state with a record

`Step16` is one change of the sixteenth seed: the ninth's four kinds — a new
term; a direct assertion of either relation between two terms that are there;
the removal of an asserted assertion, which records a leftover of its pair; the
identification of two terms, in every assertion and in the record — and the
*admission* of a recorded leftover into either relation, which is the fourth
kind (adding an assertion) performed by admitting.  `Reach16 s t n`: `t` is
reached from `s` by `n` changes.

Cited from the ninth derivation and re-checked through the two maps:
* every change projects to a change of the ninth on the ninth state, an
  admission to a direct addition (`Step16.proj`, `Reach16.proj`);
* every addition and every identification of the ninth is a change of the
  sixteenth on the embedded states (`Add9.embed`, `AddReach9.embed`,
  `Step9.embed_identify`), and a removal of the ninth is a change of the
  sixteenth whose outcome carries one recorded leftover (`Step9.embed`): the
  embedding is not a map of changes on removals, which is the whole difference.

Derived here: well-formedness is kept (`Step16.wf`); the outcome of every
change on a well-formed state has a term, and a term stays
(`Step16.nonempty_out`, `Step16.nonempty`, `Reach16.nonempty`); the first
change can only add a term (`first_change_adds_term16`); the empty state is
never returned to (`reach16_empty_iff`); the exchange of the relations carries
a change to a change of the same kind in the other relation (`Step16.swap`).
-/

namespace Seed.Sixteenth

open Seed Seed.Fourth Seed.Fifth Seed.Sixth Seed.Seventh Seed.Eighth Seed.Ninth NDSt RSt

/-- One change of the sixteenth seed. -/
inductive Step16 : RSt → RSt → Prop
  | addTerm (s : RSt) (t : ℕ) (ht : t ∉ s.st.T) : Step16 s (s.addTerm t)
  | addAssertion (s : RSt) (q : Rel) (x y : ℕ) (hx : x ∈ s.st.T) (hy : y ∈ s.st.T) :
      Step16 s (s.addAssertion q x y)
  | remove (s : RSt) (q : Rel) (x y : ℕ) (hp : s.st.M q (x, y) ≠ 0) : Step16 s (s.remove q x y)
  | admitLeftover (s : RSt) (q : Rel) (x y : ℕ) (hl : s.L (x, y) ≠ 0) : Step16 s (s.admitLeftover q x y)
  | identify (s : RSt) (u v : ℕ) (hu : u ∈ s.st.T) (hv : v ∈ s.st.T) (huv : u ≠ v) :
      Step16 s (s.identify u v)

/-- Every change projects to a change of the ninth on the ninth state; an admission to a direct
addition. -/
theorem Step16.proj {s t : RSt} (h : Step16 s t) (hw : s.WF) : Step9 s.st t.st := by
  cases h with
  | addTerm t ht => exact Step9.addTerm s.st t ht
  | addAssertion q x y hx hy => exact Step9.addAssertion s.st q x y hx hy
  | remove q x y hp => exact Step9.remove s.st q x y hp
  | admitLeftover q x y hl =>
    obtain ⟨hx, hy⟩ := mem_of_L hw hl
    exact Step9.addAssertion s.st q x y hx hy
  | identify u v hu hv huv => exact Step9.identify s.st u v hu hv huv

theorem ofRSt_addTerm (g : NDSt) (t : ℕ) : (g.addTerm t).ofRSt = g.ofRSt.addTerm t := rfl

theorem ofRSt_addAssertion (g : NDSt) (q : Rel) (x y : ℕ) :
    (g.addAssertion q x y).ofRSt = g.ofRSt.addAssertion q x y := rfl

theorem ofRSt_identify (g : NDSt) (u v : ℕ) : (g.identify u v).ofRSt = g.ofRSt.identify u v := by
  apply RSt.ext
  · rfl
  · funext p
    simp [RSt.identify]

/-- An addition of the ninth is a change of the sixteenth on the embedded states. -/
theorem _root_.Seed.Ninth.Add9.embed {g g' : NDSt} (h : Add9 g g') : Step16 g.ofRSt g'.ofRSt := by
  cases h with
  | addTerm t ht => exact Step16.addTerm g.ofRSt t ht
  | addAssertion q x y hx hy => exact Step16.addAssertion g.ofRSt q x y hx hy

/-- An identification of the ninth is a change of the sixteenth on the embedded states. -/
theorem Step9.embed_identify (g : NDSt) (u v : ℕ) (hu : u ∈ g.T) (hv : v ∈ g.T) (huv : u ≠ v) :
    Step16 g.ofRSt (g.identify u v).ofRSt := by
  rw [ofRSt_identify]
  exact Step16.identify g.ofRSt u v hu hv huv

/-- Every change of the ninth embeds: an addition or an identification exactly, a removal into a
state carrying one recorded leftover. -/
theorem _root_.Seed.Ninth.Step9.embed {g g' : NDSt} (h : Step9 g g') :
    Step16 g.ofRSt g'.ofRSt ∨ ∃ t : RSt, Step16 g.ofRSt t ∧ t.st = g' ∧ ∃ x y, t.L (x, y) = 1 := by
  cases h with
  | addTerm t ht => exact Or.inl (Step16.addTerm g.ofRSt t ht)
  | addAssertion q x y hx hy => exact Or.inl (Step16.addAssertion g.ofRSt q x y hx hy)
  | remove q x y hp => exact Or.inr ⟨_, Step16.remove g.ofRSt q x y hp, rfl, x, y, by simp [RSt.remove]⟩
  | identify u v hu hv huv => exact Or.inl (Step9.embed_identify g u v hu hv huv)

/-! ## Invariants of one change -/

theorem Step16.wf {s t : RSt} (h : Step16 s t) (hw : s.WF) : t.WF := by
  cases h with
  | addTerm t ht => exact ⟨addTerm9_wf hw.1 t, Seed.Seventh.addTerm_wf hw.2 t⟩
  | addAssertion q x y hx hy => exact ⟨(Step9.addAssertion s.st q x y hx hy).wf hw.1, hw.2⟩
  | remove q x y hp =>
    obtain ⟨hx, hy⟩ := mem_of_M hw q hp
    refine ⟨(Step9.remove s.st q x y hp).wf hw.1, ?_⟩
    show (s.record.addAssertion x y).WF
    exact (Step7.addAssertion s.record x y hx hy).wf hw.2
  | admitLeftover q x y hl =>
    obtain ⟨hx, hy⟩ := mem_of_L hw hl
    refine ⟨(Step9.addAssertion s.st q x y hx hy).wf hw.1, ?_⟩
    show (s.record.remove x y).WF
    exact (Step7.remove s.record x y hl).wf hw.2
  | identify u v hu hv huv =>
    refine ⟨(Step9.identify s.st u v hu hv huv).wf hw.1, ?_⟩
    show (s.record.identify u v).WF
    exact (Step7.identify s.record u v hu hv huv).wf hw.2

/-- The outcome of every change on a well-formed state has a term. -/
theorem Step16.nonempty_out {s t : RSt} (h : Step16 s t) (hw : s.WF) : t.st.T.Nonempty :=
  (h.proj hw).nonempty_out hw.1

/-- A term stays. -/
theorem Step16.nonempty {s t : RSt} (h : Step16 s t) (hw : s.WF) (hs : s.st.T.Nonempty) : t.st.T.Nonempty :=
  (h.proj hw).nonempty hs

/-- **The first change can only add a term.** -/
theorem first_change_adds_term16 {t : RSt} (h : Step16 empty16 t) : ∃ x, t = (empty9.addTerm x).ofRSt := by
  cases h with
  | addTerm t ht => exact ⟨t, rfl⟩
  | addAssertion q x y hx hy => exact absurd hx (Finset.notMem_empty x)
  | remove q x y hp => exact absurd rfl hp
  | admitLeftover q x y hl => exact absurd rfl hl
  | identify u v hu hv huv => exact absurd hu (Finset.notMem_empty u)

/-- The exchange of the relations carries a change to a change of the same kind. -/
theorem Step16.swap {s t : RSt} (h : Step16 s t) : Step16 s.swap t.swap := by
  cases h with
  | addTerm t ht => exact Step16.addTerm s.swap t ht
  | addAssertion q x y hx hy =>
    rw [swap16_addAssertion]
    exact Step16.addAssertion s.swap (!q) x y hx hy
  | remove q x y hp =>
    rw [swap16_remove]
    exact Step16.remove s.swap (!q) x y (by cases q <;> exact hp)
  | admitLeftover q x y hl =>
    rw [swap16_admit]
    exact Step16.admitLeftover s.swap (!q) x y hl
  | identify u v hu hv huv => exact Step16.identify s.swap u v hu hv huv

/-! ## Sequences of changes -/

/-- `Reach16 s t n`: `t` is reached from `s` by `n` changes of the sixteenth seed. -/
inductive Reach16 : RSt → RSt → ℕ → Prop
  | refl (s : RSt) : Reach16 s s 0
  | step {s t u : RSt} {n : ℕ} : Reach16 s t n → Step16 t u → Reach16 s u (n + 1)

theorem Reach16.trans {s t u : RSt} {n m : ℕ} (h1 : Reach16 s t n) (h2 : Reach16 t u m) :
    Reach16 s u (n + m) := by
  induction h2 with
  | refl => exact h1
  | step _ st ih => exact Reach16.step ih st

theorem Reach16.single {s t : RSt} (h : Step16 s t) : Reach16 s t 1 := Reach16.step (Reach16.refl s) h

theorem Reach16.wf {s t : RSt} {n : ℕ} (h : Reach16 s t n) (hs : s.WF) : t.WF := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.wf ih

/-- Every sequence projects to a sequence of the ninth of the same length. -/
theorem Reach16.proj {s t : RSt} {n : ℕ} (h : Reach16 s t n) (hs : s.WF) : Reach9 s.st t.st n := by
  induction h with
  | refl => exact Reach9.refl _
  | step r st ih => exact Reach9.step ih (st.proj (r.wf hs))

/-- Every sequence of additions of the ninth is a sequence of the sixteenth on the embedded states. -/
theorem _root_.Seed.Ninth.AddReach9.embed {g g' : NDSt} {n : ℕ} (h : AddReach9 g g' n) :
    Reach16 g.ofRSt g'.ofRSt n := by
  induction h with
  | refl => exact Reach16.refl _
  | step _ st ih => exact Reach16.step ih st.embed

/-- Once a state has a term, every later state has a term. -/
theorem Reach16.nonempty {s t : RSt} {n : ℕ} (h : Reach16 s t n) (hs : s.WF) (hne : s.st.T.Nonempty) :
    t.st.T.Nonempty :=
  (h.proj hs).nonempty hne

theorem Reach16.swap {s t : RSt} {n : ℕ} (h : Reach16 s t n) : Reach16 s.swap t.swap n := by
  induction h with
  | refl => exact Reach16.refl _
  | step _ st ih => exact Reach16.step ih st.swap

/-- **The empty state is never returned to**: it is reached from a well-formed state only from
itself, in zero changes. -/
theorem reach16_empty_iff {s : RSt} {n : ℕ} (hs : s.WF) : Reach16 s empty16 n ↔ s = empty16 ∧ n = 0 := by
  constructor
  · intro h
    cases h with
    | refl => exact ⟨rfl, rfl⟩
    | step r st => exact absurd (st.nonempty_out (r.wf hs)) empty9_not_nonempty
  · rintro ⟨rfl, rfl⟩
    exact Reach16.refl _

end Seed.Sixteenth
