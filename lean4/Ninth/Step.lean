import Ninth.State

/-!
# The four kinds of change over two relations, from nothing

`Step9` is one change of the ninth seed on a two-relation state without names:
a new term; an assertion of either relation between two terms that are there
(`xrx`, `xsx` included); the removal of an asserted assertion of either
relation; the identification of two terms that are there, in every assertion
of both relations.  `Reach9 s t n`: `t` is reached from `s` by `n` changes.

Cited from the seventh and eighth derivations and re-checked through the maps:
* every change of the eighth seed is a change of the ninth on the forgotten
  states (`Step8.forget`, `Reach8.forget`);
* every change of the ninth seed on a state with a term is a change of the
  eighth on the named states, the names following the merge (`Step9.name`,
  `Reach9.name`) — so the eighth's proofs about one change apply to every
  change here except the first, which no naming reaches;
* every change of the ninth seed is a change of the seventh on a part and
  leaves the other part as it is, or is a change of the seventh on both parts
  (`Step9.proj`); a sequence projects to a sequence of the seventh on either
  part, no longer (`Reach9.proj`);
* every change of the seventh seed is a change of the ninth on the embedded
  states (`Step7.ofR`, `Reach7.ofR`);
* well-formedness is kept (`Step9.wf`, the seventh's `Step7.wf` on each part).

Derived here, about the two dials turned at once:
* the outcome of every change on a well-formed state has a term
  (`Step9.nonempty_out`), and a state with a term leaves a state with a term
  (`Step9.nonempty`, `Reach9.nonempty`): **the one irreversible change is
  leaving the empty state**, as under the seventh; the eighth's merge of the
  names has no object;
* the first change can only add a term (`first_change_adds_term9`);
* the empty state is reached from a well-formed state only from itself, in
  zero changes (`reach9_empty_iff`);
* **the exchange of the two relations is a symmetry**: it carries every change
  to a change of the same kind in the other relation (`Step9.swap`) and every
  sequence to a sequence of the same length (`Reach9.swap`) — a symmetry the
  eighth seed did not have, its given living in `r`.
-/

namespace Seed.Ninth

open Seed Seed.Fourth Seed.Fifth Seed.Sixth Seed.Seventh Seed.Eighth NDSt

/-- One change of the ninth seed.  "Nothing else is a change": the new term is new; the added
assertion is between two terms that are there (the same term twice allowed); the removed
assertion is asserted; the identified terms are two terms that are there. -/
inductive Step9 : NDSt → NDSt → Prop
  | addTerm (s : NDSt) (t : ℕ) (ht : t ∉ s.T) : Step9 s (s.addTerm t)
  | addAssertion (s : NDSt) (q : Rel) (x y : ℕ) (hx : x ∈ s.T) (hy : y ∈ s.T) : Step9 s (s.addAssertion q x y)
  | remove (s : NDSt) (q : Rel) (x y : ℕ) (hp : s.M q (x, y) ≠ 0) : Step9 s (s.remove q x y)
  | identify (s : NDSt) (u v : ℕ) (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v) : Step9 s (s.identify u v)

/-- Every change of the eighth seed is a change of the ninth on the forgotten states. -/
theorem _root_.Seed.Eighth.Step8.forget {s t : DSt} (h : Step8 s t) : Step9 s.forget t.forget := by
  cases h with
  | addTerm t ht => exact Step9.addTerm s.forget t ht
  | addAssertion q x y hx hy => exact Step9.addAssertion s.forget q x y hx hy
  | remove q x y hp => exact Step9.remove s.forget q x y hp
  | identify u v hu hv huv => exact Step9.identify s.forget u v hu hv huv

/-- Every change of the ninth seed on a state with a term is a change of the eighth on the
named states, the names following the merge. -/
theorem Step9.name {s t : NDSt} (h : Step9 s t) {c : ℕ} (hc : c ∈ s.T) :
    ∃ c', c' ∈ t.T ∧ Step8 (s.name c) (t.name c') := by
  cases h with
  | addTerm t ht => exact ⟨c, Finset.mem_insert_of_mem hc, Step8.addTerm (s.name c) t ht⟩
  | addAssertion q x y hx hy => exact ⟨c, hc, Step8.addAssertion (s.name c) q x y hx hy⟩
  | remove q x y hp => exact ⟨c, hc, Step8.remove (s.name c) q x y hp⟩
  | identify u v hu hv huv =>
    exact ⟨merge u v c, merge_mem_erase hu huv hc, Step8.identify (s.name c) u v hu hv huv⟩

/-- Every change of the seventh seed is a change of the ninth with nothing in `s`. -/
theorem _root_.Seed.Seventh.Step7.ofR {m m' : NSt} (h : Step7 m m') : Step9 m.ofR m'.ofR := by
  cases h with
  | addTerm t ht => exact Step9.addTerm m.ofR t ht
  | addAssertion x y hx hy =>
    rw [ofR9_addAssertion]
    exact Step9.addAssertion m.ofR false x y hx hy
  | remove x y hp =>
    rw [ofR9_remove]
    exact Step9.remove m.ofR false x y hp
  | identify u v hu hv huv =>
    rw [ofR9_identify]
    exact Step9.identify m.ofR u v hu hv huv

/-- A change of the ninth seed is a change of the seventh on a part, or leaves the part as it is. -/
theorem Step9.proj {s t : NDSt} (h : Step9 s t) (q : Rel) :
    Step7 (s.proj q) (t.proj q) ∨ t.proj q = s.proj q := by
  cases h with
  | addTerm t ht =>
    rw [proj9_addTerm]
    exact Or.inl (Step7.addTerm _ t ht)
  | addAssertion q' x y hx hy =>
    by_cases hq : q = q'
    · subst hq
      rw [proj9_addAssertion_self]
      exact Or.inl (Step7.addAssertion _ x y hx hy)
    · exact Or.inr (proj9_addAssertion_other s hq x y)
  | remove q' x y hp =>
    by_cases hq : q = q'
    · subst hq
      rw [proj9_remove_self]
      exact Or.inl (Step7.remove _ x y hp)
    · exact Or.inr (proj9_remove_other s hq x y)
  | identify u v hu hv huv =>
    rw [proj9_identify]
    exact Or.inl (Step7.identify _ u v hu hv huv)

/-- The exchange of the relations carries a change to a change of the same kind. -/
theorem Step9.swap {s t : NDSt} (h : Step9 s t) : Step9 s.swap t.swap := by
  cases h with
  | addTerm t ht => exact Step9.addTerm s.swap t ht
  | addAssertion q x y hx hy =>
    rw [swap9_addAssertion]
    exact Step9.addAssertion s.swap (!q) x y hx hy
  | remove q x y hp =>
    rw [swap9_remove]
    exact Step9.remove s.swap (!q) x y (by cases q <;> exact hp)
  | identify u v hu hv huv => exact Step9.identify s.swap u v hu hv huv

/-! ## Invariants of one change -/

theorem Step9.wf {s t : NDSt} (h : Step9 s t) (hw : s.WF) : t.WF := by
  constructor
  · rcases h.proj false with st | e
    · exact st.wf hw.1
    · rw [e]; exact hw.1
  · rcases h.proj true with st | e
    · exact st.wf hw.2
    · rw [e]; exact hw.2

/-- The outcome of every change on a well-formed state has a term. -/
theorem Step9.nonempty_out {s t : NDSt} (h : Step9 s t) (hw : s.WF) : t.T.Nonempty := by
  cases h with
  | addTerm t ht => exact Finset.insert_nonempty _ _
  | addAssertion q x y hx hy => exact ⟨x, hx⟩
  | remove q x y hp => exact ⟨x, ((wf_proj9 hw q) (x, y) hp).1⟩
  | identify u v hu hv huv => exact ⟨u, Finset.mem_erase.2 ⟨huv, hu⟩⟩

/-- A state with a term leaves a state with a term: the one irreversible change (the eighth's
`Step8.names_stay_merged` has no object here). -/
theorem Step9.nonempty {s t : NDSt} (h : Step9 s t) (hs : s.T.Nonempty) : t.T.Nonempty := by
  cases h with
  | addTerm t ht => exact Finset.insert_nonempty _ _
  | addAssertion q x y hx hy => exact hs
  | remove q x y hp => exact hs
  | identify u v hu hv huv => exact ⟨u, Finset.mem_erase.2 ⟨huv, hu⟩⟩

/-- **The first change can only add a term.** -/
theorem first_change_adds_term9 {t : NDSt} (h : Step9 empty9 t) : ∃ x, t = empty9.addTerm x := by
  cases h with
  | addTerm t ht => exact ⟨t, rfl⟩
  | addAssertion q x y hx hy => exact absurd hx (Finset.notMem_empty x)
  | remove q x y hp => exact absurd rfl hp
  | identify u v hu hv huv => exact absurd hu (Finset.notMem_empty u)

/-! ## Sequences of changes -/

/-- `Reach9 s t n`: `t` is reached from `s` by `n` changes of the ninth seed. -/
inductive Reach9 : NDSt → NDSt → ℕ → Prop
  | refl (s : NDSt) : Reach9 s s 0
  | step {s t u : NDSt} {n : ℕ} : Reach9 s t n → Step9 t u → Reach9 s u (n + 1)

theorem Reach9.trans {s t u : NDSt} {n m : ℕ} (h1 : Reach9 s t n) (h2 : Reach9 t u m) :
    Reach9 s u (n + m) := by
  induction h2 with
  | refl => exact h1
  | step _ st ih => exact Reach9.step ih st

theorem Reach9.single {s t : NDSt} (h : Step9 s t) : Reach9 s t 1 := Reach9.step (Reach9.refl s) h

theorem Reach9.eq_of_zero {s t : NDSt} (h : Reach9 s t 0) : s = t := by
  cases h
  rfl

theorem Reach9.wf {s t : NDSt} {n : ℕ} (h : Reach9 s t n) (hs : s.WF) : t.WF := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.wf ih

/-- Once a state has a term, every later state has a term. -/
theorem Reach9.nonempty {s t : NDSt} {n : ℕ} (h : Reach9 s t n) (hs : s.T.Nonempty) :
    t.T.Nonempty := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.nonempty ih

/-- Every sequence of the eighth seed is a sequence of the ninth on the forgotten states. -/
theorem _root_.Seed.Eighth.Reach8.forget {s t : DSt} {n : ℕ} (h : Reach8 s t n) :
    Reach9 s.forget t.forget n := by
  induction h with
  | refl => exact Reach9.refl _
  | step _ st ih => exact Reach9.step ih st.forget

/-- Every sequence of the ninth seed from a state with a term is a sequence of the eighth on
the named states. -/
theorem Reach9.name {s t : NDSt} {n : ℕ} (h : Reach9 s t n) {c : ℕ} (hc : c ∈ s.T) :
    ∃ c', c' ∈ t.T ∧ Reach8 (s.name c) (t.name c') n := by
  induction h with
  | refl => exact ⟨c, hc, Reach8.refl _⟩
  | step _ st ih =>
    obtain ⟨c1, hc1, r⟩ := ih
    obtain ⟨c2, hc2, st'⟩ := st.name hc1
    exact ⟨c2, hc2, Reach8.step r st'⟩

/-- Every sequence of the seventh seed is a sequence of the ninth with nothing in `s`. -/
theorem _root_.Seed.Seventh.Reach7.ofR {m m' : NSt} {n : ℕ} (h : Reach7 m m' n) :
    Reach9 m.ofR m'.ofR n := by
  induction h with
  | refl => exact Reach9.refl _
  | step _ st ih => exact Reach9.step ih st.ofR

/-- A sequence of the ninth seed projects to a sequence of the seventh on either part, no longer. -/
theorem Reach9.proj {s t : NDSt} {n : ℕ} (h : Reach9 s t n) (q : Rel) :
    ∃ m, m ≤ n ∧ Reach7 (s.proj q) (t.proj q) m := by
  induction h with
  | refl => exact ⟨0, le_refl _, Reach7.refl _⟩
  | step _ st ih =>
    obtain ⟨m, hm, r⟩ := ih
    rcases st.proj q with st' | e
    · exact ⟨m + 1, by omega, Reach7.step r st'⟩
    · rw [e]
      exact ⟨m, by omega, r⟩

/-- The exchange of the relations carries a sequence to a sequence of the same length. -/
theorem Reach9.swap {s t : NDSt} {n : ℕ} (h : Reach9 s t n) : Reach9 s.swap t.swap n := by
  induction h with
  | refl => exact Reach9.refl _
  | step _ st ih => exact Reach9.step ih st.swap

/-- **The empty state is never returned to**: it is reached from a well-formed state only from
itself, in zero changes. -/
theorem reach9_empty_iff {s : NDSt} {n : ℕ} (hs : s.WF) : Reach9 s empty9 n ↔ s = empty9 ∧ n = 0 := by
  constructor
  · intro h
    cases h with
    | refl => exact ⟨rfl, rfl⟩
    | step r st => exact absurd (st.nonempty_out (r.wf hs)) empty9_not_nonempty
  · rintro ⟨rfl, rfl⟩
    exact Reach9.refl _

end Seed.Ninth
