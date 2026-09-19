import Eighth.State

/-!
# The four kinds of change over two relations

`Step8` is one change of the eighth seed: a new term; an assertion of either
relation between two terms that are there (`xrx`, `xsx` included); the removal
of an asserted assertion of either relation; the identification of two terms
that are there, in every assertion of both relations.  `Reach8 s t n`: `t` is
reached from `s` by `n` changes.

Cited from the sixth derivation and re-checked through the projections:
* every change of the sixth seed is a change of the eighth on the states
  asserting nothing with `s` (`Step6.ofR`, `Reach6.ofR`);
* every change of the eighth seed is a change of the sixth on each part, or
  leaves that part as it is (`Step8.proj`): a term and an identification act on
  both parts, an assertion and a removal on one; so a sequence of the eighth
  projects to a sequence of the sixth on either part, no longer
  (`Reach8.proj`);
* well-formedness and at least one term are kept (`Step8.wf`,
  `Step8.nonempty`), and the names once one term stay one term
  (`Step8.names_stay_merged`, `Reach8.names_stay_merged`) — the sixth's proofs
  on the `r` part.
-/

namespace Seed.Eighth

open Seed Seed.Fourth Seed.Fifth Seed.Sixth DSt

/-- One change of the eighth seed. -/
inductive Step8 : DSt → DSt → Prop
  | addTerm (s : DSt) (t : ℕ) (ht : t ∉ s.T) : Step8 s (s.addTerm t)
  | addAssertion (s : DSt) (q : Rel) (x y : ℕ) (hx : x ∈ s.T) (hy : y ∈ s.T) : Step8 s (s.addAssertion q x y)
  | remove (s : DSt) (q : Rel) (x y : ℕ) (hp : s.M q (x, y) ≠ 0) : Step8 s (s.remove q x y)
  | identify (s : DSt) (u v : ℕ) (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v) : Step8 s (s.identify u v)

/-- Every change of the sixth seed is a change of the eighth with nothing in `s`. -/
theorem _root_.Seed.Sixth.Step6.ofR {m m' : MSt} (h : Step6 m m') : Step8 m.ofR m'.ofR := by
  cases h with
  | addTerm t ht => exact Step8.addTerm m.ofR t ht
  | addAssertion x y hx hy =>
    rw [ofR_addAssertion]
    exact Step8.addAssertion m.ofR false x y hx hy
  | remove x y hp =>
    rw [ofR_remove]
    exact Step8.remove m.ofR false x y hp
  | identify u v hu hv huv =>
    rw [ofR_identify]
    exact Step8.identify m.ofR u v hu hv huv

/-- A change of the eighth seed is a change of the sixth on a part, or leaves the part as it is. -/
theorem Step8.proj {s t : DSt} (h : Step8 s t) (q : Rel) : Step6 (s.proj q) (t.proj q) ∨ t.proj q = s.proj q := by
  cases h with
  | addTerm t ht =>
    rw [proj_addTerm]
    exact Or.inl (Step6.addTerm _ t ht)
  | addAssertion q' x y hx hy =>
    by_cases hq : q = q'
    · subst hq
      rw [proj_addAssertion_self]
      exact Or.inl (Step6.addAssertion _ x y hx hy)
    · exact Or.inr (proj_addAssertion_other s hq x y)
  | remove q' x y hp =>
    by_cases hq : q = q'
    · subst hq
      rw [proj_remove_self]
      exact Or.inl (Step6.remove _ x y hp)
    · exact Or.inr (proj_remove_other s hq x y)
  | identify u v hu hv huv =>
    rw [proj_identify]
    exact Or.inl (Step6.identify _ u v hu hv huv)

/-- A term and an identification are changes of the sixth on both parts; the change of one
relation is a change of the sixth on that part. -/
theorem Step8.proj_self {s t : DSt} (h : Step8 s t) :
    (∀ q, Step6 (s.proj q) (t.proj q)) ∨ ∃ q, Step6 (s.proj q) (t.proj q) ∧ t.proj (!q) = s.proj (!q) := by
  cases h with
  | addTerm t ht => exact Or.inl (fun q => by rw [proj_addTerm]; exact Step6.addTerm _ t ht)
  | addAssertion q x y hx hy =>
    refine Or.inr ⟨q, ?_, proj_addAssertion_other s (not_ne q) x y⟩
    rw [proj_addAssertion_self]
    exact Step6.addAssertion _ x y hx hy
  | remove q x y hp =>
    refine Or.inr ⟨q, ?_, proj_remove_other s (not_ne q) x y⟩
    rw [proj_remove_self]
    exact Step6.remove _ x y hp
  | identify u v hu hv huv => exact Or.inl (fun q => by rw [proj_identify]; exact Step6.identify _ u v hu hv huv)

/-! ## Invariants of one change -/

theorem Step8.T_or {s t : DSt} (h : Step8 s t) : t.T = s.T ∨ (∃ x, t.T = insert x s.T) ∨ ∃ v, t.T = s.T.erase v := by
  cases h with
  | addTerm t ht => exact Or.inr (Or.inl ⟨t, rfl⟩)
  | addAssertion q x y hx hy => exact Or.inl rfl
  | remove q x y hp => exact Or.inl rfl
  | identify u v hu hv huv => exact Or.inr (Or.inr ⟨v, rfl⟩)

theorem Step8.wf {s t : DSt} (h : Step8 s t) (hw : s.WF) : t.WF := by
  constructor
  · rcases h.proj false with st | e
    · exact st.wf hw.1
    · rw [e]; exact hw.1
  · rcases h.proj true with st | e
    · exact st.wf hw.2
    · rw [e]; exact hw.2

theorem Step8.nonempty {s t : DSt} (h : Step8 s t) (hs : s.T.Nonempty) : t.T.Nonempty := by
  rcases h.proj false with st | e
  · exact st.nonempty hs
  · have hT : t.T = s.T := congrArg MSt.T e
    rw [hT]
    exact hs

/-- Once `a` and `b` are one term they stay one term (through the `r` part). -/
theorem Step8.names_stay_merged {s t : DSt} (h : Step8 s t) (hab : s.a = s.b) : t.a = t.b := by
  rcases h.proj false with st | e
  · exact st.names_stay_merged hab
  · have ha : (t.proj false).a = (s.proj false).a := by rw [e]
    have hb : (t.proj false).b = (s.proj false).b := by rw [e]
    simp only [proj_a, proj_b] at ha hb
    rw [ha, hb, hab]

/-! ## Sequences of changes -/

/-- `Reach8 s t n`: `t` is reached from `s` by `n` changes of the eighth seed. -/
inductive Reach8 : DSt → DSt → ℕ → Prop
  | refl (s : DSt) : Reach8 s s 0
  | step {s t u : DSt} {n : ℕ} : Reach8 s t n → Step8 t u → Reach8 s u (n + 1)

theorem Reach8.trans {s t u : DSt} {n m : ℕ} (h1 : Reach8 s t n) (h2 : Reach8 t u m) : Reach8 s u (n + m) := by
  induction h2 with
  | refl => exact h1
  | step _ st ih => exact Reach8.step ih st

theorem Reach8.single {s t : DSt} (h : Step8 s t) : Reach8 s t 1 := Reach8.step (Reach8.refl s) h

theorem Reach8.eq_of_zero {s t : DSt} (h : Reach8 s t 0) : s = t := by
  cases h
  rfl

theorem Reach8.wf {s t : DSt} {n : ℕ} (h : Reach8 s t n) (hs : s.WF) : t.WF := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.wf ih

theorem Reach8.nonempty {s t : DSt} {n : ℕ} (h : Reach8 s t n) (hs : s.T.Nonempty) : t.T.Nonempty := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.nonempty ih

theorem Reach8.names_stay_merged {s t : DSt} {n : ℕ} (h : Reach8 s t n) (hab : s.a = s.b) : t.a = t.b := by
  induction h with
  | refl => exact hab
  | step _ st ih => exact st.names_stay_merged ih

/-- Every sequence of the sixth seed is a sequence of the eighth with nothing in `s`. -/
theorem _root_.Seed.Sixth.Reach6.ofR {m m' : MSt} {n : ℕ} (h : Reach6 m m' n) : Reach8 m.ofR m'.ofR n := by
  induction h with
  | refl => exact Reach8.refl _
  | step _ st ih => exact Reach8.step ih st.ofR

/-- A sequence of the eighth seed projects to a sequence of the sixth on either part, no longer. -/
theorem Reach8.proj {s t : DSt} {n : ℕ} (h : Reach8 s t n) (q : Rel) :
    ∃ m, m ≤ n ∧ Reach6 (s.proj q) (t.proj q) m := by
  induction h with
  | refl => exact ⟨0, le_refl _, Reach6.refl _⟩
  | step _ st ih =>
    obtain ⟨m, hm, r⟩ := ih
    rcases st.proj q with st' | e
    · exact ⟨m + 1, by omega, Reach6.step r st'⟩
    · rw [e]
      exact ⟨m, by omega, r⟩

end Seed.Eighth
