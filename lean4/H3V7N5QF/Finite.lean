import H3V7N5QF.Basic

/-!
# States, changes, and what every change preserves

A state has finitely many terms (natural numbers stand for the letters),
finitely many asserted pairs, and remembers which terms carry the names `a`
and `b`.  The four kinds of change are functions on states; their outcome may
assert some `xrx` (then the change is obstructed and is not a `Step`).

Derived here:
* which changes are obstructed (`identify_legal_iff`, `addAssertion_legal_iff`,
  `remove_legal`, `addTerm_legal`), and that adding `xrx` is obstructed in
  every state (`adding_xrx_always_obstructed`);
* what removes an obstruction and what does not (`obstruction_persists`);
* every change keeps legality, well-formedness, at least one term, and keeps
  `a` and `b` one term once they are (`Step.legal`, `Step.wf`, `Step.nonempty`,
  `Step.names_stay_merged`).
-/

namespace Seed

/-- Terms, asserted pairs, and the terms named `a` and `b`. -/
@[ext]
structure St where
  T : Finset ℕ
  A : Finset (ℕ × ℕ)
  a : ℕ
  b : ℕ
  deriving DecidableEq

namespace St

/-- No `xrx` is asserted. -/
def Legal (s : St) : Prop := ∀ x, (x, x) ∉ s.A

/-- Assertions are between terms that are there, and the names are carried by terms. -/
def WF (s : St) : Prop := (∀ p ∈ s.A, p.1 ∈ s.T ∧ p.2 ∈ s.T) ∧ s.a ∈ s.T ∧ s.b ∈ s.T

/-- Adding a term. -/
def addTerm (s : St) (t : ℕ) : St := ⟨insert t s.T, s.A, s.a, s.b⟩

/-- Adding an assertion. -/
def addAssertion (s : St) (x y : ℕ) : St := ⟨s.T, insert (x, y) s.A, s.a, s.b⟩

/-- Removing an assertion. -/
def remove (s : St) (p : ℕ × ℕ) : St := ⟨s.T, s.A.erase p, s.a, s.b⟩

/-- Identifying `u` and `v`: both are replaced by one term (written `u`) in every
assertion, and the names follow. -/
def identify (s : St) (u v : ℕ) : St :=
  ⟨s.T.erase v, s.A.image (Prod.map (merge u v) (merge u v)), merge u v s.a, merge u v s.b⟩

/-- Terms plus assertions. -/
def size (s : St) : ℕ := s.T.card + s.A.card

end St

open St

/-! ## Which changes are obstructed -/

theorem mem_identify {s : St} {u v : ℕ} {p : ℕ × ℕ} :
    p ∈ (s.identify u v).A ↔ ∃ q ∈ s.A, (merge u v q.1, merge u v q.2) = p := by
  simp [St.identify, Finset.mem_image, Prod.map]

/-- Identifying `u` and `v` in a legal state is unobstructed exactly when neither
`urv` nor `vru` is asserted. -/
theorem identify_legal_iff {s : St} (hs : s.Legal) (u v : ℕ) :
    (s.identify u v).Legal ↔ (u, v) ∉ s.A ∧ (v, u) ∉ s.A := by
  constructor
  · intro h
    refine ⟨fun huv => h u ?_, fun hvu => h u ?_⟩
    · exact mem_identify.2 ⟨(u, v), huv, by simp⟩
    · exact mem_identify.2 ⟨(v, u), hvu, by simp⟩
  · rintro ⟨h1, h2⟩ w hw
    obtain ⟨⟨x, y⟩, hq, he⟩ := mem_identify.1 hw
    have hxy : x ≠ y := by
      rintro rfl
      exact hs _ hq
    simp only [Prod.mk.injEq] at he
    rcases merge_eq_merge hxy (he.1.trans he.2.symm) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1 hq
    · exact h2 hq

/-- Adding `xry` to a legal state is unobstructed exactly when `x` and `y` are two terms. -/
theorem addAssertion_legal_iff {s : St} (hs : s.Legal) (x y : ℕ) :
    (s.addAssertion x y).Legal ↔ x ≠ y := by
  constructor
  · rintro h rfl
    exact h x (by simp [St.addAssertion])
  · intro hxy w hw
    simp only [St.addAssertion, Finset.mem_insert, Prod.mk.injEq] at hw
    rcases hw with ⟨rfl, rfl⟩ | hw
    · exact hxy rfl
    · exact hs w hw

/-- Adding `xrx` is obstructed in every state: nothing can be removed or built
first that makes it unobstructed. -/
theorem adding_xrx_always_obstructed (s : St) (x : ℕ) : ¬ (s.addAssertion x x).Legal :=
  fun h => h x (by simp [St.addAssertion])

/-- Removing an assertion is never obstructed. -/
theorem remove_legal {s : St} (hs : s.Legal) (p : ℕ × ℕ) : (s.remove p).Legal :=
  fun x hx => hs x (Finset.mem_of_mem_erase hx)

/-- Adding a term is never obstructed. -/
theorem addTerm_legal {s : St} (hs : s.Legal) (t : ℕ) : (s.addTerm t).Legal := hs

/-! ## Changes that are performed -/

/-- One performed (unobstructed) change.  "Nothing else is a change": the new term
is new, the added assertion is new and between terms that are there, the removed
assertion is asserted, the identified terms are two terms that are there. -/
inductive Step : St → St → Prop
  | addTerm (s : St) (t : ℕ) (ht : t ∉ s.T) : Step s (s.addTerm t)
  | addAssertion (s : St) (x y : ℕ) (hx : x ∈ s.T) (hy : y ∈ s.T) (hxy : x ≠ y)
      (hnew : (x, y) ∉ s.A) : Step s (s.addAssertion x y)
  | remove (s : St) (p : ℕ × ℕ) (hp : p ∈ s.A) : Step s (s.remove p)
  | identify (s : St) (u v : ℕ) (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v)
      (h1 : (u, v) ∉ s.A) (h2 : (v, u) ∉ s.A) : Step s (s.identify u v)

/-- A performed change keeps the state legal. -/
theorem Step.legal {s s' : St} (h : Step s s') (hs : s.Legal) : s'.Legal := by
  cases h with
  | addTerm t ht => exact addTerm_legal hs t
  | addAssertion x y hx hy hxy hnew => exact (addAssertion_legal_iff hs x y).2 hxy
  | remove p hp => exact remove_legal hs p
  | identify u v hu hv huv h1 h2 => exact (identify_legal_iff hs u v).2 ⟨h1, h2⟩

theorem merge_mem_erase {T : Finset ℕ} {u v x : ℕ} (hu : u ∈ T) (huv : u ≠ v) (hx : x ∈ T) :
    merge u v x ∈ T.erase v := by
  by_cases hxv : x = v
  · subst hxv
    simpa using ⟨huv, hu⟩
  · rw [merge_of_ne hxv]
    exact Finset.mem_erase.2 ⟨hxv, hx⟩

/-- A performed change keeps assertions between terms that are there, and the
names on terms. -/
theorem Step.wf {s s' : St} (h : Step s s') (hs : s.WF) : s'.WF := by
  obtain ⟨hA, ha, hb⟩ := hs
  cases h with
  | addTerm t ht =>
    exact ⟨fun p hp => ⟨Finset.mem_insert_of_mem (hA p hp).1, Finset.mem_insert_of_mem (hA p hp).2⟩,
      Finset.mem_insert_of_mem ha, Finset.mem_insert_of_mem hb⟩
  | addAssertion x y hx hy hxy hnew =>
    refine ⟨fun p hp => ?_, ha, hb⟩
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact ⟨hx, hy⟩
    · exact hA p hp
  | remove p hp => exact ⟨fun q hq => hA q (Finset.mem_of_mem_erase hq), ha, hb⟩
  | identify u v hu hv huv h1 h2 =>
    refine ⟨fun p hp => ?_, merge_mem_erase hu huv ha, merge_mem_erase hu huv hb⟩
    obtain ⟨q, hq, rfl⟩ := mem_identify.1 hp
    exact ⟨merge_mem_erase hu huv (hA q hq).1, merge_mem_erase hu huv (hA q hq).2⟩

/-- There is always at least one term: no change reaches a state without terms. -/
theorem Step.nonempty {s s' : St} (h : Step s s') (hs : s.T.Nonempty) : s'.T.Nonempty := by
  cases h with
  | addTerm t ht => exact ⟨t, Finset.mem_insert_self t s.T⟩
  | addAssertion x y hx hy hxy hnew => exact hs
  | remove p hp => exact hs
  | identify u v hu hv huv h1 h2 => exact ⟨u, Finset.mem_erase.2 ⟨huv, hu⟩⟩

/-- Once `a` and `b` are one term they stay one term: no change tells them apart again. -/
theorem Step.names_stay_merged {s s' : St} (h : Step s s') (hab : s.a = s.b) : s'.a = s'.b := by
  cases h with
  | addTerm t ht => exact hab
  | addAssertion x y hx hy hxy hnew => exact hab
  | remove p hp => exact hab
  | identify u v hu hv huv h1 h2 => simp [St.identify, hab]

/-! ## What removes an obstruction and what does not -/

/-- **Persistence.**  If `urv` is asserted, then after any one performed change
either that change was the removal of `urv`, or `urv` is still asserted, or the
change was an identification and the assertion between the replaced terms is
asserted.  So identifying `u` and `v` stays obstructed until `urv` is removed. -/
theorem obstruction_persists {s s' : St} (h : Step s s') {u v : ℕ} (huv : (u, v) ∈ s.A) :
    s' = s.remove (u, v) ∨ (u, v) ∈ s'.A ∨
      ∃ p q, s' = s.identify p q ∧ (merge p q u, merge p q v) ∈ s'.A := by
  cases h with
  | addTerm t ht => exact Or.inr (Or.inl huv)
  | addAssertion x y hx hy hxy hnew => exact Or.inr (Or.inl (Finset.mem_insert_of_mem huv))
  | remove p hp =>
    by_cases hpe : p = (u, v)
    · exact Or.inl (by rw [hpe])
    · exact Or.inr (Or.inl (Finset.mem_erase.2 ⟨fun h => hpe h.symm, huv⟩))
  | identify p q hp hq hpq h1 h2 =>
    exact Or.inr (Or.inr ⟨p, q, rfl, mem_identify.2 ⟨(u, v), huv, rfl⟩⟩)

/-- In particular a performed identification never merges the two terms of an assertion. -/
theorem identify_keeps_apart {s : St} (hs : s.Legal) {p q u v : ℕ}
    (h1 : (p, q) ∉ s.A) (h2 : (q, p) ∉ s.A) (huv : (u, v) ∈ s.A) :
    merge p q u ≠ merge p q v := by
  intro h
  have hne : u ≠ v := by
    rintro rfl
    exact hs _ huv
  rcases merge_eq_merge hne h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h1 huv
  · exact h2 huv

end Seed
