import Second.Step

/-!
# The carrying map: nothing is ever un-asserted

Every change of the second seed comes with a map of terms (the identity for an
addition, `merge u v` for an identification) that carries every asserted `xry`
to an asserted `q(x) r q(y)`, every term to a term, and the names to the names
(`Step3.carries`).  Carrying maps compose, so every sequence of changes has one
(`Reach3.carries`).

Derived here from that single fact:
* `a` and `b` are never one term, and `arb` (and `bra`, if asserted) is never
  lost (`Reach3.names_apart`, `Reach3.arb_persists`, `Reach3.bra_persists`);
* every result has at least two terms (`Reach3.two_terms`);
* an obstruction is never cleared: after any sequence of changes the images of
  `u` and `v` are still related, so identifying them is still obstructed
  (`Reach3.obstruction_persists`, `Reach3.identify_images_obstructed`);
* the fewest classes of a split of the terms with no two related terms in one
  class never decreases (`Reach3.split_mono`).
-/

namespace Seed.Second

open Seed St

/-- `q` carries `s` to `t`: terms to terms, assertions to assertions, names to names. -/
structure Carries (q : ℕ → ℕ) (s t : St) : Prop where
  terms : ∀ x ∈ s.T, q x ∈ t.T
  asserted : ∀ p ∈ s.A, (q p.1, q p.2) ∈ t.A
  name_a : q s.a = t.a
  name_b : q s.b = t.b

theorem Carries.id (s : St) : Carries id s s :=
  ⟨fun _ h => h, fun p hp => by simpa using hp, rfl, rfl⟩

theorem Carries.comp {q q' : ℕ → ℕ} {s t u : St} (h : Carries q s t) (h' : Carries q' t u) :
    Carries (q' ∘ q) s u :=
  ⟨fun x hx => h'.terms _ (h.terms x hx),
    fun p hp => h'.asserted _ (h.asserted p hp),
    by simp [Function.comp, h.name_a, h'.name_a],
    by simp [Function.comp, h.name_b, h'.name_b]⟩

/-- One change carries its state to its outcome. -/
theorem Step3.carries {s t : St} (h : Step3 s t) : ∃ q, Carries q s t := by
  cases h with
  | addTerm t ht =>
    exact ⟨id, fun x hx => Finset.mem_insert_of_mem hx, fun p hp => by simpa [St.addTerm] using hp,
      rfl, rfl⟩
  | addAssertion x y hx hy hxy hnew =>
    exact ⟨id, fun z hz => hz, fun p hp => by simp [St.addAssertion, hp], rfl, rfl⟩
  | identify u v hu hv huv h1 h2 =>
    exact ⟨merge u v, fun x hx => merge_mem_erase hu huv hx,
      fun p hp => mem_identify.2 ⟨p, hp, rfl⟩, rfl, rfl⟩

/-- A sequence of changes carries its start to its end. -/
theorem Reach3.carries {s t : St} {n : ℕ} (h : Reach3 s t n) : ∃ q, Carries q s t := by
  induction h with
  | refl => exact ⟨id, Carries.id _⟩
  | step _ st ih =>
    obtain ⟨q, hq⟩ := ih
    obtain ⟨q', hq'⟩ := st.carries
    exact ⟨q' ∘ q, hq.comp hq'⟩

/-! ## What is given survives -/

theorem Carries.arb_persists {q : ℕ → ℕ} {s t : St} (h : Carries q s t) (hs : (s.a, s.b) ∈ s.A) :
    (t.a, t.b) ∈ t.A := by
  have := h.asserted _ hs
  rwa [h.name_a, h.name_b] at this

theorem Carries.bra_persists {q : ℕ → ℕ} {s t : St} (h : Carries q s t) (hs : (s.b, s.a) ∈ s.A) :
    (t.b, t.a) ∈ t.A := by
  have := h.asserted _ hs
  rwa [h.name_a, h.name_b] at this

theorem Carries.names_apart {q : ℕ → ℕ} {s t : St} (h : Carries q s t) (hs : (s.a, s.b) ∈ s.A)
    (ht : t.Legal) : t.a ≠ t.b := by
  intro he
  have := h.arb_persists hs
  rw [he] at this
  exact ht _ this

/-- `arb`, once asserted, is asserted after every sequence of changes. -/
theorem Reach3.arb_persists {s t : St} {n : ℕ} (h : Reach3 s t n) (hab : (s.a, s.b) ∈ s.A) :
    (t.a, t.b) ∈ t.A :=
  let ⟨_, hq⟩ := h.carries
  hq.arb_persists hab

/-- `bra`, once asserted, is asserted after every sequence of changes. -/
theorem Reach3.bra_persists {s t : St} {n : ℕ} (h : Reach3 s t n) (hba : (s.b, s.a) ∈ s.A) :
    (t.b, t.a) ∈ t.A :=
  let ⟨_, hq⟩ := h.carries
  hq.bra_persists hba

/-- `a` and `b` are never identified. -/
theorem Reach3.names_apart {s t : St} {n : ℕ} (h : Reach3 s t n) (hs : s.Legal)
    (hab : (s.a, s.b) ∈ s.A) : t.a ≠ t.b :=
  let ⟨_, hq⟩ := h.carries
  hq.names_apart hab (h.legal hs)

/-- Every result has at least two terms. -/
theorem Reach3.two_terms {s t : St} {n : ℕ} (h : Reach3 s t n) (hs : s.Legal) (hw : s.WF)
    (hab : (s.a, s.b) ∈ s.A) : 2 ≤ t.T.card := by
  have hwf := h.wf hw
  have hne := h.names_apart hs hab
  have hsub : ({t.a, t.b} : Finset ℕ) ⊆ t.T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hwf.2.1
    · exact hwf.2.2
  calc 2 = ({t.a, t.b} : Finset ℕ).card := (Finset.card_pair hne).symm
    _ ≤ t.T.card := Finset.card_le_card hsub

/-! ## An obstruction is never cleared -/

/-- If `urv` is asserted, then after any sequence of changes the images of `u` and `v`
are related the same way. -/
theorem Reach3.obstruction_persists {s t : St} {n : ℕ} (h : Reach3 s t n) {u v : ℕ}
    (huv : (u, v) ∈ s.A) : ∃ q, Carries q s t ∧ (q u, q v) ∈ t.A :=
  let ⟨q, hq⟩ := h.carries
  ⟨q, hq, hq.asserted _ huv⟩

/-- So identifying the images of `u` and `v` is still obstructed: no sequence of
changes removes the obstruction. -/
theorem Reach3.identify_images_obstructed {s t : St} {n : ℕ} (h : Reach3 s t n) (hs : s.Legal)
    {u v : ℕ} (huv : (u, v) ∈ s.A) :
    ∃ q, Carries q s t ∧ ¬ (t.identify (q u) (q v)).Legal := by
  obtain ⟨q, hq, hm⟩ := h.obstruction_persists huv
  exact ⟨q, hq, fun hl => ((identify_legal_iff (h.legal hs) (q u) (q v)).1 hl).1 hm⟩

/-! ## A number that never decreases -/

/-- The terms split into `k` classes with no two related terms in one class. -/
def Split (s : St) (k : ℕ) : Prop := ∃ c : ℕ → Fin k, ∀ p ∈ s.A, c p.1 ≠ c p.2

/-- A split of the outcome pulls back along the carrying map. -/
theorem Carries.split {q : ℕ → ℕ} {s t : St} (hq : Carries q s t) {k : ℕ} (h : Split t k) :
    Split s k := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c ∘ q, fun p hp => hc _ (hq.asserted p hp)⟩

/-- Every `k` that splits a result splits the state it came from: the fewest classes
never decreases along changes. -/
theorem Reach3.split_mono {s t : St} {n : ℕ} (h : Reach3 s t n) {k : ℕ} (ht : Split t k) :
    Split s k :=
  let ⟨_, hq⟩ := h.carries
  hq.split ht

end Seed.Second
