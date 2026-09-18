import Fourth.Compare

/-!
# Changes commute with rewriting the terms (counted states)

`rename4 π s` writes every term `x` of the counted state `s` as `π x`, for a
one-to-one rewriting `π` of all of `ℕ`; the multiplicity of `π x r π y` is that
of `xry`.  Derived here, the analogues of the third derivation's `Rename.lean`
for counted states (the third's lemmas are about `St` and are not reused, since
the state changes):
* `Step4.rename`, `Reach4.rename`: a change, or a sequence, after rewriting is a
  change, or a sequence of the same length;
* `size_rename4`, `legal_rename4`, `wf_rename4`: the size, legality and
  well-formedness are unchanged by rewriting;
* `result4_iff_A`, `result4_iff_B`: a state is reached from some writing of
  what is given exactly when it is legal, well formed, keeps `a` and `b` two
  terms and asserts `arb` (and `bra`, if given) — the results under the FREE
  reading of sameness;
* `fewest_changes4_every_writing_A`, `_B`: from some writing of what is given
  the state is reached in exactly `size − size(given)` changes, and from every
  writing every sequence has that length;
* `reach4_iff_some_writing`: reachability up to rewriting is containment up to
  rewriting;
* `reach4_antisymm_writing`: reachability up to rewriting is one-way.
-/

namespace Seed.Fourth

open Seed Seed.Second Seed.Third MSt

/-- The counted state with every term `x` written `π x`. -/
def rename4 (π : Equiv.Perm ℕ) (s : MSt) : MSt :=
  ⟨s.T.map π.toEmbedding, fun p => s.M (π.symm p.1, π.symm p.2), π s.a, π s.b⟩

variable (π : Equiv.Perm ℕ)

theorem mem_rename4_T {s : MSt} {x : ℕ} : π x ∈ (rename4 π s).T ↔ x ∈ s.T :=
  Finset.mem_map' _

theorem rename4_M (s : MSt) (x y : ℕ) : (rename4 π s).M (π x, π y) = s.M (x, y) := by
  simp [rename4]

theorem rename4_a (s : MSt) : (rename4 π s).a = π s.a := rfl
theorem rename4_b (s : MSt) : (rename4 π s).b = π s.b := rfl

theorem rename4_addTerm (s : MSt) (t : ℕ) :
    rename4 π (s.addTerm t) = (rename4 π s).addTerm (π t) := by
  apply MSt.ext
  · exact Finset.map_insert _ _ _
  · rfl
  · rfl
  · rfl

theorem rename4_addAssertion (s : MSt) (x y : ℕ) :
    rename4 π (s.addAssertion x y) = (rename4 π s).addAssertion (π x) (π y) := by
  apply MSt.ext
  · rfl
  · funext p
    show Function.update s.M (x, y) (s.M (x, y) + 1) (π.symm p.1, π.symm p.2) =
      Function.update (fun q => s.M (π.symm q.1, π.symm q.2)) (π x, π y)
        (s.M (π.symm (π x), π.symm (π y)) + 1) p
    by_cases hp : p = (π x, π y)
    · subst hp
      simp
    · have hne : (π.symm p.1, π.symm p.2) ≠ (x, y) := by
        intro h
        apply hp
        obtain ⟨p1, p2⟩ := p
        simp only [Prod.mk.injEq] at h ⊢
        exact ⟨(Equiv.symm_apply_eq π).1 h.1, (Equiv.symm_apply_eq π).1 h.2⟩
      rw [Function.update_of_ne hne, Function.update_of_ne hp]
  · rfl
  · rfl

theorem total_rename4 (s : MSt) : (rename4 π s).total = s.total := by
  unfold MSt.total
  symm
  refine Finset.sum_equiv (π.prodCongr π) ?_ ?_
  · intro p
    obtain ⟨x, y⟩ := p
    simp [rename4, Finset.mem_product]
  · intro p _
    obtain ⟨x, y⟩ := p
    simp [rename4]

theorem size_rename4 (s : MSt) : (rename4 π s).size = s.size := by
  unfold MSt.size
  rw [total_rename4]
  show (s.T.map π.toEmbedding).card + s.total = s.T.card + s.total
  rw [Finset.card_map]

theorem legal_rename4 {s : MSt} (hs : s.Legal) : (rename4 π s).Legal := by
  intro x
  exact hs _

theorem wf_rename4 {s : MSt} (hw : s.WF) : (rename4 π s).WF := by
  refine ⟨fun p hp => ?_, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hw.1 _ hp
    constructor
    · show p.1 ∈ s.T.map π.toEmbedding
      rw [Finset.mem_map_equiv]
      exact h1
    · show p.2 ∈ s.T.map π.toEmbedding
      rw [Finset.mem_map_equiv]
      exact h2
  · exact (mem_rename4_T π).2 hw.2.1
  · exact (mem_rename4_T π).2 hw.2.2

theorem simple_rename4 {s : MSt} (hs : s.Simple) : (rename4 π s).Simple := by
  intro p
  exact hs _

theorem rename4_symm_apply (s : MSt) : rename4 π (rename4 π.symm s) = s := by
  apply MSt.ext
  · ext x
    simp [rename4]
  · funext p
    simp [rename4]
  · simp [rename4]
  · simp [rename4]

/-- A change of the fourth seed, after rewriting, is a change of the same kind. -/
theorem Step4.rename {s t : MSt} (h : Step4 s t) : Step4 (rename4 π s) (rename4 π t) := by
  cases h with
  | addTerm t ht =>
    rw [rename4_addTerm]
    exact Step4.addTerm _ _ ((mem_rename4_T π).not.2 ht)
  | addAssertion x y hx hy hxy =>
    rw [rename4_addAssertion]
    exact Step4.addAssertion _ _ _ ((mem_rename4_T π).2 hx) ((mem_rename4_T π).2 hy)
      (π.injective.ne hxy)

/-- A sequence of changes, after rewriting, is a sequence of the same length. -/
theorem Reach4.rename {s t : MSt} {n : ℕ} (h : Reach4 s t n) :
    Reach4 (rename4 π s) (rename4 π t) n := by
  induction h with
  | refl => exact Reach4.refl _
  | step _ st ih => exact Reach4.step ih (st.rename π)

/-- Reachability up to rewriting is one-way too: from some writing of `s` to `t` and
from some writing of `t` to `s` is possible only in zero changes. -/
theorem reach4_antisymm_writing (σ : Equiv.Perm ℕ) {s t : MSt} {n m : ℕ} (hw : s.WF)
    (h1 : Reach4 (rename4 π s) t n) (h2 : Reach4 (rename4 σ t) s m) : n = 0 ∧ m = 0 := by
  have e1 := h1.size_eq (wf_rename4 π hw)
  have e2 := h2.size_eq (wf_rename4 σ (h1.wf (wf_rename4 π hw)))
  rw [size_rename4] at e1 e2
  omega

/-- A writing of `g` with `a` written `0` and `b` written `1`. -/
theorem exists_writing {g : MSt} (hne : g.a ≠ g.b) :
    ∃ π : Equiv.Perm ℕ, (rename4 π.symm g).a = 0 ∧ (rename4 π.symm g).b = 1 ∧
      (rename4 π.symm g).M (0, 1) = g.M (g.a, g.b) ∧ (rename4 π.symm g).M (1, 0) = g.M (g.b, g.a) := by
  obtain ⟨π, h0, h1⟩ := exists_perm_of_ne hne
  refine ⟨π, ?_, ?_, ?_, ?_⟩
  · rw [rename4_a, Equiv.symm_apply_eq, h0]
  · rw [rename4_b, Equiv.symm_apply_eq, h1]
  · show g.M (π.symm.symm 0, π.symm.symm 1) = g.M (g.a, g.b)
    rw [Equiv.symm_symm, h0, h1]
  · show g.M (π.symm.symm 1, π.symm.symm 0) = g.M (g.b, g.a)
    rw [Equiv.symm_symm, h0, h1]

/-- **The results, `bra` not asserted to begin with.**  A state is reached from some
writing of what is given exactly when it is legal, well formed, keeps `a` and `b` two
terms, and asserts `arb`. -/
theorem result4_iff_A (g : MSt) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach4 (rename4 π givenA4) g n) ↔
      (g.Legal ∧ g.WF ∧ g.a ≠ g.b ∧ g.M (g.a, g.b) ≠ 0) := by
  constructor
  · rintro ⟨π, n, h⟩
    have hl := legal_rename4 π givenA4_legal
    have hw := wf_rename4 π givenA4_wf
    have hab : (rename4 π givenA4).M ((rename4 π givenA4).a, (rename4 π givenA4).b) ≠ 0 := by
      rw [rename4_a, rename4_b, rename4_M]
      exact givenA4_arb_ne
    exact ⟨h.legal hl, h.wf hw, h.names_apart hl hab, h.arb_persists hab⟩
  · rintro ⟨hg, hgw, hne, hab⟩
    obtain ⟨π, ha', hb', hab', _⟩ := exists_writing hne
    obtain ⟨n, hn, _⟩ := fewest_changes4_upper_A (legal_rename4 π.symm hg) (wf_rename4 π.symm hgw)
      ha' hb' (by rw [hab']; exact hab)
    refine ⟨π, n, ?_⟩
    have := hn.rename π
    rwa [rename4_symm_apply] at this

/-- **The results, `bra` asserted to begin with.** -/
theorem result4_iff_B (g : MSt) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach4 (rename4 π givenB4) g n) ↔
      (g.Legal ∧ g.WF ∧ g.a ≠ g.b ∧ g.M (g.a, g.b) ≠ 0 ∧ g.M (g.b, g.a) ≠ 0) := by
  constructor
  · rintro ⟨π, n, h⟩
    have hl := legal_rename4 π givenB4_legal
    have hw := wf_rename4 π givenB4_wf
    have hab : (rename4 π givenB4).M ((rename4 π givenB4).a, (rename4 π givenB4).b) ≠ 0 := by
      rw [rename4_a, rename4_b, rename4_M]
      exact givenB4_arb_ne
    have hba : (rename4 π givenB4).M ((rename4 π givenB4).b, (rename4 π givenB4).a) ≠ 0 := by
      rw [rename4_a, rename4_b, rename4_M]
      exact givenB4_bra_ne
    exact ⟨h.legal hl, h.wf hw, h.names_apart hl hab, h.arb_persists hab, h.bra_persists hba⟩
  · rintro ⟨hg, hgw, hne, hab, hba⟩
    obtain ⟨π, ha', hb', hab', hba'⟩ := exists_writing hne
    obtain ⟨n, hn, _⟩ := fewest_changes4_upper_B (legal_rename4 π.symm hg) (wf_rename4 π.symm hgw)
      ha' hb' (by rw [hab']; exact hab) (by rw [hba']; exact hba)
    refine ⟨π, n, ?_⟩
    have := hn.rename π
    rwa [rename4_symm_apply] at this

/-- **Fewest changes for every writing, `bra` not asserted to begin with.**  From some
writing of what is given the state is reached in exactly `size − 3` changes, and from
every writing every sequence has that length. -/
theorem fewest_changes4_every_writing_A {g : MSt} (hg : g.Legal) (hgw : g.WF) (hne : g.a ≠ g.b)
    (hab : g.M (g.a, g.b) ≠ 0) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach4 (rename4 π givenA4) g n ∧ n + 3 = g.size) ∧
      ∀ (π : Equiv.Perm ℕ) (n : ℕ), Reach4 (rename4 π givenA4) g n → n + 3 = g.size := by
  constructor
  · obtain ⟨π, ha', hb', hab', _⟩ := exists_writing hne
    obtain ⟨n, hn, hc⟩ := fewest_changes4_upper_A (legal_rename4 π.symm hg) (wf_rename4 π.symm hgw)
      ha' hb' (by rw [hab']; exact hab)
    refine ⟨π, n, ?_, ?_⟩
    · have := hn.rename π
      rwa [rename4_symm_apply] at this
    · rwa [size_rename4] at hc
  · intro π n h
    have := h.size_eq (wf_rename4 π givenA4_wf)
    rw [size_rename4, size_givenA4] at this
    omega

/-- **Fewest changes for every writing, `bra` asserted to begin with.** -/
theorem fewest_changes4_every_writing_B {g : MSt} (hg : g.Legal) (hgw : g.WF) (hne : g.a ≠ g.b)
    (hab : g.M (g.a, g.b) ≠ 0) (hba : g.M (g.b, g.a) ≠ 0) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach4 (rename4 π givenB4) g n ∧ n + 4 = g.size) ∧
      ∀ (π : Equiv.Perm ℕ) (n : ℕ), Reach4 (rename4 π givenB4) g n → n + 4 = g.size := by
  constructor
  · obtain ⟨π, ha', hb', hab', hba'⟩ := exists_writing hne
    obtain ⟨n, hn, hc⟩ := fewest_changes4_upper_B (legal_rename4 π.symm hg) (wf_rename4 π.symm hgw)
      ha' hb' (by rw [hab']; exact hab) (by rw [hba']; exact hba)
    refine ⟨π, n, ?_, ?_⟩
    · have := hn.rename π
      rwa [rename4_symm_apply] at this
    · rwa [size_rename4] at hc
  · intro π n h
    have := h.size_eq (wf_rename4 π givenB4_wf)
    rw [size_rename4, size_givenB4] at this
    omega

/-- **Reachability up to rewriting is containment up to rewriting.**  A legal,
well-formed `t` is reached from some writing of a well-formed `s` exactly when it
contains some writing of `s`. -/
theorem reach4_iff_some_writing {s t : MSt} (hs : s.WF) (ht : t.Legal) (htw : t.WF) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach4 (rename4 π s) t n) ↔
      ∃ π : Equiv.Perm ℕ, Contains4 (rename4 π s) t := by
  constructor
  · rintro ⟨π, n, h⟩
    exact ⟨π, h.contains⟩
  · rintro ⟨π, h⟩
    obtain ⟨n, hn, _⟩ := reach4_of_contains (wf_rename4 π hs) ht htw h
    exact ⟨π, n, hn⟩

end Seed.Fourth
