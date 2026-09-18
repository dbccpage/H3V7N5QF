import Third.Cost

/-!
# Changes commute with rewriting the terms

The second derivation's `rename π s` (every term `x` written `π x`) and its lemmas
about states (`rename_addTerm`, `rename_addAssertion`, `mem_rename_T`,
`mem_rename_A`, `size_rename`, `legal_rename`, `wf_rename`, `exists_perm_of_ne`,
`rename_symm_apply`, `rename_givenA_arb`, …) mention no change and are cited.
What is re-proved for the changes of this seed: `Step2.rename`, `Reach2.rename`.

Derived here with them:
* `result2_iff_A`, `result2_iff_B`: a state is reached from some writing of what
  is given exactly when it is legal, well formed, keeps `a` and `b` two terms
  and asserts `arb` (and `bra`, if given) — the same set of results as under the
  second seed;
* `fewest_changes2_every_writing_A`, `_B`: from some writing of what is given the
  state is reached in exactly `size − size(given)` changes, and from every
  writing every sequence has that length;
* `reach2_iff_some_writing`: reachability up to rewriting is containment up to
  rewriting;
* `reach2_antisymm_writing`: reachability up to rewriting is one-way.
-/

namespace Seed.Third

open Seed Seed.Second St

variable {π : ℕ → ℕ}

/-- A change of the third seed, after rewriting, is a change of the same kind. -/
theorem Step2.rename (hπ : Function.Injective π) {s t : St} (h : Step2 s t) :
    Step2 (rename π s) (rename π t) := by
  cases h with
  | addTerm t ht =>
    rw [rename_addTerm]
    exact Step2.addTerm _ _ ((mem_rename_T hπ).not.2 ht)
  | addAssertion x y hx hy hxy hnew =>
    rw [rename_addAssertion]
    exact Step2.addAssertion _ _ _ ((mem_rename_T hπ).2 hx) ((mem_rename_T hπ).2 hy)
      (hπ.ne hxy) ((mem_rename_A hπ).not.2 hnew)

/-- A sequence of changes, after rewriting, is a sequence of the same length. -/
theorem Reach2.rename (hπ : Function.Injective π) {s t : St} {n : ℕ} (h : Reach2 s t n) :
    Reach2 (rename π s) (rename π t) n := by
  induction h with
  | refl => exact Reach2.refl _
  | step _ st ih => exact Reach2.step ih (st.rename hπ)

/-- Reachability up to rewriting is one-way too: from some writing of `s` to `t` and
from some writing of `t` to `s` is possible only in zero changes. -/
theorem reach2_antisymm_writing (π σ : Equiv.Perm ℕ) {s t : St} {n m : ℕ}
    (h1 : Reach2 (rename π s) t n) (h2 : Reach2 (rename σ t) s m) : n = 0 ∧ m = 0 := by
  have e1 := h1.size_eq
  have e2 := h2.size_eq
  rw [size_rename π.injective] at e1
  rw [size_rename σ.injective] at e2
  omega

/-- **The results, `bra` not asserted to begin with.**  A state is reached from some
writing of what is given exactly when it is legal, well formed, keeps `a` and `b` two
terms, and asserts `arb`. -/
theorem result2_iff_A (g : St) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach2 (rename π givenA) g n) ↔
      (g.Legal ∧ g.WF ∧ g.a ≠ g.b ∧ (g.a, g.b) ∈ g.A) := by
  constructor
  · rintro ⟨π, n, h⟩
    have hl := legal_rename π.injective givenA_legal
    have hw := wf_rename (π := π) givenA_wf
    exact ⟨h.legal hl, h.wf hw, h.names_apart hl (rename_givenA_arb π),
      h.arb_persists (rename_givenA_arb π)⟩
  · rintro ⟨hg, hgw, hne, hab⟩
    obtain ⟨π, h0, h1⟩ := exists_perm_of_ne hne
    have ha' : (rename π.symm g).a = 0 := by
      rw [rename_a, Equiv.symm_apply_eq, h0]
    have hb' : (rename π.symm g).b = 1 := by
      rw [rename_b, Equiv.symm_apply_eq, h1]
    have hab' : (0, 1) ∈ (rename π.symm g).A := by
      have := (mem_rename_A π.symm.injective (s := g)).2 hab
      rwa [show π.symm g.a = 0 from ha', show π.symm g.b = 1 from hb'] at this
    obtain ⟨n, hn, _⟩ := fewest_changes2_upper_A (legal_rename π.symm.injective hg)
      (wf_rename hgw) ha' hb' hab'
    refine ⟨π, n, ?_⟩
    have := hn.rename π.injective
    rwa [rename_symm_apply] at this

/-- **The results, `bra` asserted to begin with.** -/
theorem result2_iff_B (g : St) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach2 (rename π givenB) g n) ↔
      (g.Legal ∧ g.WF ∧ g.a ≠ g.b ∧ (g.a, g.b) ∈ g.A ∧ (g.b, g.a) ∈ g.A) := by
  constructor
  · rintro ⟨π, n, h⟩
    have hl := legal_rename π.injective givenB_legal
    have hw := wf_rename (π := π) givenB_wf
    exact ⟨h.legal hl, h.wf hw, h.names_apart hl (rename_givenB_arb π),
      h.arb_persists (rename_givenB_arb π), h.bra_persists (rename_givenB_bra π)⟩
  · rintro ⟨hg, hgw, hne, hab, hba⟩
    obtain ⟨π, h0, h1⟩ := exists_perm_of_ne hne
    have ha' : (rename π.symm g).a = 0 := by
      rw [rename_a, Equiv.symm_apply_eq, h0]
    have hb' : (rename π.symm g).b = 1 := by
      rw [rename_b, Equiv.symm_apply_eq, h1]
    have hab' : (0, 1) ∈ (rename π.symm g).A := by
      have := (mem_rename_A π.symm.injective (s := g)).2 hab
      rwa [show π.symm g.a = 0 from ha', show π.symm g.b = 1 from hb'] at this
    have hba' : (1, 0) ∈ (rename π.symm g).A := by
      have := (mem_rename_A π.symm.injective (s := g)).2 hba
      rwa [show π.symm g.a = 0 from ha', show π.symm g.b = 1 from hb'] at this
    obtain ⟨n, hn, _⟩ := fewest_changes2_upper_B (legal_rename π.symm.injective hg)
      (wf_rename hgw) ha' hb' hab' hba'
    refine ⟨π, n, ?_⟩
    have := hn.rename π.injective
    rwa [rename_symm_apply] at this

/-- **Fewest changes for every writing, `bra` not asserted to begin with.**  From some
writing of what is given the state is reached in exactly `size − 3` changes, and from
every writing every sequence has that length. -/
theorem fewest_changes2_every_writing_A {g : St} (hg : g.Legal) (hgw : g.WF) (hne : g.a ≠ g.b)
    (hab : (g.a, g.b) ∈ g.A) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach2 (rename π givenA) g n ∧ n + 3 = g.size) ∧
      ∀ (π : Equiv.Perm ℕ) (n : ℕ), Reach2 (rename π givenA) g n → n + 3 = g.size := by
  constructor
  · obtain ⟨π, h0, h1⟩ := exists_perm_of_ne hne
    have ha' : (rename π.symm g).a = 0 := by
      rw [rename_a, Equiv.symm_apply_eq, h0]
    have hb' : (rename π.symm g).b = 1 := by
      rw [rename_b, Equiv.symm_apply_eq, h1]
    have hab' : (0, 1) ∈ (rename π.symm g).A := by
      have := (mem_rename_A π.symm.injective (s := g)).2 hab
      rwa [show π.symm g.a = 0 from ha', show π.symm g.b = 1 from hb'] at this
    obtain ⟨n, hn, hc⟩ := fewest_changes2_upper_A (legal_rename π.symm.injective hg)
      (wf_rename hgw) ha' hb' hab'
    refine ⟨π, n, ?_, ?_⟩
    · have := hn.rename π.injective
      rwa [rename_symm_apply] at this
    · rwa [size_rename π.symm.injective] at hc
  · intro π n h
    have := h.size_eq
    rw [size_rename π.injective, size_givenA] at this
    omega

/-- **Fewest changes for every writing, `bra` asserted to begin with.** -/
theorem fewest_changes2_every_writing_B {g : St} (hg : g.Legal) (hgw : g.WF) (hne : g.a ≠ g.b)
    (hab : (g.a, g.b) ∈ g.A) (hba : (g.b, g.a) ∈ g.A) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach2 (rename π givenB) g n ∧ n + 4 = g.size) ∧
      ∀ (π : Equiv.Perm ℕ) (n : ℕ), Reach2 (rename π givenB) g n → n + 4 = g.size := by
  constructor
  · obtain ⟨π, h0, h1⟩ := exists_perm_of_ne hne
    have ha' : (rename π.symm g).a = 0 := by
      rw [rename_a, Equiv.symm_apply_eq, h0]
    have hb' : (rename π.symm g).b = 1 := by
      rw [rename_b, Equiv.symm_apply_eq, h1]
    have hab' : (0, 1) ∈ (rename π.symm g).A := by
      have := (mem_rename_A π.symm.injective (s := g)).2 hab
      rwa [show π.symm g.a = 0 from ha', show π.symm g.b = 1 from hb'] at this
    have hba' : (1, 0) ∈ (rename π.symm g).A := by
      have := (mem_rename_A π.symm.injective (s := g)).2 hba
      rwa [show π.symm g.a = 0 from ha', show π.symm g.b = 1 from hb'] at this
    obtain ⟨n, hn, hc⟩ := fewest_changes2_upper_B (legal_rename π.symm.injective hg)
      (wf_rename hgw) ha' hb' hab' hba'
    refine ⟨π, n, ?_, ?_⟩
    · have := hn.rename π.injective
      rwa [rename_symm_apply] at this
    · rwa [size_rename π.symm.injective] at hc
  · intro π n h
    have := h.size_eq
    rw [size_rename π.injective, size_givenB] at this
    omega

/-- **Reachability up to rewriting is containment up to rewriting.**  A legal,
well-formed `t` is reached from some writing of `s` exactly when it contains some
writing of `s`. -/
theorem reach2_iff_some_writing {s t : St} (ht : t.Legal) (htw : t.WF) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach2 (rename π s) t n) ↔
      ∃ π : Equiv.Perm ℕ, Contains (rename π s) t := by
  constructor
  · rintro ⟨π, n, h⟩
    exact ⟨π, h.contains⟩
  · rintro ⟨π, h⟩
    obtain ⟨n, hn, _⟩ := reach2_of_contains ht htw h
    exact ⟨π, n, hn⟩

end Seed.Third
