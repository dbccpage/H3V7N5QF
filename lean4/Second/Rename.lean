import Second.Cost

/-!
# Changes commute with rewriting the terms

`rename π s` is `s` with every term `x` written `π x`.  For a one-to-one `π`
every change of the second seed becomes a change of the same kind on the
renamed state (`Step3.rename`), and so does every sequence (`Reach3.rename`);
the size is unchanged (`size_rename`).  This is the step the first derivation
left open (its O3): it carries the statements proved for the writing `a = 0`,
`b = 1` to every writing.

Derived here with it:
* `result_iff_A`, `result_iff_B`: a state is reached from some writing of what
  is given exactly when it is legal, well formed, keeps `a` and `b` two terms
  and asserts `arb` (and `bra`, if given);
* `fewest_changes3_every_writing_A`, `_B`: from some writing of what is given
  the state is reached in exactly `size − size(given)` changes, and from no
  writing in fewer.
-/

namespace Seed.Second

open Seed St

/-- The state with every term `x` written `π x`. -/
def rename (π : ℕ → ℕ) (s : St) : St :=
  ⟨s.T.image π, s.A.image (Prod.map π π), π s.a, π s.b⟩

variable {π : ℕ → ℕ}

theorem rename_addTerm (s : St) (t : ℕ) :
    rename π (s.addTerm t) = (rename π s).addTerm (π t) := by
  simp [rename, St.addTerm, Finset.image_insert]

theorem rename_addAssertion (s : St) (x y : ℕ) :
    rename π (s.addAssertion x y) = (rename π s).addAssertion (π x) (π y) := by
  simp [rename, St.addAssertion, Finset.image_insert, Prod.map]

theorem merge_rename (hπ : Function.Injective π) (u v x : ℕ) :
    π (merge u v x) = merge (π u) (π v) (π x) := by
  unfold merge
  by_cases h : x = v
  · subst h
    simp
  · rw [if_neg h, if_neg (fun e => h (hπ e))]

theorem rename_identify (hπ : Function.Injective π) (s : St) (u v : ℕ) :
    rename π (s.identify u v) = (rename π s).identify (π u) (π v) := by
  apply St.ext
  · exact Finset.image_erase hπ s.T v
  · simp only [rename, St.identify, Finset.image_image]
    congr 1
    funext p
    obtain ⟨x, y⟩ := p
    simp [Prod.map, merge_rename hπ]
  · exact merge_rename hπ u v s.a
  · exact merge_rename hπ u v s.b

theorem mem_rename_T (hπ : Function.Injective π) {s : St} {x : ℕ} :
    π x ∈ (rename π s).T ↔ x ∈ s.T := by
  simp [rename, Finset.mem_image, hπ.eq_iff]

theorem mem_rename_A (hπ : Function.Injective π) {s : St} {x y : ℕ} :
    (π x, π y) ∈ (rename π s).A ↔ (x, y) ∈ s.A := by
  constructor
  · intro h
    obtain ⟨⟨u, v⟩, hp, he⟩ := Finset.mem_image.1 h
    simp only [Prod.map, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ : u = x ∧ v = y := ⟨hπ he.1, hπ he.2⟩
    exact hp
  · intro h
    exact Finset.mem_image.2 ⟨(x, y), h, rfl⟩

/-- A change of the second seed, after rewriting, is a change of the same kind. -/
theorem Step3.rename (hπ : Function.Injective π) {s t : St} (h : Step3 s t) :
    Step3 (rename π s) (rename π t) := by
  cases h with
  | addTerm t ht =>
    rw [rename_addTerm]
    exact Step3.addTerm _ _ ((mem_rename_T hπ).not.2 ht)
  | addAssertion x y hx hy hxy hnew =>
    rw [rename_addAssertion]
    exact Step3.addAssertion _ _ _ ((mem_rename_T hπ).2 hx) ((mem_rename_T hπ).2 hy)
      (hπ.ne hxy) ((mem_rename_A hπ).not.2 hnew)
  | identify u v hu hv huv h1 h2 =>
    rw [rename_identify hπ]
    exact Step3.identify _ _ _ ((mem_rename_T hπ).2 hu) ((mem_rename_T hπ).2 hv)
      (hπ.ne huv) ((mem_rename_A hπ).not.2 h1) ((mem_rename_A hπ).not.2 h2)

/-- A sequence of changes, after rewriting, is a sequence of the same length. -/
theorem Reach3.rename (hπ : Function.Injective π) {s t : St} {n : ℕ} (h : Reach3 s t n) :
    Reach3 (rename π s) (rename π t) n := by
  induction h with
  | refl => exact Reach3.refl _
  | step _ st ih => exact Reach3.step ih (st.rename hπ)

theorem size_rename (hπ : Function.Injective π) (s : St) : (rename π s).size = s.size := by
  simp only [St.size, rename]
  rw [Finset.card_image_of_injective _ hπ, Finset.card_image_of_injective _ (hπ.prodMap hπ)]

theorem rename_rename (π σ : ℕ → ℕ) (s : St) : rename σ (rename π s) = rename (σ ∘ π) s := by
  simp [rename, Finset.image_image, Prod.map_comp_map]

theorem rename_id (s : St) : rename id s = s := by
  apply St.ext <;> simp [rename]

theorem rename_symm_apply (π : Equiv.Perm ℕ) (s : St) : rename π (rename π.symm s) = s := by
  rw [rename_rename, Equiv.self_comp_symm]
  exact rename_id s

theorem legal_rename (hπ : Function.Injective π) {s : St} (hs : s.Legal) : (rename π s).Legal := by
  intro x hx
  obtain ⟨⟨y, z⟩, hp, he⟩ := Finset.mem_image.1 hx
  simp only [Prod.map, Prod.mk.injEq] at he
  have : y = z := hπ (he.1.trans he.2.symm)
  subst this
  exact hs _ hp

theorem wf_rename {s : St} (hs : s.WF) : (rename π s).WF := by
  obtain ⟨hA, ha, hb⟩ := hs
  refine ⟨fun p hp => ?_, Finset.mem_image_of_mem π ha, Finset.mem_image_of_mem π hb⟩
  obtain ⟨⟨y, z⟩, hq, rfl⟩ := Finset.mem_image.1 hp
  exact ⟨Finset.mem_image_of_mem π (hA _ hq).1, Finset.mem_image_of_mem π (hA _ hq).2⟩

theorem rename_a (s : St) : (rename π s).a = π s.a := rfl

theorem rename_b (s : St) : (rename π s).b = π s.b := rfl

/-- Two different terms can be written `0` and `1` by a rewriting. -/
theorem exists_perm_of_ne {a b : ℕ} (hab : a ≠ b) : ∃ π : Equiv.Perm ℕ, π 0 = a ∧ π 1 = b := by
  set b' := Equiv.swap 0 a b with hb'
  have hb0 : b' ≠ 0 := by
    intro h
    rw [hb', Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
    exact hab h.symm
  refine ⟨Equiv.swap 0 a * Equiv.swap 1 b', ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (by omega) (Ne.symm hb0),
      Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, hb', Equiv.swap_apply_self]

/-- What is given, rewritten by `π`, still asserts `arb` between its named terms. -/
theorem rename_givenA_arb (π : Equiv.Perm ℕ) :
    ((rename π givenA).a, (rename π givenA).b) ∈ (rename π givenA).A :=
  (mem_rename_A π.injective).2 givenA_arb

theorem rename_givenB_arb (π : Equiv.Perm ℕ) :
    ((rename π givenB).a, (rename π givenB).b) ∈ (rename π givenB).A :=
  (mem_rename_A π.injective).2 givenB_arb

theorem rename_givenB_bra (π : Equiv.Perm ℕ) :
    ((rename π givenB).b, (rename π givenB).a) ∈ (rename π givenB).A :=
  (mem_rename_A π.injective).2 givenB_bra

/-- **The results, `bra` not asserted to begin with.**  A state is reached from some
writing of what is given exactly when it is legal, well formed, keeps `a` and `b` two
terms, and asserts `arb`. -/
theorem result_iff_A (g : St) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach3 (rename π givenA) g n) ↔
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
    obtain ⟨n, hn, _⟩ := fewest_changes3_upper_A (legal_rename π.symm.injective hg)
      (wf_rename hgw) ha' hb' hab'
    refine ⟨π, n, ?_⟩
    have := hn.rename π.injective
    rwa [rename_symm_apply] at this

/-- **The results, `bra` asserted to begin with.** -/
theorem result_iff_B (g : St) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach3 (rename π givenB) g n) ↔
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
    obtain ⟨n, hn, _⟩ := fewest_changes3_upper_B (legal_rename π.symm.injective hg)
      (wf_rename hgw) ha' hb' hab' hba'
    refine ⟨π, n, ?_⟩
    have := hn.rename π.injective
    rwa [rename_symm_apply] at this

/-- **Fewest changes for every writing, `bra` not asserted to begin with.**  From some
writing of what is given the state is reached in exactly `size − 3` changes, and from
no writing in fewer. -/
theorem fewest_changes3_every_writing_A {g : St} (hg : g.Legal) (hgw : g.WF) (hne : g.a ≠ g.b)
    (hab : (g.a, g.b) ∈ g.A) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach3 (rename π givenA) g n ∧ n + 3 = g.size) ∧
      ∀ (π : Equiv.Perm ℕ) (n : ℕ), Reach3 (rename π givenA) g n → g.size ≤ n + 3 := by
  constructor
  · obtain ⟨π, h0, h1⟩ := exists_perm_of_ne hne
    have ha' : (rename π.symm g).a = 0 := by
      rw [rename_a, Equiv.symm_apply_eq, h0]
    have hb' : (rename π.symm g).b = 1 := by
      rw [rename_b, Equiv.symm_apply_eq, h1]
    have hab' : (0, 1) ∈ (rename π.symm g).A := by
      have := (mem_rename_A π.symm.injective (s := g)).2 hab
      rwa [show π.symm g.a = 0 from ha', show π.symm g.b = 1 from hb'] at this
    obtain ⟨n, hn, hc⟩ := fewest_changes3_upper_A (legal_rename π.symm.injective hg)
      (wf_rename hgw) ha' hb' hab'
    refine ⟨π, n, ?_, ?_⟩
    · have := hn.rename π.injective
      rwa [rename_symm_apply] at this
    · rwa [size_rename π.symm.injective] at hc
  · intro π n h
    have := h.size_le
    rw [size_rename π.injective, size_givenA] at this
    omega

/-- **Fewest changes for every writing, `bra` asserted to begin with.** -/
theorem fewest_changes3_every_writing_B {g : St} (hg : g.Legal) (hgw : g.WF) (hne : g.a ≠ g.b)
    (hab : (g.a, g.b) ∈ g.A) (hba : (g.b, g.a) ∈ g.A) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach3 (rename π givenB) g n ∧ n + 4 = g.size) ∧
      ∀ (π : Equiv.Perm ℕ) (n : ℕ), Reach3 (rename π givenB) g n → g.size ≤ n + 4 := by
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
    obtain ⟨n, hn, hc⟩ := fewest_changes3_upper_B (legal_rename π.symm.injective hg)
      (wf_rename hgw) ha' hb' hab' hba'
    refine ⟨π, n, ?_, ?_⟩
    · have := hn.rename π.injective
      rwa [rename_symm_apply] at this
    · rwa [size_rename π.symm.injective] at hc
  · intro π n h
    have := h.size_le
    rw [size_rename π.injective, size_givenB] at this
    omega

end Seed.Second
