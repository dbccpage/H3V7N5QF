import Fifth.Compare

/-!
# Changes commute with rewriting the terms (four kinds, counted states)

The fourth derivation's `rename4 π s` writes every term `x` of `s` as `π x`.  Derived
here, for the two new kinds: `rename4_remove`, `rename4_identify` (replacing after
rewriting is rewriting after replacing, `merge_perm`); so a change of the fifth seed
after rewriting is a change of the same kind (`Step5.rename`), a sequence stays a
sequence of the same length (`Reach5.rename`), and the cost is the same in every
writing (`lostA5_rename`, `costA5_rename`, `lostB5_rename`, `costB5_rename`).  Hence
the fewest changes to a result — a state up to rewriting — is the cost of any of its
writings (`fewest_changes5_every_writing_A`, `_B`), which closes the step from
written states to results that the first derivation left open (1:O3) for the four
kinds on counted states.
-/

namespace Seed.Fifth

open Seed Seed.Fourth MSt

variable (π : Equiv.Perm ℕ)

theorem rename4_remove (s : MSt) (x y : ℕ) :
    rename4 π (s.remove x y) = (rename4 π s).remove (π x) (π y) := by
  apply MSt.ext
  · rfl
  · funext p
    show Function.update s.M (x, y) (s.M (x, y) - 1) (π.symm p.1, π.symm p.2) =
      Function.update (fun q => s.M (π.symm q.1, π.symm q.2)) (π x, π y)
        (s.M (π.symm (π x), π.symm (π y)) - 1) p
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

/-- Replacing after rewriting is rewriting after replacing. -/
theorem merge_perm (u v x : ℕ) : merge (π u) (π v) (π x) = π (merge u v x) := by
  unfold merge
  by_cases h : x = v
  · subst h
    simp
  · rw [if_neg h, if_neg (fun h' => h (π.injective h'))]

theorem rename4_identify (s : MSt) (u v : ℕ) :
    rename4 π (s.identify u v) = (rename4 π s).identify (π u) (π v) := by
  apply MSt.ext
  · show (s.T.erase v).map π.toEmbedding = (s.T.map π.toEmbedding).erase (π v)
    exact Finset.map_erase _ _ _
  · funext p
    obtain ⟨p1, p2⟩ := p
    show (∑ q ∈ (s.T ×ˢ s.T).filter (fun q => (merge u v q.1, merge u v q.2) = (π.symm p1, π.symm p2)),
        s.M q) =
      ∑ q ∈ ((s.T.map π.toEmbedding) ×ˢ (s.T.map π.toEmbedding)).filter
        (fun q => (merge (π u) (π v) q.1, merge (π u) (π v) q.2) = (p1, p2)), s.M (π.symm q.1, π.symm q.2)
    refine Finset.sum_nbij' (fun q => (π q.1, π q.2)) (fun q => (π.symm q.1, π.symm q.2)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨x, y⟩ hq
      obtain ⟨⟨hx, hy⟩, hp⟩ := mem_fiber.1 hq
      simp only [Prod.mk.injEq] at hp
      rw [Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨Finset.mem_map' _ |>.2 hx, Finset.mem_map' _ |>.2 hy⟩, ?_⟩
      simp only [merge_perm, hp.1, hp.2, Equiv.apply_symm_apply]
    · rintro ⟨x, y⟩ hq
      rw [Finset.mem_filter, Finset.mem_product] at hq
      obtain ⟨⟨hx, hy⟩, hp⟩ := hq
      simp only [Prod.mk.injEq] at hp
      rw [Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · simpa using hx
      · simpa using hy
      · simp only [Prod.mk.injEq]
        constructor
        · rw [← hp.1, ← merge_perm]
          simp
        · rw [← hp.2, ← merge_perm]
          simp
    · rintro ⟨x, y⟩ _
      simp
    · rintro ⟨x, y⟩ _
      simp
    · rintro ⟨x, y⟩ _
      simp
  · show π (merge u v s.a) = merge (π u) (π v) (π s.a)
    exact (merge_perm π u v s.a).symm
  · show π (merge u v s.b) = merge (π u) (π v) (π s.b)
    exact (merge_perm π u v s.b).symm

/-- A change of the fifth seed, after rewriting, is a change of the same kind. -/
theorem Step5.rename {s t : MSt} (h : Step5 s t) : Step5 (rename4 π s) (rename4 π t) := by
  cases h with
  | addTerm t ht => exact ((Step4.addTerm s t ht).rename π).toStep5
  | addAssertion x y hx hy hxy => exact ((Step4.addAssertion s x y hx hy hxy).rename π).toStep5
  | remove x y hp =>
    rw [rename4_remove]
    exact Step5.remove _ _ _ (by rw [rename4_M]; exact hp)
  | identify u v hu hv huv h1 h2 =>
    rw [rename4_identify]
    exact Step5.identify _ _ _ ((mem_rename4_T π).2 hu) ((mem_rename4_T π).2 hv)
      (π.injective.ne huv) (by rw [rename4_M]; exact h1) (by rw [rename4_M]; exact h2)

/-- A sequence of changes, after rewriting, is a sequence of the same length. -/
theorem Reach5.rename {s t : MSt} {n : ℕ} (h : Reach5 s t n) :
    Reach5 (rename4 π s) (rename4 π t) n := by
  induction h with
  | refl => exact Reach5.refl _
  | step _ st ih => exact Reach5.step ih (st.rename π)

/-- The destroyed givens are the same in every writing. -/
theorem lostA5_rename (s : MSt) : lostA5 (rename4 π s) = lostA5 s := by
  unfold lostA5 miss5
  rw [rename4_a, rename4_b, rename4_M]
  simp only [π.injective.eq_iff]

theorem lostB5_rename (s : MSt) : lostB5 (rename4 π s) = lostB5 s := by
  unfold lostB5 miss5
  rw [rename4_a, rename4_b, rename4_M, rename4_M]
  simp only [π.injective.eq_iff]

theorem costA5_rename (s : MSt) : costA5 (rename4 π s) = costA5 s := by
  unfold costA5
  rw [size_rename4, lostA5_rename]

theorem costB5_rename (s : MSt) : costB5 (rename4 π s) = costB5 s := by
  unfold costB5
  rw [size_rename4, lostB5_rename]

/-- Every state has a writing with `a` written `0` and `b` written `1` or `0`. -/
theorem exists_writing5 (g : MSt) :
    ∃ π : Equiv.Perm ℕ, (rename4 π.symm g).a = 0 ∧ ((rename4 π.symm g).b = 1 ∨ (rename4 π.symm g).b = 0) := by
  by_cases h : g.a = g.b
  · refine ⟨Equiv.swap 0 g.a, ?_, Or.inr ?_⟩
    · rw [rename4_a, Equiv.symm_apply_eq, Equiv.swap_apply_left]
    · rw [rename4_b, Equiv.symm_apply_eq, Equiv.swap_apply_left, h]
  · obtain ⟨π, h0, h1⟩ := Seed.Second.exists_perm_of_ne h
    exact ⟨π, by rw [rename4_a, Equiv.symm_apply_eq, h0],
      Or.inl (by rw [rename4_b, Equiv.symm_apply_eq, h1])⟩

/-- **Fewest changes for every writing, `bra` not asserted to begin with.**  Every legal
well-formed state is reached from some writing of what is given in exactly
`costA5 − 3` changes, and from every writing no sequence is shorter. -/
theorem fewest_changes5_every_writing_A {g : MSt} (hg : g.Legal) (hgw : g.WF) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach5 (rename4 π givenA4) g n ∧ n + 3 = costA5 g) ∧
      ∀ (π : Equiv.Perm ℕ) (n : ℕ), Reach5 (rename4 π givenA4) g n → costA5 g ≤ n + 3 := by
  constructor
  · obtain ⟨π, ha, hb⟩ := exists_writing5 g
    obtain ⟨n, hn, hc⟩ :=
      (fewest_changes5_A (legal_rename4 π.symm hg) (wf_rename4 π.symm hgw) ha hb).1
    refine ⟨π, n, ?_, ?_⟩
    · have := hn.rename π
      rwa [rename4_symm_apply] at this
    · rwa [costA5_rename] at hc
  · intro π n h
    have := h.costA_le (wf_rename4 π givenA4_wf)
    rw [costA5_rename, costA5_givenA4] at this
    omega

/-- **Fewest changes for every writing, `bra` asserted to begin with.** -/
theorem fewest_changes5_every_writing_B {g : MSt} (hg : g.Legal) (hgw : g.WF) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach5 (rename4 π givenB4) g n ∧ n + 4 = costB5 g) ∧
      ∀ (π : Equiv.Perm ℕ) (n : ℕ), Reach5 (rename4 π givenB4) g n → costB5 g ≤ n + 4 := by
  constructor
  · obtain ⟨π, ha, hb⟩ := exists_writing5 g
    obtain ⟨n, hn, hc⟩ :=
      (fewest_changes5_B (legal_rename4 π.symm hg) (wf_rename4 π.symm hgw) ha hb).1
    refine ⟨π, n, ?_, ?_⟩
    · have := hn.rename π
      rwa [rename4_symm_apply] at this
    · rwa [costB5_rename] at hc
  · intro π n h
    have := h.costB_le (wf_rename4 π givenB4_wf)
    rw [costB5_rename, costB5_givenB4] at this
    omega

end Seed.Fifth
