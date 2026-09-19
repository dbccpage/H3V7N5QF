import Sixth.Compare

/-!
# Changes commute with rewriting the terms (nothing forbidden)

The fourth's `rename4 π s` writes every term `x` of `s` as `π x`.  The four kinds
commute with it: `rename4_addTerm`, `rename4_addAssertion` (the fourth's, stated
for any `x`, `y`), `rename4_remove`, `rename4_identify` (the fifth's) mention no
legality.  So a change of the sixth seed after rewriting is a change of the same
kind (`Step6.rename`), a sequence stays a sequence of the same length
(`Reach6.rename`), and the cost is the same in every writing (`lostA6_rename`,
`costA6_rename`, `lostB6_rename`, `costB6_rename`).  Hence the fewest changes to a
result — a state up to rewriting — is the cost of any of its writings
(`fewest_changes6_every_writing_A`, `_B`).
-/

namespace Seed.Sixth

open Seed Seed.Fourth Seed.Fifth MSt

variable (π : Equiv.Perm ℕ)

/-- A change of the sixth seed, after rewriting, is a change of the same kind. -/
theorem Step6.rename {s t : MSt} (h : Step6 s t) : Step6 (rename4 π s) (rename4 π t) := by
  cases h with
  | addTerm t ht =>
    rw [rename4_addTerm]
    exact Step6.addTerm _ _ ((mem_rename4_T π).not.2 ht)
  | addAssertion x y hx hy =>
    rw [rename4_addAssertion]
    exact Step6.addAssertion _ _ _ ((mem_rename4_T π).2 hx) ((mem_rename4_T π).2 hy)
  | remove x y hp =>
    rw [rename4_remove]
    exact Step6.remove _ _ _ (by rw [rename4_M]; exact hp)
  | identify u v hu hv huv =>
    rw [rename4_identify]
    exact Step6.identify _ _ _ ((mem_rename4_T π).2 hu) ((mem_rename4_T π).2 hv) (π.injective.ne huv)

/-- A sequence of changes, after rewriting, is a sequence of the same length. -/
theorem Reach6.rename {s t : MSt} {n : ℕ} (h : Reach6 s t n) :
    Reach6 (rename4 π s) (rename4 π t) n := by
  induction h with
  | refl => exact Reach6.refl _
  | step _ st ih => exact Reach6.step ih (st.rename π)

/-- The destroyed givens are the same in every writing. -/
theorem lostA6_rename (s : MSt) : lostA6 (rename4 π s) = lostA6 s := by
  unfold lostA6 miss5
  rw [rename4_a, rename4_b, rename4_M, rename4_M]
  simp only [π.injective.eq_iff]

theorem lostB6_rename (s : MSt) : lostB6 (rename4 π s) = lostB6 s := by
  unfold lostB6 miss5
  rw [rename4_a, rename4_b, rename4_M, rename4_M, rename4_M]
  simp only [π.injective.eq_iff]

theorem costA6_rename (s : MSt) : costA6 (rename4 π s) = costA6 s := by
  unfold costA6
  rw [size_rename4, lostA6_rename]

theorem costB6_rename (s : MSt) : costB6 (rename4 π s) = costB6 s := by
  unfold costB6
  rw [size_rename4, lostB6_rename]

/-- **Fewest changes for every writing, `bra` not asserted to begin with.**  Every
well-formed state is reached from some writing of what is given in exactly
`costA6 − 3` changes, and from every writing no sequence is shorter. -/
theorem fewest_changes6_every_writing_A {g : MSt} (hgw : g.WF) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach6 (rename4 π givenA4) g n ∧ n + 3 = costA6 g) ∧
      ∀ (π : Equiv.Perm ℕ) (n : ℕ), Reach6 (rename4 π givenA4) g n → costA6 g ≤ n + 3 := by
  constructor
  · obtain ⟨π, ha, hb⟩ := exists_writing5 g
    obtain ⟨n, hn, hc⟩ := (fewest_changes6_A (wf_rename4 π.symm hgw) ha hb).1
    refine ⟨π, n, ?_, ?_⟩
    · have := hn.rename π
      rwa [rename4_symm_apply] at this
    · rwa [costA6_rename] at hc
  · intro π n h
    have := h.costA_le (wf_rename4 π givenA4_wf)
    rw [costA6_rename, costA6_givenA4] at this
    omega

/-- **Fewest changes for every writing, `bra` asserted to begin with.** -/
theorem fewest_changes6_every_writing_B {g : MSt} (hgw : g.WF) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach6 (rename4 π givenB4) g n ∧ n + 4 = costB6 g) ∧
      ∀ (π : Equiv.Perm ℕ) (n : ℕ), Reach6 (rename4 π givenB4) g n → costB6 g ≤ n + 4 := by
  constructor
  · obtain ⟨π, ha, hb⟩ := exists_writing5 g
    obtain ⟨n, hn, hc⟩ := (fewest_changes6_B (wf_rename4 π.symm hgw) ha hb).1
    refine ⟨π, n, ?_, ?_⟩
    · have := hn.rename π
      rwa [rename4_symm_apply] at this
    · rwa [costB6_rename] at hc
  · intro π n h
    have := h.costB_le (wf_rename4 π givenB4_wf)
    rw [costB6_rename, costB6_givenB4] at this
    omega

end Seed.Sixth
