import Eighth.Compare

/-!
# Changes commute with rewriting the terms (two relations)

`rename8 π s` writes every term `x` of `s` as `π x`, in both relations: its parts
are the fourth's `rename4` of the parts (`proj_rename8`, definitionally).  So
the fourth's and fifth's commutation lemmas on a part give the eighth's
(`rename8_addTerm`, `rename8_addAssertion`, `rename8_remove`, `rename8_identify`,
through `ext_proj`), a change after rewriting is a change of the same kind
(`Step8.rename`), a sequence stays a sequence of the same length
(`Reach8.rename`), and the cost is the same in every writing (`costA8_rename`,
`costB8_rename`).  Hence the fewest changes to a result — a state up to
rewriting — is the cost of any of its writings (`fewest_changes8_every_writing_A`,
`_B`).
-/

namespace Seed.Eighth

open Seed Seed.Fourth Seed.Fifth Seed.Sixth DSt

variable (π : Equiv.Perm ℕ)

/-- Every term `x` written as `π x`, in both relations. -/
def rename8 (π : Equiv.Perm ℕ) (s : DSt) : DSt :=
  ⟨s.T.map π.toEmbedding, fun q p => s.M q (π.symm p.1, π.symm p.2), π s.a, π s.b⟩

theorem proj_rename8 (s : DSt) (q : Rel) : (rename8 π s).proj q = rename4 π (s.proj q) := rfl

theorem mem_rename8_T {s : DSt} {x : ℕ} : π x ∈ (rename8 π s).T ↔ x ∈ s.T :=
  mem_rename4_T π (s := s.proj false)

theorem rename8_M (s : DSt) (q : Rel) (x y : ℕ) : (rename8 π s).M q (π x, π y) = s.M q (x, y) :=
  rename4_M π (s.proj q) x y

theorem rename8_addTerm (s : DSt) (t : ℕ) : rename8 π (s.addTerm t) = (rename8 π s).addTerm (π t) := by
  apply ext_proj
  intro q
  rw [proj_rename8, proj_addTerm, proj_addTerm, proj_rename8]
  exact rename4_addTerm π (s.proj q) t

theorem rename8_addAssertion (s : DSt) (q : Rel) (x y : ℕ) :
    rename8 π (s.addAssertion q x y) = (rename8 π s).addAssertion q (π x) (π y) := by
  apply ext_proj
  intro q'
  by_cases hq : q' = q
  · subst hq
    rw [proj_rename8, proj_addAssertion_self, proj_addAssertion_self, proj_rename8]
    exact rename4_addAssertion π (s.proj q') x y
  · rw [proj_rename8, proj_addAssertion_other s hq, proj_addAssertion_other _ hq, proj_rename8]

theorem rename8_remove (s : DSt) (q : Rel) (x y : ℕ) :
    rename8 π (s.remove q x y) = (rename8 π s).remove q (π x) (π y) := by
  apply ext_proj
  intro q'
  by_cases hq : q' = q
  · subst hq
    rw [proj_rename8, proj_remove_self, proj_remove_self, proj_rename8]
    exact rename4_remove π (s.proj q') x y
  · rw [proj_rename8, proj_remove_other s hq, proj_remove_other _ hq, proj_rename8]

theorem rename8_identify (s : DSt) (u v : ℕ) :
    rename8 π (s.identify u v) = (rename8 π s).identify (π u) (π v) := by
  apply ext_proj
  intro q
  rw [proj_rename8, proj_identify, proj_identify, proj_rename8]
  exact rename4_identify π (s.proj q) u v

theorem wf_rename8 {s : DSt} (hw : s.WF) : (rename8 π s).WF :=
  ⟨wf_rename4 π hw.1, wf_rename4 π hw.2⟩

theorem size_rename8 (s : DSt) : (rename8 π s).size = s.size := by
  unfold DSt.size
  rw [proj_rename8, proj_rename8, size_rename4, total_rename4]

theorem rename8_a (s : DSt) : (rename8 π s).a = π s.a := rfl
theorem rename8_b (s : DSt) : (rename8 π s).b = π s.b := rfl

/-- A change of the eighth seed, after rewriting, is a change of the same kind. -/
theorem Step8.rename {s t : DSt} (h : Step8 s t) : Step8 (rename8 π s) (rename8 π t) := by
  cases h with
  | addTerm t ht =>
    rw [rename8_addTerm]
    exact Step8.addTerm _ _ ((mem_rename8_T π).not.2 ht)
  | addAssertion q x y hx hy =>
    rw [rename8_addAssertion]
    exact Step8.addAssertion _ q _ _ ((mem_rename8_T π).2 hx) ((mem_rename8_T π).2 hy)
  | remove q x y hp =>
    rw [rename8_remove]
    exact Step8.remove _ q _ _ (by rw [rename8_M]; exact hp)
  | identify u v hu hv huv =>
    rw [rename8_identify]
    exact Step8.identify _ _ _ ((mem_rename8_T π).2 hu) ((mem_rename8_T π).2 hv) (π.injective.ne huv)

theorem Reach8.rename {s t : DSt} {n : ℕ} (h : Reach8 s t n) : Reach8 (rename8 π s) (rename8 π t) n := by
  induction h with
  | refl => exact Reach8.refl _
  | step _ st ih => exact Reach8.step ih (st.rename π)

theorem costA8_rename (s : DSt) : costA8 (rename8 π s) = costA8 s := by
  rw [costA8_eq, costA8_eq, proj_rename8, proj_rename8, costA6_rename, total_rename4]

theorem costB8_rename (s : DSt) : costB8 (rename8 π s) = costB8 s := by
  rw [costB8_eq, costB8_eq, proj_rename8, proj_rename8, costB6_rename, total_rename4]

theorem rename8_symm_apply (s : DSt) : rename8 π (rename8 π.symm s) = s := by
  apply ext_proj
  intro q
  rw [proj_rename8, proj_rename8]
  exact rename4_symm_apply π (s.proj q)

theorem rename8_ofR (m : MSt) : rename8 π m.ofR = (rename4 π m).ofR := by
  apply ext_proj
  intro q
  cases q
  · rfl
  · rfl

/-- **Fewest changes for every writing, `bra` not asserted to begin with.** -/
theorem fewest_changes8_every_writing_A {g : DSt} (hgw : g.WF) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach8 (rename8 π givenA8) g n ∧ n + 3 = costA8 g) ∧
      ∀ (π : Equiv.Perm ℕ) (n : ℕ), Reach8 (rename8 π givenA8) g n → costA8 g ≤ n + 3 := by
  constructor
  · obtain ⟨π, ha, hb⟩ := exists_writing5 (g.proj false)
    obtain ⟨n, hn, hc⟩ := (fewest_changes8_A (wf_rename8 π.symm hgw) ha hb).1
    refine ⟨π, n, ?_, ?_⟩
    · have := hn.rename π
      rwa [rename8_symm_apply] at this
    · rwa [costA8_rename] at hc
  · intro π n h
    have := h.costA_le (wf_rename8 π givenA8_wf)
    rw [costA8_rename, costA8_givenA8] at this
    omega

theorem fewest_changes8_every_writing_B {g : DSt} (hgw : g.WF) :
    (∃ (π : Equiv.Perm ℕ) (n : ℕ), Reach8 (rename8 π givenB8) g n ∧ n + 4 = costB8 g) ∧
      ∀ (π : Equiv.Perm ℕ) (n : ℕ), Reach8 (rename8 π givenB8) g n → costB8 g ≤ n + 4 := by
  constructor
  · obtain ⟨π, ha, hb⟩ := exists_writing5 (g.proj false)
    obtain ⟨n, hn, hc⟩ := (fewest_changes8_B (wf_rename8 π.symm hgw) ha hb).1
    refine ⟨π, n, ?_, ?_⟩
    · have := hn.rename π
      rwa [rename8_symm_apply] at this
    · rwa [costB8_rename] at hc
  · intro π n h
    have := h.costB_le (wf_rename8 π givenB8_wf)
    rw [costB8_rename, costB8_givenB8] at this
    omega

end Seed.Eighth
