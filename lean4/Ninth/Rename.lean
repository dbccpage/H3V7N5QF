import Ninth.Compare

/-!
# Changes commute with rewriting the terms (two relations, no names)

`rename9 π s` writes every term `x` of `s` as `π x`, in both relations.  It is
the eighth's `rename8` with the names left out: naming and then rewriting is
rewriting and then naming (`rename8_name`, definitionally), so the eighth's
commutation lemmas give the ninth's by forgetting the names (`rename9_addTerm`,
`rename9_addAssertion`, `rename9_remove`, `rename9_identify`).  A change after
rewriting is a change of the same kind (`Step9.rename`), a sequence stays a
sequence of the same length (`Reach9.rename`), the size is the same in every
writing (`size_rename9`), and the empty state is its own only writing
(`rename9_empty`).  Hence the fewest changes to a result — a state up to
rewriting — is the size of any of its writings
(`fewest_changes9_every_writing`).  With no names every rewriting counts, so
there is one reading of sameness; it acts on both relations at once.
-/

namespace Seed.Ninth

open Seed Seed.Fourth Seed.Fifth Seed.Sixth Seed.Seventh Seed.Eighth NDSt

variable (π : Equiv.Perm ℕ)

/-- Every term `x` written as `π x`, in both relations. -/
def rename9 (π : Equiv.Perm ℕ) (s : NDSt) : NDSt :=
  ⟨s.T.map π.toEmbedding, fun q p => s.M q (π.symm p.1, π.symm p.2)⟩

theorem rename8_name (s : NDSt) (c : ℕ) : rename8 π (s.name c) = (rename9 π s).name (π c) := rfl

theorem forget_rename8 (s : DSt) : (rename8 π s).forget = rename9 π s.forget := rfl

theorem proj_rename9 (s : NDSt) (q : Rel) : (rename9 π s).proj q = rename7 π (s.proj q) := rfl

theorem mem_rename9_T {s : NDSt} {x : ℕ} : π x ∈ (rename9 π s).T ↔ x ∈ s.T :=
  mem_rename8_T π (s := s.name 0)

theorem rename9_M (s : NDSt) (q : Rel) (x y : ℕ) : (rename9 π s).M q (π x, π y) = s.M q (x, y) :=
  rename8_M π (s.name 0) q x y

theorem rename9_addTerm (s : NDSt) (t : ℕ) : rename9 π (s.addTerm t) = (rename9 π s).addTerm (π t) :=
  congrArg DSt.forget (rename8_addTerm π (s.name 0) t)

theorem rename9_addAssertion (s : NDSt) (q : Rel) (x y : ℕ) :
    rename9 π (s.addAssertion q x y) = (rename9 π s).addAssertion q (π x) (π y) :=
  congrArg DSt.forget (rename8_addAssertion π (s.name 0) q x y)

theorem rename9_remove (s : NDSt) (q : Rel) (x y : ℕ) :
    rename9 π (s.remove q x y) = (rename9 π s).remove q (π x) (π y) :=
  congrArg DSt.forget (rename8_remove π (s.name 0) q x y)

theorem rename9_identify (s : NDSt) (u v : ℕ) :
    rename9 π (s.identify u v) = (rename9 π s).identify (π u) (π v) :=
  congrArg DSt.forget (rename8_identify π (s.name 0) u v)

theorem size_rename9 (s : NDSt) : (rename9 π s).size = s.size := size_rename8 π (s.name 0)

theorem wf_rename9 {s : NDSt} (hw : s.WF) : (rename9 π s).WF :=
  ⟨Seed.Seventh.wf_rename7 π hw.1, Seed.Seventh.wf_rename7 π hw.2⟩

/-- The empty state is its own only writing. -/
theorem rename9_empty : rename9 π empty9 = empty9 := by
  apply NDSt.ext
  · simp [rename9, empty9]
  · funext q p
    rfl

/-- A change of the ninth seed, after rewriting, is a change of the same kind. -/
theorem Step9.rename {s t : NDSt} (h : Step9 s t) : Step9 (rename9 π s) (rename9 π t) := by
  cases h with
  | addTerm t ht =>
    rw [rename9_addTerm]
    exact Step9.addTerm _ _ ((mem_rename9_T π).not.2 ht)
  | addAssertion q x y hx hy =>
    rw [rename9_addAssertion]
    exact Step9.addAssertion _ q _ _ ((mem_rename9_T π).2 hx) ((mem_rename9_T π).2 hy)
  | remove q x y hp =>
    rw [rename9_remove]
    exact Step9.remove _ q _ _ (by rw [rename9_M]; exact hp)
  | identify u v hu hv huv =>
    rw [rename9_identify]
    exact Step9.identify _ _ _ ((mem_rename9_T π).2 hu) ((mem_rename9_T π).2 hv) (π.injective.ne huv)

/-- A sequence of changes, after rewriting, is a sequence of the same length. -/
theorem Reach9.rename {s t : NDSt} {n : ℕ} (h : Reach9 s t n) :
    Reach9 (rename9 π s) (rename9 π t) n := by
  induction h with
  | refl => exact Reach9.refl _
  | step _ st ih => exact Reach9.step ih (st.rename π)

/-- **Fewest changes for every writing.**  Every writing of a well-formed state is reached from
the empty state (its own only writing) in exactly the state's size, and in no fewer changes. -/
theorem fewest_changes9_every_writing {g : NDSt} (hgw : g.WF) :
    Reach9 empty9 (rename9 π g) g.size ∧ ∀ n, Reach9 empty9 (rename9 π g) n → g.size ≤ n := by
  have := fewest_changes9 (wf_rename9 π hgw)
  rw [size_rename9] at this
  exact this

/-- Rewriting commutes with the exchange of the relations. -/
theorem rename9_swap (s : NDSt) : rename9 π s.swap = (rename9 π s).swap := rfl

end Seed.Ninth
