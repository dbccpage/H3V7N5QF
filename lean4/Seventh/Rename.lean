import Seventh.Compare

/-!
# Changes commute with rewriting the terms (no names)

`rename7 π s` writes every term `x` of `s` as `π x`.  It is the fourth's `rename4`
with the names left out: naming and then rewriting is rewriting and then naming
(`rename4_name`, definitionally), so the fourth's and fifth's commutation lemmas
give the seventh's by forgetting the names (`rename7_addTerm`, `rename7_addAssertion`,
`rename7_remove`, `rename7_identify`).  A change after rewriting is a change of the
same kind (`Step7.rename`), a sequence stays a sequence of the same length
(`Reach7.rename`), the size is the same in every writing (`size_rename7`), and the
empty state is its own only writing (`rename7_empty`).  Hence the fewest changes
to a result — a state up to rewriting — is the size of any of its writings
(`fewest_changes7_every_writing`).
-/

namespace Seed.Seventh

open Seed Seed.Fourth Seed.Fifth Seed.Sixth NSt

variable (π : Equiv.Perm ℕ)

/-- Every term `x` written as `π x`. -/
def rename7 (π : Equiv.Perm ℕ) (s : NSt) : NSt :=
  ⟨s.T.map π.toEmbedding, fun p => s.M (π.symm p.1, π.symm p.2)⟩

theorem rename4_name (s : NSt) (c : ℕ) : rename4 π (s.name c) = (rename7 π s).name (π c) := rfl

theorem forget_rename4 (s : MSt) : (rename4 π s).forget = rename7 π s.forget := rfl

theorem mem_rename7_T {s : NSt} {x : ℕ} : π x ∈ (rename7 π s).T ↔ x ∈ s.T :=
  mem_rename4_T π (s := s.name 0)

theorem rename7_M (s : NSt) (x y : ℕ) : (rename7 π s).M (π x, π y) = s.M (x, y) :=
  rename4_M π (s.name 0) x y

theorem rename7_addTerm (s : NSt) (t : ℕ) : rename7 π (s.addTerm t) = (rename7 π s).addTerm (π t) :=
  congrArg MSt.forget (rename4_addTerm π (s.name 0) t)

theorem rename7_addAssertion (s : NSt) (x y : ℕ) :
    rename7 π (s.addAssertion x y) = (rename7 π s).addAssertion (π x) (π y) :=
  congrArg MSt.forget (rename4_addAssertion π (s.name 0) x y)

theorem rename7_remove (s : NSt) (x y : ℕ) :
    rename7 π (s.remove x y) = (rename7 π s).remove (π x) (π y) :=
  congrArg MSt.forget (rename4_remove π (s.name 0) x y)

theorem rename7_identify (s : NSt) (u v : ℕ) :
    rename7 π (s.identify u v) = (rename7 π s).identify (π u) (π v) :=
  congrArg MSt.forget (rename4_identify π (s.name 0) u v)

theorem size_rename7 (s : NSt) : (rename7 π s).size = s.size := size_rename4 π (s.name 0)

theorem wf_rename7 {s : NSt} (hw : s.WF) : (rename7 π s).WF := by
  intro p hp
  obtain ⟨h1, h2⟩ := hw _ hp
  constructor
  · have := (mem_rename7_T π).2 h1
    rwa [Equiv.apply_symm_apply] at this
  · have := (mem_rename7_T π).2 h2
    rwa [Equiv.apply_symm_apply] at this

/-- The empty state is its own only writing. -/
theorem rename7_empty : rename7 π empty = empty := by
  apply NSt.ext
  · simp [rename7, empty]
  · funext p
    rfl

/-- A change of the seventh seed, after rewriting, is a change of the same kind. -/
theorem Step7.rename {s t : NSt} (h : Step7 s t) : Step7 (rename7 π s) (rename7 π t) := by
  cases h with
  | addTerm t ht =>
    rw [rename7_addTerm]
    exact Step7.addTerm _ _ ((mem_rename7_T π).not.2 ht)
  | addAssertion x y hx hy =>
    rw [rename7_addAssertion]
    exact Step7.addAssertion _ _ _ ((mem_rename7_T π).2 hx) ((mem_rename7_T π).2 hy)
  | remove x y hp =>
    rw [rename7_remove]
    exact Step7.remove _ _ _ (by rw [rename7_M]; exact hp)
  | identify u v hu hv huv =>
    rw [rename7_identify]
    exact Step7.identify _ _ _ ((mem_rename7_T π).2 hu) ((mem_rename7_T π).2 hv) (π.injective.ne huv)

/-- A sequence of changes, after rewriting, is a sequence of the same length. -/
theorem Reach7.rename {s t : NSt} {n : ℕ} (h : Reach7 s t n) :
    Reach7 (rename7 π s) (rename7 π t) n := by
  induction h with
  | refl => exact Reach7.refl _
  | step _ st ih => exact Reach7.step ih (st.rename π)

/-- **Fewest changes for every writing.**  Every writing of a well-formed state is reached from
the empty state (its own only writing) in exactly the state's size, and in no fewer changes. -/
theorem fewest_changes7_every_writing {g : NSt} (hgw : g.WF) :
    Reach7 empty (rename7 π g) g.size ∧ ∀ n, Reach7 empty (rename7 π g) n → g.size ≤ n := by
  have := fewest_changes7 (wf_rename7 π hgw)
  rw [size_rename7] at this
  exact this

end Seed.Seventh
