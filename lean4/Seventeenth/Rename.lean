import Seventeenth.Step

/-!
# Changes commute with a one-to-one rewriting of the terms

`rename π s` writes every term `x` as `π x`. For an injective `π`, every
`Step17` becomes a `Step17` of the same kind, and so does every sequence.
-/

namespace Seed.Seventeenth

open Seed St

variable {π : ℕ → ℕ}

/-- The state with every term `x` written `π x`. -/
def rename (π : ℕ → ℕ) (s : St) : St :=
  ⟨s.T.image π, s.A.image (Prod.map π π), π s.a, π s.b⟩

theorem rename_addTerm (s : St) (t : ℕ) :
    rename π (s.addTerm t) = (rename π s).addTerm (π t) := by
  simp [rename, St.addTerm, Finset.image_insert]

theorem rename_addAssertion (s : St) (x y : ℕ) :
    rename π (s.addAssertion x y) = (rename π s).addAssertion (π x) (π y) := by
  simp [rename, St.addAssertion, Finset.image_insert, Prod.map]

theorem rename_remove (hπ : Function.Injective π) (s : St) (p : ℕ × ℕ) :
    rename π (s.remove p) = (rename π s).remove (π p.1, π p.2) := by
  apply St.ext
  · simp [rename, St.remove]
  · simp only [rename, St.remove]
    rw [Finset.image_erase (hπ.prodMap hπ)]
    rfl
  · rfl
  · rfl

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

def Step17.rename {s t : St} (h : Step17 s t) (hπ : Function.Injective π) :
    Step17 (Seed.Seventeenth.rename π s) (Seed.Seventeenth.rename π t) := by
  cases h with
  | addTerm t ht =>
    rw [rename_addTerm]
    exact Step17.addTerm _ _ ((mem_rename_T hπ).not.2 ht)
  | addAssertion x y hx hy hnew =>
    rw [rename_addAssertion]
    exact Step17.addAssertion _ _ _ ((mem_rename_T hπ).2 hx) ((mem_rename_T hπ).2 hy)
      ((mem_rename_A hπ).not.2 hnew)
  | remove p hp =>
    rw [rename_remove hπ]
    exact Step17.remove _ _ ((mem_rename_A (x := p.1) (y := p.2) hπ).2 hp)
  | identify u v hu hv huv =>
    rw [rename_identify hπ]
    exact Step17.identify _ _ _ ((mem_rename_T hπ).2 hu) ((mem_rename_T hπ).2 hv) (hπ.ne huv)

theorem Reach17.rename (hπ : Function.Injective π) {s t : St} {n : ℕ} (h : Reach17 s t n) :
    Reach17 (rename π s) (rename π t) n := by
  induction h with
  | refl => exact Reach17.refl _
  | step r st hu ih =>
    rename_i mid _ _
    cases st with
    | addTerm term ht =>
      rw [rename_addTerm]
      exact Reach17.step ih (Step17.addTerm _ _ ((mem_rename_T hπ).not.2 ht))
        (by simp [Step17.unobstructed, Step17.obstructedM1])
    | addAssertion x y hx hy hnew =>
      have hxy : x ≠ y := by
        intro heq
        exact hu (by simpa [Step17.obstructedM1] using heq)
      rw [rename_addAssertion]
      exact Reach17.step ih
        (Step17.addAssertion _ _ _ ((mem_rename_T hπ).2 hx) ((mem_rename_T hπ).2 hy)
          ((mem_rename_A hπ).not.2 hnew))
        (by simpa [Step17.unobstructed, Step17.obstructedM1] using hπ.ne hxy)
    | remove p hp =>
      rw [rename_remove hπ]
      exact Reach17.step ih
        (Step17.remove _ _ ((mem_rename_A (x := p.1) (y := p.2) hπ).2 hp))
        (by simp [Step17.unobstructed, Step17.obstructedM1])
    | identify u v hu' hv huv =>
      have hnot : ¬ ((u, v) ∈ mid.A ∨ (v, u) ∈ mid.A) := by
        simpa [Step17.unobstructed, Step17.obstructedM1] using hu
      rw [rename_identify hπ]
      refine Reach17.step ih
        (Step17.identify _ _ _ ((mem_rename_T hπ).2 hu') ((mem_rename_T hπ).2 hv) (hπ.ne huv)) ?_
      intro hmem
      apply hnot
      rcases hmem with hmem | hmem
      · exact Or.inl ((mem_rename_A hπ).1 hmem)
      · exact Or.inr ((mem_rename_A hπ).1 hmem)

theorem ReachAll.rename (hπ : Function.Injective π) {s t : St} {n : ℕ} (h : ReachAll s t n) :
    ReachAll (rename π s) (rename π t) n := by
  induction h with
  | refl => exact ReachAll.refl _
  | step r st ih => exact ReachAll.step ih (st.rename hπ)

theorem loopFree_rename (hπ : Function.Injective π) {s : St} (hs : LoopFree s) :
    LoopFree (rename π s) := by
  intro x hx
  obtain ⟨⟨y, z⟩, hp, he⟩ := Finset.mem_image.1 hx
  simp only [Prod.map, Prod.mk.injEq] at he
  obtain rfl : y = z := hπ (he.1.trans he.2.symm)
  exact hs y hp

end Seed.Seventeenth
