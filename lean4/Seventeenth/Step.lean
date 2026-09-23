import Seventeenth.State

/-!
# Changes with no ban on `xrx`

`Step17` is the base `Step` with the side-conditions that enforced the ban
dropped: adding `xrx` is a change, and identifying two terms is a change
whether or not something is asserted between them. `obstructedM1` is the
base obstruction (what would become `xrx`). `obstructedM2` is "the outcome
asserts some `xrx`". On a loop-free state they agree; on `loopyWitness`
they do not.
-/

namespace Seed.Seventeenth

open Seed St

/-- One change. Adding `xrx`, and identifying two related terms, are included.
The new term is new, the added assertion is new and between terms that are
there, the removed assertion is asserted, and the identified terms are two
terms that are there.

A `Type`, not a `Prop`: the obstruction predicate distinguishes constructors,
and a `Prop` with several constructors cannot be eliminated into `Prop`. -/
inductive Step17 : St → St → Type
  | addTerm (s : St) (t : ℕ) (ht : t ∉ s.T) : Step17 s (s.addTerm t)
  | addAssertion (s : St) (x y : ℕ) (hx : x ∈ s.T) (hy : y ∈ s.T)
      (hnew : (x, y) ∉ s.A) : Step17 s (s.addAssertion x y)
  | remove (s : St) (p : ℕ × ℕ) (hp : p ∈ s.A) : Step17 s (s.remove p)
  | identify (s : St) (u v : ℕ) (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v) :
      Step17 s (s.identify u v)

/-- M1: the assertions that would become some `xrx`. An existing `xrx` does
not obstruct an unrelated change. The target state is matched as a pattern,
not as a fixed index: the match with a fixed target did not elaborate
(`paper/seventeenth/change_log.md`, entry 6). -/
def Step17.obstructedM1 {s : St} : {s' : St} → Step17 s s' → Prop
  | _, addTerm _ _ _ => False
  | _, addAssertion _ x y _ _ _ => x = y
  | _, remove _ _ _ => False
  | _, identify s u v _ _ _ => (u, v) ∈ s.A ∨ (v, u) ∈ s.A

/-- M2: the outcome asserts some `xrx`. -/
def Step17.obstructedM2 {s s' : St} (_h : Step17 s s') : Prop := HasXrx s'

/-- The change does not make an `xrx` in the sense of M1. -/
def Step17.unobstructed {s s' : St} (h : Step17 s s') : Prop := ¬ h.obstructedM1

/-- Adding `xrx` makes an `xrx`, with no hypothesis that the state was loop-free. -/
theorem adding_xrx_obstructed (s : St) (x : ℕ) : HasXrx (s.addAssertion x x) :=
  ⟨x, by simp [St.addAssertion]⟩

theorem adding_xrx_step_obstructed {s : St} {x : ℕ} (hx : x ∈ s.T) (hnew : (x, x) ∉ s.A) :
    (Step17.addAssertion s x x hx hx hnew).obstructedM1 := rfl

/-- On a loop-free state, M1 and M2 name the same changes. -/
theorem m1_iff_m2_of_loopFree {s s' : St} (h : Step17 s s') (hs : LoopFree s) :
    h.obstructedM1 ↔ h.obstructedM2 := by
  cases h with
  | addTerm t ht =>
    constructor
    · intro hfalse
      cases hfalse
    · intro hx
      exact (hasXrx_iff_not_legal _).1 hx (addTerm_legal hs t)
  | addAssertion x y hx hy hnew =>
    constructor
    · intro hxy
      refine ⟨x, ?_⟩
      simp only [St.addAssertion, Finset.mem_insert]
      exact Or.inl (Prod.ext rfl hxy)
    · intro hx
      by_contra hxy
      exact (hasXrx_iff_not_legal _).1 hx ((addAssertion_legal_iff hs x y).2 hxy)
  | remove p hp =>
    constructor
    · intro hfalse
      exact hfalse.elim
    · intro hx
      exact (hasXrx_iff_not_legal _).1 hx (remove_legal hs p)
  | identify u v hu hv huv =>
    simp only [Step17.obstructedM1, Step17.obstructedM2, hasXrx_iff_not_legal]
    constructor
    · rintro (huvA | hvuA) hlegal
      · exact ((identify_legal_iff hs u v).1 hlegal).1 huvA
      · exact ((identify_legal_iff hs u v).1 hlegal).2 hvuA
    · intro hnot
      by_contra hneither
      exact hnot ((identify_legal_iff hs u v).2
        ⟨fun huvA => hneither (Or.inl huvA), fun hvuA => hneither (Or.inr hvuA)⟩)

theorem Step17.loopFree_out {s s' : St} (h : Step17 s s') (hs : LoopFree s)
    (hu : h.unobstructed) : LoopFree s' := by
  have hm2 : ¬ h.obstructedM2 := (m1_iff_m2_of_loopFree h hs).not.mp hu
  rw [Step17.obstructedM2, hasXrx_iff_not_loopFree] at hm2
  exact Classical.not_not.mp hm2

theorem Step17.no_xrx_of_unobstructed {s s' : St} (h : Step17 s s') (hs : LoopFree s)
    (hu : h.unobstructed) : ¬ HasXrx s' :=
  fun hx => (hasXrx_iff_not_loopFree s').mp hx (h.loopFree_out hs hu)

theorem Step17.wf {s s' : St} (h : Step17 s s') (hs : s.WF) : s'.WF := by
  obtain ⟨hA, ha, hb⟩ := hs
  cases h with
  | addTerm t ht =>
    exact ⟨fun p hp => ⟨Finset.mem_insert_of_mem (hA p hp).1,
        Finset.mem_insert_of_mem (hA p hp).2⟩,
      Finset.mem_insert_of_mem ha, Finset.mem_insert_of_mem hb⟩
  | addAssertion x y hx hy hnew =>
    refine ⟨fun p hp => ?_, ha, hb⟩
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact ⟨hx, hy⟩
    · exact hA p hp
  | remove p hp => exact ⟨fun q hq => hA q (Finset.mem_of_mem_erase hq), ha, hb⟩
  | identify u v hu hv huv =>
    refine ⟨fun p hp => ?_, merge_mem_erase hu huv ha, merge_mem_erase hu huv hb⟩
    obtain ⟨q, hq, rfl⟩ := mem_identify.1 hp
    exact ⟨merge_mem_erase hu huv (hA q hq).1, merge_mem_erase hu huv (hA q hq).2⟩

theorem Step17.nonempty {s s' : St} (h : Step17 s s') (hs : s.T.Nonempty) : s'.T.Nonempty := by
  cases h with
  | addTerm t ht => exact ⟨t, Finset.mem_insert_self t s.T⟩
  | addAssertion x y hx hy hnew => exact hs
  | remove p hp => exact hs
  | identify u v hu hv huv => exact ⟨u, Finset.mem_erase.2 ⟨huv, hu⟩⟩

theorem Step17.names_stay_merged {s s' : St} (h : Step17 s s') (hab : s.a = s.b) :
    s'.a = s'.b := by
  cases h with
  | addTerm t ht => exact hab
  | addAssertion x y hx hy hnew => exact hab
  | remove p hp => exact hab
  | identify u v hu hv huv => simp [St.identify, hab]

/-- Identifying `1` with `2` in `loopyWitness` is not obstructed under M1. -/
theorem loopy_m1_allows :
    ¬ (Step17.identify loopyWitness 1 2
        (by unfold loopyWitness; decide)
        (by unfold loopyWitness; decide)
        (by decide)).obstructedM1 := by
  intro h
  simp [Step17.obstructedM1, loopyWitness] at h

/-- The same identification is obstructed under M2: `0r0` is still asserted. -/
theorem loopy_m2_obstructs :
    (Step17.identify loopyWitness 1 2
        (by unfold loopyWitness; decide)
        (by unfold loopyWitness; decide)
        (by decide)).obstructedM2 := by
  refine ⟨0, ?_⟩
  refine mem_identify.2 ⟨(0, 0), by simp [loopyWitness], ?_⟩
  simp [merge]

/-- A sequence of changes that do not make an `xrx`. -/
inductive Reach17 : St → St → ℕ → Prop
  | refl (s : St) : Reach17 s s 0
  | step {s t u : St} {n : ℕ} : Reach17 s t n → (st : Step17 t u) → st.unobstructed →
      Reach17 s u (n + 1)

/-- A sequence of changes, obstructed or not. -/
inductive ReachAll : St → St → ℕ → Prop
  | refl (s : St) : ReachAll s s 0
  | step {s t u : St} {n : ℕ} : ReachAll s t n → Step17 t u → ReachAll s u (n + 1)

theorem Reach17.loopFree {s t : St} {n : ℕ} (h : Reach17 s t n) (hs : LoopFree s) :
    LoopFree t := by
  induction h with
  | refl => exact hs
  | step _ st hu ih => exact st.loopFree_out ih hu

theorem Reach17.wf {s t : St} {n : ℕ} (h : Reach17 s t n) (hs : s.WF) : t.WF := by
  induction h with
  | refl => exact hs
  | step _ st _ ih => exact st.wf ih

theorem ReachAll.wf {s t : St} {n : ℕ} (h : ReachAll s t n) (hs : s.WF) : t.WF := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.wf ih

theorem Reach17.nonempty {s t : St} {n : ℕ} (h : Reach17 s t n) (hs : s.T.Nonempty) :
    t.T.Nonempty := by
  induction h with
  | refl => exact hs
  | step _ st _ ih => exact st.nonempty ih

theorem ReachAll.nonempty {s t : St} {n : ℕ} (h : ReachAll s t n) (hs : s.T.Nonempty) :
    t.T.Nonempty := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.nonempty ih

theorem Reach17.names_stay_merged {s t : St} {n : ℕ} (h : Reach17 s t n) (hab : s.a = s.b) :
    t.a = t.b := by
  induction h with
  | refl => exact hab
  | step _ st _ ih => exact st.names_stay_merged ih

theorem ReachAll.names_stay_merged {s t : St} {n : ℕ} (h : ReachAll s t n) (hab : s.a = s.b) :
    t.a = t.b := by
  induction h with
  | refl => exact hab
  | step _ st ih => exact st.names_stay_merged ih

end Seed.Seventeenth
