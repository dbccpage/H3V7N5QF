import Second.Carry

/-!
# Fewest changes under the second seed: the size difference

Derived here:
* one change raises `size = terms + assertions` by at most one
  (`Step3.size_le`), so a result reached in `n` changes has size at most
  `n + size(given)` (`fewest_changes3_lower_A`, `fewest_changes3_lower_B`);
* additions alone reach every legal state that contains a state
  (`reach3_by_additions`), in exactly the size difference
  (`additions_count`); so the fewest changes to a state written with `a = 0`,
  `b = 1` that contains what is given is exactly its size minus that of what
  is given (`fewest_changes3_A`, `fewest_changes3_B`);
* whatever is reached from what is given contains it (`reach3_givenA_contains`,
  `reach3_givenB_contains`); in particular the one-term state is unreachable,
  the beginning with `bra` never reaches the beginning without, and the first
  derivation's "destroyed givens" are always zero on a result
  (`lostA_eq_zero_of_reach3`, `costA_eq_size_of_reach3`).
-/

namespace Seed.Second

open Seed St

/-! ## Lower bound -/

theorem Step3.size_le {s t : St} (h : Step3 s t) : t.size ≤ s.size + 1 := by
  cases h with
  | addTerm t ht =>
    have := size_addTerm ht
    omega
  | addAssertion x y hx hy hxy hnew =>
    have := size_addAssertion hnew
    omega
  | identify u v hu hv huv h1 h2 =>
    have := size_identify (u := u) hv
    omega

theorem Reach3.size_le {s t : St} {n : ℕ} (h : Reach3 s t n) : t.size ≤ s.size + n := by
  induction h with
  | refl => omega
  | step _ st ih =>
    have := st.size_le
    omega

theorem size_givenA : givenA.size = 3 := by decide

theorem size_givenB : givenB.size = 4 := by decide

/-- **Lower bound, `bra` not asserted to begin with.** -/
theorem fewest_changes3_lower_A {t : St} {n : ℕ} (h : Reach3 givenA t n) : t.size ≤ n + 3 := by
  have := h.size_le
  rw [size_givenA] at this
  omega

/-- **Lower bound, `bra` asserted to begin with.** -/
theorem fewest_changes3_lower_B {t : St} {n : ℕ} (h : Reach3 givenB t n) : t.size ≤ n + 4 := by
  have := h.size_le
  rw [size_givenB] at this
  omega

/-! ## Upper bound: additions alone -/

/-- Adding the terms of `D`, one change each. -/
theorem reach3_addTerms (s : St) (D : Finset ℕ) (hD : Disjoint D s.T) :
    Reach3 s ⟨s.T ∪ D, s.A, s.a, s.b⟩ D.card := by
  revert hD
  refine Finset.induction_on D ?_ ?_
  · intro _
    simp only [Finset.union_empty, Finset.card_empty]
    exact Reach3.refl s
  · intro t D ht ih hD
    rw [Finset.disjoint_insert_left] at hD
    have r := ih hD.2
    have hnew : t ∉ s.T ∪ D := by
      simp only [Finset.mem_union, not_or]
      exact ⟨hD.1, ht⟩
    have st := Step3.addTerm ⟨s.T ∪ D, s.A, s.a, s.b⟩ t hnew
    rw [Finset.card_insert_of_notMem ht, Finset.union_insert]
    exact Reach3.step r st

/-- Adding the assertions of `E`, one change each. -/
theorem reach3_addAssertions (s : St) (E : Finset (ℕ × ℕ))
    (hE : ∀ p ∈ E, p.1 ∈ s.T ∧ p.2 ∈ s.T ∧ p.1 ≠ p.2) (hdis : Disjoint E s.A) :
    Reach3 s ⟨s.T, s.A ∪ E, s.a, s.b⟩ E.card := by
  revert hE hdis
  refine Finset.induction_on E ?_ ?_
  · intro _ _
    simp only [Finset.union_empty, Finset.card_empty]
    exact Reach3.refl s
  · rintro ⟨x, y⟩ E hp ih hE hdis
    rw [Finset.disjoint_insert_left] at hdis
    have r := ih (fun q hq => hE q (Finset.mem_insert_of_mem hq)) hdis.2
    obtain ⟨hx, hy, hxy⟩ := hE (x, y) (Finset.mem_insert_self _ _)
    have hnew : (x, y) ∉ s.A ∪ E := by
      simp only [Finset.mem_union, not_or]
      exact ⟨hdis.1, hp⟩
    have st := Step3.addAssertion ⟨s.T, s.A ∪ E, s.a, s.b⟩ x y hx hy hxy hnew
    rw [Finset.card_insert_of_notMem hp, Finset.union_insert]
    exact Reach3.step r st

/-- **Additions reach everything that contains the state.**  Add the missing terms,
then the missing assertions. -/
theorem reach3_by_additions (s g : St) (hg : g.Legal) (hgw : g.WF) (hT : s.T ⊆ g.T)
    (hA : s.A ⊆ g.A) (ha : g.a = s.a) (hb : g.b = s.b) :
    Reach3 s g ((g.T \ s.T).card + (g.A \ s.A).card) := by
  have r1 := reach3_addTerms s (g.T \ s.T) Finset.sdiff_disjoint
  have hTT : s.T ∪ g.T \ s.T = g.T := Finset.union_sdiff_of_subset hT
  have r2 := reach3_addAssertions ⟨s.T ∪ g.T \ s.T, s.A, s.a, s.b⟩ (g.A \ s.A)
    (by
      rintro ⟨x, y⟩ hp
      have hp' := (Finset.mem_sdiff.1 hp).1
      refine ⟨?_, ?_, ?_⟩
      · simpa only [hTT] using (hgw.1 _ hp').1
      · simpa only [hTT] using (hgw.1 _ hp').2
      · intro hxy
        have hxy' : x = y := hxy
        subst hxy'
        exact hg _ hp')
    Finset.sdiff_disjoint
  have e : (⟨s.T ∪ g.T \ s.T, s.A ∪ g.A \ s.A, s.a, s.b⟩ : St) = g := by
    apply St.ext
    · exact hTT
    · exact Finset.union_sdiff_of_subset hA
    · exact ha.symm
    · exact hb.symm
  have r := r1.trans r2
  rw [e] at r
  exact r

/-- The number of additions, in terms of sizes. -/
theorem additions_count (s g : St) (hT : s.T ⊆ g.T) (hA : s.A ⊆ g.A) :
    (g.T \ s.T).card + (g.A \ s.A).card + s.size = g.size := by
  have h1 := Finset.card_sdiff_add_card_eq_card hT
  have h2 := Finset.card_sdiff_add_card_eq_card hA
  simp only [St.size]
  omega

/-! ## From what is given -/

theorem givenA_A_subset {g : St} (hab : (0, 1) ∈ g.A) : givenA.A ⊆ g.A := by
  intro p hp
  simp only [givenA, Finset.mem_singleton] at hp
  subst hp
  exact hab

theorem givenB_A_subset {g : St} (hab : (0, 1) ∈ g.A) (hba : (1, 0) ∈ g.A) : givenB.A ⊆ g.A := by
  intro p hp
  simp only [givenB, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl
  · exact hab
  · exact hba

/-- **Upper bound, `bra` not asserted to begin with.** -/
theorem fewest_changes3_upper_A {g : St} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1)
    (hab : (0, 1) ∈ g.A) : ∃ n, Reach3 givenA g n ∧ n + 3 = g.size := by
  have hT : givenA.T ⊆ g.T := given_terms_subset hgw ha hb
  have hA := givenA_A_subset hab
  refine ⟨_, reach3_by_additions givenA g hg hgw hT hA ha hb, ?_⟩
  have c := additions_count givenA g hT hA
  rw [size_givenA] at c
  omega

/-- **Upper bound, `bra` asserted to begin with.** -/
theorem fewest_changes3_upper_B {g : St} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1)
    (hab : (0, 1) ∈ g.A) (hba : (1, 0) ∈ g.A) : ∃ n, Reach3 givenB g n ∧ n + 4 = g.size := by
  have hT : givenB.T ⊆ g.T := given_terms_subset hgw ha hb
  have hA := givenB_A_subset hab hba
  refine ⟨_, reach3_by_additions givenB g hg hgw hT hA ha hb, ?_⟩
  have c := additions_count givenB g hT hA
  rw [size_givenB] at c
  omega

/-- **Fewest changes, `bra` not asserted to begin with.**  A legal state written with
`a = 0`, `b = 1` in which `arb` is asserted is reached in exactly `size − 3` changes,
and in no fewer. -/
theorem fewest_changes3_A {g : St} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1)
    (hab : (0, 1) ∈ g.A) :
    (∃ n, Reach3 givenA g n ∧ n + 3 = g.size) ∧ ∀ n, Reach3 givenA g n → g.size ≤ n + 3 :=
  ⟨fewest_changes3_upper_A hg hgw ha hb hab, fun _ h => fewest_changes3_lower_A h⟩

/-- **Fewest changes, `bra` asserted to begin with.** -/
theorem fewest_changes3_B {g : St} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1)
    (hab : (0, 1) ∈ g.A) (hba : (1, 0) ∈ g.A) :
    (∃ n, Reach3 givenB g n ∧ n + 4 = g.size) ∧ ∀ n, Reach3 givenB g n → g.size ≤ n + 4 :=
  ⟨fewest_changes3_upper_B hg hgw ha hb hab hba, fun _ h => fewest_changes3_lower_B h⟩

/-! ## What is reached contains what is given -/

theorem givenA_arb : (givenA.a, givenA.b) ∈ givenA.A := by decide

theorem givenB_arb : (givenB.a, givenB.b) ∈ givenB.A := by decide

theorem givenB_bra : (givenB.b, givenB.a) ∈ givenB.A := by decide

/-- Every state reached from what is given (`bra` not asserted) is legal, well formed,
keeps `a` and `b` two terms, and asserts `arb`. -/
theorem reach3_givenA_contains {g : St} {n : ℕ} (h : Reach3 givenA g n) :
    g.Legal ∧ g.WF ∧ g.a ≠ g.b ∧ (g.a, g.b) ∈ g.A :=
  ⟨h.legal givenA_legal, h.wf givenA_wf, h.names_apart givenA_legal givenA_arb,
    h.arb_persists givenA_arb⟩

/-- With `bra` asserted to begin with, `bra` is asserted in every result too. -/
theorem reach3_givenB_contains {g : St} {n : ℕ} (h : Reach3 givenB g n) :
    g.Legal ∧ g.WF ∧ g.a ≠ g.b ∧ (g.a, g.b) ∈ g.A ∧ (g.b, g.a) ∈ g.A :=
  ⟨h.legal givenB_legal, h.wf givenB_wf, h.names_apart givenB_legal givenB_arb,
    h.arb_persists givenB_arb, h.bra_persists givenB_bra⟩

/-- Every result has at least two terms. -/
theorem reach3_givenA_two_terms {g : St} {n : ℕ} (h : Reach3 givenA g n) : 2 ≤ g.T.card :=
  h.two_terms givenA_legal givenA_wf givenA_arb

theorem reach3_givenB_two_terms {g : St} {n : ℕ} (h : Reach3 givenB g n) : 2 ≤ g.T.card :=
  h.two_terms givenB_legal givenB_wf givenB_arb

/-- The one-term state is not a result. -/
theorem oneTerm_unreachable_A (n : ℕ) : ¬ Reach3 givenA oneTerm n :=
  fun h => (reach3_givenA_contains h).2.2.1 rfl

theorem oneTerm_unreachable_B (n : ℕ) : ¬ Reach3 givenB oneTerm n :=
  fun h => (reach3_givenB_contains h).2.2.1 rfl

/-- The beginning without `bra` reaches the beginning with it in one change. -/
theorem givenA_to_givenB3 : Reach3 givenA givenB 1 := by
  have st : Step3 givenA (givenA.addAssertion 1 0) :=
    Step3.addAssertion givenA 1 0 (by simp [givenA]) (by simp [givenA]) (by omega)
      (by simp [givenA])
  have e : givenA.addAssertion 1 0 = givenB := by
    simp only [givenA, givenB, St.addAssertion]
    congr 1
    exact Finset.pair_comm _ _
  exact e ▸ Reach3.step (Reach3.refl givenA) st

/-- The beginning with `bra` never reaches the beginning without it. -/
theorem givenB_never_givenA (n : ℕ) : ¬ Reach3 givenB givenA n := by
  intro h
  have := h.bra_persists givenB_bra
  exact absurd this (by decide)

/-- On a result the first derivation's "destroyed givens" are zero, so its cost formula
collapses to the size. -/
theorem lostA_eq_zero_of_reach3 {g : St} {n : ℕ} (h : Reach3 givenA g n) : lostA g = 0 := by
  obtain ⟨_, _, hne, hab⟩ := reach3_givenA_contains h
  rw [lostA_of_ne hne, miss_of_mem hab]

theorem lostB_eq_zero_of_reach3 {g : St} {n : ℕ} (h : Reach3 givenB g n) : lostB g = 0 := by
  obtain ⟨_, _, hne, hab, hba⟩ := reach3_givenB_contains h
  rw [lostB_of_ne hne, miss_of_mem hab, miss_of_mem hba]

theorem costA_eq_size_of_reach3 {g : St} {n : ℕ} (h : Reach3 givenA g n) : costA g = g.size := by
  simp [costA, lostA_eq_zero_of_reach3 h]

theorem costB_eq_size_of_reach3 {g : St} {n : ℕ} (h : Reach3 givenB g n) : costB g = g.size := by
  simp [costB, lostB_eq_zero_of_reach3 h]

end Seed.Second
