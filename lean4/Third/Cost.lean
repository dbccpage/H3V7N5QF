import Third.Contain

/-!
# Every sequence has the same length: the size difference

Derived here:
* one change raises `size = terms + assertions` by exactly one (`Step2.size_eq`),
  so a sequence of `n` changes raises it by exactly `n` (`Reach2.size_eq`), and
  any two sequences between the same two states have the same length
  (`Reach2.length_unique`);
* additions reach every legal state that contains a state
  (`reach2_by_additions`), in exactly the size difference (second derivation's
  `additions_count`, cited); so a state written with `a = 0`, `b = 1` that
  contains what is given is reached in exactly its size minus that of what is
  given, by every sequence (`fewest_changes2_A`, `fewest_changes2_B`);
* a state is reachable from a state exactly when it contains it (`reach2_iff`);
* reachability is one-way: two states reachable from each other are reached in
  zero changes and are the same state (`Reach2.antisymm`); a state once left is
  never returned to (`Reach2.no_return`);
* whatever is reached from what is given contains it (`reach2_givenA_contains`,
  `reach2_givenB_contains`), the one-term state is unreachable, the beginning
  with `bra` never reaches the beginning without, and the first derivation's
  "destroyed givens" are zero on every result (all through the embedding).
-/

namespace Seed.Third

open Seed Seed.Second St

/-! ## Size rises by exactly one -/

theorem Step2.size_eq {s t : St} (h : Step2 s t) : t.size = s.size + 1 := by
  cases h with
  | addTerm t ht => exact size_addTerm ht
  | addAssertion x y hx hy hxy hnew => exact size_addAssertion hnew

theorem Reach2.size_eq {s t : St} {n : ℕ} (h : Reach2 s t n) : t.size = s.size + n := by
  induction h with
  | refl => omega
  | step _ st ih =>
    have := st.size_eq
    omega

/-- Any two sequences of changes between the same two states have the same length. -/
theorem Reach2.length_unique {s t : St} {n m : ℕ} (h1 : Reach2 s t n) (h2 : Reach2 s t m) :
    n = m := by
  have e1 := h1.size_eq
  have e2 := h2.size_eq
  omega

/-- Reachability is one-way: reached both ways means reached in zero changes, and
the two states are the same. -/
theorem Reach2.antisymm {s t : St} {n m : ℕ} (h1 : Reach2 s t n) (h2 : Reach2 t s m) :
    n = 0 ∧ m = 0 ∧ s = t := by
  have e1 := h1.size_eq
  have e2 := h2.size_eq
  have hn : n = 0 := by omega
  have hm : m = 0 := by omega
  subst hn
  exact ⟨rfl, hm, h1.eq_of_zero⟩

/-- A state once left is never returned to. -/
theorem Reach2.no_return {s t : St} {n m : ℕ} (h1 : Reach2 s t n) (hn : 0 < n)
    (h2 : Reach2 t s m) : False := by
  have := (h1.antisymm h2).1
  omega

/-- **Lower bound, `bra` not asserted to begin with**: exact. -/
theorem fewest_changes2_lower_A {t : St} {n : ℕ} (h : Reach2 givenA t n) : t.size = n + 3 := by
  have := h.size_eq
  rw [size_givenA] at this
  omega

/-- **Lower bound, `bra` asserted to begin with**: exact. -/
theorem fewest_changes2_lower_B {t : St} {n : ℕ} (h : Reach2 givenB t n) : t.size = n + 4 := by
  have := h.size_eq
  rw [size_givenB] at this
  omega

/-! ## Upper bound: additions reach everything that contains the state -/

/-- Adding the terms of `D`, one change each. -/
theorem reach2_addTerms (s : St) (D : Finset ℕ) (hD : Disjoint D s.T) :
    Reach2 s ⟨s.T ∪ D, s.A, s.a, s.b⟩ D.card := by
  revert hD
  refine Finset.induction_on D ?_ ?_
  · intro _
    simp only [Finset.union_empty, Finset.card_empty]
    exact Reach2.refl s
  · intro t D ht ih hD
    rw [Finset.disjoint_insert_left] at hD
    have r := ih hD.2
    have hnew : t ∉ s.T ∪ D := by
      simp only [Finset.mem_union, not_or]
      exact ⟨hD.1, ht⟩
    have st := Step2.addTerm ⟨s.T ∪ D, s.A, s.a, s.b⟩ t hnew
    rw [Finset.card_insert_of_notMem ht, Finset.union_insert]
    exact Reach2.step r st

/-- Adding the assertions of `E`, one change each. -/
theorem reach2_addAssertions (s : St) (E : Finset (ℕ × ℕ))
    (hE : ∀ p ∈ E, p.1 ∈ s.T ∧ p.2 ∈ s.T ∧ p.1 ≠ p.2) (hdis : Disjoint E s.A) :
    Reach2 s ⟨s.T, s.A ∪ E, s.a, s.b⟩ E.card := by
  revert hE hdis
  refine Finset.induction_on E ?_ ?_
  · intro _ _
    simp only [Finset.union_empty, Finset.card_empty]
    exact Reach2.refl s
  · rintro ⟨x, y⟩ E hp ih hE hdis
    rw [Finset.disjoint_insert_left] at hdis
    have r := ih (fun q hq => hE q (Finset.mem_insert_of_mem hq)) hdis.2
    obtain ⟨hx, hy, hxy⟩ := hE (x, y) (Finset.mem_insert_self _ _)
    have hnew : (x, y) ∉ s.A ∪ E := by
      simp only [Finset.mem_union, not_or]
      exact ⟨hdis.1, hp⟩
    have st := Step2.addAssertion ⟨s.T, s.A ∪ E, s.a, s.b⟩ x y hx hy hxy hnew
    rw [Finset.card_insert_of_notMem hp, Finset.union_insert]
    exact Reach2.step r st

/-- **Additions reach everything that contains the state.**  Add the missing terms,
then the missing assertions (the second derivation's path, re-proved as changes of
this seed). -/
theorem reach2_by_additions (s g : St) (hg : g.Legal) (hgw : g.WF) (hT : s.T ⊆ g.T)
    (hA : s.A ⊆ g.A) (ha : g.a = s.a) (hb : g.b = s.b) :
    Reach2 s g ((g.T \ s.T).card + (g.A \ s.A).card) := by
  have r1 := reach2_addTerms s (g.T \ s.T) Finset.sdiff_disjoint
  have hTT : s.T ∪ g.T \ s.T = g.T := Finset.union_sdiff_of_subset hT
  have r2 := reach2_addAssertions ⟨s.T ∪ g.T \ s.T, s.A, s.a, s.b⟩ (g.A \ s.A)
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

/-- A legal, well-formed state that contains `s` is reached from `s`, in exactly the
size difference. -/
theorem reach2_of_contains {s g : St} (hg : g.Legal) (hgw : g.WF) (h : Contains s g) :
    ∃ n, Reach2 s g n ∧ n + s.size = g.size :=
  ⟨_, reach2_by_additions s g hg hgw h.terms h.asserted h.name_a h.name_b,
    additions_count s g h.terms h.asserted⟩

/-- **Reachability is containment.**  A legal, well-formed state is reached from `s`
exactly when it contains `s`. -/
theorem reach2_iff {s g : St} (hg : g.Legal) (hgw : g.WF) :
    (∃ n, Reach2 s g n) ↔ Contains s g :=
  ⟨fun ⟨_, h⟩ => h.contains, fun h => let ⟨n, hn, _⟩ := reach2_of_contains hg hgw h; ⟨n, hn⟩⟩

/-! ## From what is given -/

/-- **Upper bound, `bra` not asserted to begin with.** -/
theorem fewest_changes2_upper_A {g : St} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1)
    (hab : (0, 1) ∈ g.A) : ∃ n, Reach2 givenA g n ∧ n + 3 = g.size := by
  have hT : givenA.T ⊆ g.T := given_terms_subset hgw ha hb
  have hA := givenA_A_subset hab
  refine ⟨_, reach2_by_additions givenA g hg hgw hT hA ha hb, ?_⟩
  have c := additions_count givenA g hT hA
  rw [size_givenA] at c
  omega

/-- **Upper bound, `bra` asserted to begin with.** -/
theorem fewest_changes2_upper_B {g : St} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1)
    (hab : (0, 1) ∈ g.A) (hba : (1, 0) ∈ g.A) : ∃ n, Reach2 givenB g n ∧ n + 4 = g.size := by
  have hT : givenB.T ⊆ g.T := given_terms_subset hgw ha hb
  have hA := givenB_A_subset hab hba
  refine ⟨_, reach2_by_additions givenB g hg hgw hT hA ha hb, ?_⟩
  have c := additions_count givenB g hT hA
  rw [size_givenB] at c
  omega

/-- **Fewest changes, `bra` not asserted to begin with.**  A legal state written with
`a = 0`, `b = 1` in which `arb` is asserted is reached in exactly `size − 3` changes,
and every sequence reaching it has that length. -/
theorem fewest_changes2_A {g : St} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1)
    (hab : (0, 1) ∈ g.A) :
    (∃ n, Reach2 givenA g n ∧ n + 3 = g.size) ∧ ∀ n, Reach2 givenA g n → n + 3 = g.size :=
  ⟨fewest_changes2_upper_A hg hgw ha hb hab, fun _ h => (fewest_changes2_lower_A h).symm⟩

/-- **Fewest changes, `bra` asserted to begin with.** -/
theorem fewest_changes2_B {g : St} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1)
    (hab : (0, 1) ∈ g.A) (hba : (1, 0) ∈ g.A) :
    (∃ n, Reach2 givenB g n ∧ n + 4 = g.size) ∧ ∀ n, Reach2 givenB g n → n + 4 = g.size :=
  ⟨fewest_changes2_upper_B hg hgw ha hb hab hba, fun _ h => (fewest_changes2_lower_B h).symm⟩

/-! ## What is reached contains what is given (through the embedding) -/

/-- Every state reached from what is given (`bra` not asserted) is legal, well formed,
keeps `a` and `b` two terms, and asserts `arb` (second derivation's
`reach3_givenA_contains`, through the embedding). -/
theorem reach2_givenA_contains {g : St} {n : ℕ} (h : Reach2 givenA g n) :
    g.Legal ∧ g.WF ∧ g.a ≠ g.b ∧ (g.a, g.b) ∈ g.A :=
  reach3_givenA_contains h.toReach3

/-- With `bra` asserted to begin with, `bra` is asserted in every result too. -/
theorem reach2_givenB_contains {g : St} {n : ℕ} (h : Reach2 givenB g n) :
    g.Legal ∧ g.WF ∧ g.a ≠ g.b ∧ (g.a, g.b) ∈ g.A ∧ (g.b, g.a) ∈ g.A :=
  reach3_givenB_contains h.toReach3

/-- Every result has at least two terms. -/
theorem reach2_givenA_two_terms {g : St} {n : ℕ} (h : Reach2 givenA g n) : 2 ≤ g.T.card :=
  reach3_givenA_two_terms h.toReach3

theorem reach2_givenB_two_terms {g : St} {n : ℕ} (h : Reach2 givenB g n) : 2 ≤ g.T.card :=
  reach3_givenB_two_terms h.toReach3

/-- The one-term state is not a result. -/
theorem oneTerm_unreachable2_A (n : ℕ) : ¬ Reach2 givenA oneTerm n :=
  fun h => oneTerm_unreachable_A n h.toReach3

theorem oneTerm_unreachable2_B (n : ℕ) : ¬ Reach2 givenB oneTerm n :=
  fun h => oneTerm_unreachable_B n h.toReach3

/-- The beginning without `bra` reaches the beginning with it in one change (the second
derivation's `givenA_to_givenB3`, re-proved as a change of this seed). -/
theorem givenA_to_givenB2 : Reach2 givenA givenB 1 := by
  have st : Step2 givenA (givenA.addAssertion 1 0) :=
    Step2.addAssertion givenA 1 0 (by simp [givenA]) (by simp [givenA]) (by omega)
      (by simp [givenA])
  have e : givenA.addAssertion 1 0 = givenB := by
    simp only [givenA, givenB, St.addAssertion]
    congr 1
    exact Finset.pair_comm _ _
  exact e ▸ Reach2.step (Reach2.refl givenA) st

/-- The beginning with `bra` never reaches the beginning without it. -/
theorem givenB_never_givenA2 (n : ℕ) : ¬ Reach2 givenB givenA n :=
  fun h => givenB_never_givenA n h.toReach3

/-- On a result the first derivation's "destroyed givens" are zero, so its cost
formula collapses to the size (second derivation, through the embedding). -/
theorem lostA_eq_zero_of_reach2 {g : St} {n : ℕ} (h : Reach2 givenA g n) : lostA g = 0 :=
  lostA_eq_zero_of_reach3 h.toReach3

theorem lostB_eq_zero_of_reach2 {g : St} {n : ℕ} (h : Reach2 givenB g n) : lostB g = 0 :=
  lostB_eq_zero_of_reach3 h.toReach3

theorem costA_eq_size_of_reach2 {g : St} {n : ℕ} (h : Reach2 givenA g n) : costA g = g.size :=
  costA_eq_size_of_reach3 h.toReach3

theorem costB_eq_size_of_reach2 {g : St} {n : ℕ} (h : Reach2 givenB g n) : costB g = g.size :=
  costB_eq_size_of_reach3 h.toReach3

end Seed.Third
