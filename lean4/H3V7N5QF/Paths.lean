import H3V7N5QF.Cost

/-!
# Every result is reached in exactly its cost

Derived here: explicit sequences of changes.  From any state `s` to any legal
state `g` on at least the same terms, with the names on the same terms: remove
what `g` does not assert, add the missing terms, add the missing assertions
(`reach_by_edits`).  Counting these changes (`edits_count`) and combining with
the lower bounds of `Cost.lean` gives the fewest changes exactly
(`fewest_changes_A`, `fewest_changes_B`).

The states here are written with `a = 0`, `b = 1` (and `a = b = 0` after an
identification of the two).  A state written otherwise is the same result
under a rewriting of its terms; that step is not formalised here.
-/

namespace Seed

open St

theorem Reach.trans {s t u : St} {n m : ℕ} (h1 : Reach s t n) (h2 : Reach t u m) :
    Reach s u (n + m) := by
  induction h2 with
  | refl => exact h1
  | step _ st ih => exact Reach.step ih st

/-- Adding the terms of `D`, one change each. -/
theorem reach_addTerms (s : St) (D : Finset ℕ) (hD : Disjoint D s.T) :
    Reach s ⟨s.T ∪ D, s.A, s.a, s.b⟩ D.card := by
  revert hD
  refine Finset.induction_on D ?_ ?_
  · intro _
    simp only [Finset.union_empty, Finset.card_empty]
    exact Reach.refl s
  · intro t D ht ih hD
    rw [Finset.disjoint_insert_left] at hD
    have r := ih hD.2
    have hnew : t ∉ s.T ∪ D := by
      simp only [Finset.mem_union, not_or]
      exact ⟨hD.1, ht⟩
    have st := Step.addTerm ⟨s.T ∪ D, s.A, s.a, s.b⟩ t hnew
    rw [Finset.card_insert_of_notMem ht, Finset.union_insert]
    exact Reach.step r st

/-- Adding the assertions of `E`, one change each. -/
theorem reach_addAssertions (s : St) (E : Finset (ℕ × ℕ))
    (hE : ∀ p ∈ E, p.1 ∈ s.T ∧ p.2 ∈ s.T ∧ p.1 ≠ p.2) (hdis : Disjoint E s.A) :
    Reach s ⟨s.T, s.A ∪ E, s.a, s.b⟩ E.card := by
  revert hE hdis
  refine Finset.induction_on E ?_ ?_
  · intro _ _
    simp only [Finset.union_empty, Finset.card_empty]
    exact Reach.refl s
  · rintro ⟨x, y⟩ E hp ih hE hdis
    rw [Finset.disjoint_insert_left] at hdis
    have r := ih (fun q hq => hE q (Finset.mem_insert_of_mem hq)) hdis.2
    obtain ⟨hx, hy, hxy⟩ := hE (x, y) (Finset.mem_insert_self _ _)
    have hnew : (x, y) ∉ s.A ∪ E := by
      simp only [Finset.mem_union, not_or]
      exact ⟨hdis.1, hp⟩
    have st := Step.addAssertion ⟨s.T, s.A ∪ E, s.a, s.b⟩ x y hx hy hxy hnew
    rw [Finset.card_insert_of_notMem hp, Finset.union_insert]
    exact Reach.step r st

/-- Removing the assertions of `E`, one change each. -/
theorem reach_removes (s : St) (E : Finset (ℕ × ℕ)) (hE : E ⊆ s.A) :
    Reach s ⟨s.T, s.A \ E, s.a, s.b⟩ E.card := by
  revert hE
  refine Finset.induction_on E ?_ ?_
  · intro _
    simp only [Finset.sdiff_empty, Finset.card_empty]
    exact Reach.refl s
  · intro p E hp ih hE
    rw [Finset.insert_subset_iff] at hE
    have r := ih hE.2
    have hmem : p ∈ s.A \ E := Finset.mem_sdiff.2 ⟨hE.1, hp⟩
    have st := Step.remove ⟨s.T, s.A \ E, s.a, s.b⟩ p hmem
    rw [Finset.card_insert_of_notMem hp, Finset.sdiff_insert]
    exact Reach.step r st

/-- **Edit path.**  Remove what `g` does not assert, add the missing terms, add the
missing assertions. -/
theorem reach_by_edits (s g : St) (hg : g.Legal) (hgw : g.WF) (hT : s.T ⊆ g.T)
    (ha : g.a = s.a) (hb : g.b = s.b) :
    Reach s g ((s.A \ g.A).card + (g.T \ s.T).card + (g.A \ s.A).card) := by
  have r1 := reach_removes s (s.A \ g.A) Finset.sdiff_subset
  have r2 := reach_addTerms ⟨s.T, s.A \ (s.A \ g.A), s.a, s.b⟩ (g.T \ s.T) Finset.sdiff_disjoint
  have hTT : s.T ∪ g.T \ s.T = g.T := Finset.union_sdiff_of_subset hT
  have r3 := reach_addAssertions ⟨s.T ∪ g.T \ s.T, s.A \ (s.A \ g.A), s.a, s.b⟩ (g.A \ s.A)
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
    (Finset.disjoint_left.2 fun p hp hq => (Finset.mem_sdiff.1 hp).2 (Finset.mem_sdiff.1 hq).1)
  have e : (⟨s.T ∪ g.T \ s.T, s.A \ (s.A \ g.A) ∪ g.A \ s.A, s.a, s.b⟩ : St) = g := by
    apply St.ext
    · exact hTT
    · ext p
      simp only [Finset.mem_union, Finset.mem_sdiff]
      tauto
    · exact ha.symm
    · exact hb.symm
  have r : Reach s (⟨s.T ∪ g.T \ s.T, s.A \ (s.A \ g.A) ∪ g.A \ s.A, s.a, s.b⟩ : St)
      ((s.A \ g.A).card + (g.T \ s.T).card + (g.A \ s.A).card) := (r1.trans r2).trans r3
  rw [e] at r
  exact r

/-- The number of changes of the edit path, in terms of sizes. -/
theorem edits_count (s g : St) (hT : s.T ⊆ g.T) :
    (s.A \ g.A).card + (g.T \ s.T).card + (g.A \ s.A).card + s.size
      = g.size + 2 * (s.A \ g.A).card := by
  have h1 := Finset.card_sdiff_add_card_eq_card hT
  have h2 := Finset.card_sdiff_add_card_inter g.A s.A
  have h3 := Finset.card_sdiff_add_card_inter s.A g.A
  rw [Finset.inter_comm] at h3
  simp only [St.size]
  omega

/-! ## From what is given -/

/-- One term, nothing asserted, `a` and `b` identified. -/
def oneTerm : St := ⟨{0}, ∅, 0, 0⟩

theorem card_singleton_sdiff (p : ℕ × ℕ) (S : Finset (ℕ × ℕ)) :
    (({p} : Finset (ℕ × ℕ)) \ S).card = if p ∈ S then 0 else 1 := by
  by_cases h : p ∈ S
  · rw [Finset.sdiff_eq_empty_iff_subset.2 (Finset.singleton_subset_iff.2 h)]
    simp [h]
  · rw [Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_singleton_left.2 h)]
    simp [h]

theorem card_pair_sdiff {p q : ℕ × ℕ} (hpq : p ≠ q) (S : Finset (ℕ × ℕ)) :
    (({p, q} : Finset (ℕ × ℕ)) \ S).card
      = (if p ∈ S then 0 else 1) + (if q ∈ S then 0 else 1) := by
  by_cases h : p ∈ S
  · rw [Finset.insert_sdiff_of_mem _ h, card_singleton_sdiff]
    simp [h]
  · have hnot : p ∉ ({q} : Finset (ℕ × ℕ)) \ S := by
      simp [hpq]
    rw [Finset.insert_sdiff_of_notMem _ h, Finset.card_insert_of_notMem hnot,
      card_singleton_sdiff]
    simp only [h, if_false]
    omega

theorem lostA_eq_card {g : St} (ha : g.a = 0) (hb : g.b = 1) :
    (givenA.A \ g.A).card = lostA g := by
  have hne : g.a ≠ g.b := by rw [ha, hb]; omega
  rw [lostA_of_ne hne, ha, hb]
  exact card_singleton_sdiff (0, 1) g.A

theorem lostB_eq_card {g : St} (ha : g.a = 0) (hb : g.b = 1) :
    (givenB.A \ g.A).card = lostB g := by
  have hne : g.a ≠ g.b := by rw [ha, hb]; omega
  rw [lostB_of_ne hne, ha, hb]
  exact card_pair_sdiff (by decide) g.A

theorem given_terms_subset {g : St} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1) :
    ({0, 1} : Finset ℕ) ⊆ g.T := by
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl
  · exact ha ▸ hgw.2.1
  · exact hb ▸ hgw.2.2

/-- Removing `arb` and then identifying `a` and `b`: two changes. -/
theorem givenA_to_oneTerm : Reach givenA oneTerm 2 := by
  have st1 : Step givenA (givenA.remove (0, 1)) := Step.remove _ _ (by decide)
  have st2 : Step (givenA.remove (0, 1)) ((givenA.remove (0, 1)).identify 0 1) :=
    Step.identify _ 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have e : (givenA.remove (0, 1)).identify 0 1 = oneTerm := by decide
  exact e ▸ Reach.step (Reach.step (Reach.refl _) st1) st2

/-- Removing `arb`, removing `bra`, then identifying `a` and `b`: three changes. -/
theorem givenB_to_oneTerm : Reach givenB oneTerm 3 := by
  have st1 : Step givenB (givenB.remove (0, 1)) := Step.remove _ _ (by decide)
  have st2 : Step (givenB.remove (0, 1)) ((givenB.remove (0, 1)).remove (1, 0)) :=
    Step.remove _ _ (by decide)
  have st3 : Step ((givenB.remove (0, 1)).remove (1, 0))
      (((givenB.remove (0, 1)).remove (1, 0)).identify 0 1) :=
    Step.identify _ 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have e : ((givenB.remove (0, 1)).remove (1, 0)).identify 0 1 = oneTerm := by decide
  exact e ▸ Reach.step (Reach.step (Reach.step (Reach.refl _) st1) st2) st3

/-- **Upper bound, `a` and `b` apart, `bra` not asserted to begin with.** -/
theorem fewest_changes_upper_A_apart {g : St} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0)
    (hb : g.b = 1) : ∃ n, Reach givenA g n ∧ n + 3 = costA g := by
  have hT : givenA.T ⊆ g.T := given_terms_subset hgw ha hb
  refine ⟨_, reach_by_edits givenA g hg hgw hT ha hb, ?_⟩
  have c := edits_count givenA g hT
  have l := lostA_eq_card ha hb
  have sz : givenA.size = 3 := by decide
  unfold costA
  omega

/-- **Upper bound, `a` and `b` identified, `bra` not asserted to begin with.** -/
theorem fewest_changes_upper_A_merged {g : St} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0)
    (hb : g.b = 0) : ∃ n, Reach givenA g n ∧ n + 3 = costA g := by
  have hT : oneTerm.T ⊆ g.T := by
    intro t ht
    simp only [oneTerm, Finset.mem_singleton] at ht
    subst ht
    exact ha ▸ hgw.2.1
  refine ⟨_, givenA_to_oneTerm.trans (reach_by_edits oneTerm g hg hgw hT ha hb), ?_⟩
  have c := edits_count oneTerm g hT
  have e : (oneTerm.A \ g.A).card = 0 := by simp [oneTerm]
  have sz : oneTerm.size = 1 := by decide
  have l : lostA g = 2 := lostA_of_eq (ha.trans hb.symm)
  unfold costA
  omega

/-- **Upper bound, `a` and `b` apart, `bra` asserted to begin with.** -/
theorem fewest_changes_upper_B_apart {g : St} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0)
    (hb : g.b = 1) : ∃ n, Reach givenB g n ∧ n + 4 = costB g := by
  have hT : givenB.T ⊆ g.T := given_terms_subset hgw ha hb
  refine ⟨_, reach_by_edits givenB g hg hgw hT ha hb, ?_⟩
  have c := edits_count givenB g hT
  have l := lostB_eq_card ha hb
  have sz : givenB.size = 4 := by decide
  unfold costB
  omega

/-- **Upper bound, `a` and `b` identified, `bra` asserted to begin with.** -/
theorem fewest_changes_upper_B_merged {g : St} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0)
    (hb : g.b = 0) : ∃ n, Reach givenB g n ∧ n + 4 = costB g := by
  have hT : oneTerm.T ⊆ g.T := by
    intro t ht
    simp only [oneTerm, Finset.mem_singleton] at ht
    subst ht
    exact ha ▸ hgw.2.1
  refine ⟨_, givenB_to_oneTerm.trans (reach_by_edits oneTerm g hg hgw hT ha hb), ?_⟩
  have c := edits_count oneTerm g hT
  have e : (oneTerm.A \ g.A).card = 0 := by simp [oneTerm]
  have sz : oneTerm.size = 1 := by decide
  have l : lostB g = 3 := lostB_of_eq (ha.trans hb.symm)
  unfold costB
  omega

/-- **Fewest changes, `bra` not asserted to begin with.**  A legal state with
`a = 0` and `b ∈ {0, 1}` is reached in exactly `costA g - 3` changes and no fewer. -/
theorem fewest_changes_A {g : St} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0)
    (hb : g.b = 1 ∨ g.b = 0) :
    (∃ n, Reach givenA g n ∧ n + 3 = costA g) ∧ ∀ n, Reach givenA g n → costA g ≤ n + 3 :=
  ⟨hb.elim (fewest_changes_upper_A_apart hg hgw ha) (fewest_changes_upper_A_merged hg hgw ha),
    fun _ h => fewest_changes_lower_A h⟩

/-- **Fewest changes, `bra` asserted to begin with.** -/
theorem fewest_changes_B {g : St} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0)
    (hb : g.b = 1 ∨ g.b = 0) :
    (∃ n, Reach givenB g n ∧ n + 4 = costB g) ∧ ∀ n, Reach givenB g n → costB g ≤ n + 4 :=
  ⟨hb.elim (fewest_changes_upper_B_apart hg hgw ha) (fewest_changes_upper_B_merged hg hgw ha),
    fun _ h => fewest_changes_lower_B h⟩

end Seed
