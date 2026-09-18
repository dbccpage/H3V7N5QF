import Fourth.Contain

/-!
# Every sequence has the same length: the size difference, multiplicities counted

Derived here:
* one change raises `size = terms + sum of multiplicities` by exactly one
  (`Step4.size_eq`), so a sequence of `n` changes raises it by exactly `n`
  (`Reach4.size_eq`), and any two sequences between the same two states have
  the same length (`Reach4.length_unique`);
* additions reach every legal, well-formed state that contains a state
  (`reach4_by_additions`): add the missing terms, then raise each multiplicity
  as often as it falls short (`reach4_addTerms`, `reach4_raise`); so a state
  written with `a = 0`, `b = 1` that contains what is given is reached in
  exactly its size minus that of what is given, by every sequence
  (`fewest_changes4_A`, `fewest_changes4_B`);
* a state is reachable from a state exactly when it contains it (`reach4_iff`);
* reachability is one-way: two states reachable from each other are reached in
  zero changes and are the same state (`Reach4.antisymm`); a state once left is
  never returned to (`Reach4.no_return`);
* whatever is reached from what is given contains it
  (`reach4_givenA_contains`, `reach4_givenB_contains`), the one-term state is
  unreachable, the beginning without `bra` reaches the beginning with it in one
  change, and the beginning with `bra` never reaches the one without.

Cited from the third derivation and re-checked: the third's `Step2.size_eq`,
`Reach2.size_eq`, `reach2_by_additions`, `reach2_iff`, `Reach2.antisymm` are
the statements below on the supports of states asserting nothing twice
(`Fourth/Compare.lean`); here they are proved afresh for all counted states,
with the size counting multiplicities.
-/

namespace Seed.Fourth

open Seed Seed.Second Seed.Third MSt

/-! ## Size rises by exactly one -/

theorem Step4.size_eq {s t : MSt} (h : Step4 s t) (hw : s.WF) : t.size = s.size + 1 := by
  cases h with
  | addTerm t ht => exact size_addTerm hw ht
  | addAssertion x y hx hy hxy => exact size_addAssertion hx hy

theorem Reach4.size_eq {s t : MSt} {n : ℕ} (h : Reach4 s t n) (hw : s.WF) :
    t.size = s.size + n := by
  induction h with
  | refl => omega
  | step r st ih =>
    have := st.size_eq (r.wf hw)
    omega

/-- Any two sequences of changes between the same two states have the same length. -/
theorem Reach4.length_unique {s t : MSt} {n m : ℕ} (h1 : Reach4 s t n) (h2 : Reach4 s t m)
    (hw : s.WF) : n = m := by
  have e1 := h1.size_eq hw
  have e2 := h2.size_eq hw
  omega

/-- Reachability is one-way: reached both ways means reached in zero changes, and
the two states are the same. -/
theorem Reach4.antisymm {s t : MSt} {n m : ℕ} (h1 : Reach4 s t n) (h2 : Reach4 t s m)
    (hw : s.WF) : n = 0 ∧ m = 0 ∧ s = t := by
  have e1 := h1.size_eq hw
  have e2 := h2.size_eq (h1.wf hw)
  have hn : n = 0 := by omega
  have hm : m = 0 := by omega
  subst hn
  exact ⟨rfl, hm, h1.eq_of_zero⟩

/-- A state once left is never returned to. -/
theorem Reach4.no_return {s t : MSt} {n m : ℕ} (h1 : Reach4 s t n) (hn : 0 < n)
    (h2 : Reach4 t s m) (hw : s.WF) : False := by
  have := (h1.antisymm h2 hw).1
  omega

/-- **Lower bound, `bra` not asserted to begin with**: exact. -/
theorem fewest_changes4_lower_A {t : MSt} {n : ℕ} (h : Reach4 givenA4 t n) : t.size = n + 3 := by
  have := h.size_eq givenA4_wf
  rw [size_givenA4] at this
  omega

/-- **Lower bound, `bra` asserted to begin with**: exact. -/
theorem fewest_changes4_lower_B {t : MSt} {n : ℕ} (h : Reach4 givenB4 t n) : t.size = n + 4 := by
  have := h.size_eq givenB4_wf
  rw [size_givenB4] at this
  omega

/-! ## Upper bound: additions reach everything that contains the state -/

/-- Adding the terms of `D`, one change each. -/
theorem reach4_addTerms (s : MSt) (D : Finset ℕ) (hD : Disjoint D s.T) :
    Reach4 s ⟨s.T ∪ D, s.M, s.a, s.b⟩ D.card := by
  revert hD
  refine Finset.induction_on D ?_ ?_
  · intro _
    simp only [Finset.union_empty, Finset.card_empty]
    exact Reach4.refl s
  · intro t D ht ih hD
    rw [Finset.disjoint_insert_left] at hD
    have r := ih hD.2
    have hnew : t ∉ s.T ∪ D := by
      simp only [Finset.mem_union, not_or]
      exact ⟨hD.1, ht⟩
    have st := Step4.addTerm ⟨s.T ∪ D, s.M, s.a, s.b⟩ t hnew
    rw [Finset.card_insert_of_notMem ht, Finset.union_insert]
    exact Reach4.step r st

/-- Raising multiplicities one at a time: from `s` to a legal, well-formed `g` with the
same terms and names that contains `s`, in exactly the missing total. -/
theorem reach4_raise (g : MSt) (hg : g.Legal) (hgw : g.WF) :
    ∀ (d : ℕ) (s : MSt), s.T = g.T → s.a = g.a → s.b = g.b → s.WF → (∀ p, s.M p ≤ g.M p) →
      g.total = s.total + d → Reach4 s g d := by
  intro d
  induction d with
  | zero =>
    intro s hT ha hb hw hle htot
    have e : s = g := by
      apply MSt.ext
      · exact hT
      · funext p
        by_cases hp : p ∈ g.T ×ˢ g.T
        · -- Inside the terms the sums agree, so with pointwise ≤ the values agree.
          by_contra hne
          have hlt : s.M p < g.M p := lt_of_le_of_ne (hle p) hne
          have : ∑ q ∈ g.T ×ˢ g.T, s.M q < ∑ q ∈ g.T ×ˢ g.T, g.M q :=
            Finset.sum_lt_sum (fun q _ => hle q) ⟨p, hp, hlt⟩
          unfold MSt.total at htot
          rw [hT] at htot
          omega
        · have h1 : g.M p = 0 := by
            by_contra h
            exact hp (Finset.mem_product.2 (hgw.1 p h))
          have h2 : s.M p = 0 := by
            by_contra h
            have := hw.1 p h
            rw [hT] at this
            exact hp (Finset.mem_product.2 this)
          rw [h1, h2]
      · exact ha
      · exact hb
    rw [e]
    exact Reach4.refl g
  | succ d ih =>
    intro s hT ha hb hw hle htot
    -- Some pair falls short.
    have hlt : ∑ q ∈ g.T ×ˢ g.T, s.M q < ∑ q ∈ g.T ×ˢ g.T, g.M q := by
      unfold MSt.total at htot
      rw [hT] at htot
      omega
    obtain ⟨p, hp, hplt⟩ := Finset.exists_lt_of_sum_lt hlt
    obtain ⟨x, y⟩ := p
    have hxT : x ∈ s.T := by rw [hT]; exact (Finset.mem_product.1 hp).1
    have hyT : y ∈ s.T := by rw [hT]; exact (Finset.mem_product.1 hp).2
    have hxy : x ≠ y := by
      rintro rfl
      have := hg x
      omega
    have st := Step4.addAssertion s x y hxT hyT hxy
    have hw' := st.wf hw
    have hle' : ∀ q, (s.addAssertion x y).M q ≤ g.M q := by
      intro q
      show Function.update s.M (x, y) (s.M (x, y) + 1) q ≤ g.M q
      rw [Function.update_apply]
      split_ifs with hq
      · subst hq
        omega
      · exact hle q
    have htot' : g.total = (s.addAssertion x y).total + d := by
      rw [total_addAssertion hxT hyT]
      omega
    have r := ih (s.addAssertion x y) hT ha hb hw' hle' htot'
    have : Reach4 s g (1 + d) := Reach4.trans (Reach4.step (Reach4.refl s) st) r
    rw [Nat.add_comm] at this
    exact this

/-- The total of a state with more terms and the same multiplicities is the same. -/
theorem total_widen {s : MSt} (hw : s.WF) {T : Finset ℕ} (hT : s.T ⊆ T) :
    (⟨T, s.M, s.a, s.b⟩ : MSt).total = s.total := by
  unfold MSt.total
  symm
  apply Finset.sum_subset (Finset.product_subset_product hT hT)
  intro p _ hp
  by_contra h
  exact hp (Finset.mem_product.2 (hw.1 p h))

/-- **Additions reach everything that contains the state.**  Add the missing terms,
then raise the multiplicities that fall short. -/
theorem reach4_by_additions (s g : MSt) (hs : s.WF) (hg : g.Legal) (hgw : g.WF)
    (h : Contains4 s g) : Reach4 s g ((g.T \ s.T).card + (g.total - s.total)) := by
  have r1 := reach4_addTerms s (g.T \ s.T) Finset.sdiff_disjoint
  have hTT : s.T ∪ g.T \ s.T = g.T := Finset.union_sdiff_of_subset h.terms
  rw [hTT] at r1
  have hw1 : (⟨g.T, s.M, s.a, s.b⟩ : MSt).WF :=
    ⟨fun p hp => ⟨h.terms (hs.1 p hp).1, h.terms (hs.1 p hp).2⟩, h.terms hs.2.1, h.terms hs.2.2⟩
  have htot1 : (⟨g.T, s.M, s.a, s.b⟩ : MSt).total = s.total := total_widen hs h.terms
  have hle := h.total_le
  have r2 := reach4_raise g hg hgw (g.total - s.total) ⟨g.T, s.M, s.a, s.b⟩ rfl h.name_a.symm
    h.name_b.symm hw1 h.mult (by rw [htot1]; omega)
  exact r1.trans r2

/-- A legal, well-formed state that contains `s` is reached from `s`, in exactly the
size difference. -/
theorem reach4_of_contains {s g : MSt} (hs : s.WF) (hg : g.Legal) (hgw : g.WF)
    (h : Contains4 s g) : ∃ n, Reach4 s g n ∧ n + s.size = g.size := by
  refine ⟨_, reach4_by_additions s g hs hg hgw h, ?_⟩
  have hc := Finset.card_sdiff_add_card_eq_card h.terms
  have hle := h.total_le
  unfold MSt.size
  omega

/-- **Reachability is containment.**  A legal, well-formed state is reached from a
well-formed `s` exactly when it contains `s`. -/
theorem reach4_iff {s g : MSt} (hs : s.WF) (hg : g.Legal) (hgw : g.WF) :
    (∃ n, Reach4 s g n) ↔ Contains4 s g :=
  ⟨fun ⟨_, h⟩ => h.contains, fun h => let ⟨n, hn, _⟩ := reach4_of_contains hs hg hgw h; ⟨n, hn⟩⟩

/-! ## From what is given -/

theorem givenA4_contains {g : MSt} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1)
    (hab : g.M (0, 1) ≠ 0) : Contains4 givenA4 g := by
  refine ⟨given_terms_subset (toSt_wf hgw) ha hb, fun p => ?_, ha, hb⟩
  show (if p ∈ givenA.A then 1 else 0) ≤ g.M p
  by_cases hp : p ∈ givenA.A
  · simp only [givenA, Finset.mem_singleton] at hp
    subst hp
    simp only [givenA, Finset.mem_singleton, if_true]
    omega
  · simp [hp]

theorem givenB4_contains {g : MSt} (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1)
    (hab : g.M (0, 1) ≠ 0) (hba : g.M (1, 0) ≠ 0) : Contains4 givenB4 g := by
  refine ⟨given_terms_subset (toSt_wf hgw) ha hb, fun p => ?_, ha, hb⟩
  show (if p ∈ givenB.A then 1 else 0) ≤ g.M p
  by_cases hp : p ∈ givenB.A
  · simp only [givenB, Finset.mem_insert, Finset.mem_singleton] at hp
    rw [if_pos (by simp [givenB, hp])]
    rcases hp with rfl | rfl <;> omega
  · simp [hp]

/-- **Upper bound, `bra` not asserted to begin with.** -/
theorem fewest_changes4_upper_A {g : MSt} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1)
    (hab : g.M (0, 1) ≠ 0) : ∃ n, Reach4 givenA4 g n ∧ n + 3 = g.size := by
  obtain ⟨n, hn, hc⟩ := reach4_of_contains givenA4_wf hg hgw (givenA4_contains hgw ha hb hab)
  rw [size_givenA4] at hc
  exact ⟨n, hn, hc⟩

/-- **Upper bound, `bra` asserted to begin with.** -/
theorem fewest_changes4_upper_B {g : MSt} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1)
    (hab : g.M (0, 1) ≠ 0) (hba : g.M (1, 0) ≠ 0) : ∃ n, Reach4 givenB4 g n ∧ n + 4 = g.size := by
  obtain ⟨n, hn, hc⟩ := reach4_of_contains givenB4_wf hg hgw (givenB4_contains hgw ha hb hab hba)
  rw [size_givenB4] at hc
  exact ⟨n, hn, hc⟩

/-- **Fewest changes, `bra` not asserted to begin with.**  A legal state written with
`a = 0`, `b = 1` in which `arb` is asserted is reached in exactly `size − 3` changes,
and every sequence reaching it has that length. -/
theorem fewest_changes4_A {g : MSt} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1)
    (hab : g.M (0, 1) ≠ 0) :
    (∃ n, Reach4 givenA4 g n ∧ n + 3 = g.size) ∧ ∀ n, Reach4 givenA4 g n → n + 3 = g.size :=
  ⟨fewest_changes4_upper_A hg hgw ha hb hab, fun _ h => (fewest_changes4_lower_A h).symm⟩

/-- **Fewest changes, `bra` asserted to begin with.** -/
theorem fewest_changes4_B {g : MSt} (hg : g.Legal) (hgw : g.WF) (ha : g.a = 0) (hb : g.b = 1)
    (hab : g.M (0, 1) ≠ 0) (hba : g.M (1, 0) ≠ 0) :
    (∃ n, Reach4 givenB4 g n ∧ n + 4 = g.size) ∧ ∀ n, Reach4 givenB4 g n → n + 4 = g.size :=
  ⟨fewest_changes4_upper_B hg hgw ha hb hab hba, fun _ h => (fewest_changes4_lower_B h).symm⟩

/-- Every state reached from what is given (`bra` not asserted) is legal, well formed,
keeps `a` and `b` two terms, and asserts `arb`. -/
theorem reach4_givenA_contains {g : MSt} {n : ℕ} (h : Reach4 givenA4 g n) :
    g.Legal ∧ g.WF ∧ g.a ≠ g.b ∧ g.M (g.a, g.b) ≠ 0 :=
  ⟨h.legal givenA4_legal, h.wf givenA4_wf, h.names_apart givenA4_legal givenA4_arb_ne,
    h.arb_persists givenA4_arb_ne⟩

/-- With `bra` asserted to begin with, `bra` is asserted in every result too. -/
theorem reach4_givenB_contains {g : MSt} {n : ℕ} (h : Reach4 givenB4 g n) :
    g.Legal ∧ g.WF ∧ g.a ≠ g.b ∧ g.M (g.a, g.b) ≠ 0 ∧ g.M (g.b, g.a) ≠ 0 :=
  ⟨h.legal givenB4_legal, h.wf givenB4_wf, h.names_apart givenB4_legal givenB4_arb_ne,
    h.arb_persists givenB4_arb_ne, h.bra_persists givenB4_bra_ne⟩

/-- Every result has at least two terms. -/
theorem reach4_givenA_two_terms {g : MSt} {n : ℕ} (h : Reach4 givenA4 g n) : 2 ≤ g.T.card :=
  h.two_terms givenA4_legal givenA4_wf givenA4_arb_ne

theorem reach4_givenB_two_terms {g : MSt} {n : ℕ} (h : Reach4 givenB4 g n) : 2 ≤ g.T.card :=
  h.two_terms givenB4_legal givenB4_wf givenB4_arb_ne

/-- The one-term state, counted. -/
def oneTerm4 : MSt := ofSt oneTerm

/-- The one-term state is not a result. -/
theorem oneTerm_unreachable4_A (n : ℕ) : ¬ Reach4 givenA4 oneTerm4 n := by
  intro h
  have := reach4_givenA_two_terms h
  simp [oneTerm4, ofSt, oneTerm] at this

theorem oneTerm_unreachable4_B (n : ℕ) : ¬ Reach4 givenB4 oneTerm4 n := by
  intro h
  have := reach4_givenB_two_terms h
  simp [oneTerm4, ofSt, oneTerm] at this

/-- The beginning without `bra` reaches the beginning with it in one change. -/
theorem givenA4_to_givenB4 : Reach4 givenA4 givenB4 1 := by
  have st : Step4 givenA4 (givenA4.addAssertion 1 0) :=
    Step4.addAssertion givenA4 1 0 (by simp [givenA4, ofSt, givenA]) (by simp [givenA4, ofSt, givenA])
      (by omega)
  have e : givenA4.addAssertion 1 0 = givenB4 := by
    have h := ofSt_addAssertion (s := givenA) (x := 1) (y := 0) (by simp [givenA])
    rw [givenA4, ← h]
    show ofSt (givenA.addAssertion 1 0) = ofSt givenB
    congr 1
    simp only [givenA, givenB, St.addAssertion]
    congr 1
    exact Finset.pair_comm _ _
  exact e ▸ Reach4.step (Reach4.refl givenA4) st

/-- The beginning with `bra` never reaches the beginning without it: its size is smaller. -/
theorem givenB4_never_givenA4 (n : ℕ) : ¬ Reach4 givenB4 givenA4 n := by
  intro h
  have := h.size_eq givenB4_wf
  rw [size_givenA4, size_givenB4] at this
  omega

end Seed.Fourth
