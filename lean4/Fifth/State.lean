import Fourth.Rename

/-!
# The fifth seed: removal and identification on counted states

`prompt/fifth/seed_prompt.md` differs from the fourth seed in two sentences:
removing an assertion lowers its multiplicity by one, and a change is one of
four kinds — identifying two terms, removing an assertion, adding a term,
adding an assertion; identifying two terms replaces both by one term in every
assertion.  The state is the fourth's `MSt` (terms, a multiplicity for each
ordered pair, the two names); two operations are new:

* `MSt.remove x y`: the multiplicity of `xry` falls by one;
* `MSt.identify u v`: `v` is replaced by `u` (the first derivation's `merge`);
  the multiplicity of a pair of the outcome is the sum of the multiplicities of
  the pairs of terms that become it (the reading C5″ of the paper: every one of
  the times an assertion is asserted has its terms replaced).

Derived here:
* a merged multiplicity is at least each part (`identify_M_ge`); a multiplicity
  of the outcome is zero exactly when every pair that becomes it had
  multiplicity zero (`identify_M_eq_zero_iff`);
* an identification keeps the total multiplicity and lowers the number of
  terms by one; a removal lowers the total by one (`total_identify`,
  `size_identify`, `total_remove`, `size_remove`);
* the support map to the first seed's states commutes with an identification,
  and with a removal of an assertion asserted once (`toSt_identify`,
  `toSt_remove`) — the formal form of rule 5 for the first derivation's
  statements about supports.
-/

namespace Seed.Fifth

open Seed Seed.Fourth MSt

/-- Removing an assertion: its multiplicity falls by one. -/
def _root_.Seed.Fourth.MSt.remove (s : MSt) (x y : ℕ) : MSt :=
  ⟨s.T, Function.update s.M (x, y) (s.M (x, y) - 1), s.a, s.b⟩

/-- Identifying `u` and `v`: both are replaced by one term (written `u`) in every
assertion.  The multiplicity of a pair of the outcome is the sum, over the pairs of
terms that become it, of their multiplicities; the names follow their terms. -/
def _root_.Seed.Fourth.MSt.identify (s : MSt) (u v : ℕ) : MSt :=
  ⟨s.T.erase v,
    fun p => ∑ q ∈ (s.T ×ˢ s.T).filter (fun q => (merge u v q.1, merge u v q.2) = p), s.M q,
    merge u v s.a, merge u v s.b⟩

/-! ## Removal -/

@[simp] theorem remove_T (s : MSt) (x y : ℕ) : (s.remove x y).T = s.T := rfl
@[simp] theorem remove_a (s : MSt) (x y : ℕ) : (s.remove x y).a = s.a := rfl
@[simp] theorem remove_b (s : MSt) (x y : ℕ) : (s.remove x y).b = s.b := rfl

theorem remove_M (s : MSt) (x y : ℕ) (p : ℕ × ℕ) :
    (s.remove x y).M p = Function.update s.M (x, y) (s.M (x, y) - 1) p := rfl

theorem remove_M_self (s : MSt) (x y : ℕ) : (s.remove x y).M (x, y) = s.M (x, y) - 1 := by
  rw [remove_M, Function.update_self]

theorem remove_M_of_ne (s : MSt) (x y : ℕ) {p : ℕ × ℕ} (h : p ≠ (x, y)) :
    (s.remove x y).M p = s.M p := by
  rw [remove_M, Function.update_of_ne h]

theorem total_remove (s : MSt) {x y : ℕ} (hx : x ∈ s.T) (hy : y ∈ s.T) (hp : s.M (x, y) ≠ 0) :
    (s.remove x y).total + 1 = s.total := by
  unfold MSt.total
  have hm : (x, y) ∈ s.T ×ˢ s.T := Finset.mem_product.2 ⟨hx, hy⟩
  show ∑ p ∈ s.T ×ˢ s.T, Function.update s.M (x, y) (s.M (x, y) - 1) p + 1 = ∑ p ∈ s.T ×ˢ s.T, s.M p
  rw [Finset.sum_update_of_mem hm, Finset.sdiff_singleton_eq_erase, ← Finset.sum_erase_add _ _ hm]
  omega

theorem size_remove (s : MSt) {x y : ℕ} (hx : x ∈ s.T) (hy : y ∈ s.T) (hp : s.M (x, y) ≠ 0) :
    (s.remove x y).size + 1 = s.size := by
  unfold MSt.size
  have := total_remove s hx hy hp
  rw [remove_T]
  omega

/-! ## Identification -/

@[simp] theorem identify_T (s : MSt) (u v : ℕ) : (s.identify u v).T = s.T.erase v := rfl
@[simp] theorem identify_a (s : MSt) (u v : ℕ) : (s.identify u v).a = merge u v s.a := rfl
@[simp] theorem identify_b (s : MSt) (u v : ℕ) : (s.identify u v).b = merge u v s.b := rfl

theorem identify_M (s : MSt) (u v : ℕ) (p : ℕ × ℕ) :
    (s.identify u v).M p =
      ∑ q ∈ (s.T ×ˢ s.T).filter (fun q => (merge u v q.1, merge u v q.2) = p), s.M q := rfl

theorem mem_fiber {s : MSt} {u v : ℕ} {p q : ℕ × ℕ} :
    q ∈ (s.T ×ˢ s.T).filter (fun q => (merge u v q.1, merge u v q.2) = p) ↔
      (q.1 ∈ s.T ∧ q.2 ∈ s.T) ∧ (merge u v q.1, merge u v q.2) = p := by
  simp [Finset.mem_filter, Finset.mem_product]

/-- A merged multiplicity is at least each of its parts. -/
theorem identify_M_ge (s : MSt) (u v : ℕ) {x y : ℕ} (hx : x ∈ s.T) (hy : y ∈ s.T) :
    s.M (x, y) ≤ (s.identify u v).M (merge u v x, merge u v y) := by
  rw [identify_M]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_fiber.2 ⟨⟨hx, hy⟩, rfl⟩)

theorem identify_M_eq_zero_iff (s : MSt) (u v : ℕ) (p : ℕ × ℕ) :
    (s.identify u v).M p = 0 ↔
      ∀ x y, x ∈ s.T → y ∈ s.T → (merge u v x, merge u v y) = p → s.M (x, y) = 0 := by
  rw [identify_M, Finset.sum_eq_zero_iff]
  constructor
  · intro h x y hx hy hp
    exact h (x, y) (mem_fiber.2 ⟨⟨hx, hy⟩, hp⟩)
  · rintro h ⟨x, y⟩ hq
    obtain ⟨⟨hx, hy⟩, hp⟩ := mem_fiber.1 hq
    exact h x y hx hy hp

theorem identify_M_ne_zero (s : MSt) (u v : ℕ) {p : ℕ × ℕ} (h : (s.identify u v).M p ≠ 0) :
    ∃ x y, x ∈ s.T ∧ y ∈ s.T ∧ (merge u v x, merge u v y) = p ∧ s.M (x, y) ≠ 0 := by
  rw [identify_M] at h
  obtain ⟨⟨x, y⟩, hq, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨⟨hx, hy⟩, hp⟩ := mem_fiber.1 hq
  exact ⟨x, y, hx, hy, hp, hne⟩

/-- A term that is there differs from one that is not. -/
theorem ne_of_notMem {T : Finset ℕ} {x t : ℕ} (hx : x ∈ T) (ht : t ∉ T) : x ≠ t :=
  fun h => ht (h ▸ hx)

theorem merge_eq_left_iff (u v x : ℕ) : merge u v x = u ↔ x = u ∨ x = v := by
  unfold merge
  split_ifs with h
  · simp [h]
  · simp [h]

/-- An identification keeps the total multiplicity: every unit of multiplicity is
carried to exactly one pair of the outcome. -/
theorem total_identify (s : MSt) {u v : ℕ} (hu : u ∈ s.T) (huv : u ≠ v) :
    (s.identify u v).total = s.total := by
  unfold MSt.total
  rw [identify_T]
  refine Finset.sum_fiberwise_of_maps_to (g := fun q : ℕ × ℕ => (merge u v q.1, merge u v q.2))
    (fun q hq => ?_) s.M
  obtain ⟨h1, h2⟩ := Finset.mem_product.1 hq
  exact Finset.mem_product.2 ⟨merge_mem_erase hu huv h1, merge_mem_erase hu huv h2⟩

theorem size_identify (s : MSt) {u v : ℕ} (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v) :
    (s.identify u v).size + 1 = s.size := by
  unfold MSt.size
  rw [total_identify s hu huv, identify_T, Finset.card_erase_of_mem hv]
  have := Finset.card_pos.2 ⟨v, hv⟩
  omega

/-! ## The support map commutes -/

/-- The support of a removal of an assertion asserted once is the first seed's removal. -/
theorem toSt_remove {s : MSt} {x y : ℕ} (h1 : s.M (x, y) = 1) :
    toSt (s.remove x y) = (toSt s).remove (x, y) := by
  apply St.ext
  · rfl
  · ext p
    rw [mem_toSt_A]
    show ((p.1 ∈ s.T ∧ p.2 ∈ s.T) ∧ Function.update s.M (x, y) (s.M (x, y) - 1) p ≠ 0) ↔
      p ∈ (toSt s).A.erase (x, y)
    rw [Finset.mem_erase, mem_toSt_A, Function.update_apply]
    by_cases hp : p = (x, y)
    · subst hp
      simp [h1]
    · simp [hp]
  · rfl
  · rfl

/-- The support of an identification is the first seed's identification of the support. -/
theorem toSt_identify {s : MSt} (hw : s.WF) {u v : ℕ} (hu : u ∈ s.T) (huv : u ≠ v) :
    toSt (s.identify u v) = (toSt s).identify u v := by
  apply St.ext
  · rfl
  · ext p
    rw [mem_toSt_A, mem_identify]
    constructor
    · rintro ⟨_, h⟩
      obtain ⟨x, y, _, _, hp, hne⟩ := identify_M_ne_zero s u v h
      exact ⟨(x, y), (mem_toSt_A_of_wf hw).2 hne, hp⟩
    · rintro ⟨⟨x, y⟩, hq, hp⟩
      have hne : s.M (x, y) ≠ 0 := (mem_toSt_A_of_wf hw).1 hq
      have hxy : x ∈ s.T ∧ y ∈ s.T := hw.1 (x, y) hne
      have hge := identify_M_ge s u v hxy.1 hxy.2
      have hp' : (merge u v x, merge u v y) = p := hp
      rw [← hp']
      refine ⟨⟨merge_mem_erase hu huv hxy.1, merge_mem_erase hu huv hxy.2⟩, ?_⟩
      omega
  · rfl
  · rfl

end Seed.Fifth
