import Twentythird.Nothing

/-!
# The fewest changes to a result

`Cost3 G c`: `c` changes from the empty state reach some state of the result
of `G`, and no fewer do.  Derived here:
* `cost3_iff`: the cost is the least `phi` (terms plus the assertions of the
  plain part) among the states of the result — the twenty-second's cost of a
  state being the fewest changes to it (`reach_plainSt`, `Reach.phi_le`,
  imported);
* `phi_eq_sum`: `phi` is the terms plus `Σ |e(x, y)|` over the pairs of
  terms; so **the cost is `n + min_g Σ |e(x, y) + g x − g y|`**
  (`cost3_iff_min`);
* with two terms, `n + |e(0, 0)| + |e(1, 1)| + |e(0, 1) + e(1, 0)|`
  (`cost3_two`);
* with three terms, the sums around the terms bound it below
  (`phi_ge_around`), and the loops and two-way sums do not fix it: two results
  with the same loops and two-way sums cost 6 and 12
  (`loops_and_two_way_do_not_fix_the_cost`);
* parity: raising adds an even number of atoms, so the size's parity is a
  mark of the result; every change changes it; so no change returns a state
  to its own result (`Step.not_same3`) and the costs of a state's result and
  of its outcome's differ by an odd number (`Step.cost3_odd`);
* a change performed on a state asserting the fewest raises the cost by at
  most one (`Step.cost3_le`), while adding a term to another state of the
  same result can raise it by `2k + 1` for every `k`
  (`adding_a_term_raises_the_cost`).
-/

namespace Twentythird

open Twentysecond

/-- `c` is the fewest changes from the empty state to a state of the result of `G`. -/
def Cost3 (G : St) (c : Nat) : Prop :=
  (∃ H, Same3 H G ∧ Reach empty H c) ∧ ∀ H k, Same3 H G → Reach empty H k → c ≤ k

theorem Cost3.unique {G : St} {c c' : Nat} (h : Cost3 G c) (h' : Cost3 G c') : c = c' := by
  obtain ⟨⟨H, s, r⟩, lo⟩ := h
  obtain ⟨⟨H', s', r'⟩, lo'⟩ := h'
  have a := lo H' c' s' r'
  have b := lo' H c s r
  omega

/-- The cost is a mark of the result. -/
theorem Cost3.congr {G G' : St} (h : Same3 G G') {c : Nat} : Cost3 G c ↔ Cost3 G' c := by
  constructor
  · rintro ⟨⟨H, s, r⟩, lo⟩
    exact ⟨⟨H, s.trans h, r⟩, fun K k s' r' => lo K k (s'.trans h.symm) r'⟩
  · rintro ⟨⟨H, s, r⟩, lo⟩
    exact ⟨⟨H, s.trans h.symm, r⟩, fun K k s' r' => lo K k (s'.trans h) r'⟩

/-- **The cost of a result is the least `phi` among its states.** -/
theorem cost3_iff {G : St} {c : Nat} :
    Cost3 G c ↔ (∃ H, H.WF ∧ Same3 H G ∧ phi H = c) ∧ ∀ H, H.WF → Same3 H G → c ≤ phi H := by
  constructor
  · rintro ⟨⟨H, s, r⟩, lo⟩
    have hH := r.wf empty_wf
    have up : phi H ≤ c := by
      have := r.phi_le
      rw [phi_empty] at this
      omega
    have down (K : St) (hK : K.WF) (sK : Same3 K G) : c ≤ phi K :=
      lo K.plainSt (phi K) ((Same.same3 (same_plainSt K).symm).trans sK) (reach_plainSt hK).reach
    exact ⟨⟨H, hH, s, Nat.le_antisymm up (down H hH s)⟩, down⟩
  · rintro ⟨⟨H, hH, s, e⟩, lo⟩
    refine ⟨⟨H.plainSt, (Same.same3 (same_plainSt H).symm).trans s, e ▸ (reach_plainSt hH).reach⟩, ?_⟩
    intro K k sK r
    have hK := r.wf empty_wf
    have a := lo K hK sK
    have b := r.phi_le
    rw [phi_empty] at b
    omega

/-! ## Sums over the pairs of terms -/

/-- `f 0 + … + f (n − 1)`. -/
def rsum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => rsum f k + f k

/-- The sum of `f x y` over the pairs of terms `x, y < n`. -/
def dsum (f : Nat → Nat → Nat) (n : Nat) : Nat := rsum (fun x => rsum (fun y => f x y) n) n

theorem rsum_congr {f g : Nat → Nat} : ∀ n, (∀ k, k < n → f k = g k) → rsum f n = rsum g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [rsum]
    rw [rsum_congr n (fun k hk => h k (by omega)), h n (by omega)]

theorem rsum_add (f g : Nat → Nat) : ∀ n, rsum (fun k => f k + g k) n = rsum f n + rsum g n
  | 0 => rfl
  | n + 1 => by
    simp only [rsum]
    rw [rsum_add f g n]
    omega

theorem rsum_point (y0 c : Nat) : ∀ n, rsum (fun y => if y = y0 then c else 0) n = if y0 < n then c else 0
  | 0 => by rw [if_neg (Nat.not_lt_zero _)]; rfl
  | n + 1 => by
    simp only [rsum]
    rw [rsum_point y0 c n]
    by_cases h1 : y0 < n
    · rw [if_pos h1, if_neg (show ¬ n = y0 by omega), if_pos (show y0 < n + 1 by omega)]
      omega
    · by_cases h2 : n = y0
      · rw [if_neg h1, if_pos h2, if_pos (show y0 < n + 1 by omega)]
        omega
      · rw [if_neg h1, if_neg h2, if_neg (show ¬ y0 < n + 1 by omega)]

theorem dsum_congr {f g : Nat → Nat → Nat} (n : Nat) (h : ∀ x y, x < n → y < n → f x y = g x y) :
    dsum f n = dsum g n :=
  rsum_congr n (fun x hx => rsum_congr n (fun y hy => h x y hx hy))

theorem dsum_add (f g : Nat → Nat → Nat) (n : Nat) :
    dsum (fun x y => f x y + g x y) n = dsum f n + dsum g n := by
  unfold dsum
  rw [← rsum_add]
  exact rsum_congr n (fun x _ => rsum_add _ _ n)

theorem dsum_zero (n : Nat) : dsum (fun _ _ => 0) n = 0 := by
  unfold dsum
  have : ∀ m, rsum (fun _ => 0) m = 0 := fun m => by
    induction m with
    | zero => rfl
    | succ m ih => simp only [rsum, ih]
  rw [rsum_congr n (fun x _ => this n), this n]

theorem dsum_point {x0 y0 n : Nat} (hx : x0 < n) (hy : y0 < n) :
    dsum (fun x y => if x = x0 ∧ y = y0 then 1 else 0) n = 1 := by
  unfold dsum
  have inner : ∀ x, x < n → rsum (fun y => if x = x0 ∧ y = y0 then 1 else 0) n = if x = x0 then 1 else 0 := by
    intro x _
    by_cases e : x = x0
    · rw [if_pos e, rsum_congr n (g := fun y => if y = y0 then 1 else 0) (fun y _ => by
        by_cases e' : y = y0
        · rw [if_pos ⟨e, e'⟩, if_pos e']
        · rw [if_neg (fun h => e' h.2), if_neg e']), rsum_point, if_pos hy]
    · rw [if_neg e, rsum_congr n (g := fun _ => 0) (fun y _ => by rw [if_neg (fun h => e h.1)])]
      have : ∀ m, rsum (fun _ => 0) m = 0 := fun m => by
        induction m with
        | zero => rfl
        | succ m ih => simp only [rsum, ih]
      exact this n
  rw [rsum_congr n inner, rsum_point, if_pos hx]

theorem atom_ind (a : Atom) (x y : Nat) :
    (if a = ⟨.r, x, y⟩ then 1 else 0) + (if a = ⟨.s, x, y⟩ then 1 else 0) =
      (if x = a.x ∧ y = a.y then 1 else 0 : Nat) := by
  obtain ⟨q, ax, ay⟩ := a
  show (if (⟨q, ax, ay⟩ : Atom) = ⟨.r, x, y⟩ then 1 else 0) + (if (⟨q, ax, ay⟩ : Atom) = ⟨.s, x, y⟩ then 1 else 0) =
    (if x = ax ∧ y = ay then 1 else 0 : Nat)
  by_cases hx : x = ax
  · by_cases hy : y = ay
    · subst hx
      subst hy
      cases q
      · rw [if_pos rfl, if_neg atom_rs, if_pos ⟨rfl, rfl⟩]
      · rw [if_neg atom_sr, if_pos rfl, if_pos ⟨rfl, rfl⟩]
    · cases q
      · rw [if_neg (show ¬ ((⟨.r, ax, ay⟩ : Atom) = ⟨.r, x, y⟩) from fun h => hy (atom_rr.1 h).2.symm),
          if_neg atom_rs, if_neg (show ¬ (x = ax ∧ y = ay) from fun h => hy h.2)]
      · rw [if_neg atom_sr,
          if_neg (show ¬ ((⟨.s, ax, ay⟩ : Atom) = ⟨.s, x, y⟩) from fun h => hy (atom_ss.1 h).2.symm),
          if_neg (show ¬ (x = ax ∧ y = ay) from fun h => hy h.2)]
  · cases q
    · rw [if_neg (show ¬ ((⟨.r, ax, ay⟩ : Atom) = ⟨.r, x, y⟩) from fun h => hx (atom_rr.1 h).1.symm),
        if_neg atom_rs, if_neg (show ¬ (x = ax ∧ y = ay) from fun h => hx h.1)]
    · rw [if_neg atom_sr,
        if_neg (show ¬ ((⟨.s, ax, ay⟩ : Atom) = ⟨.s, x, y⟩) from fun h => hx (atom_ss.1 h).1.symm),
        if_neg (show ¬ (x = ax ∧ y = ay) from fun h => hx h.1)]

/-- The length of a list of atoms between terms `< n` is the sum of its counts over the pairs. -/
theorem length_eq_dsum (n : Nat) :
    ∀ l : List Atom, (∀ a ∈ l, a.x < n ∧ a.y < n) →
      l.length = dsum (fun x y => l.count ⟨.r, x, y⟩ + l.count ⟨.s, x, y⟩) n
  | [], _ => by
    have e := dsum_congr (f := fun x y => List.count (⟨.r, x, y⟩ : Atom) ([] : List Atom) +
      List.count (⟨.s, x, y⟩ : Atom) ([] : List Atom)) (g := fun _ _ => 0) n (fun _ _ _ _ => rfl)
    rw [e, dsum_zero]
    rfl
  | a :: t, h => by
    have ih := length_eq_dsum n t (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a List.mem_cons_self
    have e : dsum (fun x y => (a :: t).count ⟨.r, x, y⟩ + (a :: t).count ⟨.s, x, y⟩) n =
        dsum (fun x y => (t.count ⟨.r, x, y⟩ + t.count ⟨.s, x, y⟩) +
          (if x = a.x ∧ y = a.y then 1 else 0)) n := by
      refine dsum_congr n (fun x y _ _ => ?_)
      rw [count_cons', count_cons', ← atom_ind a x y]
      omega
    rw [e, dsum_add, dsum_point ha.1 ha.2, ← ih, List.length_cons]

/-- **`phi` is the terms plus `Σ |e(x, y)|` over the pairs of terms.** -/
theorem phi_eq_sum {G : St} (hw : G.WF) : phi G = G.n + dsum (fun x y => (excess G x y).natAbs) G.n := by
  unfold phi
  rw [length_eq_dsum G.n (plain G.A) (fun a ha => hw a (mem_of_mem_plain ha))]
  congr 1
  refine dsum_congr _ (fun x y _ _ => ?_)
  rw [count_plain, count_plain]
  simp only [Atom.partner, Rel.other, excess]
  omega

/-- The count of the state moved by `g`: `Σ |e(x, y) + g x − g y|`. -/
def shiftSum (G : St) (g : Nat → Int) : Nat := dsum (fun x y => (excess G x y + (g x - g y)).natAbs) G.n

theorem phi_of_same3 {G H : St} (hH : H.WF) (s : Same3 H G) : ∃ g, phi H = G.n + shiftSum G g := by
  obtain ⟨hn, g, hg⟩ := s
  refine ⟨g, ?_⟩
  rw [phi_eq_sum hH, hn]
  unfold shiftSum
  congr 1
  refine dsum_congr _ (fun x y hx hy => ?_)
  rw [hg x y (hn ▸ hx) (hn ▸ hy)]

/-- `g` moved up to be at least zero on the terms `x < n`, as a whole number of raisings. -/
def lift (g : Nat → Int) (n : Nat) : Nat → Nat := fun x => (g x - lowBound g n).toNat

theorem lift_eq (g : Nat → Int) {n x : Nat} (hx : x < n) : (lift g n x : Int) = g x - lowBound g n := by
  have := lowBound_le g n x hx
  simp only [lift]
  omega

theorem state_of_shift {G : St} (hG : G.WF) (g : Nat → Int) :
    ∃ H, H.WF ∧ Same3 H G ∧ phi H = G.n + shiftSum G g := by
  have hR : (raiseTo G (lift g G.n) G.n).WF := raiseTo_wf _ hG G.n (Nat.le_refl _)
  have hRn : (raiseTo G (lift g G.n) G.n).n = G.n := raiseTo_n G _ G.n
  refine ⟨(raiseTo G (lift g G.n) G.n).plainSt, plainSt_wf hR,
    (Same.same3 (same_plainSt _).symm).trans (Gen3.same3 (gen3_raiseTo G _ G.n (Nat.le_refl _))).symm, ?_⟩
  rw [(same_plainSt _).phi.symm, phi_eq_sum hR, hRn]
  unfold shiftSum
  congr 1
  refine dsum_congr _ (fun x y hx hy => ?_)
  rw [excess_raiseTo_all G _ x y hx hy, lift_eq g hx, lift_eq g hy]
  congr 1
  omega

/-- **The fewest changes to a result: `n + min_g Σ |e(x, y) + g x − g y|`.** -/
theorem cost3_iff_min {G : St} (hG : G.WF) {c : Nat} :
    Cost3 G c ↔ (∃ g, c = G.n + shiftSum G g) ∧ ∀ g, c ≤ G.n + shiftSum G g := by
  rw [cost3_iff]
  constructor
  · rintro ⟨⟨H, hH, s, e⟩, lo⟩
    obtain ⟨g, hg⟩ := phi_of_same3 hH s
    refine ⟨⟨g, e ▸ hg⟩, fun g' => ?_⟩
    obtain ⟨K, hK, sK, eK⟩ := state_of_shift hG g'
    rw [← eK]
    exact lo K hK sK
  · rintro ⟨⟨g, e⟩, lo⟩
    obtain ⟨H, hH, s, eH⟩ := state_of_shift hG g
    refine ⟨⟨H, hH, s, eH.trans e.symm⟩, fun K hK sK => ?_⟩
    obtain ⟨g', hg'⟩ := phi_of_same3 hK sK
    rw [hg']
    exact lo g'

theorem dsum_two (f : Nat → Nat → Nat) : dsum f 2 = f 0 0 + f 0 1 + (f 1 0 + f 1 1) := by
  simp only [dsum, rsum]
  omega

theorem dsum_three (f : Nat → Nat → Nat) :
    dsum f 3 = f 0 0 + f 0 1 + f 0 2 + (f 1 0 + f 1 1 + f 1 2) + (f 2 0 + f 2 1 + f 2 2) := by
  simp only [dsum, rsum]
  omega

theorem natAbs_add2 (a b : Int) : (a + b).natAbs ≤ a.natAbs + b.natAbs := by omega

theorem natAbs_add3 (a b c : Int) : (a + b + c).natAbs ≤ a.natAbs + b.natAbs + c.natAbs := by omega

/-- **With two terms the cost is `2 + |e(0, 0)| + |e(1, 1)| + |e(0, 1) + e(1, 0)|`.** -/
theorem cost3_two {G : St} (hG : G.WF) (hn : G.n = 2) :
    Cost3 G (2 + (excess G 0 0).natAbs + (excess G 1 1).natAbs + (excess G 0 1 + excess G 1 0).natAbs) := by
  rw [cost3_iff_min hG]
  refine ⟨⟨fun x => if x = 1 then - excess G 1 0 else 0, ?_⟩, fun g => ?_⟩
  · unfold shiftSum
    rw [hn, dsum_two]
    show _ = 2 + ((excess G 0 0 + (0 - 0)).natAbs + (excess G 0 1 + (0 - - excess G 1 0)).natAbs +
      ((excess G 1 0 + (- excess G 1 0 - 0)).natAbs + (excess G 1 1 + (- excess G 1 0 - - excess G 1 0)).natAbs))
    have h1 : excess G 0 0 + (0 - 0) = excess G 0 0 := by omega
    have h2 : excess G 0 1 + (0 - - excess G 1 0) = excess G 0 1 + excess G 1 0 := by omega
    have h3 : excess G 1 0 + (- excess G 1 0 - 0) = 0 := by omega
    have h4 : excess G 1 1 + (- excess G 1 0 - - excess G 1 0) = excess G 1 1 := by omega
    rw [h1, h2, h3, h4]
    omega
  · unfold shiftSum
    rw [hn, dsum_two]
    have t := natAbs_add2 (excess G 0 1 + (g 0 - g 1)) (excess G 1 0 + (g 1 - g 0))
    have e : excess G 0 1 + (g 0 - g 1) + (excess G 1 0 + (g 1 - g 0)) = excess G 0 1 + excess G 1 0 := by omega
    rw [e] at t
    have l0 : (excess G 0 0 + (g 0 - g 0)).natAbs = (excess G 0 0).natAbs := by rw [Int.sub_self, Int.add_zero]
    have l1 : (excess G 1 1 + (g 1 - g 1)).natAbs = (excess G 1 1).natAbs := by rw [Int.sub_self, Int.add_zero]
    show _ ≤ 2 + ((excess G 0 0 + (g 0 - g 0)).natAbs + (excess G 0 1 + (g 0 - g 1)).natAbs +
      ((excess G 1 0 + (g 1 - g 0)).natAbs + (excess G 1 1 + (g 1 - g 1)).natAbs))
    rw [l0, l1]
    omega

theorem sum_nine_ge (a00 a01 a02 a10 a11 a12 a20 a21 a22 u v : Nat) (hu : u ≤ a01 + a12 + a20)
    (hv : v ≤ a02 + a21 + a10) : 3 + u + v ≤ 3 + (a00 + a01 + a02 + (a10 + a11 + a12) + (a20 + a21 + a22)) := by
  omega

/-- **With three terms the sums around the terms, both ways round, bound the cost below.** -/
theorem phi_ge_around {H : St} (hH : H.WF) (hn : H.n = 3) :
    3 + (excess H 0 1 + excess H 1 2 + excess H 2 0).natAbs + (excess H 0 2 + excess H 2 1 + excess H 1 0).natAbs
      ≤ phi H := by
  rw [phi_eq_sum hH, hn, dsum_three]
  exact sum_nine_ge _ _ _ _ _ _ _ _ _ _ _ (natAbs_add3 _ _ _) (natAbs_add3 _ _ _)

theorem cost3_three_ge {G : St} (hG : G.WF) (hn : G.n = 3) {c : Nat} (h : Cost3 G c) :
    3 + (excess G 0 1 + excess G 1 2 + excess G 2 0).natAbs + (excess G 0 2 + excess G 2 1 + excess G 1 0).natAbs
      ≤ c := by
  obtain ⟨⟨H, hH, s, e⟩, _⟩ := cost3_iff.1 h
  have hHn : H.n = 3 := s.n.trans hn
  have a := s.around (x := 0) (y := 1) (z := 2) (by omega) (by omega) (by omega)
  have b := s.around (x := 0) (y := 2) (z := 1) (by omega) (by omega) (by omega)
  have := phi_ge_around hH hHn
  have := hG
  omega

/-- `a b c; arb(2) brc(2) cra(2) asc bsa csb`. -/
def triTwelve : St :=
  ⟨3, [⟨.r, 0, 1⟩, ⟨.r, 0, 1⟩, ⟨.r, 1, 2⟩, ⟨.r, 1, 2⟩, ⟨.r, 2, 0⟩, ⟨.r, 2, 0⟩, ⟨.s, 1, 0⟩, ⟨.s, 2, 1⟩, ⟨.s, 0, 2⟩]⟩

/-- `a b c; arb brc cra`. -/
def triSix : St := ⟨3, [⟨.r, 0, 1⟩, ⟨.r, 1, 2⟩, ⟨.r, 2, 0⟩]⟩

theorem triTwelve_wf : triTwelve.WF := by
  intro a ha
  simp only [triTwelve, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h | h | h | h | h | h | h | h <;> subst h <;> decide

theorem triSix_wf : triSix.WF := by
  intro a ha
  simp only [triSix, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h | h <;> subst h <;> decide

theorem cost3_of_phi_le {G : St} (hG : G.WF) {c : Nat} (hc : phi G = c) (lo : ∀ c', Cost3 G c' → c ≤ c')
    (ex : ∃ c', Cost3 G c') : Cost3 G c := by
  obtain ⟨c', h'⟩ := ex
  have := lo c' h'
  have := (cost3_iff.1 h').2 G hG (Same3.refl G)
  have e : c' = c := by omega
  exact e ▸ h'

/-- **The loops and the two-way sums do not fix the cost**: two results with the same loops (zero) and the
same two-way sums (one each), the first costing 12 changes, the second 6. -/
theorem loops_and_two_way_do_not_fix_the_cost :
    (∀ x, x < 3 → excess triTwelve x x = excess triSix x x) ∧
    (∀ x y, x < 3 → y < 3 → excess triTwelve x y + excess triTwelve y x = excess triSix x y + excess triSix y x) ∧
    Cost3 triTwelve 12 ∧ Cost3 triSix 6 := by
  refine ⟨fun x hx => ?_, fun x y hx hy => ?_, ?_, ?_⟩
  · have : x = 0 ∨ x = 1 ∨ x = 2 := by omega
    rcases this with rfl | rfl | rfl <;> decide
  · have hx' : x = 0 ∨ x = 1 ∨ x = 2 := by omega
    have hy' : y = 0 ∨ y = 1 ∨ y = 2 := by omega
    rcases hx' with rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl <;> decide
  · refine cost3_iff.2 ⟨⟨triTwelve, triTwelve_wf, Same3.refl _, by decide⟩, fun H hH s => ?_⟩
    have hn : H.n = 3 := s.n
    have a := s.around (x := 0) (y := 1) (z := 2) (by omega) (by omega) (by omega)
    have b := s.around (x := 0) (y := 2) (z := 1) (by omega) (by omega) (by omega)
    have c := phi_ge_around hH hn
    have e1 : excess triTwelve 0 1 + excess triTwelve 1 2 + excess triTwelve 2 0 = 6 := by decide
    have e2 : excess triTwelve 0 2 + excess triTwelve 2 1 + excess triTwelve 1 0 = -3 := by decide
    omega
  · refine cost3_iff.2 ⟨⟨triSix, triSix_wf, Same3.refl _, by decide⟩, fun H hH s => ?_⟩
    have hn : H.n = 3 := s.n
    have a := s.around (x := 0) (y := 1) (z := 2) (by omega) (by omega) (by omega)
    have b := s.around (x := 0) (y := 2) (z := 1) (by omega) (by omega) (by omega)
    have c := phi_ge_around hH hn
    have e1 : excess triSix 0 1 + excess triSix 1 2 + excess triSix 2 0 = 3 := by decide
    have e2 : excess triSix 0 2 + excess triSix 2 1 + excess triSix 1 0 = 0 := by decide
    omega

/-! ## Parity -/

theorem gen_size_parity {G H : St} (h : Gen G H) : G.size % 2 = H.size % 2 := by
  induction h with
  | perm hn hp =>
    simp only [St.size, hn, hp.length_eq]
  | pair G x y _ _ =>
    simp only [St.size, List.length_cons]
    omega
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem Gen3.size_parity {G H : St} (h : Gen3 G H) : G.size % 2 = H.size % 2 := by
  induction h with
  | gen g => exact gen_size_parity g
  | raise G x hx =>
    rw [raise_size G x hx]
    omega
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **The parity of the size is a mark of the result.** -/
theorem Same3.size_parity {G H : St} (hG : G.WF) (hH : H.WF) (h : Same3 G H) : G.size % 2 = H.size % 2 :=
  ((gen3_iff_same3 hG hH).2 h).size_parity

/-- **No change returns a state to its own result.** -/
theorem Step.not_same3 {G H : St} (st : Step G H) (hG : G.WF) : ¬ Same3 G H := by
  intro h
  have := h.size_parity hG (st.wf hG)
  rcases st.size_step with ⟨e, _⟩ | e <;> omega

/-- The cost of a result has the parity of the size of any of its states. -/
theorem Cost3.parity {G : St} (hG : G.WF) {c : Nat} (h : Cost3 G c) : c % 2 = G.size % 2 := by
  obtain ⟨⟨H, hH, s, e⟩, _⟩ := cost3_iff.1 h
  have a := phi_parity_size H
  have b := s.size_parity hH hG
  omega

/-- **Every change changes the cost of the result by an odd number.** -/
theorem Step.cost3_odd {G H : St} (st : Step G H) (hG : G.WF) {c c' : Nat} (h : Cost3 G c) (h' : Cost3 H c') :
    (c + c') % 2 = 1 := by
  have a := h.parity hG
  have b := h'.parity (st.wf hG)
  rcases st.size_step with ⟨e, _⟩ | e <;> omega

/-- **A change performed on a state asserting the fewest raises the cost by at most one.** -/
theorem Step.cost3_le {G H : St} (st : Step G H) (hG : G.WF) (h : Cost3 G (phi G)) {c' : Nat}
    (h' : Cost3 H c') : c' ≤ phi G + 1 := by
  have a := (cost3_iff.1 h').2 H (st.wf hG) (Same3.refl H)
  have b := st.phi_le
  have := h
  omega

/-! ## Adding a term to a state that does not assert the fewest -/

theorem count_replicate_self' (a : Atom) : ∀ k, (List.replicate k a).count a = k
  | 0 => rfl
  | k + 1 => by rw [List.replicate_succ, count_cons_self', count_replicate_self' a k]

theorem count_replicate_ne' {a b : Atom} (h : a ≠ b) : ∀ k, (List.replicate k a).count b = 0
  | 0 => rfl
  | k + 1 => by rw [List.replicate_succ, count_cons_ne' _ h, count_replicate_ne' h k]

/-- `a b; arb(k) bsa(k)`: two terms, `a` raised `k` times — the result asserting nothing on two terms. -/
def pairK (k : Nat) : St := ⟨2, List.replicate k ⟨.r, 0, 1⟩ ++ List.replicate k ⟨.s, 1, 0⟩⟩

theorem count_pairK_r (k x y : Nat) :
    (List.replicate k (⟨.r, 0, 1⟩ : Atom) ++ List.replicate k (⟨.s, 1, 0⟩ : Atom)).count (⟨.r, x, y⟩ : Atom) =
      if x = 0 ∧ y = 1 then k else 0 := by
  rw [List.count_append, count_replicate_ne' atom_sr, Nat.add_zero]
  by_cases hx : x = 0
  · by_cases hy : y = 1
    · subst hx
      subst hy
      rw [count_replicate_self', if_pos (show (0 : Nat) = 0 ∧ (1 : Nat) = 1 from ⟨rfl, rfl⟩)]
    · rw [count_replicate_ne' (show (⟨.r, 0, 1⟩ : Atom) ≠ ⟨.r, x, y⟩ from fun h => hy (atom_rr.1 h).2.symm),
        if_neg (show ¬ (x = 0 ∧ y = 1) from fun h => hy h.2)]
  · rw [count_replicate_ne' (show (⟨.r, 0, 1⟩ : Atom) ≠ ⟨.r, x, y⟩ from fun h => hx (atom_rr.1 h).1.symm),
      if_neg (show ¬ (x = 0 ∧ y = 1) from fun h => hx h.1)]

theorem count_pairK_s (k x y : Nat) :
    (List.replicate k (⟨.r, 0, 1⟩ : Atom) ++ List.replicate k (⟨.s, 1, 0⟩ : Atom)).count (⟨.s, x, y⟩ : Atom) =
      if x = 1 ∧ y = 0 then k else 0 := by
  rw [List.count_append, count_replicate_ne' atom_rs, Nat.zero_add]
  by_cases hx : x = 1
  · by_cases hy : y = 0
    · subst hx
      subst hy
      rw [count_replicate_self', if_pos (show (1 : Nat) = 1 ∧ (0 : Nat) = 0 from ⟨rfl, rfl⟩)]
    · rw [count_replicate_ne' (show (⟨.s, 1, 0⟩ : Atom) ≠ ⟨.s, x, y⟩ from fun h => hy (atom_ss.1 h).2.symm),
        if_neg (show ¬ (x = 1 ∧ y = 0) from fun h => hy h.2)]
  · rw [count_replicate_ne' (show (⟨.s, 1, 0⟩ : Atom) ≠ ⟨.s, x, y⟩ from fun h => hx (atom_ss.1 h).1.symm),
      if_neg (show ¬ (x = 1 ∧ y = 0) from fun h => hx h.1)]

theorem excess_pairK (k n x y : Nat) :
    excess ⟨n, List.replicate k ⟨.r, 0, 1⟩ ++ List.replicate k ⟨.s, 1, 0⟩⟩ x y =
      ((if x = 0 ∧ y = 1 then k else 0 : Nat) : Int) - ((if x = 1 ∧ y = 0 then k else 0 : Nat) : Int) := by
  unfold excess
  rw [count_pairK_r, count_pairK_s]

theorem pairK_wf (k : Nat) (n : Nat) (hn : 2 ≤ n) :
    St.WF ⟨n, List.replicate k ⟨.r, 0, 1⟩ ++ List.replicate k ⟨.s, 1, 0⟩⟩ := by
  intro a ha
  rcases List.mem_append.1 ha with h | h
  · rw [List.eq_of_mem_replicate h]
    exact ⟨by show 0 < n; omega, by show 1 < n; omega⟩
  · rw [List.eq_of_mem_replicate h]
    exact ⟨by show 1 < n; omega, by show 0 < n; omega⟩

theorem pairK_nothing (k : Nat) : Same3 (pairK k) ⟨2, []⟩ :=
  ⟨rfl, fun x => if x = 0 then (k : Int) else 0, fun x y hx hy => by
    show excess (pairK k) x y = excess ⟨2, []⟩ x y +
      ((if x = 0 then (k : Int) else 0) - (if y = 0 then (k : Int) else 0))
    rw [excess_nothing, pairK, excess_pairK]
    have hx' : x = 0 ∨ x = 1 := by show x = 0 ∨ x = 1; have : x < 2 := hx; omega
    have hy' : y = 0 ∨ y = 1 := by show y = 0 ∨ y = 1; have : y < 2 := hy; omega
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl <;> simp⟩

theorem plain_pairK (k n : Nat) :
    plain (List.replicate k ⟨.r, 0, 1⟩ ++ List.replicate k ⟨.s, 1, 0⟩) =
      List.replicate k ⟨.r, 0, 1⟩ ++ List.replicate k ⟨.s, 1, 0⟩ := by
  have := n
  apply plain_eq_self
  intro a ha hp
  rcases List.mem_append.1 ha with h | h <;> rcases List.mem_append.1 hp with h' | h' <;>
    rw [List.eq_of_mem_replicate h] at h' <;> have := List.eq_of_mem_replicate h' <;>
    simp [Atom.partner, Rel.other] at this

/-- **Adding a term can raise the cost by `2k + 1`, for every `k`**: `a b; arb(k) bsa(k)` is the result
asserting nothing on two terms (cost 2); with a term added it costs `3 + 2k`. -/
theorem adding_a_term_raises_the_cost (k : Nat) : Cost3 (pairK k) 2 ∧ Cost3 (pairK k).addTerm (3 + 2 * k) := by
  have w2 : St.WF ⟨2, ([] : List Atom)⟩ := fun _ h => absurd h List.not_mem_nil
  have c2 : Cost3 (⟨2, []⟩ : St) 2 := cost3_two w2 rfl
  refine ⟨(Cost3.congr (pairK_nothing k)).2 c2, ?_⟩
  have hw : (pairK k).addTerm.WF := pairK_wf k 3 (by omega)
  refine cost3_iff.2 ⟨⟨(pairK k).addTerm, hw, Same3.refl _, ?_⟩, fun H hH s => ?_⟩
  · show 3 + (plain (List.replicate k ⟨.r, 0, 1⟩ ++ List.replicate k ⟨.s, 1, 0⟩)).length = 3 + 2 * k
    rw [plain_pairK k 3, List.length_append, List.length_replicate, List.length_replicate]
    omega
  · have hn : H.n = 3 := s.n
    have a := s.around (x := 0) (y := 1) (z := 2) (by omega) (by omega) (by omega)
    have b := s.around (x := 0) (y := 2) (z := 1) (by omega) (by omega) (by omega)
    have c := phi_ge_around hH hn
    have e : ∀ x y, excess (pairK k).addTerm x y =
        ((if x = 0 ∧ y = 1 then k else 0 : Nat) : Int) - ((if x = 1 ∧ y = 0 then k else 0 : Nat) : Int) :=
      fun x y => excess_pairK k 3 x y
    simp only [e] at a b
    simp at a b
    omega

end Twentythird
