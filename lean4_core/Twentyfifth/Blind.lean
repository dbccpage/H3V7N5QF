import Twentyfifth.Balance

/-!
# Results no filling tells, and filled triples that decide

A result is *blind* when every sum around three different terms, both ways
round, is zero: then every filling balances, and no set of filled triples
tells it from the result asserting nothing.

Derived here:
* **with five terms or more, a blind result with every loop zero is the result
  asserting nothing** (`blind_five`): its two-way sums are zero
  (`blind_twoWay_five`, from the sums around the triples of five terms), and
  then the twenty-third's criterion applies (`same3_nothing_iff`, imported).
  With loops (never gone along, `loop_unseen`) that is all a blind result can
  carry;
* with three terms, blind exactly when the sum around `0, 1, 2` is zero and the
  three two-way sums add up to zero (`blind_three_iff`); with four terms, a
  blind result has equal two-way sums on the two pairs of each split of the
  four terms, the three values adding up to zero (`blind_four`); both happen
  with non-zero two-way sums (`blind_three_not_nothing`, `blind_four_not_nothing`);
* **with every loop and two-way sum zero, the triples through one term
  decide**: if they all balance, the result is the one asserting nothing
  (`cone_decides`); with four terms, three triples through one term decide and
  two do not (`two_triples_do_not_decide`).
-/

namespace Twentyfifth

open Twentysecond Twentythird

/-- Three terms below five, different from each other and from `x` and `y`. -/
theorem three_others (x y : Nat) :
    ∃ z w v : Nat, z < 5 ∧ w < 5 ∧ v < 5 ∧ z ≠ x ∧ z ≠ y ∧ w ≠ x ∧ w ≠ y ∧ v ≠ x ∧ v ≠ y ∧
      z ≠ w ∧ z ≠ v ∧ w ≠ v := by
  have hx : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ 5 ≤ x := by omega
  have hy : y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 ∨ 5 ≤ y := by omega
  rcases hx with rfl | rfl | rfl | rfl | rfl | hx <;> rcases hy with rfl | rfl | rfl | rfl | rfl | hy <;>
    first
    | exact ⟨2, 3, 4, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega⟩
    | exact ⟨1, 3, 4, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega⟩
    | exact ⟨1, 2, 4, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega⟩
    | exact ⟨1, 2, 3, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega⟩
    | exact ⟨0, 3, 4, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega⟩
    | exact ⟨0, 2, 4, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega⟩
    | exact ⟨0, 2, 3, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega⟩
    | exact ⟨0, 1, 4, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega⟩
    | exact ⟨0, 1, 3, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega⟩
    | exact ⟨0, 1, 2, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega⟩

/-- Every sum around three different terms of `G`, both ways round, is zero. -/
def Blind (G : St) : Prop :=
  ∀ x y z, x < G.n → y < G.n → z < G.n → x ≠ y → y ≠ z → x ≠ z → around G ⟨x, y, z⟩ = 0

/-- A blind result balances every triple that can be filled: no filling tells it. -/
theorem Blind.balanced {G : St} (h : Blind G) {t : Tri} (hw : t.Within G.n) (hd : t.Distinct) : Balanced G t :=
  h t.x t.y t.z hw.1 hw.2.1 hw.2.2 hd.1 hd.2.1 hd.2.2

/-- **With five terms or more, a blind result has every two-way sum zero.** -/
theorem blind_twoWay_five {G : St} (hn : 5 ≤ G.n) (h : Blind G) {x y : Nat} (hx : x < G.n) (hy : y < G.n)
    (hxy : x ≠ y) : excess G x y + excess G y x = 0 := by
  obtain ⟨z, w, v, hz, hw, hv, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := three_others x y
  have t1 := h x y z hx hy (by omega) hxy (by omega) (by omega)
  have t2 := h x z y hx (by omega) hy (by omega) (by omega) hxy
  have t3 := h x y w hx hy (by omega) hxy (by omega) (by omega)
  have t4 := h x w y hx (by omega) hy (by omega) (by omega) hxy
  have t5 := h x y v hx hy (by omega) hxy (by omega) (by omega)
  have t6 := h x v y hx (by omega) hy (by omega) (by omega) hxy
  have t7 := h x z w hx (by omega) (by omega) (by omega) (by omega) (by omega)
  have t8 := h x w z hx (by omega) (by omega) (by omega) (by omega) (by omega)
  have t9 := h x z v hx (by omega) (by omega) (by omega) (by omega) (by omega)
  have t10 := h x v z hx (by omega) (by omega) (by omega) (by omega) (by omega)
  have t11 := h x w v hx (by omega) (by omega) (by omega) (by omega) (by omega)
  have t12 := h x v w hx (by omega) (by omega) (by omega) (by omega) (by omega)
  have t13 := h y z w hy (by omega) (by omega) (by omega) (by omega) (by omega)
  have t14 := h y w z hy (by omega) (by omega) (by omega) (by omega) (by omega)
  have t15 := h y z v hy (by omega) (by omega) (by omega) (by omega) (by omega)
  have t16 := h y v z hy (by omega) (by omega) (by omega) (by omega) (by omega)
  have t17 := h y w v hy (by omega) (by omega) (by omega) (by omega) (by omega)
  have t18 := h y v w hy (by omega) (by omega) (by omega) (by omega) (by omega)
  have t19 := h z w v (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have t20 := h z v w (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  simp only [around] at t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 t16 t17 t18 t19 t20
  omega

/-- **With five terms or more, a blind result whose loops are zero is the result asserting nothing**: with
five terms or more, what no filling can tell from nothing lies at the loops only. -/
theorem blind_five {G : St} (hn : 5 ≤ G.n) (h : Blind G) (hl : ∀ x, x < G.n → excess G x x = 0) :
    Same3 G ⟨G.n, []⟩ := by
  have h2 : ∀ x y, x < G.n → y < G.n → excess G x y + excess G y x = 0 := by
    intro x y hx hy
    by_cases e : x = y
    · subst e
      have := hl x hx
      omega
    · exact blind_twoWay_five hn h hx hy e
  refine (same3_nothing_iff G).2 ⟨hl, h2, fun x y z hx hy hz => ?_⟩
  by_cases e1 : x = y
  · subst e1
    have a := hl x hx
    have b := h2 x z hx hz
    omega
  · by_cases e2 : y = z
    · subst e2
      have a := hl y hy
      have b := h2 x y hx hy
      omega
    · by_cases e3 : x = z
      · subst e3
        have a := hl x hx
        have b := h2 x y hx hy
        omega
      · have := h x y z hx hy hz e1 e2 e3
        simp only [around] at this
        exact this

/-- **With three terms, blind exactly when the sum around `0, 1, 2` is zero and the two-way sums add up to
zero** (the sum the other way round is their total less the first). -/
theorem blind_three_iff (G : St) :
    (around G ⟨0, 1, 2⟩ = 0 ∧ around G ⟨0, 2, 1⟩ = 0) ↔
      (around G ⟨0, 1, 2⟩ = 0 ∧
        (excess G 0 1 + excess G 1 0) + (excess G 1 2 + excess G 2 1) + (excess G 0 2 + excess G 2 0) = 0) := by
  simp only [around]
  constructor
  · rintro ⟨a, b⟩
    exact ⟨a, by omega⟩
  · rintro ⟨a, b⟩
    exact ⟨a, by omega⟩

/-- **With four terms, a blind result has equal two-way sums on the two pairs of each split of the four
terms, the three values adding up to zero.** -/
theorem blind_four {G : St} (hn : G.n = 4) (h : Blind G) :
    excess G 0 1 + excess G 1 0 = excess G 2 3 + excess G 3 2 ∧
      excess G 0 2 + excess G 2 0 = excess G 1 3 + excess G 3 1 ∧
      excess G 0 3 + excess G 3 0 = excess G 1 2 + excess G 2 1 ∧
      (excess G 0 1 + excess G 1 0) + (excess G 0 2 + excess G 2 0) + (excess G 0 3 + excess G 3 0) = 0 := by
  have t1 := h 0 1 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have t2 := h 0 2 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have t3 := h 0 1 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have t4 := h 0 3 1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have t5 := h 0 2 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have t6 := h 0 3 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have t7 := h 1 2 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have t8 := h 1 3 2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  simp only [around] at t1 t2 t3 t4 t5 t6 t7 t8
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- `a b c d; bra crd asc dsb`: every sum around zero, the two-way sums one, minus one and zero on the three
splits. -/
def blindFour : St := ⟨4, [⟨.r, 1, 0⟩, ⟨.r, 2, 3⟩, ⟨.s, 0, 2⟩, ⟨.s, 3, 1⟩]⟩

theorem lt_four {x : Nat} (h : x < 4) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega

/-- **A four-term blind result with no loop that is not the result asserting nothing.** -/
theorem blind_four_not_nothing : Blind blindFour ∧ ¬ Same3 blindFour ⟨4, []⟩ := by
  refine ⟨fun x y z hx hy hz d1 d2 d3 => ?_, fun s => ?_⟩
  · have hx' : x < 4 := hx
    have hy' : y < 4 := hy
    have hz' : z < 4 := hz
    rcases lt_four hx' with rfl | rfl | rfl | rfl <;> rcases lt_four hy' with rfl | rfl | rfl | rfl <;>
      rcases lt_four hz' with rfl | rfl | rfl | rfl <;> first | decide | (exfalso; omega)
  · have := s.twoWay (x := 0) (y := 1) (by show (0 : Nat) < 4; decide) (by show (1 : Nat) < 4; decide)
    exact absurd this (by decide)

theorem blindThree_blind : Blind blindThree := by
  intro x y z hx hy hz d1 d2 d3
  have hx' : x < 3 := hx
  have hy' : y < 3 := hy
  have hz' : z < 3 := hz
  rcases lt_three hx' with rfl | rfl | rfl <;> rcases lt_three hy' with rfl | rfl | rfl <;>
    rcases lt_three hz' with rfl | rfl | rfl <;> first | decide | (exfalso; omega)

/-- **With every loop and every two-way sum zero, the triples through one term decide**: if every triple
through `c` balances, the result is the one asserting nothing. -/
theorem cone_decides {G : St} {c : Nat} (hc : c < G.n) (hl : ∀ x, x < G.n → excess G x x = 0)
    (h2 : ∀ x y, x < G.n → y < G.n → x ≠ y → excess G x y + excess G y x = 0)
    (h3 : ∀ x y, x < G.n → y < G.n → c ≠ x → c ≠ y → x ≠ y → around G ⟨c, x, y⟩ = 0) :
    Same3 G ⟨G.n, []⟩ := by
  have s2 : ∀ x y, x < G.n → y < G.n → excess G x y + excess G y x = 0 := by
    intro x y hx hy
    by_cases e : x = y
    · subst e
      have := hl x hx
      omega
    · exact h2 x y hx hy e
  have p : ∀ a b, a < G.n → b < G.n → excess G c a + excess G a b + excess G b c = 0 := by
    intro a b ha hb
    by_cases e1 : c = a
    · subst e1
      have := hl c hc
      have := s2 b c hb hc
      omega
    · by_cases e2 : c = b
      · subst e2
        have := s2 c a hc ha
        have := hl c hc
        omega
      · by_cases e3 : a = b
        · subst e3
          have := s2 c a hc ha
          have := hl a ha
          omega
        · have := h3 a b ha hb e1 e2 e3
          simp only [around] at this
          exact this
  refine (same3_nothing_iff G).2 ⟨hl, s2, fun x y z hx hy hz => ?_⟩
  have a := p x y hx hy
  have b := p y z hy hz
  have d := p z x hz hx
  have sx := s2 c x hc hx
  have sy := s2 c y hc hy
  have sz := s2 c z hc hz
  omega

/-- `a b c d; crd dsc`: every loop and two-way sum zero; the sums around `a b c` and `a b d` zero, around
`a c d` one. -/
def twoTriples : St := ⟨4, [⟨.r, 2, 3⟩, ⟨.s, 3, 2⟩]⟩

/-- **Two triples through one term do not decide**: `a b c d; crd dsc` balances `a b c` and `a b d`, has
every loop and two-way sum zero, and is not the result asserting nothing; the third triple through `a`
tells it. -/
theorem two_triples_do_not_decide :
    around twoTriples ⟨0, 1, 2⟩ = 0 ∧ around twoTriples ⟨0, 1, 3⟩ = 0 ∧ around twoTriples ⟨0, 2, 3⟩ = 1 ∧
      (∀ x, x < 4 → excess twoTriples x x = 0) ∧
      (∀ x y, x < 4 → y < 4 → excess twoTriples x y + excess twoTriples y x = 0) ∧
      ¬ Same3 twoTriples ⟨4, []⟩ := by
  refine ⟨by decide, by decide, by decide, fun x hx => ?_, fun x y hx hy => ?_, fun s => ?_⟩
  · rcases lt_four hx with rfl | rfl | rfl | rfl <;> decide
  · rcases lt_four hx with rfl | rfl | rfl | rfl <;> rcases lt_four hy with rfl | rfl | rfl | rfl <;> decide
  · have := s.around (x := 0) (y := 2) (z := 3) (by show (0 : Nat) < 4; decide) (by show (2 : Nat) < 4; decide)
      (by show (3 : Nat) < 4; decide)
    exact absurd this (by decide)

end Twentyfifth
