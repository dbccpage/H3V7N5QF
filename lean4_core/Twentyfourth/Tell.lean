import Twentyfourth.Same

/-!
# Which results filled terms that do not balance tell apart from the one asserting nothing

"A result with nothing asserted on as many terms" (reading C-N of the paper):
the same terms, the same filled terms, nothing asserted (`nothingOf`).  A
result is that result exactly when its assertions are the twenty-third's
result asserting nothing (`same24_nothing_iff`, and 23:D2).

The record of which filled terms balance, at a fixed writing (`balRec`): a
term is recorded as a filled term that balances.  Derived here:
* in the result asserting nothing every filled term balances
  (`nothing_balances`);
* **a result is told apart from it by its record exactly when some filled
  term does not balance** — some filled term whose loop's excess is not zero
  (`told_iff`); such a result is not the one asserting nothing
  (`told_not_nothing`);
* **every other result that is not the one asserting nothing is one of three
  kinds** (`not_told_cases`): a loop of non-zero excess only at unfilled terms
  — one filling away from being told (`told_after_fill`); every loop of excess
  zero and some two-way sum not zero; every loop and two-way sum zero and some
  sum around three terms not zero.  In the last two, **no filling ever tells**
  (`never_told_of_loops_zero`);
* witnesses of each kind (`toldOne`, `awayOne`, `twoWayFilled`,
  `aroundFilled`), and an identification that turns a two-term kind into a
  told one (`identify_tells`).
-/

namespace Twentyfourth

open Twentysecond Twentythird

/-- The result with nothing asserted on the terms of `X`, the same terms filled. -/
def nothingOf (X : FSt) : FSt := ⟨⟨X.G.n, []⟩, X.F⟩

theorem same24_nothing_iff (X : FSt) : Same24 X (nothingOf X) ↔ Same3 X.G ⟨X.G.n, []⟩ :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ _ => rfl⟩⟩

/-- **In the result asserting nothing every filled term balances.** -/
theorem nothing_balances (X : FSt) {x : Nat} (hf : X.F x = true) : Balances (nothingOf X) x :=
  ⟨hf, rfl⟩

/-- The record at a fixed writing: `x` is recorded as a filled term that balances. -/
def balRec (X : FSt) (x : Nat) : Bool :=
  X.F x && decide (X.G.A.count ⟨.r, x, x⟩ = X.G.A.count ⟨.s, x, x⟩)

theorem balRec_true {X : FSt} {x : Nat} : balRec X x = true ↔ Balances X x := by
  unfold balRec Balances
  simp only [Bool.and_eq_true, decide_eq_true_eq]

theorem balRec_nothing (X : FSt) (x : Nat) : balRec (nothingOf X) x = X.F x := by
  unfold balRec nothingOf
  cases X.F x <;> rfl

/-- Some filled term does not balance: its loop's excess is not zero. -/
def Told (X : FSt) : Prop := ∃ x, x < X.G.n ∧ X.F x = true ∧ excess X.G x x ≠ 0

/-- **A result is told apart from the one asserting nothing by its record exactly when some filled term
does not balance.** -/
theorem told_iff (X : FSt) : (∃ x, x < X.G.n ∧ balRec X x ≠ balRec (nothingOf X) x) ↔ Told X := by
  constructor
  · rintro ⟨x, hx, hne⟩
    rw [balRec_nothing] at hne
    cases hf : X.F x with
    | false =>
      exfalso
      apply hne
      unfold balRec
      rw [hf]
      rfl
    | true =>
      refine ⟨x, hx, hf, fun e => hne ?_⟩
      rw [hf]
      exact balRec_true.2 (balances_iff.2 ⟨hf, e⟩)
  · rintro ⟨x, hx, hf, he⟩
    refine ⟨x, hx, fun e => he ?_⟩
    rw [balRec_nothing, hf] at e
    exact (balances_iff.1 (balRec_true.1 e)).2

/-- Told is a mark of the result. -/
theorem Same24.told {X Y : FSt} (h : Same24 X Y) : Told X ↔ Told Y := by
  constructor
  · rintro ⟨x, hx, hf, he⟩
    exact ⟨x, h.n ▸ hx, (h.2 x hx) ▸ hf, (h.1.loop hx) ▸ he⟩
  · rintro ⟨x, hx, hf, he⟩
    have hx' : x < X.G.n := h.n ▸ hx
    exact ⟨x, hx', (h.2 x hx').symm ▸ hf, fun e => he ((h.1.loop hx').symm.trans e)⟩

/-- **A told result is not the one asserting nothing.** -/
theorem told_not_nothing {X : FSt} (h : Told X) : ¬ Same3 X.G ⟨X.G.n, []⟩ := by
  intro s
  obtain ⟨x, hx, _, he⟩ := h
  exact he (((same3_nothing_iff X.G).1 s).1 x hx)

/-- **When every loop balances, no filling tells**: whatever terms are filled, every filled term balances. -/
theorem never_told_of_loops_zero {G : St} (h : ∀ x, x < G.n → excess G x x = 0) (F : Nat → Bool) :
    ¬ Told ⟨G, F⟩ := by
  rintro ⟨x, hx, _, he⟩
  exact he (h x hx)

/-- **A loop of non-zero excess at an unfilled term: one filling away from being told.** -/
theorem told_after_fill {X : FSt} {x : Nat} (hx : x < X.G.n) (he : excess X.G x x ≠ 0) : Told (X.fill x) :=
  ⟨x, hx, by simp [FSt.fill], he⟩

/-- **Every result that is not the one asserting nothing, and not told, is one of three kinds.** -/
theorem not_told_cases (X : FSt) (hn : ¬ Same3 X.G ⟨X.G.n, []⟩) (ht : ¬ Told X) :
    (∃ x, x < X.G.n ∧ X.F x = false ∧ excess X.G x x ≠ 0) ∨
    ((∀ x, x < X.G.n → excess X.G x x = 0) ∧
      ∃ x, x < X.G.n ∧ ∃ y, y < X.G.n ∧ excess X.G x y + excess X.G y x ≠ 0) ∨
    ((∀ x, x < X.G.n → excess X.G x x = 0) ∧
      (∀ x y, x < X.G.n → y < X.G.n → excess X.G x y + excess X.G y x = 0) ∧
      ∃ x, x < X.G.n ∧ ∃ y, y < X.G.n ∧ ∃ z, z < X.G.n ∧ excess X.G x y + excess X.G y z + excess X.G z x ≠ 0) := by
  rw [same3_nothing_iff] at hn
  by_cases l0 : ∃ x, x < X.G.n ∧ excess X.G x x ≠ 0
  · -- a loop that is not zero is at an unfilled term, since the result is not told
    obtain ⟨x, hx, he⟩ := l0
    refine Or.inl ⟨x, hx, ?_, he⟩
    cases hf : X.F x with
    | false => rfl
    | true => exact absurd ⟨x, hx, hf, he⟩ ht
  · have l : ∀ x, x < X.G.n → excess X.G x x = 0 := fun x hx => by
      by_cases e : excess X.G x x = 0
      · exact e
      · exact absurd ⟨x, hx, e⟩ l0
    right
    by_cases t : ∃ x, x < X.G.n ∧ ∃ y, y < X.G.n ∧ excess X.G x y + excess X.G y x ≠ 0
    · exact Or.inl ⟨l, t⟩
    · have two : ∀ x y, x < X.G.n → y < X.G.n → excess X.G x y + excess X.G y x = 0 := by
        intro x y hx hy
        by_cases e : excess X.G x y + excess X.G y x = 0
        · exact e
        · exact absurd ⟨x, hx, y, hy, e⟩ t
      refine Or.inr ⟨l, two, ?_⟩
      by_cases a : ∃ x, x < X.G.n ∧ ∃ y, y < X.G.n ∧ ∃ z, z < X.G.n ∧
          excess X.G x y + excess X.G y z + excess X.G z x ≠ 0
      · exact a
      · exfalso
        apply hn
        refine ⟨l, two, fun x y z hx hy hz => ?_⟩
        by_cases e : excess X.G x y + excess X.G y z + excess X.G z x = 0
        · exact e
        · exact absurd ⟨x, hx, y, hy, z, hz, e⟩ a

/-! ## Witnesses -/

/-- `a; ara`, `a` filled: told. -/
def toldOne : FSt := ⟨⟨1, [⟨.r, 0, 0⟩]⟩, fun x => decide (x = 0)⟩

/-- `a b; brb`, `a` filled: not told, one filling away. -/
def awayOne : FSt := ⟨⟨2, [⟨.r, 1, 1⟩]⟩, fun x => decide (x = 0)⟩

/-- `a b; arb`, both filled: every filled term balances, and it is not the one asserting nothing. -/
def twoWayFilled : FSt := ⟨⟨2, [⟨.r, 0, 1⟩]⟩, fun x => decide (x < 2)⟩

/-- `a b c; arb bsa`, all filled: every loop and two-way sum zero, the sum around one. -/
def aroundFilled : FSt := ⟨arcThree, fun x => decide (x < 3)⟩

theorem toldOne_told : Told toldOne := ⟨0, by decide, rfl, by decide⟩

theorem awayOne_not_told : ¬ Told awayOne := by
  rintro ⟨x, hx, hf, he⟩
  have hx' : x < 2 := hx
  rcases lt_two hx' with rfl | rfl
  · exact he (by decide)
  · exact absurd hf (by decide)

theorem awayOne_fill_told : Told (awayOne.fill 1) := told_after_fill (by decide) (by decide)

theorem twoWayFilled_not_nothing : ¬ Same3 twoWayFilled.G ⟨twoWayFilled.G.n, []⟩ := by
  intro s
  have := ((same3_nothing_iff _).1 s).2.1 0 1 (by decide) (by decide)
  exact absurd this (by decide)

/-- **`a b; arb` with both terms filled: not the result asserting nothing, and no filling tells.** -/
theorem twoWayFilled_never_told (F : Nat → Bool) : ¬ Told ⟨twoWayFilled.G, F⟩ :=
  never_told_of_loops_zero (fun x hx => by
    have hx' : x < 2 := hx
    rcases lt_two hx' with rfl | rfl <;> decide) F

/-- **`a b c; arb bsa` with every term filled: not the result asserting nothing, every loop and two-way sum
zero, and no filling tells.** -/
theorem aroundFilled_never_told (F : Nat → Bool) :
    ¬ Same3 aroundFilled.G ⟨aroundFilled.G.n, []⟩ ∧
    (∀ x y, x < 3 → y < 3 → excess arcThree x y + excess arcThree y x = 0) ∧ ¬ Told ⟨arcThree, F⟩ := by
  refine ⟨arcThree_not_nothing, fun x y hx hy => ?_, never_told_of_loops_zero (fun x hx => ?_) F⟩
  · rcases lt_three hx with rfl | rfl | rfl <;> rcases lt_three hy with rfl | rfl | rfl <;> decide
  · have hx' : x < 3 := hx
    rcases lt_three hx' with rfl | rfl | rfl <;> decide

/-- **Identifying the two terms of `a b; arb`, both filled, gives `a; ara` with `a` filled: told.** -/
theorem identify_tells : Step24 twoWayFilled (twoWayFilled.identify 0 1) ∧ ¬ Told twoWayFilled ∧
    Told (twoWayFilled.identify 0 1) := by
  refine ⟨Step24.identify _ 0 1 (by decide) (by decide) (by decide), twoWayFilled_never_told _, ?_⟩
  exact ⟨0, by decide, rfl, by decide⟩

end Twentyfourth
