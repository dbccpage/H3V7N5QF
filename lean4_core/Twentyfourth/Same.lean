import Twentyfourth.Basic

/-!
# The sameness of results, and balance

The sameness sentence is the twenty-third's word for word; it says nothing of
filled terms.  Reading C-S of the paper: pairs asserted together and raising
touch no filled term, and two results that differ in which terms are filled
are two results.  At a fixed writing (rewriting is `Rename.lean`):
`Same24 X Y` — the twenty-third's `Same3` on the assertions, and the same
filled terms.

Derived here:
* `Same24` is an equivalence, and on the twenty-third's states with nothing
  filled it is exactly the twenty-third's sameness (`same24_ofSt_iff`): the
  twenty-third's results map in one to one, and no two of them are made one
  (`no_merge`);
* **balance belongs to the result**: a filled term `x` balances when `xrx`
  and `xsx` are asserted equally often (`Balances`, counts of atoms); that is
  its loop's excess being zero (`balances_iff`), and it is the same in every
  state of a result (`Same24.balances`);
* filling respects the sameness (`Same24.fill`), as adding an assertion does
  and adding a term does not (23:D4);
* reading C-F3 (filling also asserts `xrx` and `xsx` once each) reaches C-F1's
  result (`fillLoops_same`).
-/

namespace Twentyfourth

open Twentysecond Twentythird

/-- The seed's sameness at a fixed writing: the twenty-third's on the assertions, and the same filled terms. -/
def Same24 (X Y : FSt) : Prop := Same3 X.G Y.G ∧ ∀ x, x < X.G.n → X.F x = Y.F x

theorem Same24.refl (X : FSt) : Same24 X X := ⟨Same3.refl _, fun _ _ => rfl⟩

theorem Same24.symm {X Y : FSt} (h : Same24 X Y) : Same24 Y X :=
  ⟨h.1.symm, fun x hx => (h.2 x (h.1.n ▸ hx)).symm⟩

theorem Same24.trans {X Y Z : FSt} (h1 : Same24 X Y) (h2 : Same24 Y Z) : Same24 X Z :=
  ⟨h1.1.trans h2.1, fun x hx => (h1.2 x hx).trans (h2.2 x (h1.1.n ▸ hx))⟩

theorem Same24.n {X Y : FSt} (h : Same24 X Y) : X.G.n = Y.G.n := h.1.n

/-- Two same results fill equally many terms. -/
theorem Same24.fc {X Y : FSt} (h : Same24 X Y) : X.fc = Y.fc := by
  unfold FSt.fc
  rw [← h.n]
  exact rsum_congr _ (fun x hx => by unfold ind; rw [h.2 x hx])

theorem Same24.hasFilled {X Y : FSt} (h : Same24 X Y) (hf : X.HasFilled) : Y.HasFilled := by
  obtain ⟨x, hx, fx⟩ := hf
  exact ⟨x, h.n ▸ hx, (h.2 x hx) ▸ fx⟩

/-- **The twenty-third's states with nothing filled: one result here exactly when one result there.** -/
theorem same24_ofSt_iff {G H : St} : Same24 (ofSt G) (ofSt H) ↔ Same3 G H :=
  ⟨fun h => h.1, fun h => ⟨h, fun _ _ => rfl⟩⟩

/-- **This seed makes no two of the twenty-third's results one.** -/
theorem no_merge {G H : St} (h : Same24 (ofSt G) (ofSt H)) : Same3 G H := same24_ofSt_iff.1 h

/-! ## Balance -/

/-- `x` is filled, and `xrx` and `xsx` are asserted equally often. -/
def Balances (X : FSt) (x : Nat) : Prop :=
  X.F x = true ∧ X.G.A.count ⟨.r, x, x⟩ = X.G.A.count ⟨.s, x, x⟩

theorem balances_iff {X : FSt} {x : Nat} : Balances X x ↔ X.F x = true ∧ excess X.G x x = 0 := by
  unfold Balances excess
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [h2]; omega⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by omega⟩

/-- **Whether a filled term balances is the same in every state of a result.** -/
theorem Same24.balances {X Y : FSt} (h : Same24 X Y) {x : Nat} (hx : x < X.G.n) : Balances X x ↔ Balances Y x := by
  rw [balances_iff, balances_iff, h.2 x hx, h.1.loop hx]

/-- **Filling respects the sameness**: filling one term of two states of one result gives one result. -/
theorem Same24.fill {X Y : FSt} (h : Same24 X Y) (x : Nat) : Same24 (X.fill x) (Y.fill x) := by
  refine ⟨h.1, fun y hy => ?_⟩
  simp only [FSt.fill]
  split
  · rfl
  · exact h.2 y hy

/-- Reading C-F3: filling `x` also asserts `xrx` and `xsx` once each. -/
def FSt.fillLoops (X : FSt) (x : Nat) : FSt := ⟨⟨X.G.n, ⟨.r, x, x⟩ :: ⟨.s, x, x⟩ :: X.G.A⟩, (X.fill x).F⟩

/-- **C-F3 reaches C-F1's result**: the loops it adds are a pair asserted together. -/
theorem fillLoops_same (X : FSt) {x : Nat} (hx : x < X.G.n) : Same24 (X.fillLoops x) (X.fill x) :=
  ⟨Same.same3 (Gen.pair X.G x x hx hx).same.symm, fun _ _ => rfl⟩

end Twentyfourth
