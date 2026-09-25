import Twentyfourth.Map

/-!
# Every writing of the terms

"Two results that differ only in how their terms are written … are the same
result."  A rewriting `f` (with inverse `g`) of the terms `0 … n − 1` carries
the assertions (the twenty-second's `St.rename`) and the filled terms
(`FSt.rename`).  `SameW24`: some rewriting, then `Same24`.

Derived here:
* the twenty-third's results map in one to one in every writing too
  (`sameW24_ofSt_iff`);
* **whether a filled term balances is carried by every rewriting**
  (`SameW24.balances`), so the told results are the same in every writing
  (`SameW24.told`);
* a rewriting keeps the number of filled terms (`fc_rename`, a count through a
  one-to-one map, `rsum_image_le` both ways) and the potential
  (`pot_rename`), so **the cost is the fewest changes to the result in every
  writing** (`cost24_every_writing`).
-/

namespace Twentyfourth

open Twentysecond Twentythird

/-- The state with its terms rewritten by `f` (`g` the inverse): the assertions and the filled terms. -/
def FSt.rename (X : FSt) (f g : Nat → Nat) : FSt := ⟨X.G.rename f, fun x => decide (x < X.G.n) && X.F (g x)⟩

/-- The seed's sameness in every writing. -/
def SameW24 (X Y : FSt) : Prop := ∃ f g, IsRw X.G.n f g ∧ Same24 (X.rename f g) Y

theorem Same24.sameW24 {X Y : FSt} (h : Same24 X Y) : SameW24 X Y := by
  refine ⟨id, id, IsRw.id _, ⟨?_, fun x hx => ?_⟩⟩
  · simp only [FSt.rename]
    rw [rename_id]
    exact h.1
  · simp only [FSt.rename, id]
    have hx' : x < X.G.n := hx
    rw [decide_eq_true hx', Bool.true_and]
    exact h.2 x hx'

/-- **The twenty-third's results map in one to one in every writing.** -/
theorem sameW24_ofSt_iff {G H : St} : SameW24 (ofSt G) (ofSt H) ↔ SameW3 G H := by
  constructor
  · rintro ⟨f, g, hr, s⟩
    exact ⟨f, g, hr, s.1⟩
  · rintro ⟨f, g, hr, s⟩
    refine ⟨f, g, hr, s, fun x _ => ?_⟩
    simp [FSt.rename, ofSt]

theorem rename_wf24 {X : FSt} {f g : Nat → Nat} (hr : IsRw X.G.n f g) (hw : X.WF) : (X.rename f g).WF := by
  refine ⟨rename_wf hr hw.1, fun x hx => ?_⟩
  simp only [FSt.rename, Bool.and_eq_true, decide_eq_true_eq] at hx
  exact hx.1

/-- Every rewriting carries each term's filling and its loop's excess to the term it writes. -/
theorem SameW24.pointwise {X Y : FSt} (hX : X.WF) (h : SameW24 X Y) :
    X.G.n = Y.G.n ∧ ∃ f g, IsRw X.G.n f g ∧
      ∀ x, x < X.G.n → Y.F (f x) = X.F x ∧ excess Y.G (f x) (f x) = excess X.G x x := by
  obtain ⟨f, g, hr, s⟩ := h
  refine ⟨s.n, f, g, hr, fun x hx => ⟨?_, ?_⟩⟩
  · have hfx : f x < X.G.n := hr.f_lt x hx
    have := s.2 (f x) hfx
    rw [← this]
    simp only [FSt.rename]
    rw [decide_eq_true hfx, Bool.true_and, hr.gf x hx]
  · have := s.1.loop (x := f x) (hr.f_lt x hx)
    rw [← this]
    exact excess_rename hr hX.1 hx hx

/-- **Whether a filled term balances is carried by every rewriting.** -/
theorem SameW24.balances {X Y : FSt} (hX : X.WF) (h : SameW24 X Y) :
    ∃ f g, IsRw X.G.n f g ∧ ∀ x, x < X.G.n → (Balances X x ↔ Balances Y (f x)) := by
  obtain ⟨_, f, g, hr, p⟩ := h.pointwise hX
  refine ⟨f, g, hr, fun x hx => ?_⟩
  rw [balances_iff, balances_iff, (p x hx).1, (p x hx).2]

/-- **The told results are the same in every writing.** -/
theorem SameW24.told {X Y : FSt} (hX : X.WF) (h : SameW24 X Y) : Told X ↔ Told Y := by
  obtain ⟨hn, f, g, hr, p⟩ := h.pointwise hX
  constructor
  · rintro ⟨x, hx, hf, he⟩
    refine ⟨f x, hn ▸ hr.f_lt x hx, (p x hx).1.trans hf, fun e => he ?_⟩
    rw [← (p x hx).2]
    exact e
  · rintro ⟨y, hy, hf, he⟩
    have hy' : y < X.G.n := hn ▸ hy
    have hgy := hr.g_lt y hy'
    have hfg := hr.fg y hy'
    refine ⟨g y, hgy, ?_, fun e => he ?_⟩
    · rw [← (p (g y) hgy).1, hfg]
      exact hf
    · have := (p (g y) hgy).2
      rw [hfg] at this
      rw [this]
      exact e

/-! ## The cost in every writing -/

/-- **A rewriting keeps the number of filled terms.** -/
theorem fc_rename {X : FSt} {f g : Nat → Nat} (hr : IsRw X.G.n f g) : (X.rename f g).fc = X.fc := by
  unfold FSt.fc
  show rsum (ind fun x => decide (x < X.G.n) && X.F (g x)) X.G.n = rsum (ind X.F) X.G.n
  apply Nat.le_antisymm
  · refine rsum_image_le f X.F X.G.n X.G.n _ (fun w hw hq => ?_)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    exact ⟨g w, hr.g_lt w hw, hr.fg w hw, hq.2⟩
  · refine rsum_image_le g _ X.G.n X.G.n X.F (fun w hw hq => ?_)
    refine ⟨f w, hr.f_lt w hw, hr.gf w hw, ?_⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hr.f_lt w hw, by rw [hr.gf w hw]; exact hq⟩

theorem pot_rename {X : FSt} {f g : Nat → Nat} (hr : IsRw X.G.n f g) (hw : X.WF) : pot (X.rename f g) = pot X := by
  unfold pot
  rw [fc_rename hr]
  show phi (X.G.rename f) + X.fc = phi X.G + X.fc
  rw [phi_rename hr hw.1]

/-- The fewest changes to a result, writing included. -/
def Cost24W (X : FSt) (c : Nat) : Prop :=
  (∃ Y, SameW24 Y X ∧ Reach24 empty24 Y c) ∧ ∀ Y k, SameW24 Y X → Reach24 empty24 Y k → c ≤ k

/-- **The cost of a result is the fewest changes to it in every writing.** -/
theorem cost24_every_writing {X : FSt} {c : Nat} (h : Cost24 X c) : Cost24W X c := by
  obtain ⟨⟨Y, s, r⟩, lo⟩ := h
  refine ⟨⟨Y, s.sameW24, r⟩, fun Z k sZ rZ => ?_⟩
  obtain ⟨f, g, hr, s'⟩ := sZ
  have hZ := rZ.wf empty24_wf
  have hR := rename_wf24 hr hZ
  have a := lo _ _ ((same24_plainSt (Z.rename f g)).trans s') (reach24_upper hR)
  have b := rZ.pot_le empty24_wf
  rw [pot_empty] at b
  have e := pot_rename hr hZ
  unfold pot at e b
  omega

end Twentyfourth
