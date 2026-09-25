import Twentyfourth.Record

/-!
# The fewest changes to a result

`pot X`: the twenty-second's `phi` of the assertions (terms plus the plain
part's assertions) plus the filled terms.  Derived here:
* every change raises `pot` by at most one (`Step24.pot_le`): a filling by
  exactly one, an identification lowers `phi` and fills no more terms;
* from the empty state, additions then fillings reach a state of every result
  in `phi + fc` changes (`reach24_upper`, `reach24_fillUpTo`);
* so **the fewest changes to a result is the twenty-third's cost of its
  assertions plus its number of filled terms** (`cost24_eq`); on the
  twenty-third's results, with nothing filled, it is the twenty-third's cost
  (`cost24_ofSt`); filling moves it by exactly one (`fill_cost`);
* a shortest sequence adds terms, adds assertions and fills, and nothing else
  (`shortest24`);
* **parity fails**: identifying two filled terms moves the cost by two
  (`identify_two_filled_even`), where every change of the twenty-third moved
  it by an odd number (23:D6); still no change returns a state to its own
  result (`Step24.not_same24`);
* a change performed on a state asserting the fewest raises the cost by at
  most one (`Step24.cost_le`).
-/

namespace Twentyfourth

open Twentysecond Twentythird

/-- The twenty-second's `phi` of the assertions plus the filled terms. -/
def pot (X : FSt) : Nat := phi X.G + X.fc

theorem pot_empty : pot empty24 = 0 := rfl

theorem Step24.pot_le {X Y : FSt} (h : Step24 X Y) (hw : X.WF) : pot Y ≤ pot X + 1 := by
  cases h with
  | addTerm =>
    show phi X.G.addTerm + X.addTerm.fc ≤ phi X.G + X.fc + 1
    have := (Step.addTerm X.G).phi_le
    rw [fc_addTerm hw]
    omega
  | add a hx hy =>
    show phi (X.G.add a) + (X.add a).fc ≤ phi X.G + X.fc + 1
    have := (Step.add X.G a hx hy).phi_le
    have e : (X.add a).fc = X.fc := rfl
    omega
  | remove a ha =>
    show phi (X.G.remove a) + (X.remove a).fc ≤ phi X.G + X.fc + 1
    have := (Step.remove X.G a ha).phi_le
    have e : (X.remove a).fc = X.fc := rfl
    omega
  | identify u v _ hv _ =>
    show phi (X.G.identify u v) + (X.identify u v).fc ≤ phi X.G + X.fc + 1
    have := Step.phi_identify (G := X.G) (u := u) hv
    have := fc_identify_le X u v
    omega
  | fill x hx hf =>
    show phi X.G + (X.fill x).fc ≤ phi X.G + X.fc + 1
    rw [fc_fill hx hf]
    omega

theorem Reach24.pot_le {X Y : FSt} {k : Nat} (h : Reach24 X Y k) (hw : X.WF) : pot Y ≤ pot X + k := by
  induction h with
  | refl => omega
  | step r st ih =>
    have := st.pot_le (r.wf hw)
    omega

theorem decide_lt_succ {x m : Nat} (h : x ≠ m) : decide (x < m + 1) = decide (x < m) :=
  decide_eq_decide.2 ⟨fun a => by omega, fun a => by omega⟩

/-- Filling the terms `x < m` for which `F x`, one by one. -/
theorem reach24_fillUpTo (G : St) (F : Nat → Bool) : ∀ m, m ≤ G.n →
    Reach24 ⟨G, fun _ => false⟩ ⟨G, fun x => F x && decide (x < m)⟩ (rsum (ind F) m)
  | 0, _ => by
    have e : (fun x => F x && decide (x < 0)) = fun _ => false := by
      funext x
      simp
    rw [e]
    exact Reach24.refl _
  | m + 1, hm => by
    have ih := reach24_fillUpTo G F m (by omega)
    show Reach24 _ _ (rsum (ind F) m + ind F m)
    cases hF : F m with
    | false =>
      have e : (fun x => F x && decide (x < m + 1)) = fun x => F x && decide (x < m) := by
        funext x
        by_cases hx : x = m
        · subst hx
          simp [hF]
        · rw [decide_lt_succ hx]
      rw [e, show ind F m = 0 by unfold ind; rw [hF]; rfl]
      exact ih
    | true =>
      have st := Step24.fill ⟨G, fun x => F x && decide (x < m)⟩ m (by show m < G.n; omega) (by simp)
      have e : (⟨G, fun x => F x && decide (x < m)⟩ : FSt).fill m = ⟨G, fun x => F x && decide (x < m + 1)⟩ := by
        simp only [FSt.fill, FSt.mk.injEq, true_and]
        funext x
        by_cases hx : x = m
        · subst hx
          simp [hF]
        · rw [if_neg hx, decide_lt_succ hx]
      rw [e] at st
      rw [show ind F m = 1 by unfold ind; rw [hF]; rfl]
      exact Reach24.step ih st

/-- **From the empty state, additions then fillings reach a state of every result in `phi + fc` changes.** -/
theorem reach24_upper {X : FSt} (hw : X.WF) : Reach24 empty24 ⟨X.G.plainSt, X.F⟩ (phi X.G + X.fc) := by
  have r1 := Reach.toReach24 (reach_plainSt hw.1).reach
  have r2 := reach24_fillUpTo X.G.plainSt X.F X.G.plainSt.n (Nat.le_refl _)
  have e : (fun x => X.F x && decide (x < X.G.plainSt.n)) = X.F := by
    funext x
    cases hf : X.F x with
    | false => rfl
    | true => simp [St.plainSt, hw.2 x hf]
  rw [e] at r2
  exact Reach24.trans r1 r2

/-- `c` is the fewest changes from the empty state to a state of the result of `X`. -/
def Cost24 (X : FSt) (c : Nat) : Prop :=
  (∃ Y, Same24 Y X ∧ Reach24 empty24 Y c) ∧ ∀ Y k, Same24 Y X → Reach24 empty24 Y k → c ≤ k

theorem Cost24.unique {X : FSt} {c c' : Nat} (h : Cost24 X c) (h' : Cost24 X c') : c = c' := by
  obtain ⟨⟨Y, s, r⟩, lo⟩ := h
  obtain ⟨⟨Y', s', r'⟩, lo'⟩ := h'
  have a := lo Y' c' s' r'
  have b := lo' Y c s r
  omega

/-- The cost is a mark of the result. -/
theorem Cost24.congr {X X' : FSt} (h : Same24 X X') {c : Nat} : Cost24 X c ↔ Cost24 X' c := by
  constructor
  · rintro ⟨⟨Y, s, r⟩, lo⟩
    exact ⟨⟨Y, s.trans h, r⟩, fun Z k s' r' => lo Z k (s'.trans h.symm) r'⟩
  · rintro ⟨⟨Y, s, r⟩, lo⟩
    exact ⟨⟨Y, s.trans h.symm, r⟩, fun Z k s' r' => lo Z k (s'.trans h) r'⟩

/-- **The fewest changes to a result: the twenty-third's cost of its assertions plus its filled terms.** -/
theorem cost24_eq {X : FSt} (hw : X.WF) {c : Nat} (hc : Cost3 X.G c) : Cost24 X (c + X.fc) := by
  obtain ⟨⟨H, hH, s, e⟩, lo⟩ := cost3_iff.1 hc
  have hHn : H.n = X.G.n := s.n
  have hY : (⟨H, X.F⟩ : FSt).WF := ⟨hH, fun x hx => hHn ▸ hw.2 x hx⟩
  have hfc : (⟨H, X.F⟩ : FSt).fc = X.fc := by
    unfold FSt.fc
    simp only
    rw [hHn]
  refine ⟨⟨⟨H.plainSt, X.F⟩, ⟨(Same.same3 (same_plainSt H).symm).trans s, fun _ _ => rfl⟩, ?_⟩, ?_⟩
  · have := reach24_upper hY
    simp only at this
    rw [hfc, e] at this
    exact this
  · intro Z k sZ r
    have hZ := r.wf empty24_wf
    have a := r.pot_le empty24_wf
    have b := lo Z.G hZ.1 sZ.1
    have f := sZ.fc
    rw [pot_empty] at a
    unfold pot at a
    omega

/-- **On the twenty-third's results, with nothing filled, the cost is the twenty-third's.** -/
theorem cost24_ofSt {G : St} (hG : G.WF) {c : Nat} (hc : Cost3 G c) : Cost24 (ofSt G) c := by
  have := cost24_eq (ofSt_wf hG) hc
  rwa [ofSt_fc, Nat.add_zero] at this

/-- **Filling a term raises the cost by exactly one.** -/
theorem fill_cost {X : FSt} (hw : X.WF) {c : Nat} (hc : Cost3 X.G c) {x : Nat} (hx : x < X.G.n)
    (hf : X.F x = false) : Cost24 X (c + X.fc) ∧ Cost24 (X.fill x) (c + X.fc + 1) := by
  refine ⟨cost24_eq hw hc, ?_⟩
  have := cost24_eq ((Step24.fill X x hx hf).wf hw) hc
  rwa [fc_fill hx hf, ← Nat.add_assoc] at this

/-- The cost of a result is at most the potential of any of its states. -/
theorem cost24_le_pot {X : FSt} (hw : X.WF) {c : Nat} (h : Cost24 X c) : c ≤ pot X :=
  h.2 ⟨X.G.plainSt, X.F⟩ (phi X.G + X.fc) ⟨Same.same3 (same_plainSt X.G).symm, fun _ _ => rfl⟩ (reach24_upper hw)

/-- **A change performed on a state asserting the fewest raises the cost by at most one.** -/
theorem Step24.cost_le {X Y : FSt} (st : Step24 X Y) (hw : X.WF) {c' : Nat} (h' : Cost24 Y c') :
    c' ≤ pot X + 1 := by
  have a := cost24_le_pot (st.wf hw) h'
  have b := st.pot_le hw
  omega

/-! ## Shortest sequences -/

/-- The changes a shortest sequence may use: adding a term, adding an assertion, filling. -/
inductive RaiseStep : FSt → FSt → Prop
  | addTerm (X : FSt) : RaiseStep X X.addTerm
  | add (X : FSt) (a : Atom) (hx : a.x < X.G.n) (hy : a.y < X.G.n) : RaiseStep X (X.add a)
  | fill (X : FSt) (x : Nat) (hx : x < X.G.n) (hf : X.F x = false) : RaiseStep X (X.fill x)

inductive RaiseReach : FSt → FSt → Nat → Prop
  | refl (X : FSt) : RaiseReach X X 0
  | step {X Y Z : FSt} {k : Nat} : RaiseReach X Y k → RaiseStep Y Z → RaiseReach X Z (k + 1)

/-- The ninth's size plus the filled terms. -/
def size24 (X : FSt) : Nat := X.G.size + X.fc

theorem Step24.size24_step {X Y : FSt} (h : Step24 X Y) (hw : X.WF) :
    (size24 Y = size24 X + 1 ∧ RaiseStep X Y) ∨ size24 Y + 1 ≤ size24 X := by
  cases h with
  | addTerm =>
    left
    refine ⟨?_, RaiseStep.addTerm X⟩
    show X.G.addTerm.size + X.addTerm.fc = X.G.size + X.fc + 1
    rw [fc_addTerm hw]
    simp only [St.size, St.addTerm]
    omega
  | add a hx hy =>
    left
    refine ⟨?_, RaiseStep.add X a hx hy⟩
    show (X.G.add a).size + (X.add a).fc = X.G.size + X.fc + 1
    have e : (X.add a).fc = X.fc := rfl
    simp only [St.size, St.add, List.length_cons] at *
    omega
  | remove a ha =>
    right
    show (X.G.remove a).size + (X.remove a).fc + 1 ≤ X.G.size + X.fc
    have e : (X.remove a).fc = X.fc := rfl
    have := length_del ha
    simp only [St.size, St.remove] at *
    omega
  | identify u v _ hv _ =>
    right
    show (X.G.identify u v).size + (X.identify u v).fc + 1 ≤ X.G.size + X.fc
    have := fc_identify_le X u v
    simp only [St.size, St.identify, List.length_map]
    omega
  | fill x hx hf =>
    left
    refine ⟨?_, RaiseStep.fill X x hx hf⟩
    show X.G.size + (X.fill x).fc = X.G.size + X.fc + 1
    rw [fc_fill hx hf]
    omega

theorem Reach24.size24_le {X Y : FSt} {k : Nat} (h : Reach24 X Y k) (hw : X.WF) : size24 Y ≤ size24 X + k := by
  induction h with
  | refl => omega
  | step r st ih =>
    rcases st.size24_step (r.wf hw) with ⟨e, _⟩ | e <;> omega

theorem Reach24.raising {X Y : FSt} {k : Nat} (h : Reach24 X Y k) (hw : X.WF) (e : size24 Y = size24 X + k) :
    RaiseReach X Y k := by
  induction h with
  | refl => exact RaiseReach.refl _
  | step r st ih =>
    have hr := r.size24_le hw
    rcases st.size24_step (r.wf hw) with ⟨e', ad⟩ | e'
    · exact RaiseReach.step (ih (by omega)) ad
    · exfalso
      omega

theorem pot_le_size24 (X : FSt) : pot X ≤ size24 X := by
  have := phi_le_size X.G
  unfold pot size24
  omega

/-- **A shortest sequence adds terms, adds assertions and fills; it never removes or identifies.** -/
theorem shortest24 {Y : FSt} {k : Nat} (r : Reach24 empty24 Y k) (hk : k = pot Y) : RaiseReach empty24 Y k := by
  have a := r.size24_le empty24_wf
  have b := pot_le_size24 Y
  have c : size24 empty24 = 0 := rfl
  exact r.raising empty24_wf (by omega)

/-! ## Parity -/

/-- `a b`, both filled. -/
def pairFilled : FSt := ⟨⟨2, []⟩, fun x => decide (x < 2)⟩

/-- `a`, filled. -/
def oneFilled : FSt := ⟨⟨1, []⟩, fun x => decide (x = 0)⟩

theorem pairFilled_wf : pairFilled.WF := ⟨nothing_wf 2, fun _ h => of_decide_eq_true h⟩

theorem oneFilled_wf : oneFilled.WF := ⟨nothing_wf 1, fun x h => by
  have := of_decide_eq_true h
  show x < 1
  omega⟩

theorem cost24_oneFilled : Cost24 oneFilled 2 := cost24_eq oneFilled_wf (cost3_nothing 1)

/-- **Identifying two filled terms moves the cost by two**: `a b` both filled costs 4; identified, `a` filled
costs 2.  Every change of the twenty-third moved the cost by an odd number (23:D6). -/
theorem identify_two_filled_even :
    Step24 pairFilled (pairFilled.identify 0 1) ∧ Cost24 pairFilled 4 ∧ Cost24 (pairFilled.identify 0 1) 2 := by
  have st := Step24.identify pairFilled 0 1 (by decide) (by decide) (by decide)
  refine ⟨st, cost24_eq pairFilled_wf (cost3_nothing 2), ?_⟩
  exact cost24_eq (st.wf pairFilled_wf) (cost3_nothing 1)

/-- **No change returns a state to its own result.** -/
theorem Step24.not_same24 {X Y : FSt} (st : Step24 X Y) (hw : X.WF) : ¬ Same24 X Y := by
  intro h
  cases st with
  | addTerm =>
    have := h.n
    simp only [FSt.addTerm, St.addTerm] at this
    omega
  | add a hx hy =>
    have p := h.1.size_parity hw.1 ((Step.add X.G a hx hy).wf hw.1)
    simp only [St.size, St.add, List.length_cons] at p
    omega
  | remove a ha =>
    have p := h.1.size_parity hw.1 ((Step.remove X.G a ha).wf hw.1)
    have := length_del ha
    simp only [St.size, St.remove] at p
    omega
  | identify u v hu _ _ =>
    have := h.n
    simp only [FSt.identify, St.identify] at this
    omega
  | fill x hx hf =>
    have := h.2 x hx
    simp [FSt.fill, hf] at this

end Twentyfourth
