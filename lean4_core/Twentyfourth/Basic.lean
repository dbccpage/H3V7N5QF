import Twentythird

/-!
# States with filled terms, and the five changes

The twenty-fourth seed adds a fifth kind of change, "filling one term", and
says when a filled term balances.  A state here (reading C-F1 of the paper)
is the twenty-second's `St` — terms `0 … n − 1`, the assertions of both
relations as a list of atoms — together with which terms are filled
(`F : Nat → Bool`).  Filling `x` makes `x` filled and changes nothing
asserted; filling a filled term is not a change.  The four earlier kinds act
on the assertions as before; adding a term adds an unfilled term; identifying
two terms (reading C-I1) fills a term of the outcome when some term that goes
onto it was filled (`idF`).

Derived here:
* the changes keep well-formedness (`Step24.wf`);
* `fc`, the number of filled terms: adding a term keeps it (`fc_addTerm`),
  filling raises it by one (`fc_fill`), identifying never raises it
  (`fc_identify_le`, from a general count of an image, `rsum_image_le`);
* **a filled term never goes away** under C-I1 (`Step24.hasFilled`,
  `Reach24.hasFilled`);
* the twenty-third's states, with no term filled (`ofSt`), and each of their
  changes are states and changes here (`Step.toStep24`, `Reach.toReach24`);
  forgetting the filled terms carries each change to a change of the
  twenty-third or to none, a filling (`Step24.forget`).
-/

namespace Twentyfourth

open Twentysecond Twentythird

/-- A state of this seed: the twenty-third's state, and which terms are filled. -/
structure FSt where
  G : St
  F : Nat → Bool

/-- `1` for a filled term, `0` otherwise. -/
def ind (F : Nat → Bool) (x : Nat) : Nat := if F x = true then 1 else 0

namespace FSt

/-- Assertions between terms that are there, and only terms that are there filled. -/
def WF (X : FSt) : Prop := X.G.WF ∧ ∀ x, X.F x = true → x < X.G.n

/-- How many terms are filled. -/
def fc (X : FSt) : Nat := rsum (ind X.F) X.G.n

/-- Adding a term (unfilled). -/
def addTerm (X : FSt) : FSt := ⟨X.G.addTerm, X.F⟩

/-- Adding an assertion. -/
def add (X : FSt) (a : Atom) : FSt := ⟨X.G.add a, X.F⟩

/-- Removing an assertion. -/
def remove (X : FSt) (a : Atom) : FSt := ⟨X.G.remove a, X.F⟩

/-- Filling the term `x`. -/
def fill (X : FSt) (x : Nat) : FSt := ⟨X.G, fun y => if y = x then true else X.F y⟩

/-- Some term is filled. -/
def HasFilled (X : FSt) : Prop := ∃ x, x < X.G.n ∧ X.F x = true

/-- Deciding it by searching the terms (without it `by_cases` would fall back on a classical decision). -/
instance (X : FSt) : Decidable X.HasFilled := inferInstanceAs (Decidable (∃ x, x < X.G.n ∧ X.F x = true))

end FSt

/-- The filled terms after identifying `u` and `v` in a state with `n` terms (reading C-I1): a term of the
outcome is filled when some term that goes onto it was. -/
def idF (n u v : Nat) (F : Nat → Bool) (w : Nat) : Bool :=
  decide (w < n - 1) && (List.range n).any (fun w' => decide (glue n u v w' = w) && F w')

/-- Identifying `u` and `v`: both become one term in every assertion; the one term is filled when either was. -/
def FSt.identify (X : FSt) (u v : Nat) : FSt := ⟨X.G.identify u v, idF X.G.n u v X.F⟩

/-- What is given: no terms, nothing asserted, nothing filled. -/
def empty24 : FSt := ⟨empty, fun _ => false⟩

/-- One change of the seed: the four kinds of the twenty-third, and filling one term. -/
inductive Step24 : FSt → FSt → Prop
  | addTerm (X : FSt) : Step24 X X.addTerm
  | add (X : FSt) (a : Atom) (hx : a.x < X.G.n) (hy : a.y < X.G.n) : Step24 X (X.add a)
  | remove (X : FSt) (a : Atom) (h : a ∈ X.G.A) : Step24 X (X.remove a)
  | identify (X : FSt) (u v : Nat) (hu : u < X.G.n) (hv : v < X.G.n) (huv : u ≠ v) : Step24 X (X.identify u v)
  | fill (X : FSt) (x : Nat) (hx : x < X.G.n) (hf : X.F x = false) : Step24 X (X.fill x)

/-- `Reach24 X Y k`: `Y` is reached from `X` by `k` changes. -/
inductive Reach24 : FSt → FSt → Nat → Prop
  | refl (X : FSt) : Reach24 X X 0
  | step {X Y Z : FSt} {k : Nat} : Reach24 X Y k → Step24 Y Z → Reach24 X Z (k + 1)

theorem Reach24.trans {X Y Z : FSt} {j k : Nat} (h1 : Reach24 X Y j) (h2 : Reach24 Y Z k) :
    Reach24 X Z (j + k) := by
  induction h2 with
  | refl => exact h1
  | step _ st ih => exact Reach24.step ih st

theorem Reach24.single {X Y : FSt} (h : Step24 X Y) : Reach24 X Y 1 := Reach24.step (Reach24.refl X) h

/-! ## The filled terms of an identification -/

theorem idF_iff {n u v : Nat} {F : Nat → Bool} {w : Nat} :
    idF n u v F w = true ↔ w < n - 1 ∧ ∃ w', w' < n ∧ glue n u v w' = w ∧ F w' = true := by
  unfold idF
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_range]

theorem idF_of {n u v : Nat} {F : Nat → Bool} {w' : Nat} (hu : u < n) (hv : v < n) (huv : u ≠ v)
    (hw : w' < n) (hF : F w' = true) : idF n u v F (glue n u v w') = true :=
  idF_iff.2 ⟨glue_lt hu hv huv hw, w', hw, rfl, hF⟩

theorem idF_false (n u v : Nat) : idF n u v (fun _ => false) = fun _ => false := by
  funext w
  cases h : idF n u v (fun _ => false) w with
  | false => rfl
  | true =>
    obtain ⟨_, _, _, _, e⟩ := idF_iff.1 h
    exact absurd e (by decide)

/-! ## Well-formedness -/

theorem Step24.wf {X Y : FSt} (h : Step24 X Y) (hw : X.WF) : Y.WF := by
  cases h with
  | addTerm =>
    refine ⟨(Step.addTerm X.G).wf hw.1, fun x hx => ?_⟩
    have := hw.2 x hx
    show x < X.G.n + 1
    omega
  | add a hx hy => exact ⟨(Step.add X.G a hx hy).wf hw.1, hw.2⟩
  | remove a ha => exact ⟨(Step.remove X.G a ha).wf hw.1, hw.2⟩
  | identify u v hu hv huv =>
    refine ⟨(Step.identify X.G u v hu hv huv).wf hw.1, fun w hw' => ?_⟩
    exact (idF_iff.1 hw').1
  | fill x hx _ =>
    refine ⟨hw.1, fun y hy => ?_⟩
    simp only [FSt.fill] at hy
    by_cases e : y = x
    · subst e
      exact hx
    · rw [if_neg e] at hy
      exact hw.2 y hy

theorem Reach24.wf {X Y : FSt} {k : Nat} (h : Reach24 X Y k) (hw : X.WF) : Y.WF := by
  induction h with
  | refl => exact hw
  | step _ st ih => exact st.wf ih

theorem empty24_wf : empty24.WF := ⟨empty_wf, fun _ h => Bool.noConfusion h⟩

/-- A well-formed state fills no term at or beyond its number of terms. -/
theorem FSt.F_out {X : FSt} (hw : X.WF) {x : Nat} (hx : X.G.n ≤ x) : X.F x = false := by
  cases h : X.F x with
  | false => rfl
  | true =>
    have := hw.2 x h
    omega

/-! ## Counting the filled terms -/

theorem rsum_zero : ∀ m, rsum (fun _ => 0) m = 0
  | 0 => rfl
  | m + 1 => by simp only [rsum, rsum_zero m]

theorem rsum_le {f g : Nat → Nat} : ∀ m, (∀ k, k < m → f k ≤ g k) → rsum f m ≤ rsum g m
  | 0, _ => Nat.le_refl _
  | m + 1, h => by
    simp only [rsum]
    have := rsum_le m (fun k hk => h k (by omega))
    have := h m (by omega)
    omega

theorem ind_le_one (F : Nat → Bool) (x : Nat) : ind F x ≤ 1 := by
  unfold ind
  split <;> omega

/-- **Counting an image**: when every `w < m` with `Q w` comes from some `w' < n` with `P w'` along `f`,
there are at most as many `w` as `w'`. -/
theorem rsum_image_le (f : Nat → Nat) (P : Nat → Bool) (m : Nat) :
    ∀ n (Q : Nat → Bool), (∀ w, w < m → Q w = true → ∃ w', w' < n ∧ f w' = w ∧ P w' = true) →
      rsum (ind Q) m ≤ rsum (ind P) n
  | 0, Q, h => by
    have : rsum (ind Q) m = rsum (fun _ => 0) m := rsum_congr m (fun w hw => by
      unfold ind
      split
      · next hq =>
        obtain ⟨w', h1, _, _⟩ := h w hw hq
        exact absurd h1 (Nat.not_lt_zero _)
      · rfl)
    rw [this, rsum_zero]
    exact Nat.zero_le _
  | n + 1, Q, h => by
    let Q1 : Nat → Bool := fun w => Q w && !(decide (f n = w) && P n)
    have h1 : ∀ w, w < m → Q1 w = true → ∃ w', w' < n ∧ f w' = w ∧ P w' = true := by
      intro w hw hq
      simp only [Q1, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not] at hq
      obtain ⟨hq, hn⟩ := hq
      obtain ⟨w', hw', e, p⟩ := h w hw hq
      refine ⟨w', ?_, e, p⟩
      by_cases hwn : w' = n
      · subst hwn
        rcases hn with hn | hn
        · exact absurd e hn
        · rw [p] at hn
          exact absurd hn (by decide)
      · omega
    have ih := rsum_image_le f P m n Q1 h1
    have pt : ∀ w, w < m → ind Q w ≤ ind Q1 w + (if w = f n then ind P n else 0) := by
      intro w _
      unfold ind
      by_cases hq : Q w = true
      · by_cases hq1 : Q1 w = true
        · rw [if_pos hq, if_pos hq1]
          omega
        · have hc : (decide (f n = w) && P n) = true := by
            cases hc : (decide (f n = w) && P n)
            · exfalso
              apply hq1
              simp only [Q1, hq, Bool.true_and, Bool.not_eq_true']
              exact hc
            · rfl
          have : f n = w ∧ P n = true := by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
            exact hc
          rw [if_pos hq, if_pos this.1.symm, if_pos this.2]
          omega
      · rw [if_neg hq]
        omega
    have s1 := rsum_le m pt
    rw [rsum_add, rsum_point] at s1
    simp only [rsum]
    have : (if f n < m then ind P n else 0) ≤ ind P n := by split <;> omega
    omega

theorem fc_addTerm {X : FSt} (hw : X.WF) : X.addTerm.fc = X.fc := by
  simp only [FSt.fc, FSt.addTerm, St.addTerm, rsum]
  have : ind X.F X.G.n = 0 := by
    unfold ind
    rw [X.F_out hw (Nat.le_refl _)]
    rfl
  omega

theorem fc_fill {X : FSt} {x : Nat} (hx : x < X.G.n) (hf : X.F x = false) : (X.fill x).fc = X.fc + 1 := by
  simp only [FSt.fc, FSt.fill]
  have : rsum (ind fun y => if y = x then true else X.F y) X.G.n =
      rsum (fun y => ind X.F y + (if y = x then 1 else 0)) X.G.n := by
    refine rsum_congr _ (fun y _ => ?_)
    unfold ind
    by_cases e : y = x
    · subst e
      simp [hf]
    · simp [e]
  rw [this, rsum_add, rsum_point, if_pos hx]

theorem fc_identify_le (X : FSt) (u v : Nat) : (X.identify u v).fc ≤ X.fc := by
  simp only [FSt.fc, FSt.identify, St.identify]
  refine rsum_image_le (glue X.G.n u v) X.F (X.G.n - 1) X.G.n _ (fun w _ hq => ?_)
  obtain ⟨_, w', h1, h2, h3⟩ := idF_iff.1 hq
  exact ⟨w', h1, h2, h3⟩

/-! ## A filled term never goes away (reading C-I1) -/

theorem Step24.hasFilled {X Y : FSt} (h : Step24 X Y) (hf : X.HasFilled) : Y.HasFilled := by
  obtain ⟨x, hx, fx⟩ := hf
  cases h with
  | addTerm => exact ⟨x, by show x < X.G.n + 1; omega, fx⟩
  | add a _ _ => exact ⟨x, hx, fx⟩
  | remove a _ => exact ⟨x, hx, fx⟩
  | identify u v hu hv huv =>
    exact ⟨glue X.G.n u v x, glue_lt hu hv huv hx, idF_of hu hv huv hx fx⟩
  | fill y _ _ =>
    refine ⟨x, hx, ?_⟩
    simp only [FSt.fill]
    split
    · rfl
    · exact fx

/-- **Under C-I1 a filled term never goes away.** -/
theorem Reach24.hasFilled {X Y : FSt} {k : Nat} (h : Reach24 X Y k) (hf : X.HasFilled) : Y.HasFilled := by
  induction h with
  | refl => exact hf
  | step _ st ih => exact st.hasFilled ih

/-! ## The twenty-third's states and changes, with nothing filled -/

/-- A state of the twenty-third seed read as a state of this one with no term filled. -/
def ofSt (G : St) : FSt := ⟨G, fun _ => false⟩

theorem ofSt_wf {G : St} (hw : G.WF) : (ofSt G).WF := ⟨hw, fun _ h => Bool.noConfusion h⟩

theorem ofSt_empty : ofSt empty = empty24 := rfl

theorem rsum_ind_false (n : Nat) : rsum (ind fun _ => false) n = 0 := by
  have : rsum (ind fun _ => false) n = rsum (fun _ => 0) n := rsum_congr _ (fun _ _ => rfl)
  rw [this, rsum_zero]

theorem ofSt_fc (G : St) : (ofSt G).fc = 0 := rsum_ind_false G.n

/-- **Every change of the twenty-third seed is a change here, of the same kind, on its states with nothing
filled.** -/
theorem Step.toStep24 {G H : St} (h : Step G H) : Step24 (ofSt G) (ofSt H) := by
  cases h with
  | addTerm => exact Step24.addTerm (ofSt G)
  | add a hx hy => exact Step24.add (ofSt G) a hx hy
  | remove a ha => exact Step24.remove (ofSt G) a ha
  | identify u v hu hv huv =>
    have e : (ofSt G).identify u v = ofSt (G.identify u v) := by
      simp only [FSt.identify, ofSt, idF_false]
    rw [← e]
    exact Step24.identify (ofSt G) u v hu hv huv

theorem Reach.toReach24 {G H : St} {k : Nat} (h : Reach G H k) : Reach24 (ofSt G) (ofSt H) k := by
  induction h with
  | refl => exact Reach24.refl _
  | step _ st ih => exact Reach24.step ih (Step.toStep24 st)

/-- **Forgetting the filled terms carries every change to a change of the twenty-third seed, or to none (a
filling).** -/
theorem Step24.forget {X Y : FSt} (h : Step24 X Y) : Step X.G Y.G ∨ X.G = Y.G := by
  cases h with
  | addTerm => exact Or.inl (Step.addTerm X.G)
  | add a hx hy => exact Or.inl (Step.add X.G a hx hy)
  | remove a ha => exact Or.inl (Step.remove X.G a ha)
  | identify u v hu hv huv => exact Or.inl (Step.identify X.G u v hu hv huv)
  | fill _ _ _ => exact Or.inr rfl

end Twentyfourth
