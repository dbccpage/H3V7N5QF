import Twentyfourth.Cost

/-!
# Reachability between results

`ReachR24 X Y`: some sequence of changes from `X` ends at a state of `Y`'s
result.  Derived here, under reading C-I1:
* **a result reaches another exactly when the other has a term or the first is
  empty, and the other has a filled term or the first has none**
  (`reach24_criterion`).  The necessity is the twenty-third's (the terms never
  run out, 22:D9) and `Reach24.hasFilled` (a filled term never goes away).
  The path: remove every assertion, identify the terms down to one — filled
  exactly when some term was (`reach24_collapse`) — add terms, fill, add the
  assertions of the target's plain part; when the one term is filled and the
  target's first term is not, one more term is added and identified with it,
  which moves the filled term to a filled term of the target (`idF_move`);
* so **the twenty-third's criterion fails** exactly on the pairs from a result
  with a filled term to one without (`twentythird_criterion_fails`);
* under reading C-I2 (the one term filled only when both were) a filled term
  can go away (`i2_unfills`), and under C-I3 (never filled) always.
-/

namespace Twentyfourth

open Twentysecond Twentythird

/-- Some sequence of changes from `X` ends at a state of `Y`'s result. -/
def ReachR24 (X Y : FSt) : Prop := ∃ k Y', Reach24 X Y' k ∧ Same24 Y' Y

/-- Forgetting the filled terms along a sequence gives a sequence of the twenty-third's changes. -/
theorem Reach24.forget {X Y : FSt} {k : Nat} (h : Reach24 X Y k) : ∃ j, Reach X.G Y.G j := by
  induction h with
  | refl => exact ⟨0, Reach.refl _⟩
  | step _ st ih =>
    obtain ⟨j, r⟩ := ih
    rcases st.forget with s | e
    · exact ⟨j + 1, Reach.step r s⟩
    · exact ⟨j, e ▸ r⟩

theorem reach24_clear (n : Nat) (F : Nat → Bool) : ∀ A : List Atom, Reach24 ⟨⟨n, A⟩, F⟩ ⟨⟨n, []⟩, F⟩ A.length
  | [] => Reach24.refl _
  | a :: t => by
    have st := Step24.remove ⟨⟨n, a :: t⟩, F⟩ a List.mem_cons_self
    have e : (⟨⟨n, a :: t⟩, F⟩ : FSt).remove a = ⟨⟨n, t⟩, F⟩ := by
      simp only [FSt.remove, St.remove, del_cons_self]
    rw [e] at st
    have := Reach24.trans (Reach24.single st) (reach24_clear n F t)
    rw [List.length_cons, Nat.add_comm]
    exact this

theorem reach24_grow (n : Nat) (F : Nat → Bool) : ∀ m, Reach24 ⟨⟨n, []⟩, F⟩ ⟨⟨n + m, []⟩, F⟩ m
  | 0 => Reach24.refl _
  | m + 1 => Reach24.step (reach24_grow n F m) (Step24.addTerm ⟨⟨n + m, []⟩, F⟩)

theorem reach24_atoms (n : Nat) (F : Nat → Bool) :
    ∀ L : List Atom, (∀ a ∈ L, a.x < n ∧ a.y < n) → Reach24 ⟨⟨n, []⟩, F⟩ ⟨⟨n, L⟩, F⟩ L.length
  | [], _ => Reach24.refl _
  | a :: L, h => by
    have r := reach24_atoms n F L (fun b hb => h b (List.mem_cons_of_mem _ hb))
    exact Reach24.step r (Step24.add ⟨⟨n, L⟩, F⟩ a (h a List.mem_cons_self).1 (h a List.mem_cons_self).2)

/-- Identifying the terms down to one: the one term is filled exactly when some term was. -/
theorem reach24_collapse : ∀ (m : Nat) (F : Nat → Bool), (∀ x, F x = true → x < m + 1) →
    ∃ F' : Nat → Bool, Reach24 ⟨⟨m + 1, []⟩, F⟩ ⟨⟨1, []⟩, F'⟩ m ∧
      (F' 0 = true ↔ ∃ x, x < m + 1 ∧ F x = true) ∧ (∀ x, F' x = true → x < 1)
  | 0, F, hF => by
    -- (a term-mode pattern `fun ⟨x, hx, h⟩` followed by `subst` would bring in `Classical.choice`)
    refine ⟨F, Reach24.refl _, ⟨fun h => ⟨0, Nat.zero_lt_one, h⟩, ?_⟩, hF⟩
    rintro ⟨x, hx, h⟩
    have : x = 0 := by omega
    rw [this] at h
    exact h
  | m + 1, F, hF => by
    have st := Step24.identify ⟨⟨m + 2, []⟩, F⟩ 0 (m + 1) (by show 0 < m + 2; omega)
      (by show m + 1 < m + 2; omega) (by omega)
    have e : (⟨⟨m + 2, []⟩, F⟩ : FSt).identify 0 (m + 1) = ⟨⟨m + 1, []⟩, idF (m + 2) 0 (m + 1) F⟩ := rfl
    rw [e] at st
    obtain ⟨F', r, h1, h2⟩ := reach24_collapse m (idF (m + 2) 0 (m + 1) F) (fun x hx => (idF_iff.1 hx).1)
    refine ⟨F', ?_, ?_, h2⟩
    · have := Reach24.trans (Reach24.single st) r
      rw [Nat.add_comm 1 m] at this
      exact this
    · rw [h1]
      constructor
      · rintro ⟨x, _, hx⟩
        obtain ⟨_, w', hw', _, hf⟩ := idF_iff.1 hx
        exact ⟨w', hw', hf⟩
      · rintro ⟨x, hx, hf⟩
        exact ⟨glue (m + 2) 0 (m + 1) x, glue_lt (by omega) (by omega) (by omega) hx,
          idF_of (by omega) (by omega) (by omega) hx hf⟩

theorem decide_lt_succ' {x m : Nat} (h : x ≠ m) : decide (x < m + 1) = decide (x < m) :=
  decide_eq_decide.2 ⟨fun _ => by omega, fun _ => by omega⟩

/-- Filling, starting from any filled terms, towards a target. -/
theorem reach24_fillFrom (G : St) (F0 F : Nat → Bool) : ∀ m, m ≤ G.n →
    ∃ k, Reach24 ⟨G, F0⟩ ⟨G, fun x => F0 x || (F x && decide (x < m))⟩ k
  | 0, _ => ⟨0, by
      have e : (fun x => F0 x || (F x && decide (x < 0))) = F0 := by
        funext x
        simp
      rw [e]
      exact Reach24.refl _⟩
  | m + 1, hm => by
    obtain ⟨k, r⟩ := reach24_fillFrom G F0 F m (by omega)
    have same : ∀ x, x ≠ m →
        (F0 x || (F x && decide (x < m + 1))) = (F0 x || (F x && decide (x < m))) := by
      intro x hx
      rw [decide_lt_succ' hx]
    cases hF : F m with
    | false =>
      refine ⟨k, ?_⟩
      have e : (fun x => F0 x || (F x && decide (x < m + 1))) = fun x => F0 x || (F x && decide (x < m)) := by
        funext x
        by_cases hx : x = m
        · subst hx
          simp [hF]
        · exact same x hx
      rw [e]
      exact r
    | true =>
      cases h0 : F0 m with
      | true =>
        refine ⟨k, ?_⟩
        have e : (fun x => F0 x || (F x && decide (x < m + 1))) = fun x => F0 x || (F x && decide (x < m)) := by
          funext x
          by_cases hx : x = m
          · subst hx
            simp [h0]
          · exact same x hx
        rw [e]
        exact r
      | false =>
        refine ⟨k + 1, ?_⟩
        have st := Step24.fill ⟨G, fun x => F0 x || (F x && decide (x < m))⟩ m (by show m < G.n; omega)
          (by simp [h0])
        have e : (⟨G, fun x => F0 x || (F x && decide (x < m))⟩ : FSt).fill m =
            ⟨G, fun x => F0 x || (F x && decide (x < m + 1))⟩ := by
          simp only [FSt.fill, FSt.mk.injEq, true_and]
          funext x
          by_cases hx : x = m
          · subst hx
            simp [hF]
          · rw [if_neg hx, same x hx]
        rw [e] at st
        exact Reach24.step r st

/-- Where identifying `x0` with `0` sends each term, in a state with `N + 1` terms. -/
theorem glue_move {N x0 w' : Nat} (h2 : x0 < N) :
    glue (N + 1) x0 0 w' = if w' = 0 then x0 else if w' = N then 0 else w' := by
  unfold glue
  have e : N + 1 - 1 = N := by omega
  rw [e]
  by_cases a : w' = 0
  · rw [if_pos a, if_pos a, if_neg (by omega : ¬ x0 = N)]
  · rw [if_neg a, if_neg a]

/-- **Moving a filled term**: with `0` filled and the target's filled terms filled, identifying `x0` with `0`
leaves exactly the target's filled terms, when the target fills `x0` and not `0`. -/
theorem idF_move {N x0 : Nat} {T : Nat → Bool} (h1 : 0 < x0) (h2 : x0 < N) (h0 : T 0 = false)
    (hx0 : T x0 = true) (hT : ∀ x, T x = true → x < N) :
    idF (N + 1) x0 0 (fun x => decide (x = 0) || (T x && decide (x < N + 1))) = T := by
  funext w
  apply Bool.eq_iff_iff.2
  rw [idF_iff]
  constructor
  · rintro ⟨_, w', _, hg, hf⟩
    rw [glue_move h2] at hg
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hf
    by_cases a : w' = 0
    · rw [if_pos a] at hg
      subst hg
      exact hx0
    · rw [if_neg a] at hg
      by_cases b : w' = N
      · exfalso
        subst b
        rcases hf with e | ⟨hTN, _⟩
        · omega
        · have := hT _ hTN
          omega
      · rw [if_neg b] at hg
        subst hg
        rcases hf with e | ⟨hTw, _⟩
        · exact absurd e a
        · exact hTw
  · intro hw
    have hwN := hT w hw
    refine ⟨by omega, ?_⟩
    by_cases a : w = x0
    · subst a
      exact ⟨0, by omega, by rw [glue_move h2, if_pos rfl], by simp⟩
    · have w0 : w ≠ 0 := by
        intro e
        subst e
        rw [h0] at hw
        exact absurd hw (by decide)
      refine ⟨w, by omega, ?_, ?_⟩
      · rw [glue_move h2, if_neg w0, if_neg (by omega)]
      · simp [hw, show w < N + 1 by omega]

theorem funext_plain_fill {Y : FSt} (hY : Y.WF) : (fun x => Y.F x && decide (x < Y.G.n)) = Y.F := by
  funext x
  cases hf : Y.F x with
  | false => rfl
  | true => simp [hY.2 x hf]

theorem same24_plainSt (Y : FSt) : Same24 ⟨Y.G.plainSt, Y.F⟩ Y :=
  ⟨Same.same3 (same_plainSt Y.G).symm, fun _ _ => rfl⟩

/-- From one term (filled or not) to every result with a term whose filled terms allow it. -/
theorem reach24_from_one (F1 : Nat → Bool) (h1 : ∀ x, F1 x = true → x < 1) {Y : FSt} (hY : Y.WF)
    (hn : 0 < Y.G.n) (hf : F1 0 = true → Y.HasFilled) : ReachR24 ⟨⟨1, []⟩, F1⟩ Y := by
  have hpl : ∀ a ∈ plain Y.G.A, a.x < Y.G.n ∧ a.y < Y.G.n := fun a ha => hY.1 a (mem_of_mem_plain ha)
  have e1 : 1 + (Y.G.n - 1) = Y.G.n := by omega
  cases h0 : F1 0 with
  | false =>
    have eF : F1 = fun _ => false := by
      funext x
      cases hx : F1 x with
      | false => rfl
      | true =>
        have := h1 x hx
        have : x = 0 := by omega
        subst this
        rw [h0] at hx
        exact absurd hx (by decide)
    subst eF
    have r1 := reach24_grow 1 (fun _ => false) (Y.G.n - 1)
    rw [e1] at r1
    have r2 := reach24_atoms Y.G.n (fun _ => false) (plain Y.G.A) hpl
    have r3 := reach24_fillUpTo Y.G.plainSt Y.F Y.G.plainSt.n (Nat.le_refl _)
    have e3 : (fun x => Y.F x && decide (x < Y.G.plainSt.n)) = Y.F := funext_plain_fill hY
    rw [e3] at r3
    exact ⟨_, _, (r1.trans r2).trans r3, same24_plainSt Y⟩
  | true =>
    obtain ⟨x0, hx0, fx0⟩ := hf h0
    have eF : F1 = fun x => decide (x = 0) := by
      funext x
      cases hx : F1 x with
      | false =>
        have : x ≠ 0 := by
          intro e
          subst e
          rw [h0] at hx
          exact absurd hx (by decide)
        simp [this]
      | true =>
        have := h1 x hx
        have : x = 0 := by omega
        subst this
        rfl
    subst eF
    cases hY0 : Y.F 0 with
    | true =>
      have r1 := reach24_grow 1 (fun x => decide (x = 0)) (Y.G.n - 1)
      rw [e1] at r1
      have r2 := reach24_atoms Y.G.n (fun x => decide (x = 0)) (plain Y.G.A) hpl
      obtain ⟨k, r3⟩ := reach24_fillFrom Y.G.plainSt (fun x => decide (x = 0)) Y.F Y.G.plainSt.n (Nat.le_refl _)
      have e3 : (fun x => decide (x = 0) || (Y.F x && decide (x < Y.G.plainSt.n))) = Y.F := by
        funext x
        by_cases hx : x = 0
        · subst hx
          simp [hY0]
        · cases hfx : Y.F x with
          | false => simp [hx]
          | true => simp [hx, St.plainSt, hY.2 x hfx]
      rw [e3] at r3
      exact ⟨_, _, (r1.trans r2).trans r3, same24_plainSt Y⟩
    | false =>
      have hx0' : 0 < x0 := by
        cases x0 with
        | zero => rw [hY0] at fx0; exact absurd fx0 (by decide)
        | succ k => omega
      -- grow to one more term than the target, fill the target's terms, move the filled term onto `x0`
      have r1 := reach24_grow 1 (fun x => decide (x = 0)) Y.G.n
      rw [Nat.add_comm 1 Y.G.n] at r1
      obtain ⟨k, r2⟩ := reach24_fillFrom ⟨Y.G.n + 1, []⟩ (fun x => decide (x = 0)) Y.F (Y.G.n + 1) (Nat.le_refl _)
      have st := Step24.identify ⟨⟨Y.G.n + 1, []⟩, fun x => decide (x = 0) || (Y.F x && decide (x < Y.G.n + 1))⟩
        x0 0 (by show x0 < Y.G.n + 1; omega) (by show 0 < Y.G.n + 1; omega) (by omega)
      have e : (⟨⟨Y.G.n + 1, []⟩, fun x => decide (x = 0) || (Y.F x && decide (x < Y.G.n + 1))⟩ : FSt).identify x0 0 =
          ⟨⟨Y.G.n, []⟩, Y.F⟩ := by
        simp only [FSt.identify, St.identify, List.map_nil, FSt.mk.injEq]
        exact ⟨by rw [Nat.add_sub_cancel], idF_move hx0' hx0 hY0 fx0 hY.2⟩
      rw [e] at st
      have r3 := reach24_atoms Y.G.n Y.F (plain Y.G.A) hpl
      exact ⟨_, _, ((r1.trans r2).step st).trans r3, same24_plainSt Y⟩

/-- **Reachability between results (reading C-I1)**: a result reaches another exactly when the other has a
term or the first is empty, and the other has a filled term or the first has none. -/
theorem reach24_criterion {X Y : FSt} (hX : X.WF) (hY : Y.WF) :
    ReachR24 X Y ↔ (0 < Y.G.n ∨ X.G.n = 0) ∧ (Y.HasFilled ∨ ¬ X.HasFilled) := by
  constructor
  · rintro ⟨k, Y', r, s⟩
    refine ⟨?_, ?_⟩
    · by_cases h0 : X.G.n = 0
      · exact Or.inr h0
      · obtain ⟨j, rG⟩ := r.forget
        exact Or.inl (s.n ▸ rG.n_pos hX.1 (by omega))
    · by_cases hf : X.HasFilled
      · exact Or.inl (s.hasFilled (r.hasFilled hf))
      · exact Or.inr hf
  · rintro ⟨hn, hfill⟩
    obtain ⟨⟨n, A⟩, F⟩ := X
    by_cases h0 : n = 0
    · subst h0
      have hA : A = [] := by
        have := eq_empty_of_wf (G := ⟨0, A⟩) hX.1 rfl
        cases this
        rfl
      subst hA
      have hF : F = fun _ => false := by
        funext x
        exact FSt.F_out (X := ⟨⟨0, []⟩, F⟩) hX (Nat.zero_le x)
      subst hF
      exact ⟨_, _, reach24_upper hY, same24_plainSt Y⟩
    · have hYn : 0 < Y.G.n := by
        rcases hn with h | h
        · exact h
        · exact absurd h h0
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have r1 := reach24_clear (m + 1) F A
      obtain ⟨F', r2, hiff, h1⟩ := reach24_collapse m F (fun x hx => hX.2 x hx)
      obtain ⟨k, Y', r3, s⟩ := reach24_from_one F' h1 hY hYn (fun h => by
        rcases hfill with h' | h'
        · exact h'
        · exact absurd (hiff.1 h) h')
      exact ⟨_, _, (r1.trans r2).trans r3, s⟩

/-- **The twenty-third's criterion fails here**: `a` filled has a term, `a` unfilled has a term, and the
first does not reach the second. -/
theorem twentythird_criterion_fails : ¬ ReachR24 oneFilled (ofSt ⟨1, []⟩) := by
  rintro ⟨k, Y', r, s⟩
  obtain ⟨x, hx, fx⟩ := s.hasFilled (r.hasFilled ⟨0, by decide, rfl⟩)
  exact Bool.noConfusion fx

/-- Results with a filled term reach each other both ways; so do results with no filled term and a term. -/
theorem reach24_mutual {X Y : FSt} (hX : X.WF) (hY : Y.WF) (gx : 0 < X.G.n) (gy : 0 < Y.G.n)
    (h : X.HasFilled ↔ Y.HasFilled) : ReachR24 X Y ∧ ReachR24 Y X := by
  refine ⟨(reach24_criterion hX hY).2 ⟨Or.inl gy, ?_⟩, (reach24_criterion hY hX).2 ⟨Or.inl gx, ?_⟩⟩
  · by_cases hf : X.HasFilled
    · exact Or.inl (h.1 hf)
    · exact Or.inr hf
  · by_cases hf : Y.HasFilled
    · exact Or.inl (h.2 hf)
    · exact Or.inr hf

/-! ## The unchosen readings of identifying -/

/-- Reading C-I2: a term of an identification's outcome is filled only when every term that goes onto it was. -/
def idF2 (n u v : Nat) (F : Nat → Bool) (w : Nat) : Bool :=
  decide (w < n - 1) && (List.range n).all (fun w' => !(decide (glue n u v w' = w)) || F w')

/-- **Under C-I2 a filled term can go away**: `a` filled, a term added, the two identified — nothing is
filled. -/
theorem i2_unfills : Step24 oneFilled oneFilled.addTerm ∧ (fun w => idF2 2 0 1 oneFilled.addTerm.F w) = fun _ => false := by
  refine ⟨Step24.addTerm _, ?_⟩
  funext w
  cases w with
  | zero => rfl
  | succ k =>
    simp only [idF2]
    have : decide (k + 1 < 2 - 1) = false := decide_eq_false (by omega)
    rw [this, Bool.false_and]

end Twentyfourth
