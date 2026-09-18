import H3V7N5QF.Finite

/-!
# No result is reached in fewer changes than its cost

`lostA s` counts the givens that `s` has destroyed when `bra` was not asserted
to begin with: `arb` no longer asserted (1), or `a` and `b` identified (2, the
identification and the assertion).  `lostB` does the same when `bra` was
asserted.  `costA s = size s + 2 * lostA s`.

Derived here: one performed change raises the cost by at most one
(`Step.costA_le`, `Step.costB_le`); so a result reached in `n` changes from
what is given has cost at most `n` plus the cost of what is given
(`fewest_changes_lower_A`, `fewest_changes_lower_B`).  A refused change changes
nothing, so counting refused changes only makes `n` larger.
-/

namespace Seed

open St

/-- `1` if `xry` is not asserted, `0` if it is. -/
def miss (s : St) (x y : ℕ) : ℕ := if (x, y) ∈ s.A then 0 else 1

/-- Destroyed givens, when what is given is `arb` alone. -/
def lostA (s : St) : ℕ := if s.a = s.b then 2 else miss s s.a s.b

/-- Destroyed givens, when `arb` and `bra` were asserted to begin with. -/
def lostB (s : St) : ℕ := if s.a = s.b then 3 else miss s s.a s.b + miss s s.b s.a

/-- Size plus two for each destroyed given (`bra` not asserted to begin with). -/
def costA (s : St) : ℕ := s.size + 2 * lostA s

/-- Size plus two for each destroyed given (`bra` asserted to begin with). -/
def costB (s : St) : ℕ := s.size + 2 * lostB s

/-! ## Size under each kind of change -/

theorem size_addTerm {s : St} {t : ℕ} (ht : t ∉ s.T) : (s.addTerm t).size = s.size + 1 := by
  simp only [St.size, St.addTerm, Finset.card_insert_of_notMem ht]
  omega

theorem size_addAssertion {s : St} {x y : ℕ} (hnew : (x, y) ∉ s.A) :
    (s.addAssertion x y).size = s.size + 1 := by
  simp only [St.size, St.addAssertion, Finset.card_insert_of_notMem hnew]
  omega

theorem size_remove {s : St} {p : ℕ × ℕ} (hp : p ∈ s.A) : (s.remove p).size + 1 = s.size := by
  have := Finset.card_erase_add_one hp
  simp only [St.size, St.remove]
  omega

theorem size_identify {s : St} {u v : ℕ} (hv : v ∈ s.T) : (s.identify u v).size + 1 ≤ s.size := by
  have h1 := Finset.card_erase_add_one hv
  have h2 : (s.A.image (Prod.map (merge u v) (merge u v))).card ≤ s.A.card := Finset.card_image_le
  simp only [St.size, St.identify]
  omega

/-! ## Destroyed givens under each kind of change -/

theorem miss_of_mem {s : St} {x y : ℕ} (h : (x, y) ∈ s.A) : miss s x y = 0 := by
  simp [miss, h]

theorem miss_of_not_mem {s : St} {x y : ℕ} (h : (x, y) ∉ s.A) : miss s x y = 1 := by
  simp [miss, h]

theorem miss_le_one (s : St) (x y : ℕ) : miss s x y ≤ 1 := by
  by_cases h : (x, y) ∈ s.A
  · rw [miss_of_mem h]; omega
  · rw [miss_of_not_mem h]

theorem lostA_of_eq {s : St} (h : s.a = s.b) : lostA s = 2 := by
  simp [lostA, h]

theorem lostA_of_ne {s : St} (h : s.a ≠ s.b) : lostA s = miss s s.a s.b := by
  simp [lostA, h]

theorem lostB_of_eq {s : St} (h : s.a = s.b) : lostB s = 3 := by
  simp [lostB, h]

theorem lostB_of_ne {s : St} (h : s.a ≠ s.b) : lostB s = miss s s.a s.b + miss s s.b s.a := by
  simp [lostB, h]

theorem lostA_le_two (s : St) : lostA s ≤ 2 := by
  by_cases h : s.a = s.b
  · rw [lostA_of_eq h]
  · have := miss_le_one s s.a s.b
    rw [lostA_of_ne h]
    omega

theorem lostB_le_three (s : St) : lostB s ≤ 3 := by
  by_cases h : s.a = s.b
  · rw [lostB_of_eq h]
  · have h1 := miss_le_one s s.a s.b
    have h2 := miss_le_one s s.b s.a
    rw [lostB_of_ne h]
    omega

theorem lostA_addTerm (s : St) (t : ℕ) : lostA (s.addTerm t) = lostA s := rfl

theorem lostB_addTerm (s : St) (t : ℕ) : lostB (s.addTerm t) = lostB s := rfl

/-- Adding an assertion destroys nothing. -/
theorem miss_addAssertion (s : St) (x y u v : ℕ) :
    miss (s.addAssertion x y) u v ≤ miss s u v := by
  by_cases h : (u, v) ∈ s.A
  · have h' : (u, v) ∈ (s.addAssertion x y).A := Finset.mem_insert_of_mem h
    rw [miss_of_mem h', miss_of_mem h]
  · have := miss_le_one (s.addAssertion x y) u v
    rw [miss_of_not_mem h]
    exact this

theorem lostA_addAssertion (s : St) (x y : ℕ) : lostA (s.addAssertion x y) ≤ lostA s := by
  by_cases h : s.a = s.b
  · rw [lostA_of_eq (s := s.addAssertion x y) h, lostA_of_eq h]
  · rw [lostA_of_ne (s := s.addAssertion x y) h, lostA_of_ne h]
    exact miss_addAssertion s x y s.a s.b

theorem lostB_addAssertion (s : St) (x y : ℕ) : lostB (s.addAssertion x y) ≤ lostB s := by
  by_cases h : s.a = s.b
  · rw [lostB_of_eq (s := s.addAssertion x y) h, lostB_of_eq h]
  · rw [lostB_of_ne (s := s.addAssertion x y) h, lostB_of_ne h]
    exact Nat.add_le_add (miss_addAssertion s x y s.a s.b) (miss_addAssertion s x y s.b s.a)

/-- Removing another assertion leaves `xry` as it was. -/
theorem miss_remove_of_ne {s : St} {p : ℕ × ℕ} {x y : ℕ} (h : p ≠ (x, y)) :
    miss (s.remove p) x y = miss s x y := by
  by_cases hm : (x, y) ∈ s.A
  · have h' : (x, y) ∈ (s.remove p).A := Finset.mem_erase.2 ⟨fun e => h e.symm, hm⟩
    rw [miss_of_mem h', miss_of_mem hm]
  · have h' : (x, y) ∉ (s.remove p).A := fun hh => hm (Finset.mem_of_mem_erase hh)
    rw [miss_of_not_mem h', miss_of_not_mem hm]

theorem lostA_remove (s : St) (p : ℕ × ℕ) : lostA (s.remove p) ≤ lostA s + 1 := by
  by_cases h : s.a = s.b
  · rw [lostA_of_eq (s := s.remove p) h, lostA_of_eq h]
    omega
  · have := miss_le_one (s.remove p) s.a s.b
    rw [lostA_of_ne (s := s.remove p) h]
    exact this.trans (Nat.le_add_left 1 _)

/-- One removal destroys at most one given: it cannot be both `arb` and `bra`. -/
theorem lostB_remove (s : St) (p : ℕ × ℕ) : lostB (s.remove p) ≤ lostB s + 1 := by
  by_cases h : s.a = s.b
  · rw [lostB_of_eq (s := s.remove p) h, lostB_of_eq h]
    omega
  · rw [lostB_of_ne (s := s.remove p) h, lostB_of_ne h]
    by_cases h1 : p = (s.a, s.b)
    · have h2 : p ≠ (s.b, s.a) := by
        intro h2
        rw [h1] at h2
        exact h (Prod.mk.inj h2).1
      have e := miss_remove_of_ne (s := s) h2
      have le := miss_le_one (s.remove p) s.a s.b
      show miss (s.remove p) s.a s.b + miss (s.remove p) s.b s.a ≤ _
      rw [e]
      omega
    · have e := miss_remove_of_ne (s := s) h1
      have le := miss_le_one (s.remove p) s.b s.a
      show miss (s.remove p) s.a s.b + miss (s.remove p) s.b s.a ≤ _
      rw [e]
      omega

/-- What is asserted stays asserted, between the replaced terms, after an identification. -/
theorem miss_identify {s : St} {u v x y : ℕ} (h : (x, y) ∈ s.A) :
    miss (s.identify u v) (merge u v x) (merge u v y) = 0 :=
  miss_of_mem (mem_identify.2 ⟨(x, y), h, rfl⟩)

theorem lostA_identify {s : St} (hs : s.Legal) {u v : ℕ} (h1 : (u, v) ∉ s.A)
    (h2 : (v, u) ∉ s.A) : lostA (s.identify u v) ≤ lostA s + 1 := by
  by_cases hab : s.a = s.b
  · have h' : (s.identify u v).a = (s.identify u v).b := by simp [St.identify, hab]
    rw [lostA_of_eq h', lostA_of_eq hab]
    omega
  · by_cases hmem : (s.a, s.b) ∈ s.A
    · have hapart : (s.identify u v).a ≠ (s.identify u v).b :=
        identify_keeps_apart hs h1 h2 hmem
      have hz : miss (s.identify u v) (s.identify u v).a (s.identify u v).b = 0 :=
        miss_identify hmem
      rw [lostA_of_ne hapart, hz]
      omega
    · have := lostA_le_two (s.identify u v)
      rw [lostA_of_ne hab, miss_of_not_mem hmem]
      exact this

theorem lostB_identify {s : St} (hs : s.Legal) {u v : ℕ} (h1 : (u, v) ∉ s.A)
    (h2 : (v, u) ∉ s.A) : lostB (s.identify u v) ≤ lostB s + 1 := by
  by_cases hab : s.a = s.b
  · have h' : (s.identify u v).a = (s.identify u v).b := by simp [St.identify, hab]
    rw [lostB_of_eq h', lostB_of_eq hab]
    omega
  · rw [lostB_of_ne hab]
    by_cases hab' : (s.a, s.b) ∈ s.A
    · have hapart : (s.identify u v).a ≠ (s.identify u v).b :=
        identify_keeps_apart hs h1 h2 hab'
      have z1 : miss (s.identify u v) (s.identify u v).a (s.identify u v).b = 0 :=
        miss_identify hab'
      rw [lostB_of_ne hapart, z1, miss_of_mem hab']
      by_cases hba' : (s.b, s.a) ∈ s.A
      · have z2 : miss (s.identify u v) (s.identify u v).b (s.identify u v).a = 0 :=
          miss_identify hba'
        rw [z2]
        omega
      · have := miss_le_one (s.identify u v) (s.identify u v).b (s.identify u v).a
        rw [miss_of_not_mem hba']
        omega
    · by_cases hba' : (s.b, s.a) ∈ s.A
      · have hapart : (s.identify u v).a ≠ (s.identify u v).b := fun h =>
          identify_keeps_apart hs h1 h2 hba' h.symm
        have z2 : miss (s.identify u v) (s.identify u v).b (s.identify u v).a = 0 :=
          miss_identify hba'
        have := miss_le_one (s.identify u v) (s.identify u v).a (s.identify u v).b
        rw [lostB_of_ne hapart, z2, miss_of_not_mem hab']
        omega
      · have := lostB_le_three (s.identify u v)
        rw [miss_of_not_mem hab', miss_of_not_mem hba']
        omega

/-! ## One change raises the cost by at most one -/

theorem Step.costA_le {s s' : St} (h : Step s s') (hs : s.Legal) : costA s' ≤ costA s + 1 := by
  unfold costA
  cases h with
  | addTerm t ht =>
    rw [size_addTerm ht, lostA_addTerm]
    omega
  | addAssertion x y hx hy hxy hnew =>
    have := lostA_addAssertion s x y
    rw [size_addAssertion hnew]
    omega
  | remove p hp =>
    have h1 := size_remove hp
    have h2 := lostA_remove s p
    omega
  | identify u v hu hv huv h1 h2 =>
    have h3 := size_identify (u := u) hv
    have h4 := lostA_identify hs h1 h2
    omega

theorem Step.costB_le {s s' : St} (h : Step s s') (hs : s.Legal) : costB s' ≤ costB s + 1 := by
  unfold costB
  cases h with
  | addTerm t ht =>
    rw [size_addTerm ht, lostB_addTerm]
    omega
  | addAssertion x y hx hy hxy hnew =>
    have := lostB_addAssertion s x y
    rw [size_addAssertion hnew]
    omega
  | remove p hp =>
    have h1 := size_remove hp
    have h2 := lostB_remove s p
    omega
  | identify u v hu hv huv h1 h2 =>
    have h3 := size_identify (u := u) hv
    have h4 := lostB_identify hs h1 h2
    omega

/-! ## Sequences of changes -/

/-- `Reach s t n`: `t` is reached from `s` by `n` performed changes. -/
inductive Reach : St → St → ℕ → Prop
  | refl (s : St) : Reach s s 0
  | step {s t u : St} {n : ℕ} : Reach s t n → Step t u → Reach s u (n + 1)

theorem Reach.legal {s t : St} {n : ℕ} (h : Reach s t n) (hs : s.Legal) : t.Legal := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.legal ih

theorem Reach.wf {s t : St} {n : ℕ} (h : Reach s t n) (hs : s.WF) : t.WF := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.wf ih

/-- No sequence of changes reaches a state without terms. -/
theorem Reach.nonempty {s t : St} {n : ℕ} (h : Reach s t n) (hs : s.T.Nonempty) :
    t.T.Nonempty := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.nonempty ih

/-- Identifying `a` and `b` cannot be undone by any sequence of changes. -/
theorem Reach.names_stay_merged {s t : St} {n : ℕ} (h : Reach s t n) (hab : s.a = s.b) :
    t.a = t.b := by
  induction h with
  | refl => exact hab
  | step _ st ih => exact st.names_stay_merged ih

/-- After `a` and `b` are identified, `arb` is never asserted again. -/
theorem Reach.arb_gone_for_good {s t : St} {n : ℕ} (h : Reach s t n) (hs : s.Legal)
    (hab : s.a = s.b) : (t.a, t.b) ∉ t.A := by
  have := h.names_stay_merged hab
  rw [this]
  exact h.legal hs _

theorem Reach.costA_le {s t : St} {n : ℕ} (h : Reach s t n) (hs : s.Legal) :
    costA t ≤ costA s + n := by
  induction h with
  | refl => omega
  | step r st ih =>
    have := st.costA_le (r.legal hs)
    omega

theorem Reach.costB_le {s t : St} {n : ℕ} (h : Reach s t n) (hs : s.Legal) :
    costB t ≤ costB s + n := by
  induction h with
  | refl => omega
  | step r st ih =>
    have := st.costB_le (r.legal hs)
    omega

/-! ## What is given -/

/-- What is given, `bra` not asserted: terms `a = 0`, `b = 1`; `arb`. -/
def givenA : St := ⟨{0, 1}, {(0, 1)}, 0, 1⟩

/-- What is given, `bra` asserted: terms `a = 0`, `b = 1`; `arb`, `bra`. -/
def givenB : St := ⟨{0, 1}, {(0, 1), (1, 0)}, 0, 1⟩

theorem givenA_legal : givenA.Legal := by
  intro x hx
  simp [givenA] at hx
  omega

theorem givenB_legal : givenB.Legal := by
  intro x hx
  simp [givenB] at hx
  omega

theorem givenA_wf : givenA.WF := by
  refine ⟨fun p hp => ?_, by simp [givenA], by simp [givenA]⟩
  simp only [givenA, Finset.mem_singleton] at hp
  subst hp
  simp [givenA]

theorem givenB_wf : givenB.WF := by
  refine ⟨fun p hp => ?_, by simp [givenB], by simp [givenB]⟩
  simp only [givenB, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl <;> simp [givenB]

theorem costA_givenA : costA givenA = 3 := by decide

theorem costB_givenB : costB givenB = 4 := by decide

/-- **Lower bound, `bra` not asserted to begin with.**  A state reached from what is
given by `n` changes has `size + 2 * (destroyed givens) ≤ n + 3`. -/
theorem fewest_changes_lower_A {t : St} {n : ℕ} (h : Reach givenA t n) : costA t ≤ n + 3 := by
  have := h.costA_le givenA_legal
  rw [costA_givenA] at this
  omega

/-- **Lower bound, `bra` asserted to begin with.** -/
theorem fewest_changes_lower_B {t : St} {n : ℕ} (h : Reach givenB t n) : costB t ≤ n + 4 := by
  have := h.costB_le givenB_legal
  rw [costB_givenB] at this
  omega

/-- Each alternative for what is given is one change away from the other. -/
theorem givenA_to_givenB : Reach givenA givenB 1 := by
  have st : Step givenA (givenA.addAssertion 1 0) :=
    Step.addAssertion givenA 1 0 (by simp [givenA]) (by simp [givenA]) (by omega)
      (by simp [givenA])
  have e : givenA.addAssertion 1 0 = givenB := by
    simp only [givenA, givenB, St.addAssertion]
    congr 1
    exact Finset.pair_comm _ _
  exact e ▸ Reach.step (Reach.refl givenA) st

theorem givenB_to_givenA : Reach givenB givenA 1 := by
  have st : Step givenB (givenB.remove (1, 0)) := Step.remove givenB (1, 0) (by simp [givenB])
  have e : givenB.remove (1, 0) = givenA := by
    simp only [givenA, givenB, St.remove]
    congr 1
  exact e ▸ Reach.step (Reach.refl givenB) st

end Seed
