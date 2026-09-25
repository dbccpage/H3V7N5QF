import Twentyfifth.Map

/-!
# Reachability and the exchange of the two relations

`ReachR25 A B`: some sequence of changes from `A` ends at a state of `B`'s
result.  Derived here:
* **the twenty-third's criterion holds** (`reach25_criterion`): a result reaches
  another exactly when the other has a term or the first is the empty state.
  The path: remove every assertion, identify the terms down to one — a
  well-formed state with one term has nothing filled, so every filled triple
  is gone (`nothing_filled_of_lt_three`) — add terms, add the plain part of the
  target, fill its triples.  So results with a term reach each other both ways
  (`reach25_mutual`), and the empty result is never returned to;
* **the exchange of the two relations is still a symmetry**: it carries every
  change to a change (`Step25.swap`), keeps the sameness both ways
  (`same25_swap_iff`), the cost (`cost25_swap`), reachability
  (`reach25_swap`) and which triples balance (`told_swap`).
-/

namespace Twentyfifth

open Twentysecond Twentythird

/-- Some sequence of changes from `A` ends at a state of `B`'s result. -/
def ReachR25 (A B : FSt) : Prop := ∃ k B', Reach25 A B' k ∧ Same25 B' B

theorem Step25.n_pos {A B : FSt} (h : Step25 A B) (hw : A.WF) : 0 < B.G.n := by
  cases h with
  | addTerm => exact (Step.addTerm A.G).n_pos hw.1
  | add a hx hy => exact (Step.add A.G a hx hy).n_pos hw.1
  | remove a ha => exact (Step.remove A.G a ha).n_pos hw.1
  | identify u v hu hv huv => exact (Step.identify A.G u v hu hv huv).n_pos hw.1
  | fill t hwt _ _ =>
    show 0 < A.G.n
    have := hwt.1
    omega

theorem Reach25.n_pos {A B : FSt} {k : Nat} (h : Reach25 A B k) (hw : A.WF) (hn : 0 < A.G.n) : 0 < B.G.n := by
  induction h with
  | refl => exact hn
  | step r st _ => exact st.n_pos (r.wf hw)

/-- Removing every assertion, the filled triples kept. -/
theorem reach25_clear (n : Nat) (F : List Tri) : ∀ A : List Atom, Reach25 ⟨⟨n, A⟩, F⟩ ⟨⟨n, []⟩, F⟩ A.length
  | [] => Reach25.refl _
  | a :: t => by
    have h1 : Reach25 ⟨⟨n, a :: t⟩, F⟩ ⟨⟨n, t⟩, F⟩ 1 := by
      have st := Step25.remove ⟨⟨n, a :: t⟩, F⟩ a List.mem_cons_self
      have e : (⟨⟨n, a :: t⟩, F⟩ : FSt).remove a = ⟨⟨n, t⟩, F⟩ := by
        simp only [FSt.remove, St.remove, del_cons_self]
      rw [e] at st
      exact Reach25.single st
    have := Reach25.trans h1 (reach25_clear n F t)
    simpa [Nat.add_comm] using this

/-- Identifying the terms down to one, the filled triples carried. -/
theorem reach25_collapse : ∀ (m : Nat) (F : List Tri), ∃ F', Reach25 ⟨⟨m + 1, []⟩, F⟩ ⟨⟨1, []⟩, F'⟩ m
  | 0, F => ⟨F, Reach25.refl _⟩
  | m + 1, F => by
    have st := Step25.identify ⟨⟨m + 2, []⟩, F⟩ 0 (m + 1) (by show 0 < m + 2; omega)
      (by show m + 1 < m + 2; omega) (by omega)
    have e : (⟨⟨m + 2, []⟩, F⟩ : FSt).identify 0 (m + 1) = ⟨⟨m + 1, []⟩, carry (m + 2) 0 (m + 1) F⟩ := rfl
    rw [e] at st
    obtain ⟨F', r⟩ := reach25_collapse m (carry (m + 2) 0 (m + 1) F)
    have := Reach25.trans (Reach25.single st) r
    rw [Nat.add_comm 1 m] at this
    exact ⟨F', this⟩

/-- Adding terms, nothing asserted or filled. -/
theorem reach25_grow (n m : Nat) : Reach25 (embed ⟨n, []⟩) (embed ⟨n + m, []⟩) m :=
  embed_reach (reach_grow n m)

/-- From `n` terms asserting nothing and nothing filled, the plain part of `B` and its filled triples. -/
theorem reach25_fill_in {B : FSt} (hB : B.WF) :
    Reach25 (embed ⟨B.G.n, []⟩) ⟨B.G.plainSt, B.F⟩ ((plain B.G.A).length + B.F.length) := by
  have r1 : Reach25 (embed ⟨B.G.n, []⟩) (embed B.G.plainSt) (plain B.G.A).length :=
    embed_reach (addReach_atoms B.G.n (plain B.G.A) (fun a ha => hB.1 a (mem_of_mem_plain ha))).reach
  exact Reach25.trans r1 (reach_fill_all B.G.plainSt B.F (fun t ht => hB.2.1 t ht) hB.2.2)

/-- **Reachability between results: a result reaches another exactly when the other has a term or the first
is the empty state.** -/
theorem reach25_criterion {A B : FSt} (hA : A.WF) (hB : B.WF) : ReachR25 A B ↔ 0 < B.G.n ∨ A.G.n = 0 := by
  constructor
  · rintro ⟨k, B', r, s⟩
    by_cases h0 : A.G.n = 0
    · exact Or.inr h0
    · exact Or.inl (s.n ▸ r.n_pos hA (by omega))
  · intro h
    by_cases h0 : A.G.n = 0
    · have hG : A.G = empty := eq_empty_of_wf hA.1 h0
      have hF : A.F = [] := nothing_filled_of_lt_three hA (by omega)
      have e : A = empty25 := by
        cases A with
        | mk G F =>
          simp only at hG hF
          subst hG
          subst hF
          rfl
      rw [e]
      exact ⟨_, _, reach_build hB, same_build B⟩
    · have hn : 0 < B.G.n := by omega
      obtain ⟨m, hm⟩ : ∃ m, A.G.n = m + 1 := ⟨A.G.n - 1, by omega⟩
      have r1 : Reach25 A ⟨⟨A.G.n, []⟩, A.F⟩ A.G.A.length := by
        cases A with
        | mk G F =>
          cases G with
          | mk n As => exact reach25_clear n F As
      rw [hm] at r1
      obtain ⟨F', r2⟩ := reach25_collapse m A.F
      have r12 := Reach25.trans r1 r2
      have hw := r12.wf hA
      have hF' : F' = [] := nothing_filled_of_lt_three hw (by show 1 < 3; omega)
      rw [hF'] at r12
      have r3 := Reach25.trans r12 (reach25_grow 1 (B.G.n - 1))
      have e : 1 + (B.G.n - 1) = B.G.n := by omega
      rw [e] at r3
      exact ⟨_, _, Reach25.trans r3 (reach25_fill_in hB), same_build B⟩

theorem reach25_mutual {A B : FSt} (hA : A.WF) (hB : B.WF) (a : 0 < A.G.n) (b : 0 < B.G.n) :
    ReachR25 A B ∧ ReachR25 B A :=
  ⟨(reach25_criterion hA hB).2 (Or.inl b), (reach25_criterion hB hA).2 (Or.inl a)⟩

/-- The empty result is never returned to. -/
theorem empty_never_returned25 {A : FSt} (hA : A.WF) (a : 0 < A.G.n) : ¬ ReachR25 A empty25 := by
  intro h
  rcases (reach25_criterion hA empty25_wf).1 h with e | e
  · exact absurd e (by decide)
  · omega

/-! ## Which changes respect the sameness -/

/-- **Filling respects the sameness**: the same triple filled in two states of one result gives one result. -/
theorem Same25.fill {A B : FSt} (h : Same25 A B) (t : Tri) : Same25 (A.fill t) (B.fill t) :=
  ⟨h.1, h.2.cons _⟩

/-- **Adding a term does not** (the twenty-third's witness, nothing filled): `a b` and `a b; arb bsa` are one
result, and with a term added they are two. -/
theorem addTerm_not_respected25 :
    Same25 (embed raisedPair) (embed ⟨2, []⟩) ∧ ¬ Same25 (embed raisedPair).addTerm (embed ⟨2, []⟩).addTerm :=
  ⟨embed_same_iff.2 raisedPair_nothing, fun s => addTerm_not_respected.2 s.1⟩

/-! ## The exchange of the two relations -/

/-- The two relations exchanged; the filled triples kept. -/
def FSt.swap (A : FSt) : FSt := ⟨A.G.swap, A.F⟩

theorem FSt.swap_swap (A : FSt) : A.swap.swap = A := by
  cases A with
  | mk G F =>
    show (⟨G.swap.swap, F⟩ : FSt) = ⟨G, F⟩
    rw [Twentysecond.swap_swap]

theorem Same25.swap {A B : FSt} (h : Same25 A B) : Same25 A.swap B.swap := ⟨h.1.swap, h.2⟩

/-- **The exchange keeps the sameness, both ways.** -/
theorem same25_swap_iff {A B : FSt} : Same25 A B ↔ Same25 A.swap B.swap := by
  constructor
  · exact Same25.swap
  · intro h
    have := h.swap
    rwa [FSt.swap_swap, FSt.swap_swap] at this

theorem swap25_wf {A : FSt} (hw : A.WF) : A.swap.WF := ⟨swap_wf hw.1, hw.2.1, hw.2.2⟩

/-- **The exchange carries every change to a change of the same kind.** -/
theorem Step25.swap {A B : FSt} (st : Step25 A B) : Step25 A.swap B.swap := by
  cases st with
  | addTerm => exact Step25.addTerm A.swap
  | add a hx hy => exact Step25.add A.swap a.partner hx hy
  | remove a ha =>
    have e : (A.remove a).swap = A.swap.remove a.partner := by
      simp only [FSt.swap, FSt.remove, St.swap, St.remove, map_del_of_inj partner_injective]
    rw [e]
    exact Step25.remove A.swap a.partner (List.mem_map_of_mem ha)
  | identify u v hu hv huv =>
    have e : (A.identify u v).swap = A.swap.identify u v := by
      simp only [FSt.swap, FSt.identify, St.swap, St.identify, List.map_map]
      rfl
    rw [e]
    exact Step25.identify A.swap u v hu hv huv
  | fill t hw hd hn => exact Step25.fill A.swap t hw hd hn

theorem Reach25.swap {A B : FSt} {k : Nat} (h : Reach25 A B k) : Reach25 A.swap B.swap k := by
  induction h with
  | refl => exact Reach25.refl _
  | step _ st ih => exact Reach25.step ih st.swap

theorem empty25_swap : empty25.swap = empty25 := rfl

/-- **The exchange keeps the cost.** -/
theorem cost25_swap {A : FSt} {c : Nat} : Cost25 A c ↔ Cost25 A.swap c := by
  have key : ∀ {A : FSt}, Cost25 A c → Cost25 A.swap c := by
    intro A ⟨⟨B, s, r⟩, lo⟩
    refine ⟨⟨B.swap, s.swap, empty25_swap ▸ r.swap⟩, fun C k sC rC => ?_⟩
    have := sC.swap
    rw [FSt.swap_swap] at this
    exact lo C.swap k this (empty25_swap ▸ rC.swap)
  constructor
  · exact key
  · intro h
    have := key h
    rwa [FSt.swap_swap] at this

/-- **The exchange keeps reachability.** -/
theorem reach25_swap {A B : FSt} (hA : A.WF) (hB : B.WF) : ReachR25 A B ↔ ReachR25 A.swap B.swap := by
  rw [reach25_criterion hA hB, reach25_criterion (swap25_wf hA) (swap25_wf hB)]
  rfl

/-- **The exchange keeps which filled triples balance**: a result is told exactly when its exchange is. -/
theorem told_swap (A : FSt) : Told A ↔ Told A.swap := by
  constructor
  · rintro ⟨t, ht, hn⟩
    exact ⟨t, ht, fun b => hn ((balanced_swap A.G t).1 b)⟩
  · rintro ⟨t, ht, hn⟩
    exact ⟨t, ht, fun b => hn ((balanced_swap A.G t).2 b)⟩

end Twentyfifth
