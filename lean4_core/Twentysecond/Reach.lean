import Twentysecond.Merge

/-!
# Reachability between results: the ninth's criterion, re-proved

`ReachR G H`: some sequence of changes from `G` ends at a state of `H`'s
result.  By `step_of_same`, starting from `G` or from any other state of its
result reaches the same results (`reach_of_same`), so this is reachability
between results (reading C-X).

Derived here (the ninth's D8, re-proved for this seed's results):
`reach_criterion` — a result reaches another exactly when the other has a
term or the first is the empty state.  So results with a term reach each
other both ways (`reach_mutual`), and the empty result is never returned to
(`empty_never_returned`).  The paths: remove every assertion, identify the
terms down to one, add terms, add the plain part of the target.
-/

namespace Twentysecond

/-- Some sequence of changes from `G` ends at a state of `H`'s result. -/
def ReachR (G H : St) : Prop := ∃ k H', Reach G H' k ∧ Same H' H

/-- Starting from any state of a result reaches the same results. -/
theorem reach_of_same {G H G' : St} {k : Nat} (hs : Same G H) (hG : G.WF) (r : Reach G G' k) :
    ∃ H', Reach H H' k ∧ Same G' H' := by
  induction r with
  | refl => exact ⟨H, Reach.refl H, hs⟩
  | step r st ih =>
    obtain ⟨H1, r1, s1⟩ := ih
    obtain ⟨H2, st2, s2⟩ := step_of_same s1 (r.wf hG) st
    exact ⟨H2, Reach.step r1 st2, s2⟩

theorem reach_clear (n : Nat) : ∀ A : List Atom, Reach ⟨n, A⟩ ⟨n, []⟩ A.length
  | [] => Reach.refl _
  | a :: t => by
    have h1 : Reach ⟨n, a :: t⟩ ⟨n, t⟩ 1 := by
      have st := Step.remove ⟨n, a :: t⟩ a List.mem_cons_self
      simp only [St.remove, del_cons_self] at st
      exact Reach.single st
    have := Reach.trans h1 (reach_clear n t)
    simpa [Nat.add_comm] using this

theorem reach_collapse : ∀ m : Nat, Reach ⟨m + 1, []⟩ ⟨1, []⟩ m
  | 0 => Reach.refl _
  | m + 1 => by
    have st := Step.identify ⟨m + 2, []⟩ 0 (m + 1) (by show 0 < m + 2; omega)
      (by show m + 1 < m + 2; omega) (by omega)
    have e : (⟨m + 2, []⟩ : St).identify 0 (m + 1) = ⟨m + 1, []⟩ := rfl
    rw [e] at st
    have := Reach.trans (Reach.single st) (reach_collapse m)
    rw [Nat.add_comm 1 m] at this
    exact this

theorem reach_grow (n : Nat) : ∀ m : Nat, Reach ⟨n, []⟩ ⟨n + m, []⟩ m
  | 0 => Reach.refl _
  | m + 1 => Reach.step (reach_grow n m) (Step.addTerm ⟨n + m, []⟩)

/-- **Reachability between results**: a result reaches another exactly when the other has a term or
the first is the empty state. -/
theorem reach_criterion {G H : St} (hG : G.WF) (hH : H.WF) : ReachR G H ↔ 0 < H.n ∨ G.n = 0 := by
  constructor
  · rintro ⟨k, H', r, hs⟩
    by_cases h0 : G.n = 0
    · exact Or.inr h0
    · exact Or.inl (hs.1 ▸ r.n_pos hG (by omega))
  · intro h
    by_cases h0 : G.n = 0
    · rw [eq_empty_of_wf hG h0]
      exact ⟨_, _, (reach_plainSt hH).reach, (same_plainSt H).symm⟩
    · have hn : 0 < H.n := by omega
      obtain ⟨m, hm⟩ : ∃ m, G.n = m + 1 := ⟨G.n - 1, by omega⟩
      have r1 : Reach G ⟨G.n, []⟩ G.A.length := by
        cases G with
        | mk n A => exact reach_clear n A
      rw [hm] at r1
      have r2 := Reach.trans r1 (reach_collapse m)
      have r3 := Reach.trans r2 (reach_grow 1 (H.n - 1))
      have e : 1 + (H.n - 1) = H.n := by omega
      rw [e] at r3
      have r4 := Reach.trans r3 (addReach_atoms H.n (plain H.A) (fun a ha => hH a (mem_of_mem_plain ha))).reach
      exact ⟨_, _, r4, (same_plainSt H).symm⟩

/-- **The first change can only add a term.** -/
theorem first_change_adds_term {H : St} (st : Step empty H) : H = empty.addTerm := by
  cases st with
  | addTerm => rfl
  | add a hx _ => exact absurd hx (Nat.not_lt_zero _)
  | remove a ha => exact absurd ha List.not_mem_nil
  | identify u v hu _ _ => exact absurd hu (Nat.not_lt_zero _)

/-- Results with a term reach each other both ways. -/
theorem reach_mutual {G H : St} (hG : G.WF) (hH : H.WF) (g : 0 < G.n) (h : 0 < H.n) :
    ReachR G H ∧ ReachR H G :=
  ⟨(reach_criterion hG hH).2 (Or.inl h), (reach_criterion hH hG).2 (Or.inl g)⟩

/-- The empty result is never returned to. -/
theorem empty_never_returned {G : St} (hG : G.WF) (g : 0 < G.n) : ¬ ReachR G empty := by
  intro h
  rcases (reach_criterion hG empty_wf).1 h with e | e
  · exact absurd e (by decide)
  · omega

end Twentysecond
