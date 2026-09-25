import Twentyfourth.Reach

/-!
# The exchange of the two relations

Exchanging `r` and `s` in every assertion, the filled terms kept
(`FSt.swap`).  Derived here: it keeps this seed's sameness both ways
(`same24_swap_iff`), whether each filled term balances (`balances_swap`: it
negates every loop's excess), the told results (`told_swap`), the cost
(`cost24_swap`) and reachability (`reach24_swap`), and carries every change to
a change of the same kind (`Step24.swap`): a symmetry of the results, as in the
twenty-third (23:D13).
-/

namespace Twentyfourth

open Twentysecond Twentythird

/-- The two relations exchanged; the filled terms kept. -/
def FSt.swap (X : FSt) : FSt := ⟨X.G.swap, X.F⟩

theorem FSt.swap_swap (X : FSt) : X.swap.swap = X := by
  cases X with
  | mk G F => simp only [FSt.swap, Twentysecond.swap_swap]

theorem Same24.swap {X Y : FSt} (h : Same24 X Y) : Same24 X.swap Y.swap := ⟨h.1.swap, h.2⟩

/-- **The exchange keeps the sameness, both ways.** -/
theorem same24_swap_iff {X Y : FSt} : Same24 X Y ↔ Same24 X.swap Y.swap := by
  constructor
  · exact Same24.swap
  · intro h
    have := h.swap
    rwa [FSt.swap_swap, FSt.swap_swap] at this

/-- **The exchange keeps whether each filled term balances.** -/
theorem balances_swap {X : FSt} {x : Nat} : Balances X.swap x ↔ Balances X x := by
  rw [balances_iff, balances_iff]
  show X.F x = true ∧ excess X.G.swap x x = 0 ↔ _
  rw [excess_swap]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

theorem told_swap {X : FSt} : Told X.swap ↔ Told X := by
  constructor
  · rintro ⟨x, hx, hf, he⟩
    refine ⟨x, hx, hf, fun e => he ?_⟩
    show excess X.G.swap x x = 0
    rw [excess_swap, e]
    rfl
  · rintro ⟨x, hx, hf, he⟩
    refine ⟨x, hx, hf, fun e => he ?_⟩
    have : excess X.G.swap x x = 0 := e
    rw [excess_swap] at this
    omega

theorem swap_wf24 {X : FSt} (hw : X.WF) : X.swap.WF := ⟨swap_wf hw.1, hw.2⟩

/-- **The exchange carries every change to a change of the same kind.** -/
theorem Step24.swap {X Y : FSt} (h : Step24 X Y) : Step24 X.swap Y.swap := by
  cases h with
  | addTerm => exact Step24.addTerm X.swap
  | add a hx hy => exact Step24.add X.swap a.partner hx hy
  | remove a ha =>
    have e : (X.remove a).swap = X.swap.remove a.partner := by
      simp only [FSt.swap, FSt.remove, St.swap, St.remove, map_del_of_inj partner_injective]
    rw [e]
    exact Step24.remove X.swap a.partner (List.mem_map_of_mem ha)
  | identify u v hu hv huv =>
    have e : (X.identify u v).swap = X.swap.identify u v := by
      simp only [FSt.swap, FSt.identify, St.swap, St.identify, List.map_map]
      rfl
    rw [e]
    exact Step24.identify X.swap u v hu hv huv
  | fill x hx hf => exact Step24.fill X.swap x hx hf

theorem Reach24.swap {X Y : FSt} {k : Nat} (h : Reach24 X Y k) : Reach24 X.swap Y.swap k := by
  induction h with
  | refl => exact Reach24.refl _
  | step _ st ih => exact Reach24.step ih st.swap

theorem empty24_swap : empty24.swap = empty24 := rfl

/-- **The exchange keeps the cost.** -/
theorem cost24_swap {X : FSt} {c : Nat} : Cost24 X c ↔ Cost24 X.swap c := by
  have key : ∀ {X : FSt}, Cost24 X c → Cost24 X.swap c := by
    intro X ⟨⟨Y, s, r⟩, lo⟩
    refine ⟨⟨Y.swap, s.swap, empty24_swap ▸ r.swap⟩, fun Z k sZ rZ => ?_⟩
    have := sZ.swap
    rw [FSt.swap_swap] at this
    exact lo Z.swap k this (empty24_swap ▸ rZ.swap)
  constructor
  · exact key
  · intro h
    have := key h
    rwa [FSt.swap_swap] at this

/-- **The exchange keeps reachability.** -/
theorem reach24_swap {X Y : FSt} : ReachR24 X Y ↔ ReachR24 X.swap Y.swap := by
  have key : ∀ {X Y : FSt}, ReachR24 X Y → ReachR24 X.swap Y.swap := by
    intro X Y ⟨k, Y', r, s⟩
    exact ⟨k, Y'.swap, r.swap, s.swap⟩
  constructor
  · exact key
  · intro h
    have := key h
    rwa [FSt.swap_swap, FSt.swap_swap] at this

end Twentyfourth
