import Twentysecond.Cost

/-!
# Can an addition undo an earlier addition?

In the ninth (`paper/ninth/`, D4): every addition raises the size by one, and
two states that are the same ninth result have the same size (at a fixed
writing: `SameState9.size`; in every writing: `Rename.lean`).  So a non-empty
sequence of additions never ends at the ninth result it started from
(`ninth_additions_never_return`).

Here: adding `xry` and then `xsy` ends at the result it started from
(`addition_undoes_addition`): the second addition undoes the first.  Removing
`xry` and adding `xsy` have the same result (`same_remove_add_partner`), so
the addition does what the removal of the earlier addition would do.  At a
fixed writing, two additions in a row return to their start's result exactly
when they are one pair in the two relations (`two_additions_return_iff`).
-/

namespace Twentysecond

/-- **In the ninth, a non-empty sequence of additions never returns to its start's state.** -/
theorem ninth_additions_never_return {G H : St} {k : Nat} (r : AddReach G H k) (hk : 0 < k) :
    ¬ SameState9 G H := by
  intro h
  have := r.size
  have := h.size
  omega

/-- **Here an addition undoes an earlier addition**: `xry` added, then `xsy` added, is the result
the state was before either. -/
theorem addition_undoes_addition (G : St) (x y : Nat) (hx : x < G.n) (hy : y < G.n) :
    AddStep G (G.add ⟨.r, x, y⟩) ∧ AddStep (G.add ⟨.r, x, y⟩) ((G.add ⟨.r, x, y⟩).add ⟨.s, x, y⟩) ∧
      Same G ((G.add ⟨.r, x, y⟩).add ⟨.s, x, y⟩) := by
  refine ⟨AddStep.add G _ hx hy, AddStep.add _ _ hx hy, ?_⟩
  have g := Gen.pair G x y hx hy
  refine g.same.trans ⟨rfl, plain_perm (List.Perm.swap _ _ _)⟩

/-- The ninth's result and this seed's: the two states of `addition_undoes_addition` are two ninth
states (sizes differ by two). -/
theorem addition_undoes_not_in_ninth (G : St) (x y : Nat) :
    ¬ SameState9 G ((G.add ⟨.r, x, y⟩).add ⟨.s, x, y⟩) := by
  intro h
  have := h.size
  simp [St.size, St.add] at this
  omega

/-- Two additions in a row keep the result exactly when the two atoms added are as many `xry` as
`xsy` on every pair. -/
theorem same_add_add_iff (G : St) (a b : Atom) :
    Same G ((G.add a).add b) ↔ ∀ z, [a, b].count z = [a, b].count z.partner := by
  have split2 : ∀ z, ((G.add a).add b).A.count z = [a, b].count z + G.A.count z := by
    intro z
    have e : ((G.add a).add b).A = [b, a] ++ G.A := rfl
    rw [e, List.count_append, (List.Perm.swap a b []).count_eq]
  constructor
  · intro h z
    have e := plain_perm_iff.1 h.2 z
    rw [split2, split2] at e
    omega
  · intro h
    refine ⟨rfl, plain_perm_iff.2 fun z => ?_⟩
    rw [split2, split2]
    have := h z
    omega

/-- At a fixed writing, two additions in a row give back their start's result exactly when they are
one pair in the two relations. -/
theorem two_additions_return_iff (G : St) (a b : Atom) : Same G ((G.add a).add b) ↔ b = a.partner := by
  rw [same_add_add_iff]
  constructor
  · intro h
    have e := h a
    have pos : 0 < [a, b].count a := count_pos_of_mem List.mem_cons_self
    have mem : a.partner ∈ [a, b] := mem_of_count_pos (by omega)
    rcases List.mem_cons.1 mem with e1 | e2
    · exact absurd e1 (Atom.partner_ne a)
    · rcases List.mem_cons.1 e2 with e3 | e4
      · exact e3.symm
      · exact absurd e4 List.not_mem_nil
  · intro hb z
    subst hb
    have hm : [a, a.partner] = [a.partner, a].map Atom.partner := by simp
    have hi : ∀ c d : Atom, c.partner = d.partner → c = d := fun _ _ h => Atom.partner_inj h
    rw [hm, count_map_of_inj hi, ← hm]
    exact ((List.Perm.swap a a.partner []).count_eq z).symm

end Twentysecond
