import Thirteenth.Step

/-!
# What survives a coarser writing that forgets the relation

Under C-C1 the coarser writing is computed from the two multiplicities, not a
third relation.  The ninth's results, cost and reachability survive by the
identity on states (`Step13` as `Step9`).  The unchosen coarser reading has
two finer results that are one coarser result.
-/

namespace Seed.Thirteenth

open Seed Seed.Ninth Seed.Seventh Seed.Eighth Seed.Eleventh NDSt

theorem fewest_changes13 {g : NDSt} (hgw : g.WF) :
    Reach13 empty9 g g.size ∧ ∀ n, Reach13 empty9 g n → g.size ≤ n :=
  fewest_changes9 hgw

theorem reach13_iff {s g : NDSt} (hs : s.WF) (hg : g.WF) :
    (∃ n, Reach13 s g n) ↔ (s.T.Nonempty → g.T.Nonempty) :=
  reach9_iff hs hg

theorem results_pair13 {m m' : Seed.Seventh.NSt} (hm : m.WF) (hm' : m'.WF)
    (hT : m'.T = m.T) :
    ∃ n, Reach13 empty9 ⟨m.T, fun q => match q with | false => m.M | true => m'.M⟩ n :=
  results_pair9 hm hm' hT

theorem no_third_rel (s : NDSt) :
    (s.proj false).M = s.M false ∧ (s.proj true).M = s.M true :=
  coarse_not_assertion s

theorem no_cross_constraint :
    coarse twoBetween = coarse twoBetween.swap ∧
      twoBetween.M false (0, 0) = twoBetween.swap.M false (0, 0) ∧
      twoBetween.M true (0, 0) = twoBetween.swap.M true (0, 0) := by
  refine ⟨(coarse_swap twoBetween).symm, ?_, ?_⟩
  · simp [NDSt.swap, twoBetween]
  · simp [NDSt.swap, twoBetween]

theorem coarse_extra :
    twoBetween ≠ twoBetween.swap ∧ coarse twoBetween = coarse twoBetween.swap :=
  ⟨Ne.symm twoBetween_ne_swap, (coarse_swap twoBetween).symm⟩

theorem coarse_cost_descends (s : NDSt) : (coarse s).size = s.size :=
  size_coarse s

theorem coarse_has_term (s : NDSt) : (coarse s).T.Nonempty ↔ s.T.Nonempty := by
  simp [coarse]

theorem toNDSt (s : NDSt) : s = s := rfl

end Seed.Thirteenth
