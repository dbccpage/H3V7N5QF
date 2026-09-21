import Eleventh.Step

/-!
# What survives colliding writings

Under C-W1 a writing is a reading of a result, not a third multiplicity.
The ninth's results, cost and reachability survive by the identity on states
(`Step11` as `Step9`).  The unchosen label has results the ninth has not.
-/

namespace Seed.Eleventh

open Seed Seed.Ninth Seed.Eighth NDSt

theorem fewest_changes11 {g : NDSt} (hgw : g.WF) :
    Reach11 empty9 g g.size ∧ ∀ n, Reach11 empty9 g n → g.size ≤ n :=
  fewest_changes9 hgw

theorem reach11_iff {s g : NDSt} (hs : s.WF) (hg : g.WF) :
    (∃ n, Reach11 s g n) ↔ (s.T.Nonempty → g.T.Nonempty) :=
  reach9_iff hs hg

theorem results_pair11 {m m' : Seed.Seventh.NSt} (hm : m.WF) (hm' : m'.WF)
    (hT : m'.T = m.T) :
    ∃ n, Reach11 empty9 ⟨m.T, fun q => match q with | false => m.M | true => m'.M⟩ n :=
  results_pair9 hm hm' hT

theorem no_third_rel (s : NDSt) :
    (s.proj false).M = s.M false ∧ (s.proj true).M = s.M true :=
  writing_not_assertion s

theorem split_injective {s : NDSt} {w : ℕ → ℕ} (h : injOn w s.T) :
    determines s w :=
  inj_determines s w h

theorem no_cross_constraint :
    ¬ determinesRel twoBetween collide false ∧ determinesRel twoBetween collide true :=
  r_collision_not_s

theorem writing_not_identify :
    (twoTerms9.identify 0 1).T.card + 1 = twoTerms9.T.card ∧ twoTerms9.T.card = 2 :=
  ⟨identify_drops_a_term, collide_keeps_terms⟩

theorem labeled_extra :
    ({ state := twoTerms9, letter := apart } : Labeled) ≠
      { state := twoTerms9, letter := collide } := by
  intro h
  have : apart (1 : ℕ) = collide 1 := congrArg (fun t : Labeled => t.letter 1) h
  simp [apart, collide] at this

theorem labeled_cost_is_size (t : Labeled) : t.size = t.state.size := rfl

end Seed.Eleventh
