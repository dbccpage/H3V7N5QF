import Fourteenth.Step

/-!
# What survives leftover as a writing that is not an assertion

Under C-F1 leftover is recorded on the change, not as a third multiplicity.
The ninth's results, cost and reachability survive by the identity on states
(`Step14` as `Step9`).  The unchosen tag has results the ninth has not, and a
cost that is not the size.
-/

namespace Seed.Fourteenth

open Seed Seed.Ninth Seed.Eighth Seed.Tenth NDSt

theorem fewest_changes14 {g : NDSt} (hgw : g.WF) :
    Reach14 empty9 g g.size ∧ ∀ n, Reach14 empty9 g n → g.size ≤ n :=
  fewest_changes9 hgw

theorem reach14_iff {s g : NDSt} (hs : s.WF) (hg : g.WF) :
    (∃ n, Reach14 s g n) ↔ (s.T.Nonempty → g.T.Nonempty) :=
  reach9_iff hs hg

theorem results_pair14 {m m' : Seed.Seventh.NSt} (hm : m.WF) (hm' : m'.WF)
    (hT : m'.T = m.T) :
    ∃ n, Reach14 empty9 ⟨m.T, fun q => match q with | false => m.M | true => m'.M⟩ n :=
  results_pair9 hm hm' hT

theorem no_third_rel (s : NDSt) :
    (s.proj false).M = s.M false ∧ (s.proj true).M = s.M true :=
  leftover_not_in_M s

theorem r_leftover_is_s :
    leftoverRemove 0 1 = leftoverRemove 0 1 ∧
      Step9 twoBoth (twoBoth.remove false 0 1) ∧
      Step9 twoBoth (twoBoth.remove true 0 1) :=
  ⟨leftover_remove_r_s 0 1, twoBoth_remove_r, twoBoth_remove_s⟩

theorem no_cross_constraint :
    leftoverRemove 0 1 = .pair 0 1 ∧
      Step9 twoBoth (twoBoth.remove false 0 1) ∧
      Step9 twoBoth (twoBoth.remove true 0 1) :=
  ⟨rfl, twoBoth_remove_r, twoBoth_remove_s⟩

theorem toNDSt (s : NDSt) : s = s := rfl

inductive StepTagged : Tagged → Tagged → Prop
  | addTerm {s : NDSt} {L : LeftWriting} (u : ℕ) (ht : u ∉ s.T) :
      StepTagged ⟨s, L⟩ ⟨s.addTerm u, leftoverAdd⟩
  | addAssertion {s : NDSt} {L : LeftWriting} (q : Rel) (x y : ℕ)
      (hx : x ∈ s.T) (hy : y ∈ s.T) :
      StepTagged ⟨s, L⟩ ⟨s.addAssertion q x y, leftoverAdd⟩
  | remove {s : NDSt} {L : LeftWriting} (q : Rel) (x y : ℕ)
      (hp : s.M q (x, y) ≠ 0) :
      StepTagged ⟨s, L⟩ ⟨s.remove q x y, leftoverRemove x y⟩
  | identify {s : NDSt} {L : LeftWriting} (u v : ℕ)
      (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v) :
      StepTagged ⟨s, L⟩ ⟨s.identify u v, leftoverIdentify u v⟩

inductive ReachTagged : Tagged → Tagged → ℕ → Prop
  | refl (s : Tagged) : ReachTagged s s 0
  | step {s t u : Tagged} {n : ℕ} : ReachTagged s t n → StepTagged t u → ReachTagged s u (n + 1)

theorem tagged_one_nothing :
    ReachTagged Tagged.start ⟨oneTerm9, leftoverAdd⟩ 1 := by
  have st : StepTagged Tagged.start ⟨empty9.addTerm 0, leftoverAdd⟩ :=
    StepTagged.addTerm (s := empty9) (L := .nothing) 0 (by simp [empty9])
  have st' : StepTagged Tagged.start ⟨oneTerm9, leftoverAdd⟩ := by
    simpa [oneTerm9] using st
  exact ReachTagged.step (ReachTagged.refl Tagged.start) st'

theorem add_remove (s : NDSt) (q : Rel) (x y : ℕ) :
    (s.addAssertion q x y).remove q x y = s := by
  apply NDSt.ext
  · rfl
  · funext q' p
    by_cases hq : q' = q
    · subst hq
      by_cases he : p = (x, y)
      · subst he
        simp [NDSt.remove, NDSt.addAssertion]
      · simp [NDSt.remove, NDSt.addAssertion]
    · simp [NDSt.remove, NDSt.addAssertion]

theorem tagged_extra :
    (⟨oneTerm9, leftoverAdd⟩ : Tagged) ≠ ⟨oneTerm9, leftoverRemove 0 0⟩ := by
  intro h
  injection h with _ hL
  cases hL

theorem oneTerm9_add_M : (oneTerm9.addAssertion false 0 0).M false (0, 0) = 1 := by
  simp [oneTerm9, empty9, NDSt.addTerm, NDSt.addAssertion]

theorem tagged_cost_fails :
    oneTerm9.size = 1 ∧ ∃ n, n ≠ oneTerm9.size ∧ ReachTagged Tagged.start ⟨oneTerm9, leftoverRemove 0 0⟩ n := by
  refine ⟨size_oneTerm9 0, 3, by decide, ?_⟩
  let ara := oneTerm9.addAssertion false 0 0
  have hx : 0 ∈ oneTerm9.T := by simp [oneTerm9, empty9, NDSt.addTerm]
  have st0 : StepTagged Tagged.start ⟨empty9.addTerm 0, leftoverAdd⟩ :=
    StepTagged.addTerm (s := empty9) (L := .nothing) 0 (by simp [empty9])
  have st0' : StepTagged Tagged.start ⟨oneTerm9, leftoverAdd⟩ := by
    simpa [oneTerm9] using st0
  have st1 : StepTagged ⟨oneTerm9, leftoverAdd⟩ ⟨ara, leftoverAdd⟩ :=
    StepTagged.addAssertion (s := oneTerm9) (L := leftoverAdd) false 0 0 hx hx
  have hp : ara.M false (0, 0) ≠ 0 := by
    simp [ara, oneTerm9_add_M]
  have st2 : StepTagged ⟨ara, leftoverAdd⟩ ⟨ara.remove false 0 0, leftoverRemove 0 0⟩ :=
    StepTagged.remove (s := ara) (L := leftoverAdd) false 0 0 hp
  have st2' : StepTagged ⟨ara, leftoverAdd⟩ ⟨oneTerm9, leftoverRemove 0 0⟩ := by
    have hS : ara.remove false 0 0 = oneTerm9 := add_remove oneTerm9 false 0 0
    simpa [hS] using st2
  exact ReachTagged.step (ReachTagged.step (ReachTagged.step (ReachTagged.refl _) st0') st1) st2'

end Seed.Fourteenth
