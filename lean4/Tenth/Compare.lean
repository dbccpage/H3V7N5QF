import Tenth.Step

/-!
# What survives leftover outcomes

Under C-L1 leftover is recorded on the change, not as a third multiplicity.
The ninth's results, cost and reachability survive by the identity on states
(`Step10` as `Step9`).  The unchosen tag has results the ninth has not, and a
cost that is not the size.
-/

namespace Seed.Tenth

open Seed Seed.Ninth Seed.Eighth NDSt

theorem fewest_changes10 {g : NDSt} (hgw : g.WF) :
    Reach10 empty9 g g.size ∧ ∀ n, Reach10 empty9 g n → g.size ≤ n :=
  fewest_changes9 hgw

theorem reach10_iff {s g : NDSt} (hs : s.WF) (hg : g.WF) :
    (∃ n, Reach10 s g n) ↔ (s.T.Nonempty → g.T.Nonempty) :=
  reach9_iff hs hg

theorem results_pair10 {m m' : Seed.Seventh.NSt} (hm : m.WF) (hm' : m'.WF)
    (hT : m'.T = m.T) :
    ∃ n, Reach10 empty9 ⟨m.T, fun q => match q with | false => m.M | true => m'.M⟩ n :=
  results_pair9 hm hm' hT

theorem no_third_rel (s : NDSt) :
    (s.proj false).M = s.M false ∧ (s.proj true).M = s.M true :=
  ⟨rfl, rfl⟩

theorem split_kinds (s t : NDSt) :
    leftoverOf s t = .nothingLeft ∨ leftoverOf s t = .clearable ∨ leftoverOf s t = .uncleared :=
  leftover_not_assertion s t

theorem split_additions {s : NDSt} (hw : s.WF) (t : ℕ) (ht : t ∉ s.T) :
    leftoverOf s (s.addTerm t) = .nothingLeft := leftover_addTerm hw ht

theorem split_removals {s : NDSt} (hw : s.WF) (q : Rel) (x y : ℕ) (hp : s.M q (x, y) ≠ 0) :
    leftoverOf s (s.remove q x y) = .clearable := leftover_remove hw q x y hp

/-- A change of the other relation does not restore the removed multiplicity. -/
theorem other_rel_not_clear (s : NDSt) {q q' : Rel} (hne : q' ≠ q) (x y x' y' : ℕ) :
    ((s.remove q x y).addAssertion q' x' y').M q (x, y) = (s.remove q x y).M q (x, y) := by
  have hne' : q ≠ q' := hne.symm
  have := proj9_addAssertion_other (s.remove q x y) hne' x' y'
  simpa [NDSt.proj] using congrArg (fun m : Seed.Seventh.NSt => m.M (x, y)) this

inductive StepTagged : Tagged → Tagged → Prop
  | mk {s t : NDSt} {L : LeftOver} (h : Step9 s t) :
      StepTagged ⟨s, L⟩ ⟨t, leftoverOf s t⟩

inductive ReachTagged : Tagged → Tagged → ℕ → Prop
  | refl (s : Tagged) : ReachTagged s s 0
  | step {s t u : Tagged} {n : ℕ} : ReachTagged s t n → StepTagged t u → ReachTagged s u (n + 1)

theorem oneTerm9_eq_add : oneTerm9 = empty9.addTerm 0 := rfl

theorem tagged_one_nothing :
    ReachTagged Tagged.start ⟨oneTerm9, .nothingLeft⟩ 1 := by
  have h : Step9 empty9 oneTerm9 :=
    Step9.addTerm empty9 0 (by simp [empty9])
  have hL : leftoverOf empty9 oneTerm9 = .nothingLeft := by
    simpa [oneTerm9_eq_add] using leftover_addTerm empty9_wf (by simp [empty9])
  have st : StepTagged Tagged.start ⟨oneTerm9, leftoverOf empty9 oneTerm9⟩ :=
    StepTagged.mk (L := .nothingLeft) h
  simpa [hL, Tagged.start] using ReachTagged.step (ReachTagged.refl _) st

theorem twoEmpty_eq_add : twoEmpty = oneTerm9.addTerm 1 := by
  simp [oneTerm9, twoEmpty, empty9, NDSt.addTerm]

theorem identify_twoEmpty_eq_one : twoEmpty.identify 0 1 = oneTerm9 := by
  apply NDSt.ext
  · simp [identify_twoEmpty, oneTerm9, empty9, NDSt.addTerm]
  · funext q p
    simp [identify_twoEmpty_M, oneTerm9, empty9, NDSt.addTerm]

theorem tagged_cost_fails :
    oneTerm9.size = 1 ∧ ∃ n, n ≠ oneTerm9.size ∧ ReachTagged Tagged.start ⟨oneTerm9, .clearable⟩ n := by
  refine ⟨size_oneTerm9 0, 3, by decide, ?_⟩
  have h0 : Step9 empty9 oneTerm9 :=
    Step9.addTerm empty9 0 (by simp [empty9])
  have h1 : Step9 oneTerm9 twoEmpty := by
    have : 1 ∉ oneTerm9.T := by simp [oneTerm9, empty9, NDSt.addTerm]
    have := Step9.addTerm oneTerm9 1 this
    rwa [← twoEmpty_eq_add] at this
  have h2 : Step9 twoEmpty (twoEmpty.identify 0 1) :=
    Step9.identify twoEmpty 0 1
      (by simp [twoEmpty, empty9, NDSt.addTerm])
      (by simp [twoEmpty, empty9, NDSt.addTerm])
      (by decide)
  have st0 : StepTagged Tagged.start ⟨oneTerm9, leftoverOf empty9 oneTerm9⟩ :=
    StepTagged.mk (L := .nothingLeft) h0
  have st0' : StepTagged Tagged.start ⟨oneTerm9, .nothingLeft⟩ := by
    have hL : leftoverOf empty9 oneTerm9 = .nothingLeft := by
      simpa [oneTerm9_eq_add] using leftover_addTerm empty9_wf (by simp [empty9])
    simpa [hL] using st0
  have st1 : StepTagged ⟨oneTerm9, .nothingLeft⟩ ⟨twoEmpty, leftoverOf oneTerm9 twoEmpty⟩ :=
    StepTagged.mk (L := .nothingLeft) h1
  have st1' : StepTagged ⟨oneTerm9, .nothingLeft⟩ ⟨twoEmpty, .nothingLeft⟩ := by
    have hL : leftoverOf oneTerm9 twoEmpty = .nothingLeft := by
      simpa [twoEmpty_eq_add] using leftover_addTerm oneTerm9_wf (by simp [oneTerm9, empty9, NDSt.addTerm])
    simpa [hL] using st1
  have st2 : StepTagged ⟨twoEmpty, .nothingLeft⟩
      ⟨twoEmpty.identify 0 1, leftoverOf twoEmpty (twoEmpty.identify 0 1)⟩ :=
    StepTagged.mk (L := .nothingLeft) h2
  have st2c : StepTagged ⟨twoEmpty, .nothingLeft⟩ ⟨twoEmpty.identify 0 1, .clearable⟩ := by
    simpa [leftover_identify_twoEmpty] using st2
  have st2' : StepTagged ⟨twoEmpty, .nothingLeft⟩ ⟨oneTerm9, .clearable⟩ := by
    rwa [identify_twoEmpty_eq_one] at st2c
  exact ReachTagged.step (ReachTagged.step (ReachTagged.step (ReachTagged.refl _) st0') st1') st2'

theorem tagged_extra :
    (⟨oneTerm9, LeftOver.nothingLeft⟩ : Tagged) ≠ ⟨oneTerm9, .clearable⟩ := by
  intro h
  injection h with _ hL
  cases hL

end Seed.Tenth
