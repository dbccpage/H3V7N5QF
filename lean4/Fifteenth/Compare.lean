import Fifteenth.Step

/-!
# What survives once reaching does not admit

Under C-A1 admission is recorded with the result, not as a third multiplicity.
The ninth's results, cost and reachability survive by the identity on states
(`Step15` as `Step9`).  The unchosen tag has results the ninth has not, and a
cost that is not the size.
-/

namespace Seed.Fifteenth

open Seed Seed.Ninth Seed.Eighth NDSt

theorem fewest_changes15 {g : NDSt} (hgw : g.WF) :
    Reach15 empty9 g g.size ∧ ∀ n, Reach15 empty9 g n → g.size ≤ n :=
  fewest_changes9 hgw

theorem reach15_iff {s g : NDSt} (hs : s.WF) (hg : g.WF) :
    (∃ n, Reach15 s g n) ↔ (s.T.Nonempty → g.T.Nonempty) :=
  reach9_iff hs hg

theorem results_pair15 {m m' : Seed.Seventh.NSt} (hm : m.WF) (hm' : m'.WF)
    (hT : m'.T = m.T) :
    ∃ n, Reach15 empty9 ⟨m.T, fun q => match q with | false => m.M | true => m'.M⟩ n :=
  results_pair9 hm hm' hT

theorem no_third_rel (s : NDSt) :
    (s.proj false).M = s.M false ∧ (s.proj true).M = s.M true :=
  admission_not_in_M s

theorem r_admission_is_s_result :
    reaching = reaching ∧
      Step9 twoBoth (twoBoth.remove false 0 1) ∧
      Step9 twoBoth (twoBoth.remove true 0 1) :=
  ⟨r_admission_is_s, twoBoth_remove_r, twoBoth_remove_s⟩

theorem no_cross_constraint :
    reaching = .notAdmitted ∧
      Step9 twoBoth (twoBoth.remove false 0 1) ∧
      Step9 twoBoth (twoBoth.remove true 0 1) :=
  ⟨rfl, twoBoth_remove_r, twoBoth_remove_s⟩

theorem toNDSt (s : NDSt) : s = s := rfl

inductive StepTagged : Tagged → Tagged → Prop
  | addTerm {s : NDSt} {A : Admission} (u : ℕ) (ht : u ∉ s.T) :
      StepTagged ⟨s, A⟩ ⟨s.addTerm u, reaching⟩
  | addAssertion {s : NDSt} {A : Admission} (q : Rel) (x y : ℕ)
      (hx : x ∈ s.T) (hy : y ∈ s.T) :
      StepTagged ⟨s, A⟩ ⟨s.addAssertion q x y, reaching⟩
  | remove {s : NDSt} {A : Admission} (q : Rel) (x y : ℕ)
      (hp : s.M q (x, y) ≠ 0) :
      StepTagged ⟨s, A⟩ ⟨s.remove q x y, reaching⟩
  | identify {s : NDSt} {A : Admission} (u v : ℕ)
      (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v) :
      StepTagged ⟨s, A⟩ ⟨s.identify u v, reaching⟩
  | record {s : NDSt} :
      StepTagged ⟨s, .notAdmitted⟩ ⟨s, .admitted⟩

inductive ReachTagged : Tagged → Tagged → ℕ → Prop
  | refl (s : Tagged) : ReachTagged s s 0
  | step {s t u : Tagged} {n : ℕ} : ReachTagged s t n → StepTagged t u → ReachTagged s u (n + 1)

/-- Every reached result can be admitted: recording admission is a tagged step, not a `Step9`. -/
theorem every_reached_can_be_admitted (s : NDSt) :
    StepTagged ⟨s, .notAdmitted⟩ ⟨s, .admitted⟩ :=
  StepTagged.record

/-- A change of the four kinds leaves the outcome not admitted. -/
theorem step_reaches_not_admitted {s : NDSt} {A : Admission} (u : ℕ) (ht : u ∉ s.T) :
    StepTagged ⟨s, A⟩ ⟨s.addTerm u, reaching⟩ :=
  StepTagged.addTerm u ht

theorem tagged_one_nothing :
    ReachTagged Tagged.start ⟨oneTerm9, reaching⟩ 1 := by
  have st : StepTagged Tagged.start ⟨empty9.addTerm 0, reaching⟩ :=
    StepTagged.addTerm (s := empty9) (A := .notAdmitted) 0 (by simp [empty9])
  have st' : StepTagged Tagged.start ⟨oneTerm9, reaching⟩ := by
    simpa [oneTerm9] using st
  exact ReachTagged.step (ReachTagged.refl Tagged.start) st'

theorem tagged_extra :
    (⟨oneTerm9, reaching⟩ : Tagged) ≠ ⟨oneTerm9, admitted⟩ := by
  intro h
  injection h with _ hA
  cases hA

theorem tagged_cost_fails :
    oneTerm9.size = 1 ∧ ∃ n, n ≠ oneTerm9.size ∧ ReachTagged Tagged.start ⟨oneTerm9, admitted⟩ n := by
  refine ⟨size_oneTerm9 0, 2, by decide, ?_⟩
  have st0 : StepTagged Tagged.start ⟨empty9.addTerm 0, reaching⟩ :=
    StepTagged.addTerm (s := empty9) (A := .notAdmitted) 0 (by simp [empty9])
  have st0' : StepTagged Tagged.start ⟨oneTerm9, reaching⟩ := by
    simpa [oneTerm9] using st0
  have st1 : StepTagged ⟨oneTerm9, reaching⟩ ⟨oneTerm9, admitted⟩ := by
    simpa [reaching, admitted] using StepTagged.record (s := oneTerm9)
  exact ReachTagged.step (ReachTagged.step (ReachTagged.refl _) st0') st1

end Seed.Fifteenth
