import Sixth.State

/-!
# The four kinds of change with nothing forbidden

`Step6` is one change of the sixth seed: a new term; an assertion between two
terms that are there — `xrx` included; the removal of an asserted assertion; the
identification of two terms that are there, whatever is asserted between or at
them.  `Reach6 s t n`: `t` is reached from `s` by `n` changes.

Cited from the fifth derivation and re-checked:
* every performed change of the fifth seed is a change of the sixth
  (`Step5.toStep6`, `Reach5.toReach6`);
* **nothing is obstructed**: every *attempt* of the fifth seed (`Try5`, the four
  kinds without the conditions that made them unobstructed) is a change of the
  sixth, and conversely (`Try5.toStep6`, `Step6.toTry5`, `try5_iff_step6`); so
  the fifth's `Try5.obstructed_iff` survives as a fact about which changes leave
  a state asserting some `xrx` (`Step6.not_legal_iff`), no longer a bar;
* a change of the sixth seed between states asserting no `xrx` is a change of
  the fifth (`Step6.toStep5`);
* well-formedness and at least one term are kept (`Step6.wf`, `Step6.nonempty`),
  and the names once one term stay one term (`Step6.names_stay_merged`,
  `Reach6.names_stay_merged`) — the proofs mention no legality;
* legality is *not* kept: identifying `a` and `b` in what is given makes `ara`
  asserted (`legal_not_kept`), and `arb` — now `ara` — is asserted after the
  merge, so the fifth's `Reach5.arb_gone_for_good` fails (`arb_gone_fails`).
-/

namespace Seed.Sixth

open Seed Seed.Fourth Seed.Fifth MSt

/-- One change of the sixth seed.  "Nothing else is a change": the new term is new;
the added assertion is between two terms that are there (the same term twice
allowed); the removed assertion is asserted; the identified terms are two terms
that are there. -/
inductive Step6 : MSt → MSt → Prop
  | addTerm (s : MSt) (t : ℕ) (ht : t ∉ s.T) : Step6 s (s.addTerm t)
  | addAssertion (s : MSt) (x y : ℕ) (hx : x ∈ s.T) (hy : y ∈ s.T) : Step6 s (s.addAssertion x y)
  | remove (s : MSt) (x y : ℕ) (hp : s.M (x, y) ≠ 0) : Step6 s (s.remove x y)
  | identify (s : MSt) (u v : ℕ) (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v) : Step6 s (s.identify u v)

/-- Every performed change of the fifth seed is a change of the sixth. -/
theorem _root_.Seed.Fifth.Step5.toStep6 {s t : MSt} (h : Step5 s t) : Step6 s t := by
  cases h with
  | addTerm t ht => exact Step6.addTerm s t ht
  | addAssertion x y hx hy hxy => exact Step6.addAssertion s x y hx hy
  | remove x y hp => exact Step6.remove s x y hp
  | identify u v hu hv huv h1 h2 => exact Step6.identify s u v hu hv huv

/-- Every attempt of the fifth seed is a change of the sixth: nothing is obstructed. -/
theorem _root_.Seed.Fifth.Try5.toStep6 {s t : MSt} (h : Try5 s t) : Step6 s t := by
  cases h with
  | addTerm t ht => exact Step6.addTerm s t ht
  | addAssertion x y hx hy => exact Step6.addAssertion s x y hx hy
  | remove x y hp => exact Step6.remove s x y hp
  | identify u v hu hv huv => exact Step6.identify s u v hu hv huv

/-- Every change of the sixth seed is an attempt of the fifth. -/
theorem Step6.toTry5 {s t : MSt} (h : Step6 s t) : Try5 s t := by
  cases h with
  | addTerm t ht => exact Try5.addTerm s t ht
  | addAssertion x y hx hy => exact Try5.addAssertion s x y hx hy
  | remove x y hp => exact Try5.remove s x y hp
  | identify u v hu hv huv => exact Try5.identify s u v hu hv huv

/-- **The attempts of the fifth seed are exactly the changes of the sixth.** -/
theorem try5_iff_step6 (s t : MSt) : Try5 s t ↔ Step6 s t :=
  ⟨Try5.toStep6, Step6.toTry5⟩

/-- **Which changes make some `xrx` asserted.**  On a state asserting no `xrx`, a
change leaves a state asserting some `xrx` exactly when it adds some `xrx` or
identifies two related terms (the fifth's `Try5.obstructed_iff`, now about the
outcome only). -/
theorem Step6.not_legal_iff {s t : MSt} (h : Step6 s t) (hs : s.Legal) :
    ¬ t.Legal ↔ (∃ x ∈ s.T, t = s.addAssertion x x) ∨
      ∃ u v, u ∈ s.T ∧ v ∈ s.T ∧ u ≠ v ∧ (s.M (u, v) ≠ 0 ∨ s.M (v, u) ≠ 0) ∧ t = s.identify u v :=
  h.toTry5.obstructed_iff hs

/-- A change of the sixth seed whose state and outcome assert no `xrx` is a change of
the fifth seed. -/
theorem Step6.toStep5 {s t : MSt} (h : Step6 s t) (hs : s.Legal) (ht : t.Legal) : Step5 s t :=
  (h.toTry5.legal_iff hs).1 ht

/-! ## Invariants of one change -/

theorem Step6.wf {s t : MSt} (h : Step6 s t) (hw : s.WF) : t.WF := by
  cases h with
  | addTerm t ht => exact (Step4.addTerm s t ht).wf hw
  | addAssertion x y hx hy =>
    refine ⟨fun p hp => ?_, hw.2.1, hw.2.2⟩
    show p.1 ∈ s.T ∧ p.2 ∈ s.T
    change Function.update s.M (x, y) (s.M (x, y) + 1) p ≠ 0 at hp
    rw [Function.update_apply] at hp
    split_ifs at hp with h
    · subst h
      exact ⟨hx, hy⟩
    · exact hw.1 p hp
  | remove x y hp => exact (Step5.remove s x y hp).wf hw
  | identify u v hu hv huv =>
    refine ⟨fun p hne => ?_, merge_mem_erase hu huv hw.2.1, merge_mem_erase hu huv hw.2.2⟩
    obtain ⟨x, y, hx, hy, hp, _⟩ := identify_M_ne_zero s u v hne
    rw [← hp]
    exact ⟨merge_mem_erase hu huv hx, merge_mem_erase hu huv hy⟩

theorem Step6.nonempty {s t : MSt} (h : Step6 s t) (hs : s.T.Nonempty) : t.T.Nonempty := by
  cases h with
  | addTerm t ht => exact Finset.insert_nonempty _ _
  | addAssertion x y hx hy => exact hs
  | remove x y hp => exact hs
  | identify u v hu hv huv => exact ⟨u, Finset.mem_erase.2 ⟨huv, hu⟩⟩

/-- Once `a` and `b` are one term they stay one term (the first derivation's
`Step.names_stay_merged`, re-proved: the names follow the merge map). -/
theorem Step6.names_stay_merged {s t : MSt} (h : Step6 s t) (hab : s.a = s.b) : t.a = t.b := by
  cases h with
  | addTerm t ht => exact hab
  | addAssertion x y hx hy => exact hab
  | remove x y hp => exact hab
  | identify u v hu hv huv =>
    show merge u v s.a = merge u v s.b
    rw [hab]

/-! ## Sequences of changes -/

/-- `Reach6 s t n`: `t` is reached from `s` by `n` changes of the sixth seed. -/
inductive Reach6 : MSt → MSt → ℕ → Prop
  | refl (s : MSt) : Reach6 s s 0
  | step {s t u : MSt} {n : ℕ} : Reach6 s t n → Step6 t u → Reach6 s u (n + 1)

theorem Reach6.trans {s t u : MSt} {n m : ℕ} (h1 : Reach6 s t n) (h2 : Reach6 t u m) :
    Reach6 s u (n + m) := by
  induction h2 with
  | refl => exact h1
  | step _ st ih => exact Reach6.step ih st

theorem Reach6.single {s t : MSt} (h : Step6 s t) : Reach6 s t 1 := Reach6.step (Reach6.refl s) h

theorem Reach6.eq_of_zero {s t : MSt} (h : Reach6 s t 0) : s = t := by
  cases h
  rfl

theorem Reach6.wf {s t : MSt} {n : ℕ} (h : Reach6 s t n) (hs : s.WF) : t.WF := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.wf ih

theorem Reach6.nonempty {s t : MSt} {n : ℕ} (h : Reach6 s t n) (hs : s.T.Nonempty) :
    t.T.Nonempty := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.nonempty ih

/-- Every sequence of changes of the fifth seed is a sequence of the sixth. -/
theorem _root_.Seed.Fifth.Reach5.toReach6 {s t : MSt} {n : ℕ} (h : Reach5 s t n) :
    Reach6 s t n := by
  induction h with
  | refl => exact Reach6.refl _
  | step _ st ih => exact Reach6.step ih st.toStep6

/-- Identifying `a` and `b` cannot be undone by any sequence of changes. -/
theorem Reach6.names_stay_merged {s t : MSt} {n : ℕ} (h : Reach6 s t n) (hab : s.a = s.b) :
    t.a = t.b := by
  induction h with
  | refl => exact hab
  | step _ st ih => exact st.names_stay_merged ih

/-- Between states asserting no `xrx`, a sequence of the sixth seed is a sequence of the
fifth — provided every state along it asserts no `xrx`.  (With `xrx` allowed a
sequence between two legal states may pass through an illegal one, so the
hypothesis is on every state, not only the ends.) -/
theorem Reach6.toReach5_of_legal_step {s t : MSt} (h : Step6 s t) (hs : s.Legal) (ht : t.Legal) :
    Reach5 s t 1 :=
  Reach5.single (h.toStep5 hs ht)

/-! ## Legality is not kept -/

theorem step_identify_given : Step6 givenA4 (givenA4.identify 0 1) :=
  Step6.identify _ 0 1 ((mem_givenA4_T 0).2 (Or.inl rfl)) ((mem_givenA4_T 1).2 (Or.inr rfl)) (by omega)

/-- After identifying `a` and `b` in what is given, `ara` is asserted: the outcome
asserts some `xrx`. -/
theorem identify_given_ara : (givenA4.identify 0 1).M (0, 0) ≠ 0 := by
  have h := identify_M_ge_pair givenA4 (u := 0) (v := 1) ((mem_givenA4_T 0).2 (Or.inl rfl))
    ((mem_givenA4_T 1).2 (Or.inr rfl)) (by omega)
  rw [givenA4_arb, givenA4_bra] at h
  omega

/-- One change of the sixth seed can leave a state asserting some `xrx`: the fifth's
"every result is legal" does not survive. -/
theorem legal_not_kept : Step6 givenA4 (givenA4.identify 0 1) ∧ ¬ (givenA4.identify 0 1).Legal :=
  ⟨step_identify_given, fun h => identify_given_ara (h 0)⟩

/-- After `a` and `b` are one term, `arb` — now `ara` — *can* be asserted: the fifth's
`Reach5.arb_gone_for_good` fails. -/
theorem arb_gone_fails :
    Reach6 givenA4 (givenA4.identify 0 1) 1 ∧ (givenA4.identify 0 1).a = (givenA4.identify 0 1).b ∧
      (givenA4.identify 0 1).M ((givenA4.identify 0 1).a, (givenA4.identify 0 1).b) ≠ 0 := by
  refine ⟨Reach6.single step_identify_given, ?_, ?_⟩
  · show merge 0 1 givenA4.a = merge 0 1 givenA4.b
    rw [givenA4_a, givenA4_b, merge_left, merge_right]
  · show (givenA4.identify 0 1).M (merge 0 1 givenA4.a, merge 0 1 givenA4.b) ≠ 0
    rw [givenA4_a, givenA4_b, merge_left, merge_right]
    exact identify_given_ara

end Seed.Sixth
