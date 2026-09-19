import Seventh.State

/-!
# The four kinds of change from nothing

`Step7` is one change of the seventh seed on a state without names: a new term;
an assertion between two terms that are there (`xrx` included); the removal of
an asserted assertion; the identification of two terms that are there.
`Reach7 s t n`: `t` is reached from `s` by `n` changes.

Cited from the sixth derivation and re-checked through the two maps:
* every change of the sixth seed is a change of the seventh on the forgotten
  states (`Step6.forget`, `Reach6.forget`);
* every change of the seventh seed on a state with a term is a change of the
  sixth on the named states, the names following the merge (`Step7.name`,
  `Reach7.name`) — so the sixth's proofs about one change apply to every
  change here except the first, which no naming reaches;
* well-formedness is kept (`Step7.wf`, `Reach7.wf`: the sixth's `Step6.wf`
  through `name`, and the term case proved without names).

Derived here, about nothing being given:
* the outcome of every change on a well-formed state has a term
  (`Step7.nonempty_out`), and a state with a term leaves a state with a term
  (`Step7.nonempty`, `Reach7.nonempty`): **the one irreversible change is
  leaving the empty state**, in place of the sixth's merge of the names;
* the first change can only add a term (`first_change_adds_term`);
* the empty state is reached from a well-formed state only from itself, in
  zero changes (`reach7_empty_iff`): the beginning is never returned to.
-/

namespace Seed.Seventh

open Seed Seed.Fourth Seed.Fifth Seed.Sixth NSt

/-- One change of the seventh seed.  "Nothing else is a change": the new term is new; the
added assertion is between two terms that are there (the same term twice allowed); the
removed assertion is asserted; the identified terms are two terms that are there. -/
inductive Step7 : NSt → NSt → Prop
  | addTerm (s : NSt) (t : ℕ) (ht : t ∉ s.T) : Step7 s (s.addTerm t)
  | addAssertion (s : NSt) (x y : ℕ) (hx : x ∈ s.T) (hy : y ∈ s.T) : Step7 s (s.addAssertion x y)
  | remove (s : NSt) (x y : ℕ) (hp : s.M (x, y) ≠ 0) : Step7 s (s.remove x y)
  | identify (s : NSt) (u v : ℕ) (hu : u ∈ s.T) (hv : v ∈ s.T) (huv : u ≠ v) : Step7 s (s.identify u v)

/-- Every change of the sixth seed is a change of the seventh on the forgotten states. -/
theorem _root_.Seed.Sixth.Step6.forget {s t : MSt} (h : Step6 s t) : Step7 s.forget t.forget := by
  cases h with
  | addTerm t ht => exact Step7.addTerm s.forget t ht
  | addAssertion x y hx hy => exact Step7.addAssertion s.forget x y hx hy
  | remove x y hp => exact Step7.remove s.forget x y hp
  | identify u v hu hv huv => exact Step7.identify s.forget u v hu hv huv

/-- Every change of the seventh seed on a state with a term is a change of the sixth on the
named states, the names following the merge. -/
theorem Step7.name {s t : NSt} (h : Step7 s t) {c : ℕ} (hc : c ∈ s.T) :
    ∃ c', c' ∈ t.T ∧ Step6 (s.name c) (t.name c') := by
  cases h with
  | addTerm t ht => exact ⟨c, Finset.mem_insert_of_mem hc, Step6.addTerm (s.name c) t ht⟩
  | addAssertion x y hx hy => exact ⟨c, hc, Step6.addAssertion (s.name c) x y hx hy⟩
  | remove x y hp => exact ⟨c, hc, Step6.remove (s.name c) x y hp⟩
  | identify u v hu hv huv =>
    exact ⟨merge u v c, merge_mem_erase hu huv hc, Step6.identify (s.name c) u v hu hv huv⟩

/-! ## Invariants of one change -/

theorem Step7.wf {s t : NSt} (h : Step7 s t) (hw : s.WF) : t.WF := by
  cases h with
  | addTerm t ht => exact addTerm_wf hw t
  | addAssertion x y hx hy =>
    have h' : ((s.addAssertion x y).name x).WF :=
      (Step6.addAssertion (s.name x) x y hx hy).wf (name_wf hw hx)
    exact (wf_of_name h').1
  | remove x y hp =>
    have hx : x ∈ s.T := (hw (x, y) hp).1
    have h' : ((s.remove x y).name x).WF := (Step6.remove (s.name x) x y hp).wf (name_wf hw hx)
    exact (wf_of_name h').1
  | identify u v hu hv huv =>
    have h' : ((s.identify u v).name (merge u v u)).WF :=
      (Step6.identify (s.name u) u v hu hv huv).wf (name_wf hw hu)
    exact (wf_of_name h').1

/-- The outcome of every change on a well-formed state has a term. -/
theorem Step7.nonempty_out {s t : NSt} (h : Step7 s t) (hw : s.WF) : t.T.Nonempty := by
  cases h with
  | addTerm t ht => exact Finset.insert_nonempty _ _
  | addAssertion x y hx hy => exact ⟨x, hx⟩
  | remove x y hp => exact ⟨x, (hw (x, y) hp).1⟩
  | identify u v hu hv huv => exact ⟨u, Finset.mem_erase.2 ⟨huv, hu⟩⟩

/-- A state with a term leaves a state with a term: the seventh seed's one irreversible change
(the sixth's `Step6.names_stay_merged` has no object here). -/
theorem Step7.nonempty {s t : NSt} (h : Step7 s t) (hs : s.T.Nonempty) : t.T.Nonempty := by
  cases h with
  | addTerm t ht => exact Finset.insert_nonempty _ _
  | addAssertion x y hx hy => exact hs
  | remove x y hp => exact hs
  | identify u v hu hv huv => exact ⟨u, Finset.mem_erase.2 ⟨huv, hu⟩⟩

/-- **The first change can only add a term.** -/
theorem first_change_adds_term {t : NSt} (h : Step7 empty t) : ∃ x, t = empty.addTerm x := by
  cases h with
  | addTerm t ht => exact ⟨t, rfl⟩
  | addAssertion x y hx hy => exact absurd hx (Finset.notMem_empty x)
  | remove x y hp => exact absurd rfl hp
  | identify u v hu hv huv => exact absurd hu (Finset.notMem_empty u)

/-! ## Sequences of changes -/

/-- `Reach7 s t n`: `t` is reached from `s` by `n` changes of the seventh seed. -/
inductive Reach7 : NSt → NSt → ℕ → Prop
  | refl (s : NSt) : Reach7 s s 0
  | step {s t u : NSt} {n : ℕ} : Reach7 s t n → Step7 t u → Reach7 s u (n + 1)

theorem Reach7.trans {s t u : NSt} {n m : ℕ} (h1 : Reach7 s t n) (h2 : Reach7 t u m) :
    Reach7 s u (n + m) := by
  induction h2 with
  | refl => exact h1
  | step _ st ih => exact Reach7.step ih st

theorem Reach7.single {s t : NSt} (h : Step7 s t) : Reach7 s t 1 := Reach7.step (Reach7.refl s) h

theorem Reach7.eq_of_zero {s t : NSt} (h : Reach7 s t 0) : s = t := by
  cases h
  rfl

theorem Reach7.wf {s t : NSt} {n : ℕ} (h : Reach7 s t n) (hs : s.WF) : t.WF := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.wf ih

/-- Once a state has a term, every later state has a term. -/
theorem Reach7.nonempty {s t : NSt} {n : ℕ} (h : Reach7 s t n) (hs : s.T.Nonempty) :
    t.T.Nonempty := by
  induction h with
  | refl => exact hs
  | step _ st ih => exact st.nonempty ih

/-- Every sequence of changes of the sixth seed is a sequence of the seventh on the forgotten
states. -/
theorem _root_.Seed.Sixth.Reach6.forget {s t : MSt} {n : ℕ} (h : Reach6 s t n) :
    Reach7 s.forget t.forget n := by
  induction h with
  | refl => exact Reach7.refl _
  | step _ st ih => exact Reach7.step ih st.forget

/-- Every sequence of the seventh seed from a state with a term is a sequence of the sixth on
the named states. -/
theorem Reach7.name {s t : NSt} {n : ℕ} (h : Reach7 s t n) {c : ℕ} (hc : c ∈ s.T) :
    ∃ c', c' ∈ t.T ∧ Reach6 (s.name c) (t.name c') n := by
  induction h with
  | refl => exact ⟨c, hc, Reach6.refl _⟩
  | step _ st ih =>
    obtain ⟨c1, hc1, r⟩ := ih
    obtain ⟨c2, hc2, st'⟩ := st.name hc1
    exact ⟨c2, hc2, Reach6.step r st'⟩

/-- **The empty state is never returned to**: it is reached from a well-formed state only from
itself, in zero changes. -/
theorem reach7_empty_iff {s : NSt} {n : ℕ} (hs : s.WF) : Reach7 s empty n ↔ s = empty ∧ n = 0 := by
  constructor
  · intro h
    cases h with
    | refl => exact ⟨rfl, rfl⟩
    | step r st => exact absurd (st.nonempty_out (r.wf hs)) empty_not_nonempty
  · rintro ⟨rfl, rfl⟩
    exact Reach7.refl _

end Seed.Seventh
