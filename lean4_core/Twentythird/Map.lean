import Twentythird.Fewest

/-!
# The earlier seeds mapped in, what the merge loses, and the map back

**No earlier seed of the line maps its states one to one into this seed's
results.**
* The seventh (one relation, re-written by the twenty-second as `St7`): the
  states `a b; arb arb` and `a b; arb bra` are different in every writing
  (`seventh_pair_apart`) and one result here (`seventh_pair_merge`) — raise
  `a` in the second, then take out `bra bsa`.
* The twenty-second: their images are different twenty-second results in
  every writing (`twentysecond_pair_apart`, through the twenty-second's own
  `ofR_sameW_iff`); so are they as ninth states (`ninth_pair_apart`).
* The first (one relation, each pair at most once, no `xrx`): `a b c; arb arc`
  and `a b c; bra cra` are first-seed states (`first_pair_states`), different
  in every writing (`first_pair_apart`: in the first a term is the left term
  of two pairs, in the second none is), and one result here
  (`first_pair_merge`).
* Any map sending the empty state to the empty state and each addition to
  the same addition, up to the twenty-second's sameness, merges the seventh
  pair (`carried_additions_merge3`).

**The map back** goes to the twenty-second's results: `ReadBack3 G T` — `T`
asserts the fewest among the states of the result of `G`, and every other
such state is `T` in some writing (the twenty-second's `SameW`).  It answers
at most one twenty-second result, up to writing (`ReadBack3.functional`),
and depends on the result only (`ReadBack3.congr`).  On mapped states: on
`a b; arb` it returns `a b; arb` (`readBack3_arb`); on `a b; arb bsa` it
returns another twenty-second result, `a b` (`readBack3_raisedPair`).  It
answers "none" on `a b; arb arb` (`readBack3_none`), whose states asserting
the fewest are `a b; arb arb` and `a b; arb bra`; and **every result costing
at most three changes has an answer** (`readBack3_some_of_cost_le_three`),
so the results answered "none" start at cost four.
-/

namespace Twentythird

open Twentysecond

/-! ## The earlier seeds' states do not map one to one -/

/-- `a b; arb arb`. -/
def arbTwice : St7 := ⟨2, [(0, 1), (0, 1)]⟩

/-- `a b; arb bra`. -/
def arbBra : St7 := ⟨2, [(0, 1), (1, 0)]⟩

/-- `a b c; arb arc`. -/
def outStar : St7 := ⟨3, [(0, 1), (0, 2)]⟩

/-- `a b c; bra cra`. -/
def inStar : St7 := ⟨3, [(1, 0), (2, 0)]⟩

theorem mem_two {α : Type} {p a b : α} (h : p ∈ [a, b]) : p = a ∨ p = b := by
  rcases List.mem_cons.1 h with e | h'
  · exact Or.inl e
  · rcases List.mem_cons.1 h' with e | h''
    · exact Or.inr e
    · exact absurd h'' List.not_mem_nil

/-- **`a b; arb arb` and `a b; arb bra` are two seventh results in every writing.** -/
theorem seventh_pair_apart : ¬ SameW7 arbTwice arbBra := by
  rintro ⟨f, g, _, _, hp⟩
  have m1 : ((0, 1) : Nat × Nat) ∈ [(f 0, f 1), (f 0, f 1)] := hp.mem_iff.2 List.mem_cons_self
  have m2 : ((1, 0) : Nat × Nat) ∈ [(f 0, f 1), (f 0, f 1)] :=
    hp.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self)
  have e1 : ((0, 1) : Nat × Nat) = (f 0, f 1) := by rcases mem_two m1 with e | e <;> exact e
  have e2 : ((1, 0) : Nat × Nat) = (f 0, f 1) := by rcases mem_two m2 with e | e <;> exact e
  have := e1.trans e2.symm
  exact absurd this (by decide)

theorem lt_three {x : Nat} (h : x < 3) : x = 0 ∨ x = 1 ∨ x = 2 := by omega

/-- **… and one result here.** -/
theorem seventh_pair_merge : Same3 (ofR arbTwice) (ofR arbBra) := by
  refine ⟨rfl, fun x => if x = 0 then 1 else 0, fun x y hx hy => ?_⟩
  have hx' : x < 2 := hx
  have hy' : y < 2 := hy
  rcases lt_two hx' with rfl | rfl <;> rcases lt_two hy' with rfl | rfl <;> decide

/-- Their images are two twenty-second results in every writing. -/
theorem twentysecond_pair_apart : ¬ SameW (ofR arbTwice) (ofR arbBra) :=
  fun h => seventh_pair_apart (ofR_sameW_iff.1 h)

/-- … and two ninth states in every writing. -/
theorem ninth_pair_apart : ¬ SameW9 (ofR arbTwice) (ofR arbBra) := by
  rintro ⟨f, g, hr, s⟩
  exact twentysecond_pair_apart ⟨f, g, hr, s.same⟩

/-- `a b c; arb arc` and `a b c; bra cra` are states of the first seed: no pair twice, no `xrx`. -/
theorem first_pair_states :
    outStar.P.Nodup ∧ inStar.P.Nodup ∧ (∀ p ∈ outStar.P, p.1 ≠ p.2) ∧ (∀ p ∈ inStar.P, p.1 ≠ p.2) := by
  decide

/-- **`a b c; arb arc` and `a b c; bra cra` are different in every writing.** -/
theorem first_pair_apart : ¬ SameW7 outStar inStar := by
  rintro ⟨f, g, _, _, hp⟩
  have m1 : ((1, 0) : Nat × Nat) ∈ [(f 0, f 1), (f 0, f 2)] := hp.mem_iff.2 List.mem_cons_self
  have m2 : ((2, 0) : Nat × Nat) ∈ [(f 0, f 1), (f 0, f 2)] :=
    hp.mem_iff.2 (List.mem_cons_of_mem _ List.mem_cons_self)
  have e1 : (1 : Nat) = f 0 := by
    rcases mem_two m1 with e | e
    · exact congrArg Prod.fst e
    · exact congrArg Prod.fst e
  have e2 : (2 : Nat) = f 0 := by
    rcases mem_two m2 with e | e
    · exact congrArg Prod.fst e
    · exact congrArg Prod.fst e
  omega

/-- **… and one result here**: the first is the second raised at `a`. -/
theorem first_pair_merge : Same3 (ofR outStar) (ofR inStar) := by
  refine ⟨rfl, fun x => if x = 0 then 1 else 0, fun x y hx hy => ?_⟩
  have hx' : x < 3 := hx
  have hy' : y < 3 := hy
  rcases lt_three hx' with rfl | rfl | rfl <;> rcases lt_three hy' with rfl | rfl | rfl <;> decide

/-- **Any map carrying the empty state to the empty state and each addition to the same addition, up to
the twenty-second's sameness, sends `a b; arb arb` and `a b; arb bra` to one result here.** -/
theorem carried_additions_merge3 (f : St → St) (h0 : Same (f empty) empty)
    (hT : ∀ G, Same (f G.addTerm) (f G).addTerm) (hA : ∀ G a, Same (f (G.add a)) ((f G).add a)) :
    Same3 (f (ofR arbTwice)) (f (ofR arbBra)) := by
  have h1 : Same (f ⟨1, []⟩) ⟨1, []⟩ := (hT empty).trans h0.addTerm
  have h2 : Same (f ⟨2, []⟩) ⟨2, []⟩ := (hT ⟨1, []⟩).trans h1.addTerm
  have a1 : Same (f (ofR arbTwice)) (ofR arbTwice) := by
    have e : ofR arbTwice = ((⟨2, []⟩ : St).add ⟨.r, 0, 1⟩).add ⟨.r, 0, 1⟩ := rfl
    rw [e]
    exact (hA _ _).trans (((hA _ _).trans (h2.add _)).add _)
  have a2 : Same (f (ofR arbBra)) (ofR arbBra) := by
    have e : ofR arbBra = ((⟨2, []⟩ : St).add ⟨.r, 1, 0⟩).add ⟨.r, 0, 1⟩ := rfl
    rw [e]
    exact (hA _ _).trans (((hA _ _).trans (h2.add _)).add _)
  exact (Same.same3 a1).trans (seventh_pair_merge.trans (Same.same3 a2).symm)

/-! ## The map back -/

/-- `T` is a state of the result of `G` asserting the fewest. -/
def Fewest3 (G T : St) : Prop := Same3 T G ∧ Fewest T

/-- The map back answers `T`: the result's one state asserting the fewest, up to writing. -/
def ReadBack3 (G T : St) : Prop := Fewest3 G T ∧ ∀ T', Fewest3 G T' → SameW T' T

theorem ReadBack3.functional {G T T' : St} (h : ReadBack3 G T) (h' : ReadBack3 G T') : SameW T T' :=
  h'.2 T h.1

theorem ReadBack3.congr {G G' T : St} (s : Same3 G G') : ReadBack3 G T ↔ ReadBack3 G' T := by
  constructor
  · rintro ⟨⟨a, b⟩, c⟩
    exact ⟨⟨a.trans s, b⟩, fun T' ⟨x, y⟩ => c T' ⟨x.trans s.symm, y⟩⟩
  · rintro ⟨⟨a, b⟩, c⟩
    exact ⟨⟨a.trans s.symm, b⟩, fun T' ⟨x, y⟩ => c T' ⟨x.trans s, y⟩⟩

theorem nothing_wf (n : Nat) : St.WF ⟨n, []⟩ := fun _ h => absurd h List.not_mem_nil

theorem fewest_nothing (n : Nat) : Fewest ⟨n, []⟩ := ⟨nothing_wf n, fun _ _ _ => Nat.zero_le _⟩

theorem eq_nothing_of_length {G : St} (h : G.A.length = 0) : G = ⟨G.n, []⟩ := by
  cases G with
  | mk n A =>
    cases A with
    | nil => rfl
    | cons a t => simp at h

/-- **On `a b; arb bsa` (a twenty-second result) the map back returns another one: `a b`.** -/
theorem readBack3_raisedPair : ReadBack3 raisedPair ⟨2, []⟩ := by
  refine ⟨⟨raisedPair_nothing.symm, fewest_nothing 2⟩, fun T' ⟨s, hf⟩ => ?_⟩
  have hl : T'.A.length ≤ 0 := hf.2 ⟨2, []⟩ (nothing_wf 2) (raisedPair_nothing.symm.trans s.symm)
  have hn : T'.n = 2 := s.n
  have e := eq_nothing_of_length (G := T') (by omega)
  rw [e, hn]
  exact SameW.refl _

theorem two_single {a b : Atom} (ha : a.x < 2 ∧ a.y < 2) (hb : b.x < 2 ∧ b.y < 2)
    (h : Same3 ⟨2, [b]⟩ ⟨2, [a]⟩) : SameW ⟨2, [b]⟩ ⟨2, [a]⟩ := by
  have i0 := h.loop (x := 0) (by show (0 : Nat) < 2; decide)
  have i1 := h.loop (x := 1) (by show (1 : Nat) < 2; decide)
  have i2 := h.twoWay (x := 0) (y := 1) (by show (0 : Nat) < 2; decide) (by show (1 : Nat) < 2; decide)
  have sw : IsRw 2 (fun t => 1 - t) (fun t => 1 - t) :=
    ⟨fun _ h => by omega, fun _ h => by omega, fun _ h => by omega, fun _ h => by omega⟩
  obtain ⟨q, x, y⟩ := a
  obtain ⟨q', x', y'⟩ := b
  have hx : x < 2 := ha.1
  have hy : y < 2 := ha.2
  have hx' : x' < 2 := hb.1
  have hy' : y' < 2 := hb.2
  rcases lt_two hx with rfl | rfl <;> rcases lt_two hy with rfl | rfl <;>
    rcases lt_two hx' with rfl | rfl <;> rcases lt_two hy' with rfl | rfl <;>
    cases q <;> cases q' <;>
    first
      | exact SameW.refl _
      | exact ⟨fun t => 1 - t, fun t => 1 - t, sw, Same.refl _⟩
      | (exfalso; revert i0 i1 i2; decide)

theorem fewest3_length {G T : St} (h : Fewest3 G T) {c : Nat} (hc : Cost3 G c) : phi T = c := by
  have a := (cost3_iff.1 hc).2 T h.2.1 h.1
  obtain ⟨⟨H, hH, s, e⟩, _⟩ := cost3_iff.1 hc
  have b := h.2.2 H.plainSt (plainSt_wf hH) ((Same.same3 (same_plainSt H).symm).trans (s.trans h.1.symm))
  have t := h.2.plain
  have l := length_split T.A
  rw [t, List.length_nil] at l
  simp only [phi, St.plainSt] at a b e ⊢
  have hn : T.n = H.n := h.1.n.trans s.n.symm
  omega

theorem fewest3_of_cost {G H : St} (hH : H.WF) (s : Same3 H G) {c : Nat} (hc : Cost3 G c) (e : phi H = c) :
    Fewest3 G H.plainSt := by
  refine ⟨(Same.same3 (same_plainSt H).symm).trans s, plainSt_wf hH, fun K hK sK => ?_⟩
  have a := (cost3_iff.1 hc).2 K hK (sK.trans ((Same.same3 (same_plainSt H).symm).trans s))
  have b := length_plain_le K.A
  have hn : K.n = H.n := sK.n
  simp only [phi, St.plainSt] at a e ⊢
  omega

/-- **Every result costing at most three changes has an answer**: its states asserting the fewest are one
twenty-second result, up to writing. -/
theorem readBack3_some_of_cost_le_three {G : St} {c : Nat} (hc : Cost3 G c) (h3 : c ≤ 3) : ∃ T, ReadBack3 G T := by
  obtain ⟨⟨H, hH, s, e⟩, _⟩ := cost3_iff.1 hc
  have fT := fewest3_of_cost hH s hc e
  refine ⟨H.plainSt, fT, fun T' hT' => ?_⟩
  have p1 := fewest3_length hT' hc
  have p2 := fewest3_length fT hc
  have w1 := hT'.2.1
  have w2 := fT.2.1
  have n1 : T'.n = H.plainSt.n := hT'.1.n.trans fT.1.n.symm
  have st : Same3 T' H.plainSt := hT'.1.trans fT.1.symm
  have pl1 : plain T'.A = T'.A := plain_eq_self_of_together_nil hT'.2.plain
  have pl2 : plain H.plainSt.A = H.plainSt.A := plain_eq_self_of_together_nil fT.2.plain
  simp only [phi] at p1 p2
  rw [pl1] at p1
  rw [pl2] at p2
  -- by the number of terms
  by_cases hn0 : T'.n = 0
  · have a := eq_empty_of_wf w1 hn0
    have b := eq_empty_of_wf w2 (by omega)
    rw [a, b]
    exact SameW.refl _
  · by_cases hn1 : T'.n = 1
    · refine Same.sameW (same_iff_excess.2 ⟨n1, fun u v => ?_⟩)
      by_cases hu : u < 1
      · by_cases hv : v < 1
        · have hu0 : u = 0 := by omega
          have hv0 : v = 0 := by omega
          subst hu0
          subst hv0
          exact st.loop (by omega)
        · rw [excess_out w1 (Or.inr (by omega)), excess_out w2 (Or.inr (by omega))]
      · rw [excess_out w1 (Or.inl (by omega)), excess_out w2 (Or.inl (by omega))]
    · by_cases hn2 : T'.n = 2
      · -- at most one assertion each, and as many in both
        have l : T'.A.length = H.plainSt.A.length := by omega
        cases e1 : T'.A with
        | nil =>
          have a := eq_nothing_of_length (G := T') (by rw [e1]; rfl)
          have b := eq_nothing_of_length (G := H.plainSt) (by rw [← l, e1]; rfl)
          rw [a, b, n1]
          exact SameW.refl _
        | cons b t =>
          have tb : t = [] := by
            cases t with
            | nil => rfl
            | cons _ _ => rw [e1] at p1; simp at p1; omega
          cases e2 : H.plainSt.A with
          | nil => rw [e1, e2] at l; simp at l
          | cons a t' =>
            have ta : t' = [] := by
              cases t' with
              | nil => rfl
              | cons _ _ => rw [e2] at p2; simp at p2; omega
            subst tb
            subst ta
            have hb := w1 b (by rw [e1]; exact List.mem_cons_self)
            have ha := w2 a (by rw [e2]; exact List.mem_cons_self)
            rw [hn2] at hb
            rw [← n1, hn2] at ha
            have eT' : T' = ⟨2, [b]⟩ := by
              cases T' with
              | mk n A => simp only at hn2 e1; subst hn2; subst e1; rfl
            have eT : H.plainSt = ⟨2, [a]⟩ := by
              have hn2' : H.plainSt.n = 2 := by omega
              revert e2 hn2'
              generalize H.plainSt = K
              intro e2 hn2'
              cases K with
              | mk n A => simp only at hn2' e2; subst hn2'; subst e2; rfl
            rw [eT', eT] at st ⊢
            exact two_single ha hb st
      · -- three or more terms: nothing asserted in either
        have a := eq_nothing_of_length (G := T') (by omega)
        have b := eq_nothing_of_length (G := H.plainSt) (by omega)
        rw [a, b, n1]
        exact SameW.refl _

theorem ofR_arbTwice_wf : (ofR arbTwice).WF := by
  intro a ha
  simp only [ofR, arbTwice, rAtom, List.map, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h <;> subst h <;> decide

theorem ofR_arbBra_wf : (ofR arbBra).WF := by
  intro a ha
  simp only [ofR, arbBra, rAtom, List.map, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h | h <;> subst h <;> decide

/-- `a b; arb arb` costs four changes. -/
theorem cost3_arbTwice : Cost3 (ofR arbTwice) 4 := by
  have := cost3_two ofR_arbTwice_wf rfl
  exact this

/-- **The map back answers "none" on `a b; arb arb`**: `a b; arb arb` and `a b; arb bra` both assert the
fewest of that result, and they are two twenty-second results in every writing. -/
theorem readBack3_none : ∀ T, ¬ ReadBack3 (ofR arbTwice) T := by
  intro T h
  have f1 : Fewest3 (ofR arbTwice) (ofR arbTwice) := by
    have := fewest3_of_cost ofR_arbTwice_wf (Same3.refl _) cost3_arbTwice (by decide)
    rwa [show (ofR arbTwice).plainSt = ofR arbTwice from rfl] at this
  have f2 : Fewest3 (ofR arbTwice) (ofR arbBra) := by
    have := fewest3_of_cost ofR_arbBra_wf seventh_pair_merge.symm cost3_arbTwice (by decide)
    rwa [show (ofR arbBra).plainSt = ofR arbBra from rfl] at this
  have a := h.2 _ f1
  have b := h.2 _ f2
  exact twentysecond_pair_apart (a.trans (b.symm ofR_arbBra_wf h.1.2.1) ofR_arbTwice_wf h.1.2.1)

/-- `a b; arb`. -/
def arbOnce : St := ⟨2, [⟨.r, 0, 1⟩]⟩

theorem arbOnce_wf : arbOnce.WF := by
  intro a ha
  simp only [arbOnce, List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  decide

/-- **On a mapped state the map back returns the original exactly when the original asserts the fewest of
its result and every other such state is it in some writing.** -/
theorem readBack3_self_iff (T : St) : ReadBack3 T T ↔ Fewest T ∧ ∀ T', Fewest3 T T' → SameW T' T :=
  ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨Same3.refl T, h.1⟩, h.2⟩⟩

/-- **Whatever the map back answers asserts the fewest of the result, at its cost.** -/
theorem readBack3_answer_cost {G T : St} (h : ReadBack3 G T) {c : Nat} (hc : Cost3 G c) : phi T = c :=
  fewest3_length h.1 hc

/-- **On `a b; arb` the map back returns it.** -/
theorem readBack3_arb : ReadBack3 arbOnce arbOnce := by
  have hc : Cost3 arbOnce 3 := cost3_two arbOnce_wf rfl
  have f : Fewest3 arbOnce arbOnce := by
    have := fewest3_of_cost arbOnce_wf (Same3.refl _) hc (by decide)
    rwa [show arbOnce.plainSt = arbOnce from rfl] at this
  obtain ⟨T, hT⟩ := readBack3_some_of_cost_le_three hc (by decide)
  exact ⟨f, fun T' hT' => (hT.2 T' hT').trans ((hT.2 _ f).symm arbOnce_wf hT.1.2.1) hT'.2.1 hT.1.2.1⟩

end Twentythird
