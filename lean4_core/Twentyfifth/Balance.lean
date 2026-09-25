import Twentyfifth.Fill

/-!
# Balance, the sameness with filled triples, and what filled triples tell

"Three filled terms `x`, `y`, `z` balance when, going from `x` to `y` to `z`
and back to `x`, as many assertions are written with `r` as with `s`, each
counted as often as it is asserted."  Going from `x` to `y` goes along `xry`
and `xsy` (reading C-B1), so the triple balances when
`e(x, y) + e(y, z) + e(z, x) = 0` (`Balanced`), `e` the excess
`M_r − M_s` — the twenty-third's sum around three terms.

Derived here:
* the sum around a triple is the same going round from another term
  (`around_rot`, `around_norm`), and is kept by the twenty-third's sameness
  (`Same3.around`, imported): **which filled triples balance is the same on
  every state of a result** (`Same25.balanced_iff`);
* the sameness at a fixed writing, `Same25`: the twenty-third's on the
  assertions, and the same filled triples; it is exactly what the seed's
  clauses generate, which do not touch the filled triples (`gen25_iff_same25`);
* **a result asserting nothing balances every filled triple**
  (`nothing_balanced`), so **a result is told from the one asserting nothing on
  as many terms, with the same filled triples, by filled terms that do not
  balance exactly when one of its filled triples does not balance**
  (`told_iff`); a told result is the same as no result asserting nothing
  (`told_not_nothing`);
* what filled triples do not see: a loop is never gone along
  (`around_add_loop`, `loop_unseen`); a two-way sum can be seen one way round
  and not the other (`arb_one_way`); a three-term result with a non-zero
  two-way sum balances both ways round (`blind_three_not_nothing`);
* the exchange of the two relations negates every sum around, so a triple
  balances in a state exactly when it balances in its exchange
  (`balanced_swap`).
-/

namespace Twentyfifth

open Twentysecond Twentythird

/-- The sum around a triple: `e(x, y) + e(y, z) + e(z, x)`. -/
def around (G : St) (t : Tri) : Int := excess G t.x t.y + excess G t.y t.z + excess G t.z t.x

/-- The triple balances: going round it, as many assertions with `r` as with `s`. -/
def Balanced (G : St) (t : Tri) : Prop := around G t = 0

instance (G : St) (t : Tri) : Decidable (Balanced G t) := inferInstanceAs (Decidable (_ = _))

theorem around_rot (G : St) (t : Tri) : around G t.rot = around G t := by
  show excess G t.y t.z + excess G t.z t.x + excess G t.x t.y =
    excess G t.x t.y + excess G t.y t.z + excess G t.z t.x
  omega

/-- The normal form of a triple is gone round the same way. -/
theorem around_norm (G : St) (t : Tri) : around G t.norm = around G t := by
  rcases Tri.norm_cases t with e | e | e <;> rw [e]
  · rw [around_rot]
  · rw [around_rot, around_rot]

theorem Same3.around25 {G H : St} (s : Same3 G H) {t : Tri} (ht : t.Within G.n) : around G t = around H t :=
  s.around ht.1 ht.2.1 ht.2.2

theorem around_nothing (n : Nat) (t : Tri) : around ⟨n, []⟩ t = 0 := rfl

/-- **A result asserting nothing balances every filled triple.** -/
theorem nothing_balanced {G : St} (h : Same3 G ⟨G.n, []⟩) {t : Tri} (ht : t.Within G.n) : Balanced G t := by
  unfold Balanced
  rw [Same3.around25 h ht, around_nothing]

/-! ## The sameness with filled triples -/

/-- The seed's sameness at a fixed writing: the twenty-third's on the assertions, the same filled triples. -/
def Same25 (A B : FSt) : Prop := Same3 A.G B.G ∧ A.F.Perm B.F

theorem Same25.refl (A : FSt) : Same25 A A := ⟨Same3.refl _, List.Perm.refl _⟩

theorem Same25.symm {A B : FSt} (h : Same25 A B) : Same25 B A := ⟨h.1.symm, h.2.symm⟩

theorem Same25.trans {A B C : FSt} (h1 : Same25 A B) (h2 : Same25 B C) : Same25 A C :=
  ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩

theorem Same25.n {A B : FSt} (h : Same25 A B) : A.G.n = B.G.n := h.1.n

/-- The sameness the seed's clauses generate at a fixed writing: the three clauses act on the assertions
(the twenty-third's `Gen3`), and the filled triples are the same whatever order they are listed in. -/
inductive Gen25 : FSt → FSt → Prop
  | gen {A B : FSt} : Gen3 A.G B.G → A.F = B.F → Gen25 A B
  | perm {A B : FSt} : A.G = B.G → A.F.Perm B.F → Gen25 A B
  | symm {A B : FSt} : Gen25 A B → Gen25 B A
  | trans {A B C : FSt} : Gen25 A B → Gen25 B C → Gen25 A C

theorem Gen25.same25 {A B : FSt} (h : Gen25 A B) : Same25 A B := by
  induction h with
  | gen g e => exact ⟨g.same3, e ▸ List.Perm.refl _⟩
  | perm e p => exact ⟨e ▸ Same3.refl _, p⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **The sameness the seed's clauses generate is `Same25`** (well-formed assertions). -/
theorem gen25_iff_same25 {A B : FSt} (hA : A.G.WF) (hB : B.G.WF) : Gen25 A B ↔ Same25 A B := by
  constructor
  · exact Gen25.same25
  · rintro ⟨s, p⟩
    have g : Gen3 A.G B.G := (gen3_iff_same3 hA hB).2 s
    exact Gen25.trans (B := ⟨B.G, A.F⟩) (Gen25.gen g rfl) (Gen25.perm rfl p)

/-- **Which filled triples balance is the same on every state of a result.** -/
theorem Same25.balanced_iff {A B : FSt} (s : Same25 A B) (hw : A.WF) {t : Tri} (ht : t ∈ A.F) :
    t ∈ B.F ∧ (Balanced A.G t ↔ Balanced B.G t) := by
  refine ⟨s.2.mem_iff.1 ht, ?_⟩
  unfold Balanced
  rw [Same3.around25 s.1 (hw.2.1 t ht).1]

/-! ## Told from a result asserting nothing -/

/-- Some filled triple does not balance. -/
def Told (A : FSt) : Prop := ∃ t ∈ A.F, ¬ Balanced A.G t

/-- The result asserting nothing on as many terms, with the same filled triples. -/
def nothingWith (A : FSt) : FSt := ⟨⟨A.G.n, []⟩, A.F⟩

/-- Two states record the same: the same filled triples, each balancing in one exactly when in the other. -/
def SameRecord (A B : FSt) : Prop := A.F.Perm B.F ∧ ∀ t ∈ A.F, (Balanced A.G t ↔ Balanced B.G t)

theorem exists_not_of_not_forall {P : Tri → Prop} [DecidablePred P] :
    ∀ {F : List Tri}, ¬ (∀ t ∈ F, P t) → ∃ t ∈ F, ¬ P t
  | [], h => absurd (fun _ m => absurd m List.not_mem_nil) h
  | s :: l, h => by
    by_cases hs : P s
    · have : ¬ (∀ t ∈ l, P t) := fun a => h (fun t m => by
        rcases List.mem_cons.1 m with e | m'
        · exact e ▸ hs
        · exact a t m')
      obtain ⟨t, ht, hn⟩ := exists_not_of_not_forall this
      exact ⟨t, List.mem_cons_of_mem _ ht, hn⟩
    · exact ⟨s, List.mem_cons_self, hs⟩

/-- **Told exactly when a filled triple does not balance**: a result's record of which filled triples
balance differs from the record of the result asserting nothing on as many terms with the same filled
triples exactly when one of its filled triples does not balance. -/
theorem told_iff (A : FSt) : Told A ↔ ¬ SameRecord A (nothingWith A) := by
  constructor
  · rintro ⟨t, ht, hn⟩ ⟨_, h⟩
    have : Balanced (nothingWith A).G t := around_nothing _ t
    exact hn ((h t ht).2 this)
  · intro h
    have hb : ¬ ∀ t ∈ A.F, Balanced A.G t := fun a =>
      h ⟨List.Perm.refl _, fun t ht => ⟨fun _ => around_nothing _ t, fun _ => a t ht⟩⟩
    exact exists_not_of_not_forall hb

/-- Any result asserting nothing with the same terms and filled triples records what `nothingWith` does. -/
theorem sameRecord_nothing {A B : FSt} (hB : Same3 B.G ⟨B.G.n, []⟩) (hp : B.F.Perm A.F)
    (hw : B.WF) : SameRecord B (nothingWith A) :=
  ⟨hp, fun t ht => ⟨fun _ => around_nothing _ t, fun _ => nothing_balanced hB (hw.2.1 t ht).1⟩⟩

/-- **A told result is the same as no result asserting nothing**, whatever that one has filled. -/
theorem told_not_nothing {A : FSt} (hw : A.WF) (ht : Told A) {B : FSt} (hB : Same3 B.G ⟨B.G.n, []⟩) :
    ¬ Same25 A B := by
  intro s
  obtain ⟨t, hmem, hn⟩ := ht
  have hA : Same3 A.G ⟨A.G.n, []⟩ := by
    have := s.1.trans hB
    rw [← s.n] at this
    exact this
  exact hn (nothing_balanced hA (hw.2.1 t hmem).1)

/-- A result not told records exactly what the result asserting nothing with its filled triples records;
it is that result exactly when it asserts nothing up to the sameness. -/
theorem not_told {A : FSt} (h : ¬ Told A) :
    SameRecord A (nothingWith A) ∧ (Same25 A (nothingWith A) ↔ Same3 A.G ⟨A.G.n, []⟩) := by
  have hb : ∀ t ∈ A.F, Balanced A.G t := fun t ht => by
    by_cases b : Balanced A.G t
    · exact b
    · exact absurd ⟨t, ht, b⟩ h
  exact ⟨⟨List.Perm.refl _, fun t ht => ⟨fun _ => around_nothing _ t, fun _ => hb t ht⟩⟩,
    ⟨fun s => s.1, fun s => ⟨s, List.Perm.refl _⟩⟩⟩

/-! ## What filled triples do not see -/

theorem excess_add (G : St) (a : Atom) (u v : Nat) :
    excess (G.add a) u v =
      excess G u v + (if a = ⟨.r, u, v⟩ then 1 else 0) - (if a = ⟨.s, u, v⟩ then 1 else 0) := by
  unfold excess St.add
  simp only [count_cons']
  by_cases h1 : a = ⟨.r, u, v⟩ <;> by_cases h2 : a = ⟨.s, u, v⟩ <;> simp [h1, h2] <;> omega

theorem excess_add_loop (G : St) (q : Rel) {w u v : Nat} (h : u ≠ v) : excess (G.add ⟨q, w, w⟩) u v = excess G u v := by
  rw [excess_add]
  have h1 : ¬ ((⟨q, w, w⟩ : Atom) = ⟨.r, u, v⟩) := fun e => by
    have a := congrArg Atom.x e
    have b := congrArg Atom.y e
    simp only at a b
    exact h (a.symm.trans b)
  have h2 : ¬ ((⟨q, w, w⟩ : Atom) = ⟨.s, u, v⟩) := fun e => by
    have a := congrArg Atom.x e
    have b := congrArg Atom.y e
    simp only at a b
    exact h (a.symm.trans b)
  rw [if_neg h1, if_neg h2]
  omega

/-- **A loop is never gone along**: asserting `xrx` or `xsx` once more changes no sum around three
different terms. -/
theorem around_add_loop (G : St) (q : Rel) (w : Nat) {t : Tri} (h : t.Distinct) :
    around (G.add ⟨q, w, w⟩) t = around G t := by
  unfold around
  rw [excess_add_loop G q h.1, excess_add_loop G q h.2.1, excess_add_loop G q (fun e => h.2.2 e.symm)]

/-- `a b c; ara`, both ways round filled. -/
def loopFilled : FSt := ⟨⟨3, [⟨.r, 0, 0⟩]⟩, [⟨0, 1, 2⟩, ⟨0, 2, 1⟩]⟩

theorem loopFilled_wf : loopFilled.WF := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    simp only [loopFilled, List.mem_cons, List.not_mem_nil, or_false] at ha
    subst ha
    decide
  · intro t ht
    simp only [loopFilled, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with e | e <;> subst e <;> exact ⟨by decide, by decide, rfl⟩
  · decide

/-- **A result differing from nothing only at a loop is not told**: `a b c; ara`, both ways round filled,
balances both filled triples and is not the result asserting nothing. -/
theorem loop_unseen : ¬ Told loopFilled ∧ ¬ Same3 loopFilled.G ⟨3, []⟩ := by
  refine ⟨fun ⟨t, ht, hn⟩ => ?_, fun s => ?_⟩
  · simp only [loopFilled, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with e | e <;> subst e <;> exact hn (by decide)
  · have := s.loop (x := 0) (by show (0 : Nat) < 3; decide)
    exact absurd this (by decide)

/-- **A two-way sum seen one way round and not the other**: in `a b c; arb`, the sum around `a b c` is one
and the sum around `a c b` is zero. -/
theorem arb_one_way : around ⟨3, [⟨.r, 0, 1⟩]⟩ ⟨0, 1, 2⟩ = 1 ∧ around ⟨3, [⟨.r, 0, 1⟩]⟩ ⟨0, 2, 1⟩ = 0 := by
  decide

/-- `a b c; arb arc csb csa`: two-way sums one, minus one and zero. -/
def blindThree : St := ⟨3, [⟨.r, 0, 1⟩, ⟨.r, 0, 2⟩, ⟨.s, 2, 1⟩, ⟨.s, 2, 0⟩]⟩

/-- **A three-term result with a non-zero two-way sum balances both ways round**: no filling tells it from
the result asserting nothing. -/
theorem blind_three_not_nothing :
    around blindThree ⟨0, 1, 2⟩ = 0 ∧ around blindThree ⟨0, 2, 1⟩ = 0 ∧
      excess blindThree 0 1 + excess blindThree 1 0 = 1 ∧ ¬ Same3 blindThree ⟨3, []⟩ := by
  refine ⟨by decide, by decide, by decide, fun s => ?_⟩
  have := s.twoWay (x := 0) (y := 1) (by show (0 : Nat) < 3; decide) (by show (1 : Nat) < 3; decide)
  exact absurd this (by decide)

/-- **`a b c; arb bsa` is told whichever way round it is filled**: its sums around are one and minus one. -/
theorem arcThree_told : around arcThree ⟨0, 1, 2⟩ = 1 ∧ around arcThree ⟨0, 2, 1⟩ = -1 := by decide

/-! ## The exchange of the two relations -/

theorem around_swap (G : St) (t : Tri) : around G.swap t = - around G t := by
  unfold around
  rw [excess_swap, excess_swap, excess_swap]
  omega

/-- **The exchange keeps which triples balance.** -/
theorem balanced_swap (G : St) (t : Tri) : Balanced G.swap t ↔ Balanced G t := by
  unfold Balanced
  rw [around_swap]
  constructor
  · intro h
    omega
  · intro h
    omega

end Twentyfifth
