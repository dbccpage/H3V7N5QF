import Twentysecond.Undo

/-!
# What is recorded for a result, and which changes lower it

The seed: "For every result, record how many terms and assertions it adds to
what is given."  Nothing is given, so a result records its terms and its
assertions.  A result's states assert different numbers of assertions; the
record is read on its plain state (reading C-R of the paper): `recorded G`
is the terms and the assertions of the plain part, the same for every state of
the result (`recorded_same`).  Their sum is `phi`, the fewest changes.

How each kind of change moves it (derived here):
* adding a term: terms `+1`, assertions unchanged (`record_addTerm`);
* adding `xqy`: the assertions fall by exactly one when the result asserts
  the same pair in the other relation, and rise by one otherwise
  (`record_add`);
* removing `xqy` (from a state asserting it): the assertions fall by exactly
  one when the result asserts `xqy`, and rise by one otherwise — possible
  only from a state that asserts the pair in both relations
  (`record_remove`);
* identifying two terms: terms `−1`, assertions down by an even number
  (`record_identify`), which can be any even number (`identify_takes`).

In the ninth what is recorded is the terms and the assertions of the state
itself; an addition raises it (`ninth_record_add`), a removal lowers the
assertions by one and an identification the terms by one.
-/

namespace Twentysecond

/-- What is recorded for a result: its terms, and the assertions of its plain part. -/
def recorded (G : St) : Nat × Nat := (G.n, (plain G.A).length)

theorem recorded_same {G H : St} (h : Same G H) : recorded G = recorded H := by
  simp only [recorded, h.1, h.2.length_eq]

theorem recorded_sum (G : St) : (recorded G).1 + (recorded G).2 = phi G := rfl

theorem record_addTerm (G : St) : recorded G.addTerm = (G.n + 1, (recorded G).2) := rfl

/-- **Adding `xqy`** lowers the recorded assertions by exactly one when the result asserts the other
relation on that pair, and raises them by one otherwise. -/
theorem record_add (G : St) (a : Atom) :
    (a.partner ∈ plain G.A ∧ (recorded (G.add a)).2 + 1 = (recorded G).2) ∨
    (a.partner ∉ plain G.A ∧ (recorded (G.add a)).2 = (recorded G).2 + 1) :=
  length_plain_cons a G.A

/-- **Removing `xqy`** from a state asserting it lowers the recorded assertions by exactly one when
the result asserts `xqy`, and raises them by one otherwise. -/
theorem record_remove (G : St) {a : Atom} (ha : a ∈ G.A) :
    (a ∈ plain G.A ∧ (recorded (G.remove a)).2 + 1 = (recorded G).2) ∨
    (a ∉ plain G.A ∧ (recorded (G.remove a)).2 = (recorded G).2 + 1) := by
  simp only [recorded, St.remove]
  have hp := plain_perm (perm_cons_del ha)
  rcases length_plain_cons a (del a G.A) with ⟨h1, e⟩ | ⟨h1, e⟩
  · right
    refine ⟨fun m => ?_, by rw [hp.length_eq]; omega⟩
    have m' := hp.mem_iff.1 m
    rw [plain_cons, if_pos h1] at m'
    have := plain_reduced h1
    rw [Atom.partner_partner] at this
    exact this (mem_of_mem_del m')
  · left
    refine ⟨hp.mem_iff.2 ?_, by rw [hp.length_eq]; omega⟩
    rw [plain_cons, if_neg h1]
    exact List.mem_cons_self

/-- **Identifying two terms** lowers the terms by one and the recorded assertions by an even number. -/
theorem record_identify (G : St) (u v : Nat) :
    (recorded (G.identify u v)).1 = G.n - 1 ∧
      ∃ c, (recorded G).2 = (recorded (G.identify u v)).2 + 2 * c := by
  refine ⟨rfl, ?_⟩
  simp only [recorded, St.identify]
  obtain ⟨k, hk⟩ := plain_parity G.A
  obtain ⟨k', hk'⟩ := plain_parity (G.A.map (Atom.mapT (glue G.n u v)))
  have hle := length_plain_map_le (glue G.n u v) G.A
  rw [List.length_map] at hk'
  exact ⟨k' - k, by omega⟩

/-- `c` copies of `0 r 1` and of `1 s 0`, on two terms. -/
def spread : Nat → List Atom
  | 0 => []
  | k + 1 => ⟨.r, 0, 1⟩ :: ⟨.s, 1, 0⟩ :: spread k

/-- `c` copies of `0 r 0` and of `0 s 0`. -/
def loops : Nat → List Atom
  | 0 => []
  | k + 1 => ⟨.r, 0, 0⟩ :: ⟨.s, 0, 0⟩ :: loops k

theorem mem_spread {c : Nat} {a : Atom} (h : a ∈ spread c) : a = ⟨.r, 0, 1⟩ ∨ a = ⟨.s, 1, 0⟩ := by
  induction c with
  | zero => exact absurd h List.not_mem_nil
  | succ k ih =>
    rcases List.mem_cons.1 h with e | h'
    · exact Or.inl e
    · rcases List.mem_cons.1 h' with e | h''
      · exact Or.inr e
      · exact ih h''

theorem length_spread (c : Nat) : (spread c).length = 2 * c := by
  induction c with
  | zero => rfl
  | succ k ih => simp [spread, ih]; omega

theorem loops_together (c : Nat) : Together (loops c) := by
  induction c with
  | zero => exact Together.nil
  | succ k ih => exact Together.cons ⟨.r, 0, 0⟩ ih

theorem map_spread (c : Nat) : (spread c).map (Atom.mapT (glue 2 0 1)) = loops c := by
  induction c with
  | zero => rfl
  | succ k ih =>
    simp only [spread, loops, List.map_cons, ih]
    rfl

/-- **One identification can take out any even number of recorded assertions**: `c` copies of
`0 r 1` and of `1 s 0` record `2c` assertions; identifying `0` and `1` leaves none. -/
theorem identify_takes (c : Nat) :
    ∃ G : St, G.WF ∧ G.n = 2 ∧ (recorded G).2 = 2 * c ∧ (recorded (G.identify 0 1)).2 = 0 := by
  refine ⟨⟨2, spread c⟩, ?_, rfl, ?_, ?_⟩
  · intro a ha
    rcases mem_spread ha with e | e <;> subst e <;> exact ⟨by simp, by simp⟩
  · simp only [recorded]
    rw [plain_eq_self, length_spread]
    intro a ha hp
    rcases mem_spread ha with e | e <;> subst e <;> rcases mem_spread hp with e' | e' <;> cases e'
  · simp only [recorded, St.identify]
    rw [map_spread]
    have := plain_append_together (l := []) (loops_together c)
    rw [List.nil_append] at this
    rw [this.length_eq]
    rfl

/-- In the ninth an addition raises the recorded assertions (the state's own) by one. -/
theorem ninth_record_add (G : St) (a : Atom) : (G.add a).A.length = G.A.length + 1 := rfl

end Twentysecond
