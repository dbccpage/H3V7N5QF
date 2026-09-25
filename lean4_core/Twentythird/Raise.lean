import Twentysecond

/-!
# Raising a term

The twenty-third seed adds one sentence: "Raising a term `x` adds `xry` and
`ysx` once for every other term `y`."  On a state with terms `0 … n − 1`
(the twenty-second's `St`), raising `x` puts in front of the list of atoms one
`⟨r, x, y⟩` and one `⟨s, y, x⟩` for every `y < n`, `y ≠ x` (`raiseAtoms`).

Derived here:
* `excess_raise`: raising `x` moves the excess `e(u, v)` by `[u = x] − [v = x]`
  at every pair of terms `u, v < n` — `+1` on `(x, y)`, `−1` on `(y, x)`,
  nothing on the loops or elsewhere;
* `raiseTo`: every term `x < k` raised `f x` times; its excess moves by
  `f u − f v` (`excess_raiseTo_all`);
* raising keeps the terms and the well-formedness, and adds `2(n − 1)` atoms
  (`raise_size`);
* **raising every term once is pairs asserted together** (reading C-H2 of the
  paper): the twenty-second's generated sameness already holds between a
  state and the state with every term raised (`raise_all_gen`).
-/

namespace Twentythird

open Twentysecond

/-- The atoms raising `x` adds among the terms `0 … k − 1`: `xry` and `ysx` for every `y ≠ x`. -/
def raiseAtoms (x : Nat) : Nat → List Atom
  | 0 => []
  | k + 1 => if k = x then raiseAtoms x k else ⟨.r, x, k⟩ :: ⟨.s, k, x⟩ :: raiseAtoms x k

/-- Raising the term `x`. -/
def raise (G : St) (x : Nat) : St := ⟨G.n, raiseAtoms x G.n ++ G.A⟩

/-- Raising `x` `m` times. -/
def raiseN (G : St) (x : Nat) : Nat → St
  | 0 => G
  | m + 1 => raise (raiseN G x m) x

/-- Every term `x < k` raised `f x` times. -/
def raiseTo (G : St) (f : Nat → Nat) : Nat → St
  | 0 => G
  | k + 1 => raiseN (raiseTo G f k) k (f k)

theorem atom_rr {a b c d : Nat} : ((⟨.r, a, b⟩ : Atom) = ⟨.r, c, d⟩) ↔ (a = c ∧ b = d) := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem atom_ss {a b c d : Nat} : ((⟨.s, a, b⟩ : Atom) = ⟨.s, c, d⟩) ↔ (a = c ∧ b = d) := by
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem atom_sr {a b c d : Nat} : (⟨.s, a, b⟩ : Atom) ≠ ⟨.r, c, d⟩ := fun h => nomatch congrArg Atom.q h

theorem atom_rs {a b c d : Nat} : (⟨.r, a, b⟩ : Atom) ≠ ⟨.s, c, d⟩ := fun h => nomatch congrArg Atom.q h

theorem raiseAtoms_same {x k : Nat} (hk : k = x) : raiseAtoms x (k + 1) = raiseAtoms x k := by
  simp [raiseAtoms, hk]

theorem raiseAtoms_other {x k : Nat} (hk : ¬ k = x) :
    raiseAtoms x (k + 1) = ⟨.r, x, k⟩ :: ⟨.s, k, x⟩ :: raiseAtoms x k := by
  simp [raiseAtoms, hk]

/-- Two conditions that hold together pick the same branch.  (Stated so that no negated conjunction is
ever handed to `omega`, which would reason about it classically.) -/
theorem ite_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) (a b : Nat) :
    (if P then a else b) = (if Q then a else b) := by
  by_cases hp : P
  · rw [if_pos hp, if_pos (h.1 hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.2 hq))]

theorem count_raiseAtoms_r (x u v : Nat) :
    ∀ k, (raiseAtoms x k).count ⟨.r, u, v⟩ = if u = x ∧ v < k ∧ v ≠ x then 1 else 0
  | 0 => by
    rw [if_neg (fun (h : u = x ∧ v < 0 ∧ v ≠ x) => absurd h.2.1 (Nat.not_lt_zero v))]
    rfl
  | k + 1 => by
    have ih := count_raiseAtoms_r x u v k
    by_cases hk : k = x
    · rw [raiseAtoms_same hk, ih]
      exact ite_iff ⟨fun h => ⟨h.1, by omega, h.2.2⟩, fun h => ⟨h.1, by omega, h.2.2⟩⟩ 1 0
    · rw [raiseAtoms_other hk, count_cons', count_cons', ih, if_neg atom_sr]
      by_cases q1 : x = u
      · by_cases q2 : k = v
        · have c1 : u = x ∧ v < k + 1 ∧ v ≠ x := ⟨by omega, by omega, fun e => by omega⟩
          rw [if_pos (atom_rr.2 ⟨q1, q2⟩), if_neg (show ¬ (u = x ∧ v < k ∧ v ≠ x) from fun h => by omega),
            if_pos c1]
        · rw [if_neg (show ¬ ((⟨.r, x, k⟩ : Atom) = ⟨.r, u, v⟩) from fun h => q2 (atom_rr.1 h).2),
            Nat.add_zero, Nat.add_zero]
          exact ite_iff ⟨fun h => ⟨h.1, by omega, h.2.2⟩, fun h => ⟨h.1, by omega, h.2.2⟩⟩ 1 0
      · rw [if_neg (show ¬ ((⟨.r, x, k⟩ : Atom) = ⟨.r, u, v⟩) from fun h => q1 (atom_rr.1 h).1),
          Nat.add_zero, Nat.add_zero]
        exact ite_iff ⟨fun h => ⟨h.1, by omega, h.2.2⟩, fun h => ⟨h.1, by omega, h.2.2⟩⟩ 1 0

theorem count_raiseAtoms_s (x u v : Nat) :
    ∀ k, (raiseAtoms x k).count ⟨.s, u, v⟩ = if v = x ∧ u < k ∧ u ≠ x then 1 else 0
  | 0 => by
    rw [if_neg (fun (h : v = x ∧ u < 0 ∧ u ≠ x) => absurd h.2.1 (Nat.not_lt_zero u))]
    rfl
  | k + 1 => by
    have ih := count_raiseAtoms_s x u v k
    by_cases hk : k = x
    · rw [raiseAtoms_same hk, ih]
      exact ite_iff ⟨fun h => ⟨h.1, by omega, h.2.2⟩, fun h => ⟨h.1, by omega, h.2.2⟩⟩ 1 0
    · rw [raiseAtoms_other hk, count_cons', count_cons', ih, if_neg atom_rs]
      by_cases q1 : k = u
      · by_cases q2 : x = v
        · have c1 : v = x ∧ u < k + 1 ∧ u ≠ x := ⟨by omega, by omega, fun e => by omega⟩
          rw [if_pos (atom_ss.2 ⟨q1, q2⟩), if_neg (show ¬ (v = x ∧ u < k ∧ u ≠ x) from fun h => by omega),
            if_pos c1]
        · rw [if_neg (show ¬ ((⟨.s, k, x⟩ : Atom) = ⟨.s, u, v⟩) from fun h => q2 (atom_ss.1 h).2),
            Nat.add_zero, Nat.add_zero]
          exact ite_iff ⟨fun h => ⟨h.1, by omega, h.2.2⟩, fun h => ⟨h.1, by omega, h.2.2⟩⟩ 1 0
      · rw [if_neg (show ¬ ((⟨.s, k, x⟩ : Atom) = ⟨.s, u, v⟩) from fun h => q1 (atom_ss.1 h).1),
          Nat.add_zero, Nat.add_zero]
        exact ite_iff ⟨fun h => ⟨h.1, by omega, h.2.2⟩, fun h => ⟨h.1, by omega, h.2.2⟩⟩ 1 0

/-- **Raising `x` moves the excess by `[u = x] − [v = x]`** between terms that are there. -/
theorem excess_raise (G : St) (x u v : Nat) (hu : u < G.n) (hv : v < G.n) :
    excess (raise G x) u v =
      excess G u v + (if u = x then (1 : Int) else 0) - (if v = x then (1 : Int) else 0) := by
  unfold excess raise
  simp only [List.count_append, count_raiseAtoms_r, count_raiseAtoms_s]
  by_cases h1 : u = x
  · by_cases h2 : v = x
    · rw [if_neg (show ¬ (u = x ∧ v < G.n ∧ v ≠ x) from fun h => h.2.2 h2),
        if_neg (show ¬ (v = x ∧ u < G.n ∧ u ≠ x) from fun h => h.2.2 h1), if_pos h1, if_pos h2]
      omega
    · rw [if_pos ⟨h1, hv, h2⟩, if_neg (show ¬ (v = x ∧ u < G.n ∧ u ≠ x) from fun h => h2 h.1),
        if_pos h1, if_neg h2]
      omega
  · by_cases h2 : v = x
    · rw [if_neg (show ¬ (u = x ∧ v < G.n ∧ v ≠ x) from fun h => h1 h.1), if_pos ⟨h2, hu, h1⟩,
        if_neg h1, if_pos h2]
      omega
    · rw [if_neg (show ¬ (u = x ∧ v < G.n ∧ v ≠ x) from fun h => h1 h.1),
        if_neg (show ¬ (v = x ∧ u < G.n ∧ u ≠ x) from fun h => h2 h.1), if_neg h1, if_neg h2]
      omega

theorem raise_n (G : St) (x : Nat) : (raise G x).n = G.n := rfl

theorem raiseN_n (G : St) (x : Nat) : ∀ m, (raiseN G x m).n = G.n
  | 0 => rfl
  | m + 1 => by simp only [raiseN, raise_n, raiseN_n G x m]

theorem raiseTo_n (G : St) (f : Nat → Nat) : ∀ k, (raiseTo G f k).n = G.n
  | 0 => rfl
  | k + 1 => by simp only [raiseTo, raiseN_n, raiseTo_n G f k]

theorem excess_raiseN (G : St) (x : Nat) :
    ∀ m u v, u < G.n → v < G.n →
      excess (raiseN G x m) u v = excess G u v + (if u = x then (m : Int) else 0) - (if v = x then (m : Int) else 0)
  | 0, u, v, _, _ => by
    simp only [raiseN]
    by_cases h1 : u = x <;> by_cases h2 : v = x <;> simp [h1, h2]
  | m + 1, u, v, hu, hv => by
    have h := excess_raise (raiseN G x m) x u v (by rw [raiseN_n]; exact hu) (by rw [raiseN_n]; exact hv)
    simp only [raiseN]
    rw [h, excess_raiseN G x m u v hu hv]
    by_cases h1 : u = x
    · by_cases h2 : v = x
      · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2]
        omega
      · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]
        omega
    · by_cases h2 : v = x
      · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]
        omega
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
        omega

theorem excess_raiseTo (G : St) (f : Nat → Nat) :
    ∀ k u v, u < G.n → v < G.n →
      excess (raiseTo G f k) u v =
        excess G u v + (if u < k then (f u : Int) else 0) - (if v < k then (f v : Int) else 0)
  | 0, u, v, _, _ => by
    simp only [raiseTo]
    rw [if_neg (Nat.not_lt_zero u), if_neg (Nat.not_lt_zero v)]
    omega
  | k + 1, u, v, hu, hv => by
    simp only [raiseTo]
    rw [excess_raiseN _ _ _ u v (by rw [raiseTo_n]; exact hu) (by rw [raiseTo_n]; exact hv),
      excess_raiseTo G f k u v hu hv]
    have cu : (if u < k then (f u : Int) else 0) + (if u = k then (f k : Int) else 0) =
        (if u < k + 1 then (f u : Int) else 0) := by
      by_cases h1 : u < k
      · rw [if_pos h1, if_neg (show ¬ u = k by omega), if_pos (show u < k + 1 by omega)]
        omega
      · by_cases h2 : u = k
        · subst h2
          rw [if_neg h1, if_pos rfl, if_pos (show u < u + 1 by omega)]
          omega
        · rw [if_neg h1, if_neg h2, if_neg (show ¬ u < k + 1 by omega)]
          omega
    have cv : (if v < k then (f v : Int) else 0) + (if v = k then (f k : Int) else 0) =
        (if v < k + 1 then (f v : Int) else 0) := by
      by_cases h1 : v < k
      · rw [if_pos h1, if_neg (show ¬ v = k by omega), if_pos (show v < k + 1 by omega)]
        omega
      · by_cases h2 : v = k
        · subst h2
          rw [if_neg h1, if_pos rfl, if_pos (show v < v + 1 by omega)]
          omega
        · rw [if_neg h1, if_neg h2, if_neg (show ¬ v < k + 1 by omega)]
          omega
    rw [← cu, ← cv]
    omega

/-- Every term raised `f x` times: the excess moves by `f u − f v`. -/
theorem excess_raiseTo_all (G : St) (f : Nat → Nat) (u v : Nat) (hu : u < G.n) (hv : v < G.n) :
    excess (raiseTo G f G.n) u v = excess G u v + (f u : Int) - (f v : Int) := by
  rw [excess_raiseTo G f G.n u v hu hv, if_pos hu, if_pos hv]

theorem mem_raiseAtoms {x : Nat} :
    ∀ {k : Nat} {a : Atom}, a ∈ raiseAtoms x k → (a.x = x ∧ a.y < k) ∨ (a.x < k ∧ a.y = x)
  | 0, a, h => absurd h List.not_mem_nil
  | k + 1, a, h => by
    by_cases hk : k = x
    · rw [raiseAtoms_same hk] at h
      rcases mem_raiseAtoms h with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Or.inl ⟨e1, by omega⟩
      · exact Or.inr ⟨by omega, e2⟩
    · rw [raiseAtoms_other hk] at h
      rcases List.mem_cons.1 h with e | h'
      · subst e
        exact Or.inl ⟨rfl, by show k < k + 1; omega⟩
      · rcases List.mem_cons.1 h' with e | h''
        · subst e
          exact Or.inr ⟨by show k < k + 1; omega, rfl⟩
        · rcases mem_raiseAtoms h'' with ⟨e1, e2⟩ | ⟨e1, e2⟩
          · exact Or.inl ⟨e1, by omega⟩
          · exact Or.inr ⟨by omega, e2⟩

theorem raise_wf {G : St} {x : Nat} (hx : x < G.n) (hw : G.WF) : (raise G x).WF := by
  intro a ha
  rcases List.mem_append.1 ha with h | h
  · rcases mem_raiseAtoms h with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨by rw [e1]; exact hx, e2⟩
    · exact ⟨e1, by rw [e2]; exact hx⟩
  · exact hw a h

theorem raiseN_wf {G : St} {x : Nat} (hx : x < G.n) (hw : G.WF) : ∀ m, (raiseN G x m).WF
  | 0 => hw
  | m + 1 => raise_wf (by rw [raiseN_n]; exact hx) (raiseN_wf hx hw m)

theorem raiseTo_wf {G : St} (f : Nat → Nat) (hw : G.WF) : ∀ k, k ≤ G.n → (raiseTo G f k).WF
  | 0, _ => hw
  | k + 1, hk => raiseN_wf (by rw [raiseTo_n]; omega) (raiseTo_wf f hw k (by omega)) (f k)

theorem length_raiseAtoms (x : Nat) : ∀ k, (raiseAtoms x k).length + (if x < k then 2 else 0) = 2 * k
  | 0 => by
    rw [if_neg (Nat.not_lt_zero x)]
    rfl
  | k + 1 => by
    have ih := length_raiseAtoms x k
    by_cases hk : k = x
    · rw [raiseAtoms_same hk, if_pos (show x < k + 1 by omega)]
      rw [if_neg (show ¬ x < k by omega)] at ih
      omega
    · rw [raiseAtoms_other hk, List.length_cons, List.length_cons]
      by_cases h1 : x < k
      · rw [if_pos h1] at ih
        rw [if_pos (show x < k + 1 by omega)]
        omega
      · rw [if_neg h1] at ih
        rw [if_neg (show ¬ x < k + 1 by omega)]
        omega

/-- Raising a term adds an even number of atoms (`2(n − 1)`): the parity of the size is kept. -/
theorem raise_size (G : St) (x : Nat) (hx : x < G.n) : (raise G x).size = G.size + 2 * (G.n - 1) := by
  have h := length_raiseAtoms x G.n
  rw [if_pos hx] at h
  simp only [St.size, raise, List.length_append]
  omega

/-- A well-formed state asserts nothing about a pair with a term that is not there. -/
theorem excess_out {G : St} (hw : G.WF) {u v : Nat} (h : G.n ≤ u ∨ G.n ≤ v) : excess G u v = 0 := by
  have h1 : G.A.count ⟨.r, u, v⟩ = 0 := count_eq_zero_of_not_mem (fun m => by
    have := hw _ m
    simp only at this
    omega)
  have h2 : G.A.count ⟨.s, u, v⟩ = 0 := count_eq_zero_of_not_mem (fun m => by
    have := hw _ m
    simp only at this
    omega)
  unfold excess
  rw [h1, h2]
  rfl

/-- **Reading C-H2: raising every term once is the twenty-second's sameness** — at every ordered pair of
two different terms it adds one `xry` and one `xsy`. -/
theorem raise_all_gen {G : St} (hw : G.WF) : Gen G (raiseTo G (fun _ => 1) G.n) := by
  have hw' := raiseTo_wf (fun _ => 1) hw G.n (Nat.le_refl _)
  refine (gen_iff_same hw hw').2 (same_iff_excess.2 ⟨(raiseTo_n G _ G.n).symm, fun u v => ?_⟩)
  by_cases hu : u < G.n
  · by_cases hv : v < G.n
    · rw [excess_raiseTo_all G _ u v hu hv]
      omega
    · rw [excess_out hw (Or.inr (by omega)), excess_out hw' (Or.inr (by rw [raiseTo_n]; omega))]
  · rw [excess_out hw (Or.inl (by omega)), excess_out hw' (Or.inl (by rw [raiseTo_n]; omega))]

end Twentythird
