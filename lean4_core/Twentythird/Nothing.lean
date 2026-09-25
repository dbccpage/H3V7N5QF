import Twentythird.Same

/-!
# The result asserting nothing, and what shows a result is not it

Derived here:
* the sums kept by the sameness (`Same3.loop`, `Same3.twoWay`,
  `Same3.around`): every loop's excess, every two-way sum
  `e(x, y) + e(y, x)`, every sum around three terms
  `e(x, y) + e(y, z) + e(z, x)`;
* **the result asserting nothing** (`same3_nothing_iff`): a state is the same
  result as its terms asserting nothing exactly when all those sums are zero
  — so every other result carries a loop, two terms or three terms whose sum
  is not zero, the same sum in every state of it;
* the twenty-second's answer (`same22_nothing_iff`): there, exactly when the
  excess is zero at every pair — a *state* asserting something can be the
  result asserting nothing (`ara asa` on one term), a result whose plain
  state asserts something cannot;
* witnesses: `a b; arb bsa` (raising `a`) is the result asserting nothing on
  two terms here and not in the twenty-second (`raisedPair_nothing`,
  `raisedPair_not_nothing22`); `a b c; arb bsa` is not the result asserting
  nothing on three terms, its sum around `a b c` being one
  (`arcThree_not_nothing`); so adding a term to two states of one result can
  give two results (`addTerm_not_respected`), and the twenty-second's
  `step_of_same` fails here (`step_of_same3_fails`).
-/

namespace Twentythird

open Twentysecond

theorem Same3.loop {G H : St} (h : Same3 G H) {x : Nat} (hx : x < G.n) : excess G x x = excess H x x := by
  obtain ⟨_, g, hg⟩ := h
  have := hg x x hx hx
  omega

theorem Same3.twoWay {G H : St} (h : Same3 G H) {x y : Nat} (hx : x < G.n) (hy : y < G.n) :
    excess G x y + excess G y x = excess H x y + excess H y x := by
  obtain ⟨_, g, hg⟩ := h
  have a := hg x y hx hy
  have b := hg y x hy hx
  omega

theorem Same3.around {G H : St} (h : Same3 G H) {x y z : Nat} (hx : x < G.n) (hy : y < G.n) (hz : z < G.n) :
    excess G x y + excess G y z + excess G z x = excess H x y + excess H y z + excess H z x := by
  obtain ⟨_, g, hg⟩ := h
  have a := hg x y hx hy
  have b := hg y z hy hz
  have c := hg z x hz hx
  omega

theorem excess_nothing (n x y : Nat) : excess ⟨n, []⟩ x y = 0 := rfl

/-- **A state is the result asserting nothing on its terms exactly when every loop, every two-way sum
and every sum around three terms is zero.** -/
theorem same3_nothing_iff (G : St) :
    Same3 G ⟨G.n, []⟩ ↔
      (∀ x, x < G.n → excess G x x = 0) ∧
      (∀ x y, x < G.n → y < G.n → excess G x y + excess G y x = 0) ∧
      (∀ x y z, x < G.n → y < G.n → z < G.n → excess G x y + excess G y z + excess G z x = 0) := by
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun x y hx hy => ?_, fun x y z hx hy hz => ?_⟩
    · rw [h.loop hx]
      rfl
    · rw [h.twoWay hx hy]
      rfl
    · rw [h.around hx hy hz]
      rfl
  · rintro ⟨_, h2, h3⟩
    refine ⟨rfl, fun x => excess G x 0, fun x y hx hy => ?_⟩
    show excess G x y = excess ⟨G.n, []⟩ x y + (excess G x 0 - excess G y 0)
    rw [excess_nothing]
    have a := h3 x y 0 hx hy (by omega)
    have b := h2 0 x (by omega) hx
    omega

/-- **The twenty-second's answer**: there a state is the result asserting nothing on its terms exactly
when its excess is zero at every pair. -/
theorem same22_nothing_iff (G : St) : Same G ⟨G.n, []⟩ ↔ ∀ x y, excess G x y = 0 := by
  rw [same_iff_excess]
  constructor
  · rintro ⟨_, h⟩ x y
    rw [h x y]
    rfl
  · intro h
    exact ⟨rfl, fun x y => by rw [h x y]; rfl⟩

/-- In the twenty-second, a state asserting something is the result asserting nothing: `a; ara asa`. -/
theorem state_asserting_something_is_nothing22 : Same ⟨1, [⟨.r, 0, 0⟩, ⟨.s, 0, 0⟩]⟩ ⟨1, []⟩ :=
  (Gen.pair ⟨1, []⟩ 0 0 (by decide) (by decide)).same.symm

/-- `a b; arb bsa`: two terms, `a` raised. -/
def raisedPair : St := ⟨2, [⟨.r, 0, 1⟩, ⟨.s, 1, 0⟩]⟩

/-- `a b c; arb bsa`: the same assertions, one more term. -/
def arcThree : St := ⟨3, [⟨.r, 0, 1⟩, ⟨.s, 1, 0⟩]⟩

/-- Two numbers below two are 0 or 1. -/
theorem lt_two {x : Nat} (h : x < 2) : x = 0 ∨ x = 1 := by omega

/-- **`a b; arb bsa` is the result asserting nothing on two terms here.** -/
theorem raisedPair_nothing : Same3 raisedPair ⟨2, []⟩ := by
  refine (same3_nothing_iff raisedPair).2 ⟨fun x hx => ?_, fun x y hx hy => ?_, fun x y z hx hy hz => ?_⟩
  · rcases lt_two hx with rfl | rfl <;> decide
  · rcases lt_two hx with rfl | rfl <;> rcases lt_two hy with rfl | rfl <;> decide
  · rcases lt_two hx with rfl | rfl <;> rcases lt_two hy with rfl | rfl <;> rcases lt_two hz with rfl | rfl <;>
      decide

/-- **… and not in the twenty-second**: its excess at `(a, b)` is one. -/
theorem raisedPair_not_nothing22 : ¬ Same raisedPair ⟨2, []⟩ := by
  intro h
  have := (same22_nothing_iff raisedPair).1 h 0 1
  exact absurd this (by decide)

/-- **`a b c; arb bsa` is not the result asserting nothing on three terms**: its sum around `a b c` is one,
and that sum is kept by the sameness. -/
theorem arcThree_not_nothing : ¬ Same3 arcThree ⟨3, []⟩ := by
  intro h
  have := ((same3_nothing_iff arcThree).1 h).2.2 0 1 2 (by decide) (by decide) (by decide)
  exact absurd this (by decide)

/-- **Adding a term to two states of one result can give two results.** -/
theorem addTerm_not_respected : Same3 raisedPair ⟨2, []⟩ ∧ ¬ Same3 raisedPair.addTerm (⟨2, []⟩ : St).addTerm :=
  ⟨raisedPair_nothing, arcThree_not_nothing⟩

/-- **The twenty-second's `step_of_same` fails here**: a change of one state of a result can have an outcome
no change of another state of the same result has, up to this seed's sameness. -/
theorem step_of_same3_fails :
    ¬ ∀ G H G' : St, G.WF → Same3 G H → Step G G' → ∃ H', Step H H' ∧ Same3 G' H' := by
  intro h
  obtain ⟨H', st, s⟩ := h ⟨2, []⟩ raisedPair (⟨2, []⟩ : St).addTerm (fun _ m => absurd m List.not_mem_nil)
    raisedPair_nothing.symm (Step.addTerm _)
  have hn := s.n
  cases st with
  | addTerm => exact arcThree_not_nothing s.symm
  | add a _ _ => exact absurd hn (by show ¬ ((3 : Nat) = 2); decide)
  | remove a _ => exact absurd hn (by show ¬ ((3 : Nat) = 2); decide)
  | identify u v _ _ _ => exact absurd hn (by show ¬ ((3 : Nat) = 2 - 1); decide)

end Twentythird
