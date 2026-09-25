# Reading the twenty-second seed against the ninth

Working notes for the twenty-second derivation (Phase 1). Nothing here is
cited as evidence; what survives is in `paper/twentysecond/paper.md` with its
source status. Every notion below is exactly one of **given**, **chosen**,
**derived**, **computed**, **refuted**, **open**.

Inputs: `prompt/twentysecond/prompt.md`, `prompt/twentysecond/seed_prompt.md`.
The parent is the ninth (`prompt/ninth/seed_prompt.md`, `paper/ninth/`); its
own parents (the seventh, the eighth, through them the first) may be cited
through it. No other derivation is read.

## The diff

`prompt/twentysecond/seed_prompt.md` against `prompt/ninth/seed_prompt.md`:
one sentence changes, nothing else.

    < Two results that differ only in how their terms are written are the same result.
    > Two results that differ only in how their terms are written, or only by an `xry` and an `xsy` asserted together, are the same result.

Against the seventh seed two sentences differ: this one and the ninth's
assertion-writing sentence (`xry` or `xsy`, two relations). So the state,
the empty beginning, the four kinds of change, the protocol and the bound are
the ninth's, word for word. Only *when two states are one result* changes.

## Sentence by sentence

(1) "Terms are written with letters." Given (G1). No cap on the supply of
letters (chosen, C3, as 9:C3).

(2) "An assertion is written `xry` or `xsy`, … its multiplicity. Adding …
raises …; removing … lowers …" Given (G2⁗, the ninth's). A state is terms and
two multiplicity functions on ordered pairs, `xrx`, `xsx` included (9:C1′,
chosen there, no change: the sentence is the ninth's).

(3) "Nothing is given: to begin with there are no terms and nothing is
asserted." Given (G3″). One beginning, the empty state.

(4) "A change is exactly one of: identifying two terms; removing an
assertion; adding a term; adding an assertion. Nothing else is a change.
Identifying two terms replaces both by one term in every assertion." Given
(G6, G7). The four kinds act on *states*, and the ninth's readings of them
stand (9:C5⁗: adding what is asserted is a change; removing what is not
asserted, identifying a term with itself, are not; an identification adds up
the multiplicities of the pairs it merges, per relation). What is new is a
question the ninth never had to ask: a *result* is now a class of states that
contains states asserting different things, so what is "a change of a
result"? See C-X below.

(5) "Attempt every change, fewest additions first. For every result, record
how many terms and assertions it adds to what is given." Given (G11). Two
questions become live: which state's changes are attempted for a result
(C-X), and which counts are recorded for a result whose states assert
different numbers of assertions (C-R).

(6) **The changed sentence.** "Two results that differ only in how their
terms are written, or only by an `xry` and an `xsy` asserted together, are
the same result." Given (G12′). Readings:

- **C-J1 (chosen).** Two states differ only by an `xry` and an `xsy`
  asserted together when one of them is the other with one more `xry` and
  one more `xsy`, the same `x` and the same `y` (the letters are repeated in
  the sentence; `x = y` is allowed, since the seed writes every assertion
  `xry` and the ninth has `xrx` among them). "Are the same result" is said of
  a relation that must be an equivalence: the sameness is the one generated
  by rewriting and by these one-pair steps. Derived below: two states are the
  same result exactly when they have equally many terms and, under one
  rewriting, the same *excess* `e(x, y) = M_r(x, y) − M_s(x, y)` at every
  ordered pair. Each result then has one *plain state* up to writing: at
  every pair at most one relation asserts, `M_r = max(e, 0)`,
  `M_s = max(−e, 0)`.
- **C-J2 (unchosen, kept).** The letters as placeholders: an `xry` and any
  `usv`. The equivalence generated then keeps only the terms and the
  difference of the two totals `Σ M_r − Σ M_s`: with one term or more every
  such difference occurs, with none only 0. The results with `n ≥ 1` terms
  are indexed by that one number; the fewest changes is `n + |Σ M_r − Σ M_s|`
  (an identification keeps both totals; every change moves the total
  difference by at most one). Computed at a small bound.
- **C-J3 (unchosen, kept).** Only two different terms (`x ≠ y`): `xrx` and
  `xsx` asserted together are not taken out. The excess is kept off the
  diagonal and both multiplicities on it. Computed at a small bound.
- Set aside, with the words that refuse them: "one result has `xry` where the
  other has `xsy`" — refused by "asserted together" (both in one result);
  "the same only for one extra pair, not for two" — refused by "are the same
  result", which cannot hold of the first and the second, and of the second
  and the third, and fail of the first and the third.

(7) "Attempt 100 changes along each alternative, … declare a finite bound,
export the exact frontier, and prove what is complete within it." Given
(G13). As 9:C8′: bound on terms and rounds together.

(8) "Any outcome is valid." Given (G14).

## Derivations, sketched (to be proved in Lean or the paper)

**Sameness.** Let `G`, `H` have the same writing of terms. The steps "add one
`xry` and one `xsy`" and their reverses keep every excess. Conversely, if
every excess agrees, both reduce to the same plain state by taking out
`min(M_r, M_s)` pairs at every pair. With rewriting: rewriting carries
excesses along (`e_H(πx, πy) = e_G(x, y)`), and commutes with the one-pair
steps, so the generated equivalence is "some rewriting makes all excesses
agree".

**Changes of a result (C-X).** Adding `xqy` and identifying two terms give
outcomes whose results do not depend on the state taken (adding the pair
before or after commutes with both). Removing `xry` from a state `G` that is
not plain but asserts `xry`: `G − xry` is the same result as
`P + xsy` when `e(x, y) ≤ 0` (`P` the plain state), and as `P − xry` when
`e(x, y) > 0`. On *every* state, `G − xry` and `G + xsy` are the same result
(they differ by one pair asserted together). So the results one change away
from a result are those of its plain state's changes. Chosen: C-X (a change
of a result is a change of any of its states); unchosen C-X′ (only the plain
state's): the same results one change away, hence the same rounds.

**What is recorded (C-R).** The plain state's terms and assertions:
`n` and `Σ |e|` (split: `Σ max(e, 0)` in `r`, `Σ max(−e, 0)` in `s`).

**Cost.** Let `Φ(G) = n + Σ |e|`, the size of the plain state. Φ is kept by
the sameness. Per change: a term +1; an assertion ±1; a removal ±1; an
identification −1 on the terms and `−2c` on `Σ |e|` (merged excesses add
up, `|Σ e_i| ≤ Σ |e_i|` with the same parity) — so Φ rises by at most one.
From the empty state (Φ = 0) a result needs at least Φ changes, and Φ
additions reach its plain state. Fewest changes = Φ. A shortest sequence
raises the ninth's size by one at every change (size moves by exactly one
and size ≥ Φ), so it is additions only, every state along it is plain, and
it ends at the plain state.

**Undoing.** Ninth: an addition raises the size by one and rewriting keeps
the size; a non-empty run of additions never returns to its start's result.
Here: `G`, `G + xry`, `G + xry + xsy` — the third is the first's result.

**Which changes lower the record.** As in the plan (item 3). The amount an
identification takes: at each merged pair of the outcome, the sum of the
positive parts and the sum of the negative parts of the excesses merged there
lose `min` of the two each; unbounded (`c` copies of `urv` and `c` of `vsu`,
merged: `2c` assertions go).

**Count.** A rewriting fixes an excess function exactly when it is constant
on each cycle of ordered pairs; a cycle of length `L` with constant value `e`
weighs `L·|e|`. So each cycle contributes `1 + 2(x^L + x^{2L} + …) =
(1 + x^L)/(1 − x^L)`; average over rewritings of `n` terms. With two terms:
the four excesses `(e00, e01, e10, e11)` with `Σ |e| = t`, up to the swap
`(e00, e01, e10, e11) → (e11, e10, e01, e00)`: points of `Σ|e_i| = t` in four
whole-number coordinates number `8t(t² + 2)/3` for `t ≥ 1` (by the number of
non-zero coordinates: `Σ_k C(4, k) 2^k C(t − 1, k − 1)`); the swap fixes
those with `e00 = e11`, `e01 = e10`, `2(|a| + |b|) = t`: `4(t/2) = 2t` of them
for even `t ≥ 2`. Halved: `c₂(t) = 4t(t² + 2)/3 + [t even]·t` for `t ≥ 1`,
`c₂(0) = 1`: 1, 4, 18, 44, 92, 170, … With one term: `e(0, 0)` any whole
number, round `1 + |e|`: one result in round 1, two in every round after.

**Mapping in.** The ninth's states: `a` and `a; ara asa` are two ninth
results and one result here. The seventh's: `M ↦` (`M` in `r`, nothing in
`s`) — its plain state is itself, so two seventh states give the same result
here exactly when they are the same seventh result. The eighth's and the
first's states carry the names `a`, `b`; a result here has none. Witness for
the eighth: two terms, `0r1` once, with `a`, `b` on terms 0 and 1, and the
same terms and assertion with both names on term 0 — different eighth states
(its sameness keeps whether the names are one term), one result here. The
same pair of states, read with a relation that asserts each pair at most
once, is the witness for the first.

## Core Lean without the outside library

`lean4_core/` has no `require`. Probed (`#print axioms`, pinned toolchain):
`List.Perm` constructors, `trans`, `symm`, `swap`, `cons`, `append`,
`perm_middle` use no axioms; `List.count_cons`, `count_append`,
`Perm.length_eq`, `Perm.count_eq`, `count_pos_iff`, `omega` stay within
`propext`, `Quot.sound`; but `List.perm_iff_count`, `List.count_erase`,
`List.length_erase_of_mem`, `List.perm_cons_erase`, `List.Perm.erase` depend
on `Classical.choice`, which the report must refuse. So the library defines
its own deletion of one atom and re-proves those facts for it.
