# What follows when a different writing is a different result

Eighteenth derivation. Input: `prompt/eighteenth/seed_prompt.md`. Task:
`prompt/eighteenth/prompt.md`. The parent is the base
(`prompt/seed_prompt.md`, `paper/paper.md`, `code/xry/`, `lean4/H3V7N5QF/`).
Claim IDs refer to `paper/eighteenth/claim_ledger.md`. An ID written `1:D8`
refers to the base ledger. Computed files are in `evidence/eighteenth/`,
written by `python code/run_eighteenth.py`. The axiom report is
`evidence/eighteenth/lean_axioms.txt`.

Every notion below carries one source status: **given**, **chosen**,
**derived**, **computed**, **refuted**, or **open**.

The sentence that changed is the base's sameness. Where a base result is
used, the re-check says whether it used that sentence.

## 0. Findings in brief

1. The seed is the base seed with one sentence reworded. Two results that
   differ only in how their terms are written are different results.
2. The chosen sameness is equality of the written state: the same terms, the
   same assertions, and, when the reading keeps them, the same terms carrying
   `a` and `b`. The base's least writing is not applied.
3. Inside a bound of 3 terms, the changes reach 137 written results when the
   names are kept, and 69 when they are not. The base, which still takes the
   least writing, reaches 109 and 20 of those classes. 28 named classes and
   15 nameless classes are reached in two writings.
4. The round of a named result is still the base's count of changes for that
   writing. That count is a lower bound on every sequence, inside the bound
   or not, so no detour through a fourth term reaches a named writing sooner.
   Without the names, that count is the least over writings, and the
   writing the changes reach is longer on 32 results from `arb` and on 29
   from the beginning that also asserts `bra`, by at most 2 and 4 changes.
   It is never shorter (`rounds_below_the_base_cost` is empty on all four
   runs).
5. Swapping the two terms of what is given is a different state. The base's
   reading that forgets the names calls the two nameless forms one result.
   Lean proves the written states differ. The base does not formalise that
   reading (`lean4/H3V7N5QF/Paths.lean`).
6. The changes do not terminate: adding a term is never obstructed. Inside
   the bound they do: the last new result is round 10 without `bra` and with
   the names, round 11 with `bra` and the names, and round 7 without the
   names. The frontier is the attempts that would add a fourth term.
7. An unbounded supply of letters, with every injection a result whether or
   not a change produces it, is not eliminated. On that reading the count is
   infinite for every state that has a term. The changes themselves assign
   the next index, so that reading is not the one the exploration runs.

## 1. Readings

**Given.** The base seed, except the sameness sentence. What is given is
`arb`, and `bra` is not given either way. No `xrx`. The four changes. An
obstructed change is answered or refused.

**Chosen.** A result is a legal state as written. Both of the base's
beginnings are kept: `bra` asserted or not, and the names kept or forgotten.
The bound is 3 terms and 12 rounds. Twelve is past the last round with a new
result, and short of the seed's 100. The unchosen reading that every
rewriting is a result, including one no change reaches, is computed and not
used as the exploration. Nothing in the seed says the supply of letters is
infinite, and nothing says a writing no change produces has been reached.

## 2. What is the same result

Two written states are the same result exactly when they are equal. A
permutation of the terms produces another writing. For a state of `n` terms,
the permutations are `n!`, and they split into the distinct writings times
the permutations that leave the state as written. What is given has two
writings and one permutation that fixes it: `2! = 2 · 1`.

The base's least writing, with the names forgotten, identifies what is given
with the state obtained by swapping its two terms. As written, the swap
moves the names, and that state is neither what is given nor the beginning
that asserts `bra` with the names left on `0` and `1`
(`given_ne_bra`, `swapped_ne_given`, `swapped_ne_bra`).

## 3. What the changes reach

The changes are the base's, in the base's order. The outcome is kept as the
change writes it.

With the names kept, either beginning reaches the same 137 results. The base
reaches 109 classes, and 28 of those classes are reached here in two
writings. The round of each result equals the base's count of changes for
that writing (`xry.cost.cost`, re-checked: the count does not use the
sameness sentence; it reads the size and the destroyed givens, which are the
same for every writing). The base proves that count a lower bound on the
length of every sequence of changes from what is given (`1:D8`, Lean
`fewest_changes_lower_A`, `fewest_changes_lower_B`: the potential rises by at
most one per change, whatever the number of terms). So the recorded round is
the fewest changes to that writing with no bound on terms: a sequence that
adds a fourth term and returns is not shorter. No answer lands on a writing
the unobstructed changes have not reached. 128 attempts would add a fourth
term.

With the names forgotten, either beginning reaches the same 69 results. The
base reaches 20 classes, and 15 of those are reached here in two or more
writings. The base's count without the names is the least count over
writings. The round of the writing the changes reach is that least count, or
greater: greater on 32 results from `arb`, and on 29 from the beginning that
also asserts `bra` (`rounds_above_the_base_cost`). The greatest excesses are
2 and 4 (`greatest_excess_over_the_base_cost`), and no round is below the
count (`rounds_below_the_base_cost` is empty). No answer lands on an
unreached writing. 64 attempts would add a fourth term.

Whether `bra` is asserted at the start does not change the set. It changes
the rounds, because the two starts are different writings and a removal or an
addition may be needed before they meet.

## 4. The reading that was not run

If every injection of the terms into a supply of letters is a result, the
changes no longer determine the writing. A state of `n` terms that is fixed
by `a` permutations then has, in a supply of `L` letters, `L (L − 1) ⋯ (L − n + 1) / a`
writings. For the three-term sample fixed by one permutation and `L = 25`,
that is 13 800. For `n ≥ 1` the count grows with every further letter: going
from `L` to `L + 1` letters multiplies it by `(L + 1) / (L + 1 − n) > 1`
(derived; computed for the sample over twelve further letters,
`sample_letter_supply_grows`). The seed does not give a finite supply, and it
does not say that an unreached writing has been obtained. On that reading no
finite supply bounds the count, so it is infinite for every result that has a
term, and the exploration does not run it. It is not refuted.

## 5. What survives

| Base claim | Used the sameness sentence? | Here |
|---|---|---|
| the four changes, obstruction, answers | no | the same changes; an answer's writing is reached |
| no `xrx` in a result | no | kept; an unobstructed change still does not assert it |
| adding a term never obstructed, so no last result | no | kept; the frontier is those attempts |
| fewest changes for a fixed writing (`1:D8`, names kept) | no | the round equals that count on all 137 named results, and is the fewest changes with no bound on terms |
| fewest changes with the names forgotten | yes, the least over writings | a lower bound on the round of the writing reached; strict on 32 and 29 results, by at most 2 and 4 |
| one result for a whole family of writings | yes | refuted; 28 named classes and 15 nameless classes split |

## 6. Open

- **O1.** A closed form for the 137 and the 69. The rounds are computed.
- **O2.** Without the names only: whether a sequence that adds a fourth term
  and returns can reach a written result sooner than the recorded round. With
  the names kept this is closed (section 3): the round equals the base count,
  which bounds every sequence. Without the names the recorded round can exceed
  the base count (by up to 2 and 4), so the base count does not close it.

## 7. Nearest known results, and how the findings differ

The base counted one result for every way of writing its terms. This seed
counts each writing. The difference is the sameness sentence alone. The
changes still assign the next term the next index, so inside a bound on the
number of terms the reached results are finite. They are not finite because
a family of writings was forgotten.
