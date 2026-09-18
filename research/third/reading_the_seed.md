# Reading the third seed against the second

Working notes for the third derivation. Nothing here is cited as evidence;
what survived is in `paper/third/paper.md` with its source status.

## The diff

`prompt/third/seed_prompt.md` against `prompt/second/seed_prompt.md`: one
sentence differs, and a sentence disappears with it.

    - A change is exactly one of: identifying two terms; adding a term; adding an assertion. Nothing else is a change. Identifying two terms replaces both by one term in every assertion.
    + A change is exactly one of: adding a term; adding an assertion. Nothing else is a change.

Every other sentence is identical, character for character (checked with
`diff`). Against the first seed the third has struck two kinds of change:
removing an assertion (struck by the second seed) and identifying two terms
(struck now). So every reading of the earlier seeds that does not mention
removal or identification carries over word for word, and every proof of the
earlier derivations that uses neither still stands. "Uses neither" is checked
per claim, not assumed: several second-derivation proofs go through the
carrying map, which was built from identifications; under the third seed that
map is the identity, which is a special case, so those proofs restrict rather
than break.

## Sentence by sentence, only where the meaning moves

### "A change is exactly one of: adding a term; adding an assertion. Nothing else is a change."

- Both kinds add. Nothing is ever taken away: after any change every term is
  still a term, every asserted `xry` is still asserted, and the names are
  where they were. So along any sequence of changes the start is *contained*
  in the end. This is the single fact from which most of the third derivation
  follows. It is the second derivation's carrying map with the identity as the
  map — a special case, so everything the second derived from the carrying
  map (what is given survives, obstructions persist, fewest classes never
  decrease) restricts to the third seed through the embedding of its changes
  into the second's.
- Both kinds add exactly one thing, so the size (terms plus assertions) rises
  by exactly one per change, where the second seed had "at most one"
  (identifications lowered it). Consequences to prove:
  * every sequence of changes from `s` to `t` has the same length, the size
    difference; in particular every sequence from what is given to a result
    has the length of its round, and a result is met in one round only;
  * the fewest changes is the size difference (as in the second derivation,
    whose upper-bound path was additions only — a sequence of this seed);
  * the results are the legal states containing what is given — the same set
    as under the second seed, in the same rounds; the second derivation
    computed exactly this ("additions alone reach the same results in the
    same rounds"), and under the third seed that computation *is* the
    exploration;
  * the numbers of terms and of assertions never decrease (the second's N8
    flips to derived);
  * reachability between results is containment (up to rewriting under
    FREE); it is one-way: two results reachable from each other are the same
    result (the second's N10 "antisymmetric" flips to derived, its "symmetric"
    is refuted); a result once left is never returned to (N9 flips); the only
    result that reaches what is given is what is given.
- What still does *not* follow, and needs witnesses: `bra`; exactly two
  terms; anything on which two legal states containing what is given differ;
  that any two results are comparable (neither of "add a term" and "add
  `bra`" contains the other); that a result is reached by one sequence only
  (what is given: one, the empty sequence; `a b c; arb bra`: two).

### "A change that makes some `xrx` asserted is obstructed."

- Adding a term never does; adding `xry` with `x ≠ y` never does; adding
  `xrx` always does. So the obstructed changes are exactly the additions of
  some `xrx`, and the obstruction (reading C7: the assertions that would
  become `xrx`) is the assertion the change itself would add. The second
  seed's obstructed identifications are gone.

### "An obstructed change must be answered: remove the obstruction, or build structure by further changes; declare which; ..."

- Refuse: as before. Build: as before (add a term `t`, add `xrt` or `trx`;
  the added term stands for `x`: read with `t` as `x` the build is the
  would-be outcome). Note that "identifying the added term back", the first
  derivation's way of saying what a build stands for, is a relation between
  states under this seed, not a change; the reading is kept as a relation.
- Remove the obstruction: the obstruction is `xrx` itself. Readings:
  1. (kept) un-assert `xrx` after asserting it, then the change is performed
     — impossible, no change un-asserts (recorded as such on every obstructed
     attempt);
  2. (kept, listed) do not assert it — that is to withdraw the change, which
     coincides with refusal and adds no result;
  3. the second seed's reading "move the obstruction by identifying" has no
     object: there is no identification.
  Under every reading the results are the legal states containing what is
  given; the answers change nothing about the results (second derivation's
  D10, re-checked: builds are additions).

### "Attempt every change, fewest additions first."

- Both kinds add one. "Fewest additions first" does not order the two kinds;
  the seed's own order of kinds (a term, then an assertion) is taken. Within a
  result nothing else depends on this order: every sequence to a result has
  the same length, so the round of a result does not depend on the order of
  attempts at all (a derived fact, where the earlier derivations had it as
  the convention C6).

### "For every result, record how many terms and assertions it adds to what is given."

- Never negative (contained), as under the second seed; more: along a
  sequence both numbers are non-decreasing.

### "Two results that differ only in how their terms are written are the same result."

- Both readings (FREE, ANCHORED) kept as before. Under FREE, reachability is
  containment up to a one-to-one rewriting of the smaller state's terms into
  the larger's (an embedding); it is still one-way, by sizes.

### "Attempt 100 changes along each alternative ..."

- Every round has a new result (what is given plus `k` new terms), so a bound
  is declared as before. Rounds are the layers by size: round `k` is exactly
  the set of results of size `size(given) + k`, and the counts without bound
  are the second derivation's (same set, same formula).

## Which earlier results are used, and how they are re-checked

| Earlier | Used as | Re-check |
|---|---|---|
| 1:D1, 1:D2 (`given_distinct`, `two_states_*`) | unchanged | statements about relations and states, no change mentioned |
| 1:D3 (`addAssertion_legal_iff`, `addTerm_legal`) | unchanged; `identify_legal_iff` has no object | one state operation each |
| 1:D4 (`adding_xrx_always_obstructed`) | unchanged | as above |
| 1:D6 / 2:D6 (`Step.legal` … `Reach3.nonempty`) | inherited through `Step2 → Step3 → Step` | Lean embedding |
| 2:D5 (carrying map) | the identity carries | Lean: `Contains.carries`, and `Reach2.toReach3.carries` |
| 2:D6, 2:D7 (what is given survives; obstructions persist) | restricted | Lean embedding; also proved directly from containment |
| 2:D8 (size difference) | strengthened: exact per change; every sequence has the same length | Lean re-proved (`Step2.size_eq`); the upper-bound path is re-proved with `Step2` |
| 2:D9 (results = legal states containing what is given) | unchanged as a set | Lean re-proved; computed: same results and rounds as the second's additions-only run |
| 2:D10 (answers reach nothing new) | unchanged minus identifications | builds are `Step2` sequences (re-proved) |
| 2:D11 (rename) | needed again for every-writing statements | Lean re-proved for `Step2` (two cases); the `rename` lemmas about states are cited unchanged |
| 2:D12 (reachability = carrying map) | replaced: reachability = containment, both directions in Lean | the second's O3 has no counterpart here |
| 2:D13 (fewest classes) | inherited | Lean embedding |
| 2:D14 (completeness) | same argument | the path is additions only |
| 2:K1, 2:K3 (counts) | reused | `second.orbits` unchanged; explorations agree |
| 2:N8, 2:N9, 2:N10 | flip: counts monotone, no return, one-way | Lean |

## Noticed on the way

- The third exploration is the second's with identifications left out, which
  the second derivation already ran (`additions_only=True`) as a *check*; here
  it is the whole exploration. The evidence compares the two, result by
  result, round by round, attempt count by attempt count.
- Sequences reaching a result never have more terms than the result, so the
  number of sequences (and their common length) is exact within any bound
  that holds the result.
- The number of sequences to a result is a count of orderings: each added
  assertion after both its terms. Not pursued beyond the count per result.
