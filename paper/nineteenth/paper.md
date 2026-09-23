# Identification in one chosen assertion

The seed is the base seed with one sentence changed. Identifying two terms
replaces both by one term in one chosen assertion, and nowhere else. The
parent is the base derivation. Nothing later is an input.

## 1. Notions

| Notion | Status |
|---|---|
| Terms, assertions, the ban on `xrx`, the two beginnings, the base sameness | given |
| The other three kinds of change, obstruction, refusal | given |
| A partial identification: two terms, one asserted pair that mentions at least one of them, and which of the two terms is written in that pair. The terms stay. A rewrite that does not change the pair is not a change | chosen (P1) |
| Only a pair in which the two terms already both occur | unchosen, kept, computed (P2) |
| Dropping a term while rewriting only one assertion | set aside: an assertion would then name a term that is not there |
| The declared bound: 3 terms, 12 rounds | chosen |

P2 is not dropped. Every such rewrite writes a loop (`cooccur_is_loop`), so
every such change is obstructed and refused. The results are the same as
under P1. What differs is the attempts: P2 performs no partial
identification.

## 2. What one chosen assertion does

Rewriting one pair does not change the set of terms (`performPartial_terms`).
On a state with terms `0`, `1`, `2` and the assertion `0 r 2`, writing `1`
for `0` in that pair yields `1 r 2`, still three terms, and still legal
(`side_partial_eq`, `side_partial_legal`). That outcome is not what the
base's identification of `0` with `1` does (`side_not_identify`).

A pair that already names both terms becomes a loop, whatever survivor is
written. The change is obstructed and refused. On a legal state this is the
only way a partial identification is obstructed: the census records no
disagreement (`obstruction_not_between`).

The base identification of `a` with `b` in what is given erases a term
(`identify_smaller`). Adding a term does not lower the number of terms, and
neither does a removal, an added assertion, or a partial identification
(`PStep.card_ge`). No sequence of them reaches the one-term state
(`PReach.card_ge`, `oneTerm_unreachable`).

Refusing the loop and instead removing the chosen assertion is an ordinary
removal. Inside the bound, that result is already reached
(`removal_answer_outside` is empty).

## 3. What is reached

Both beginnings, names kept: 68 results. The base reaches 109. The 41
missing results are exactly the base results in which `a` and `b` are one
term, and one of those has one term. Nothing is reached that the base does
not reach. The least number of terms is 2. P1 performs 384 partial
identifications and refuses 392. P2 performs none and refuses 392. The two
readings reach the same 68 results. 64 attempts would add a fourth term.
The new results per round, from what is given with `arb` only, are
1, 3, 9, 20, 22, 11, 2, and then none. From the beginning that also asserts
`bra`: 1, 3, 11, 29, 20, 4, and then none. The two beginnings reach the same
set.

Names forgotten: 19 results. The base reaches 20. The missing result is the
one-term class. P1 performs 96 partial identifications and refuses 102. P2
performs none. 16 attempts would add a fourth term. Rounds from `arb` only:
1, 3, 5, 4, 4, 1, 1, and then none. From `bra` as well: 1, 2, 5, 9, 1, 1,
and then none. The two beginnings reach the same set.

The one-sided rewrites are real changes, and they do not add a result the
other changes have not reached. Global identification is not recovered by
iterating them. There is no cost for that recovery, because the one-term
results are not results of this seed.

Adding a term is never obstructed, as in the base. The process does not
terminate. Inside the bound it finishes: the last round above is empty, and
no change was invented to fill 100 rounds.

## 4. What does not follow

- A partial identification does not erase a term. Witness: the three-term
  state above, and `performPartial_terms`.
- The two readings do not have different results. They do have different
  attempts: 384 performed against none, names kept.
- The base's one-term result does not survive. Witness: `oneTerm_unreachable`,
  and the census (41 missing with the names kept, 1 with the names forgotten).
- It does not follow that every base result with two or more terms survives.
  With the names kept, 40 of the missing results have two or more terms.
  They are the ones in which `a` and `b` are already one term. With the
  names forgotten, every class with two or more terms survives.
- Removing the loop instead of refusing it does not reach a new result
  inside the bound.

## 5. What survives of the base

| Base claim | Used the global identification? | Here |
|---|---|---|
| sameness, the ban on `xrx`, the other three kinds | no | kept |
| an identification erases a term and can merge the names | yes | not a change of this seed; `oneTerm_unreachable` |
| fewest changes, for a result the base reaches by an identification | yes | that result is not reached, so the count is not a count of this seed |
| answers reach nothing the unobstructed changes do not (D10) | the answers, not this sentence | a removal of the chosen pair is already a removal; the census finds no new result |
| adding a term is never obstructed, so there is no last result | no | kept; the frontier is those attempts |
| the closure inside 3 terms, names kept, has 109 results | yes, it counts the merged names | 68 of them remain |

## 6. Open

- **O1.** A closed form for the 68 and the 19. The rounds are computed.

The question whether a sequence that adds a fourth term can return inside
the bound is closed, not open: no change of this seed lowers the number of
terms (`PStep.card_ge`, `PReach.card_ge`; `PStep` admits more steps than the
seed does — a rewrite of any pair, an assertion anywhere — so the bound holds
for every sequence of the seed's changes). An attempt that leaves the bound
never returns, so the closure inside 3 terms is every result with at most 3
terms, and the frontier is exact.

## 7. Nearest known results, and how the findings differ

The nearest result in this repository is the base derivation, whose
identification rewrites every assertion and erases one term. This seed
rewrites one assertion and leaves both terms. The one-term results of the
base are not results here, and neither are the results in which the two
names have become one term. The other base results remain, at the same
bound, and the process still does not terminate.
