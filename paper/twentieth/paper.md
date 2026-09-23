# Fewest total changes first

The seed is the base seed with one sentence changed. The attempts are
ordered by how many changes a result stands from what is given, not by how
many additions it makes. The parent is the base derivation.

## 1. Notions

| Notion | Status |
|---|---|
| The four kinds, obstruction, answers, the ban on `xrx`, the two beginnings, the base sameness | given |
| A round is one performed change. "Fewest additions first" only lists the attempts inside a result. Both listings are run | chosen (O1) |
| Fewest additions ranks the results globally, and the run stops after expanding as many results as O1 has reached by round 2 | unchosen, kept, computed (O2) |
| The recorded additions: terms and assertions added to what is given, counting one given assertion | given, as the base reads it |
| The declared bound: 3 terms, 12 rounds | chosen |

The base exploration already spreads by one change per round. The sentence
it used names the listing inside a round. The new sentence names the round.
O2 is the reading on which "fewest additions first" would have been a
different search. It is not the base's code, and it is not dropped.

## 2. The two listings

Sorting the attempts by the pair (terms added, assertions added) is not the
base's list: an added assertion is `(0, 1)` and an added term is `(1, 0)`,
so the assertion comes first. The base lists the term first. Inside 3 terms
and 12 rounds, the two listings reach the same result at the same round,
for either beginning and either sameness (`layer_mismatch` is empty). The
results sitting at 3 terms, which are the ones whose next term would leave
the bound, are the same set (`frontier_mismatch` is empty). They are the
base exploration's results and frontier (`differs_from_base` is empty).

Names kept: 109 results, either beginning. The base records 700 frontier
exits. The last new result is round 10 from `arb` only, and round 11 from
the beginning that also asserts `bra`. Names forgotten: 20 results, either
beginning, and 112 frontier exits.

So the exact frontier inside this bound does not change with the listing.
No result enters or leaves. "Complete within the term bound" is not an
artifact of trying additions first. It holds under either listing, because
each performed change counts one and a round attempts every change on the
results of the previous round.

## 3. Additions are not the round

The result with one term and nothing asserted adds `(-1, -1)` to what is
given. The result with two terms and nothing asserted adds `(0, -1)`. The
first has fewer additions and is reached later.

| Beginning | Fewer additions | Round | Reached sooner | Round |
|---|---|---|---|---|
| names kept, `arb` only | `1:00:` | 2 | `2:01:` | 1 |
| names kept, `bra` as well | `1:00:` | 3 | `2:01:` | 2 |
| names forgotten, `arb` only | `1::` | 2 | `2::` | 1 |
| names forgotten, `bra` as well | `1::` | 3 | `2::` | 2 |

In Lean, for what is given with `arb` only: clearing that assertion is one
change (`reach_cleared`) and the added count is `-1` (`added_cleared`). The
one-term state is two changes (`givenA_to_oneTerm`, re-checked: its proof
uses removals and an identification, which this sentence does not change)
and the added count is `-2` (`added_oneTerm`). Fewer additions, more changes
(`additions_diverge`).

The recorded additions therefore do not track the order in which a result
is reached.

## 4. The other reading

O2 expands the reached result with the fewest additions, and stops after as
many expansions as O1 has results of round at most 2. That cap is not the
budget O1 itself spends: O1 reaches its round-2 results by expanding only the
results of rounds 0 and 1, which is 4 expansions from either beginning
(`o1_expansions_to_round_2`, `o1_at_that_cap_is_round_2`). Under the plan's
cap, then, O2 has spent 12 or 11 expansions against O1's 4, and most of what
"enters" is the extra budget, not the order. Names kept, plan's cap:

- From `arb` only, 12 expansions. Nothing that O1 has reached by round 2 is
  missing. 17 results have been reached that O1 has not reached by round 2.
- From `bra` as well, 11 expansions. 4 results leave, all of them three-term
  results at round 2 of O1: `3:01:0-1.0-2.1-0`, `3:10:0-1.0-2.1-0`,
  `3:01:0-1.1-0.2-0`, `3:10:0-1.1-0.2-0`. 18 results enter, among them the
  one-term state, which O1 reaches only at round 3.

With the budget matched — O2 given the 4 expansions O1 uses — the order
alone moves the frontier: from `arb` only, 5 of O1's round-2 results are not
yet reached and 4 others are (`matched_leave`, `matched_enter`); from `bra` as
well, 5 and 3, the one-term state among the latter.

Under a cap on how many results are expanded, before the closure has
finished, the frontier moves. Once the term bound is exhausted, O1 and the
base agree, so that cap is the only place the order changes the frontier.
The set of all results, with no cap, is independent of the order, as the
task says. O2 is kept because the cap is a real alternative and the two
frontiers differ.

## 5. What does not follow

- It does not follow that the recorded additions equal the round. The table
  in §3 is the witness, and `additions_diverge`.
- It does not follow that the listing inside a round changes the term-bound
  frontier. Both listings match the base.
- It does not follow that every reading of the old sentence has the same
  frontier before the closure finishes. O2 moves it.
- It does not follow that the process terminates. Adding a term is never
  obstructed. The changed sentence is about order, not about which changes
  exist.

## 6. What survives of the base

| Base claim | Used the listing? | Here |
|---|---|---|
| the changes, obstruction, answers, sameness | no | kept |
| the round is the number of changes, and inside the bound it equals the fewest changes (D12) | the listing is not the round | survives under O1; the census matches the base closure |
| the recorded additions are the round | the sentence could be read that way | refuted, §3 |
| the frontier exported at 3 terms | the listing | the same frontier under either listing |
| there is no last result | no | kept |

## 7. Open

Nothing is left open here. O2 run until nothing
is pending reaches the same set as O1 run until nothing is pending, for
either beginning and either sameness (`o2_closure_differs` is empty). A
sequence that leaves the term bound and returns is not shorter than the
recorded round: the round equals the base's round (`differs_from_base` is
empty), and the base proves that round is the fewest changes with no bound
on terms (base D12, D8; Lean `fewest_changes_lower_A`, `_B` bound every
sequence). The changed sentence is about order and does not touch the
changes those proofs count.

## 8. Nearest known results, and how the findings differ

The nearest result in this repository is the base derivation. It already
counts one change per round and lists additions first only inside a round.
Renaming that listing does not move the frontier inside the term bound.
What the new sentence separates is the recorded additions from the round:
a result can add less and stand further from what is given. The reading
that ranks whole results by additions does move the frontier, and only
before the closure inside the bound has finished.
