# An obstructed change is refused

The seed is the base seed with one sentence changed. An obstructed change
is refused. The ban on `xrx` stays. There is no removal of an obstruction
and no building of structure as an answer. The parent is the base
derivation.

## 1. Notions

| Notion | Status |
|---|---|
| The four kinds, the ban on `xrx`, which changes are obstructed, the two beginnings, the base sameness | given |
| A refused change is recorded and changes nothing | given |
| The only response to an obstruction is refusal. The base's other answers are computed and not performed | chosen (R1) |
| The declared bound: 3 terms, 12 rounds | chosen |

The base already reaches results along unobstructed changes and checks
answers afterwards. R1 is that exploration, so to compare the two is not to
compare the base with itself: a second exploration (`explore_refusing`)
performs every change, whatever the base's obstruction test says, and refuses
the change when its outcome asserts some `xrx`. That is the seed's sentence
applied directly. Its closure is compared with the base's, result by result
and round by round, and the answers are compared with the closure, one by
one.

## 2. What refusal does

Identifying `a` with `b` in what is given writes `ara`. That state is not
legal (`identify_given_illegal`), so there is no performed step to it
(`no_step_to_illegal`, `identify_given_refused`). Refusal leaves the state
as it was.

The alternative does not stop there. Adding a term is a performed step
(`refusal_continues_by_a_term`). Removing `arb` is a performed step
(`refusal_continues_by_removal`). Both are unobstructed in the base, and
the changed sentence does not make them obstructed.

## 3. What is reached

Inside 3 terms and 12 rounds, refusal reaches the base closure and nothing
else.

| Beginning | Results | Last new round | Frontier exits | New results bought |
|---|---|---|---|---|
| names kept, `arb` only | 109 | 10 | 700 | none |
| names kept, `bra` as well | 109 | 11 | 700 | none |
| names forgotten, `arb` only | 20 | 6 | 112 | none |
| names forgotten, `bra` as well | 20 | 5 | 112 | none |

The refusing exploration reaches the same results at the same rounds on
each of the four runs (`outside_the_base` is empty), and the changes it
refuses are exactly as many as the base's obstructed attempts: 547 with the
names kept, 92 without (`refusals`, `obstructed_attempts_in_the_base`).
`answer_buys_a_result` and `stopped_at_the_start` are empty as well. The start has unobstructed changes, so it
is not a place where every alternative stops. Every answer whose result
stays inside the bound — a removal of the assertions between two terms and
then the identification, the state itself as a build, or a build that adds
a term and one assertion when that term still fits — is a result the
unobstructed changes have already reached.

The reachable set is not smaller. No base result inside the bound was
reached only through an answered obstruction. The answers were not buying
results. They were buying records of sequences that the unobstructed
changes already contain.

Structure is built. Adding a term, removing an assertion, and adding an
assertion that is not a loop are not obstructed, and the closure above is
made of them. What is not built is the base's answer to an obstructed
change, and that answer was not a source of results.

Adding a term is never obstructed (`addTerm_legal`, re-checked: its proof
uses only that the old state was legal). The process does not terminate.
Inside the bound it finishes by round 11. No change was invented to fill
100 rounds.

## 4. What does not follow

- It does not follow that the reachable set shrinks. The four closures are
  the base's.
- It does not follow that an alternative stops at its first obstruction.
  The identification of `a` with `b` is refused, and adding a term is not
  (`refusal_continues_by_a_term`).
- It does not follow that refusing is the same as having no unobstructed
  change. The start has several.
- It does not follow that the base's builds are unreachable states. Inside
  the bound their results are already results. A build that adds a term
  past the bound is a frontier exit, as in the base, not a new result
  inside the bound.

## 5. What survives of the base

| Base claim | Used the answer menu? | Here |
|---|---|---|
| which changes are obstructed, and that a refusal changes nothing | the menu is the sentence after that | kept |
| the closure is the unobstructed changes (D10, D12) | D10 is about the answers | the census agrees, inside the bound; the answers are not performed |
| some answer reaches a result the unobstructed changes do not (R6) | yes | still refuted, inside the bound |
| adding `xrx` can be made performable by an answer (R2) | yes | still refuted: the change stays refused, and the builds were already results or frontier exits |
| there is no last result | no | kept |

## 6. Open

Nothing is left open here. An answer that leaves the bound is not followed
further, and it need not be: the recorded round is the base's round, which
the base proves is the fewest changes with no bound on terms (base D12, D8;
Lean `fewest_changes_lower_A`, `_B` bound every sequence of unobstructed
changes). A sequence that leaves the bound and returns is therefore not
shorter. The changed sentence removes answers, not changes, so that proof is
untouched.

## 7. Nearest known results, and how the findings differ

The nearest result in this repository is the base derivation. It required
an answer to an obstructed change, and then proved that those answers reach
nothing the unobstructed changes do not reach. This seed refuses and does
not answer. The reachable set inside the bound does not change. The
structure in that set was already built by changes that were not
obstructed. Refusal removes the answer record. It does not remove results,
and it does not stop the alternatives that still have an unobstructed
change.
