# Two relations, nothing given, raising, and filled triples that balance: what follows

Twenty-fifth derivation. Input: `prompt/twentyfifth/seed_prompt.md`. Task:
`prompt/twentyfifth/prompt.md`. Claim IDs refer to
`paper/twentyfifth/claim_ledger.md`; an ID written `23:D4` refers to the
twenty-third derivation's ledger (`paper/twentythird/claim_ledger.md`, paper
`paper/twentythird/paper.md`), `22:D4` to the twenty-second's, `9:D4` to the
ninth's, `7:D5` to the seventh's, `1:C4` to the first's — the twenty-third is the
parent, and the twenty-second, the ninth, the seventh, the eighth and the first
are cited through it; no other derivation is read (the twenty-fourth is a
sibling and is not an input). Lean names without a namespace are in the
namespace `Twentyfifth` of the library `Twentyfifth` in `lean4_core/` (no
`require`, toolchain `leanprover/lean4:v4.33.1`); it imports the
twenty-third's library `Twentythird` (and through it `Twentysecond`) and nothing
from `lean4/`. The axiom report is `evidence/twentyfifth/lean_axioms.txt`: the
170 theorems of the library, and the 26 theorems of `Twentythird` and
`Twentysecond` this paper cites as imported, all rest on `propext` and
`Quot.sound` at most. Computed files are in `evidence/twentyfifth/`, written by
`python code/run_twentyfifth.py`.

Every notion below carries one source status: **given** (said by the seed),
**chosen** (a reading fixed here where the seed is silent or ambiguous; the
unchosen readings are listed), **derived** (proved), **computed** (output of
`code/`), **refuted** (proved impossible), **open**.

Where a result of an earlier derivation is used it is cited, and the ledger's
re-check column says how its proof was checked from this seed: *no change*
(the statement is about states and the four kinds of change, which this seed
does not touch), *imported* (a theorem of the twenty-third's or twenty-second's
Lean library used as it stands: its statement mentions nothing this seed
changes, and Lean re-checks it when this library is built), *re-proved*
(proved afresh here or in `lean4_core/Twentyfifth/`), or *computed again* (an
earlier exploration re-run beside this one and compared).

## 0. Findings in brief

1. **The seed** is the twenty-third's with a fifth kind of change, "filling
   three different terms", and one sentence: three filled terms `x`, `y`, `z`
   balance when, going from `x` to `y` to `z` and back to `x`, as many
   assertions are written with `r` as with `s`; for every result, record which
   filled terms balance. The seed does not say what filling does beyond making
   three terms filled; the readings of §3 fill that silence, and every one that
   gives other results is computed.
2. **Balance is the twenty-third's sum around three terms.** Going from `x` to
   `y` goes along `xry` and `xsy` (reading C-B1), so a filled triple balances
   when `e(x, y) + e(y, z) + e(z, x) = 0`, `e` the excess `M_r − M_s`. That sum is
   kept by every clause of the sameness (23:D2), by going round from another
   term, and is negated by exchanging the relations: **which filled triples
   balance is a record of the result** (`Same25.balanced_iff`, `around_norm`,
   `balanced_swap`).
3. **The twenty-third's question: its record shows whether, not which.** The
   twenty-third recorded a result's terms and its assertions in `r` and in `s`.
   That record shows *whether* a result is the one asserting nothing on as many
   terms — it records no assertion exactly then (`record_shows_whether`) — but
   not *which* terms keep it from being so: `a b; ara` and `a b; arb` record
   the same (two terms, one assertion in `r`) and are kept from nothing by one
   term (a loop) and by two terms (a two-way sum) (`record_pair_two_terms`);
   `a b c; ara bsb`, `a b c; arb bsc` and `a b c; arb bsa` record the same and
   are kept by one, two and three terms (`record_does_not_show_which_terms`).
   In the five-term run 55 of the 90 records are shared by results kept by
   sets of terms of different sizes.
4. **Told, here: exactly by a filled triple that does not balance.** A result
   asserting nothing balances every filled triple (`nothing_balanced`), so a
   result is told from the result asserting nothing on as many terms by filled
   terms that do not balance exactly when one of its filled triples does not
   balance (`told_iff`); a told result is the same as no result asserting
   nothing (`told_not_nothing`); in every writing (`SameW25.told_iff`). Each such
   triple is a set of terms keeping the result from nothing.
5. **Not told, although not the result asserting nothing:** every result with
   nothing filled — all results with at most two terms among them; results
   differing from nothing only at loops, which no triple goes along
   (`around_add_loop`, `loop_unseen`); results whose sums around are zero on the
   filled triples and not elsewhere — a two-way sum can be seen one way round
   and not the other (`arb_one_way`), and filled triples force the balance of
   others only as far as a rank condition allows (D7). **No filling tells** a
   result whose every sum around three different terms, both ways round, is
   zero: with three terms, the two-way sums adding up to zero and the sum
   around zero (`blind_three_iff`); with four, the two-way sums equal on the two
   pairs of each split of the terms, the three values adding up to zero
   (`blind_four`), with a four-term witness (`blind_four_not_nothing`); **with
   five terms or more, only a result differing from nothing at loops**
   (`blind_five`).
6. **Which sets of filled triples decide** (every loop and two-way sum zero,
   all filled triples balancing, the result is the one asserting nothing):
   exactly those whose sums around have rank `C(n − 1, 2)` on such excesses; the
   triples through one term decide (`cone_decides`); with four terms exactly the
   sets holding three of the four triples; with five terms 3 of the 6 sets of
   six triples up to writing, and every set of eight or more (`decide.csv`).
7. **Fewest changes** to a result: the twenty-third's cost of its assertions
   plus the number of its filled triples,
   `n + min_g Σ |e(x, y) + g(x) − g(y)| + |F|` (`cost25_eq`; with nothing filled
   exactly the twenty-third's, `cost25_embed_iff`; in every writing,
   `cost25_every_writing`).
8. **Relating the seed to the earlier ones.** **The twenty-third maps one to
   one**: its states read with nothing filled are one result here exactly when
   they are one result there, in every writing (`embed_same_iff`,
   `embed_sameW_iff`), and each of its changes is carried to the same change
   (`embed_step`, `embed_reach`). The twenty-second, the ninth, the seventh and
   the first do not (their pairs stay merged, `seventh_pair_merge25`,
   `first_pair_merge25`). **The map back** gives the twenty-third result of a
   result with nothing filled and "none" otherwise; it returns the original on
   every mapped result (`readBack25_embed`); every result it answers "none" on
   costs at least four (`readBack25_none_cost`), and **the smallest is `a b c`
   with one triple filled and nothing asserted** — cost four, one result in
   every writing (`readBack25_none_smallest_writing`). No two twenty-third
   results are made one: nothing is lost by a merge; forgetting the filled
   triples loses them and their record (`forget_loses`).
9. **What of the twenty-third holds here.** Its cost holds exactly on the
   results with nothing filled; elsewhere the cost here is larger by the number
   of filled triples; **its parity of the cost fails** — identifying two terms of a
   filled triple can move the cost by an even number (`parity_fails`: four to
   two); "a change from a state asserting the fewest raises the cost by at most
   one" and "no change returns a state to its own result" hold
   (`Step25.cost_le`, `Step25.not_same`). Reachability holds
   (`reach25_criterion`: identifying down to one term drops every filled
   triple) — under reading C-I3 it fails. The exchange of the two relations
   holds, the balance record included (`same25_swap_iff`, `cost25_swap`,
   `reach25_swap`, `told_swap`).

## 1. What the seed gives

| ID | Given |
|---|---|
| G1 | Terms are written with letters. |
| G2⁗ | An assertion is written `xry` or `xsy`, where `x` and `y` are terms and `r` and `s` are the two relations; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one. |
| G3″ | Nothing is given: to begin with there are no terms and nothing is asserted. |
| G6′ | A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion; filling three different terms. Nothing else is a change. |
| G7 | Identifying two terms replaces both by one term in every assertion. |
| G7a | Three filled terms `x`, `y`, `z` balance when, going from `x` to `y` to `z` and back to `x`, as many assertions are written with `r` as with `s`, each counted as often as it is asserted; for every result, record which filled terms balance. |
| G11 | Attempt every change, fewest additions first. For every result, record how many terms and assertions it adds to what is given. |
| G12″ | Two results that differ only in how their terms are written, only by an `xry` and an `xsy` asserted together, or only by raising terms, are the same result. |
| G12a | Raising a term `x` adds `xry` and `ysx` once for every other term `y`. |
| G13 | Attempt 100 changes along each alternative, earlier changes on every alternative before later ones; do not invent a change; if too many, declare a finite bound, export the exact frontier, and prove what is complete within it. |
| G14 | Any outcome is valid. |

Against the twenty-third seed, G6′ replaces G6 and G7a is new; every other
sentence is the twenty-third's, character for character (`git diff --no-index
--word-diff`; `research/twentyfifth/reading_the_seed.md`).

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, letter, assertion `xry` or `xsy`, the two relations, multiplicity | given (G1, G2⁗) | the ninth's |
| the state's assertions: a multiplicity for each ordered pair in each relation | chosen (9:C1′, no change) | Lean `St` of the twenty-second |
| filled triples of a state | given (the word "filled", G6′, G7a), chosen (C-F1) | Lean `FSt`: `St` and a list of `Tri` |
| filling three different terms | given (G6′), chosen (C-F1, C-O1, C-M1) | `FSt.fill`, `Step25.fill` |
| a filled triple's way round | chosen (C-O1) | written from its least term, `Tri.norm` |
| the beginning: no terms, nothing asserted, nothing filled | given (G3″) | `empty25` |
| change, five kinds; what identifying does to assertions | given (G6′, G7) | `Step25` |
| what identifying does to filled triples | chosen (C-I1) | `carry` |
| multiplicities of merged pairs add up; removing what is not asserted is not a change | chosen (9:C5⁗, no change) | |
| balance of three filled terms | given (G7a), chosen (C-B1) | `Balanced`: the sum around is zero |
| the record of which filled terms balance | given (G7a), derived (D1) | a record of the result |
| a pair asserted together; raising | given (G12″, G12a), chosen (22:C-J1, 23:C-H1, no change) | raising touches no filled triple |
| the excess `M_r(x, y) − M_s(x, y)`; sums around; loops; two-way sums | derived (22:D1, 23:D2, imported) | `excess`, `around` |
| the sameness of results | given (G12″), chosen (a rewriting carries the filled triples), derived (D2) | `Same25`, in every writing `SameW25` |
| result | given (G12″), derived (D2) | a twenty-third result and a set of filled triples, up to one rewriting of both |
| the result asserting nothing on as many terms | the task's words, derived (D4) | the twenty-third's, with any filled triples |
| terms keeping a result from being that one | the task's words, chosen (C-K) | the least sets of terms whose reading is not nothing |
| told from it by filled terms that do not balance | the task's words, chosen (C-T), derived (D4) | `Told`, `told_iff` |
| blind result | derived (D6) | every sum around, both ways round, zero; `Blind` |
| a set of filled triples that decides | derived (D7) | rank condition; `cone_decides` |
| a change of a result | chosen (23:C-X, re-checked: D9) | a change of one of its states |
| exploration of states, results formed afterwards | the task's words, chosen (23:C-E, re-checked: §6) | states with filled triples |
| round of a result | chosen: the first round in which one of its states is reached | equals the cost (D8) |
| cost (fewest changes) | derived (D8) | `Cost25` |
| what is recorded for a result | given (G11, G7a), chosen (C-R) | the twenty-third's record and the balance record |
| bound, frontier | given (G13); bound on terms and rounds chosen (9:C8′) | §6 |
| an earlier seed mapped in; the map back; what a merge loses | the task's words, derived (D10–D12) | `embed`, `readBack25` |
| reachability between results | derived (D13) | `reach25_criterion` |
| the exchange of the two relations | derived (D14) | `FSt.swap` |
| counts of results | computed (K1), derived (D15) | independent count |
| names `a`, `b`, `arb`, `bra`, what is given | — (not in the seed) | without object, as under the ninth |

## 3. Readings that had to be chosen

Inherited without change from the twenty-third (23:C-inh: 9:C1′, C3, C5⁗, C6,
C8′, C9; 22:C-J1; 23:C-H1; 23:C-X; 23:C-E; 23:C-R): the assertions of a state,
no cap on letters, what the four kinds of change are and that merged
multiplicities add up, the bound on terms and rounds, what "an `xry` and an
`xsy` asserted together" and "raising" mean, a change of a result being a change
of one of its states, and the exploration of states with results formed
afterwards. Each is about the assertions or about a sentence this seed repeats
word for word (re-check: no change); C-X and C-E are re-checked with filled
triples in D9 and §6.

**C-F1 (chosen). Filling.** A state carries its filled triples; filling three
different terms of the state makes them a filled triple and changes nothing
else (`FSt.fill`). Filling a triple already filled changes nothing, so it is
not a change (as removing what is not asserted is not, 9:C5⁗; `Step25.fill`
requires the triple not filled). **C-F2 (unchosen, kept):** filling leaves the
state as it was, the filled triple being recorded on the change only. Then a
filling returns its state, no result is reached that the four kinds do not
reach, and no sequence is shortened by a filling: **C-F2's results and rounds
are the twenty-third's** (computed: 257 results at three terms and six rounds,
the twenty-third's at that bound, `readings.json`); "for every result, record
which filled terms balance" then has no filled terms of a result to read.

**C-O1 (chosen). Which way round.** "Three filled terms `x`, `y`, `z` balance
when, going from `x` to `y` to `z` and back to `x`": a filled triple keeps the
order in which its terms are gone round; going round from `y` or `z` is going
round the same way (`x, y, z` = `y, z, x` = `z, x, y`), and `x, z, y` is another
filled triple. Written from its least term (`Tri.norm`, `norm_rot`). Unchosen,
kept and computed (three terms, six rounds, `readings.json`): **C-O2** three
terms filled as a set, balancing both ways round (291 results, 25 told);
**C-O3** a set, balancing either way round (291 results, 7 told, against 30
under C-O1); **C-O4**
every starting term a different filled triple (478 results).

**C-B1 (chosen). What is gone along.** Going from `x` to `y` goes along the
assertions written `x q y` — `xry` with `r`, `xsy` with `s`, each counted as
often as asserted. The triple balances when `e(x, y) + e(y, z) + e(z, x) = 0`.
**C-B2 (unchosen, kept, computed):** the assertions between `x` and `y` either
way; the triple balances when its three two-way sums add up to zero — which no
raising moves either. Same results as C-B1 (the record differs, not the
states), and different answers: under C-B2 `a b c; arb bsa` balances whichever
way it is filled, while under C-B1 it is told (`arcThree_told`); 42 results told
against 30 at three terms and six rounds.

**C-M1 (chosen) / C-M2 (unchosen, computed).** A triple is filled or not /
fillings counted like a multiplicity (328 results against 319; the cost counts
every filling).

**C-I1 (chosen). Identifying.** "Identifying two terms replaces both by one
term": in every filled triple too; a triple left without three different terms
is no longer a filled triple of three different terms and is dropped; two that
become one are one (`carry`). **C-I2 (unchosen, computed):** every filled
triple naming either term is dropped — the same results at the same rounds as
C-I1 (every result is reached by additions and fillings alone, at the cost of
D8, under both; neither rule adds a triple). **C-I3 (unchosen, computed):** the
triples left without three different terms are kept — then a filled triple is
never lost, the twenty-third's reachability fails, and so does the cost of D8
(D16).

**C-A (chosen). The order of attempts.** Filling adds no term and no assertion,
so it is attempted with the changes that add nothing: identifications, removals
in `r`, in `s`, fillings, a term, additions in `r`, in `s`. Unchosen: fillings
last. The round of a result does not depend on the order within a round, so
both give the same results at the same rounds (computed: `readings.json`).

**C-R (chosen). What is recorded.** The twenty-third's record — the terms, and
the assertions in `r` and in `s` of a state asserting the fewest (a filled
triple is neither a term nor an assertion) — and, as G7a asks, the result's
filled triples each marked balancing or not. Unchosen: filled triples counted
among what a result adds to what is given (a record only; it changes no result).

**C-K (chosen). The terms that keep a result from being the one asserting
nothing.** A set of terms keeps it when the result read on those terms alone
(their assertions among themselves) is not the result asserting nothing on
them; the terms that keep it are the least such sets. By 23:D2 they are single
terms with a loop, pairs with a two-way sum not zero and every loop zero, and
triples with every loop and two-way sum among them zero and their sum around
not zero (`keeping_sets`, found again by reading every set of terms,
`keeping_sets_by_restriction`). Unchosen: every term lying in some such set —
the witnesses of D3 answer the question the same way under it.

**C-T (chosen). Told from one that is.** A result is told from a result asserting
nothing by filled terms that do not balance when their records of which filled
triples balance differ. A result asserting nothing with other filled triples
differs from it in its filled triples, not by balance; so the comparison is with
the result asserting nothing on as many terms with the same filled triples
(`nothingWith`).

Set aside, with the words that refuse them: filling also adds or removes
assertions (refused by "A change is exactly one of" — adding an assertion is
another change — and by the seed naming no assertion that filling adds: any
would be invented); filling a triple of fewer than three different terms
(refused by "three different terms").

## 4. What follows

Proofs are in Lean where a Lean name is given; otherwise the proof is here.

**D1. Balance is a record of the result.** `around G t` is the sum around a
triple, `Balanced G t` says it is zero. Going round from the next term gives the
same sum (`around_rot`), so the triple's normal form balances exactly when the
triple does (`around_norm`); the twenty-third's sameness keeps every sum around
three terms (`Same3.around`, imported; `Same3.around25`), so **every filled
triple balances in one state of a result exactly when it balances in every
other** (`Same25.balanced_iff`), and in every writing (`around_rename`,
`told_rename`). The exchange of the relations negates every sum around
(`around_swap`), so a triple balances in a state exactly when it balances in its
exchange (`balanced_swap`). Computed: on every result of every run, its
states reached, rewritten onto one writing, balance the same filled triples
(`record_mismatch` empty).

**D2. The sameness with filled triples.** At a fixed writing, `Same25 A B`: the
twenty-third's sameness on the assertions and the same filled triples (the lists
rearrangements of each other). It is an equivalence (`Same25.refl`,
`Same25.symm`, `Same25.trans`) and exactly what the seed's clauses generate,
which do not touch the filled triples (`gen25_iff_same25`, using the
twenty-third's `gen3_iff_same3`, imported). A rewriting rewrites the assertions
and every filled triple, keeping its way round (`FSt.rename`); it keeps a state
well formed (`rename25_wf`), is undone by its inverse (`rename25_rename`), and
`SameW25` — a rewriting, then `Same25` — is an equivalence (`SameW25.symm`,
`SameW25.trans`) and exactly what the clauses and rewriting generate
(`genW25_iff_sameW25`). So a result is a twenty-third result together with a set
of filled triples, up to one rewriting of both; its mark is the twenty-third's
normal excess table with the filled triples, least over the rewritings
(`result_mark` in `code/twentyfifth/state.py`).

**D3. The twenty-third's question.** In the twenty-third a result's record is
its terms and the assertions in `r` and in `s` of a state asserting the fewest.
*It shows whether the result is the one asserting nothing on as many terms:*
a result records no assertion — costs as many changes as it has terms — exactly
then (`record_shows_whether`: a state asserting the fewest with an empty plain
part has excess zero everywhere). *It does not show which terms keep it from
being so.* `a b; ara` and `a b; arb` each assert the fewest of their results,
one assertion in `r` each — the same record — and the first is kept by a loop
(one term), the second, every loop zero, by a two-way sum (two terms)
(`record_pair_two_terms`). With three terms, `a b c; ara bsb`, `a b c; arb bsc`
and `a b c; arb bsa` each record three terms, one assertion in each relation,
and are kept by single terms, by pairs, and by the three terms together
(`record_does_not_show_which_terms`). Computed on every twenty-third result of
the runs (the results here with nothing filled): 55 of the 90 records of the
five-term run, 51 of 101 in the three-term run and 44 of 324 in the two-term run
are shared by results whose least keeping sets have different sizes; the first
in the fixed order records `(2, 0, 1)`, for `a b; bsb` and `a b; bsa`
(`records_*.csv`, `whether_mismatch` empty: no assertion recorded exactly for
the result asserting nothing). *Here* the record adds which filled triples
balance: every filled triple that does not balance is a set of three terms
keeping the result from nothing (its sum around is not zero, one of the sums
23:D2 names), and contains one of the least keeping sets (computed:
`keeping_mismatch` empty) — a two-way sum or a loop among its terms, or the
triple itself. Loops, two-way sums and sums around unfilled triples are not
shown.

**D4. Told exactly by a filled triple that does not balance.** A result
asserting nothing balances every filled triple (`nothing_balanced`: every sum
around is zero on it, 23:D2). So the record of which filled triples balance
differs from the record of the result asserting nothing on as many terms with
the same filled triples exactly when some filled triple does not balance
(`told_iff`), and a result with such a triple is the same as no result asserting
nothing, whatever that one has filled (`told_not_nothing`). A result whose every
filled triple balances records exactly what that result records, and is it
exactly when it asserts nothing up to the sameness (`not_told`). Whether a
result is told is the same in every writing (`SameW25.told_iff`) and under the
exchange (`told_swap`). Computed: on every result, the two readings of "told" —
some filled triple not balancing, and the two records compared — agree
(`told_mismatch` empty). In the five-term run 2 309 of the 9 573 results are
told, 4 600 have a filled triple.

**D5. What filled triples do not tell.** A result that is not the one asserting
nothing is not told in four ways, and every one occurs:
(a) *nothing is filled* — in particular every result with at most two terms,
which has no three different terms (`nothing_filled_of_lt_three`);
(b) *it differs from nothing only at loops*: a filled triple of three different
terms never goes along a loop, so asserting `xrx` or `xsx` once more changes no
sum around (`around_add_loop`); `a b c; ara`, filled both ways round, balances
both and is not the result asserting nothing (`loop_unseen`);
(c) *it is blind* (D6): every sum around, both ways round, is zero;
(d) *its sums around are zero on the filled triples only*: a two-way sum is seen
one way round and not the other — in `a b c; arb` the sum around `a b c` is one
and around `a c b` zero (`arb_one_way`) — and the filled triples force the
balance of others only as D7 says: `a b c d; crd dsc` balances `a b c` and
`a b d`, has every loop and two-way sum zero, and is not the result asserting
nothing (`two_triples_do_not_decide`). Computed, in the five-term run: 4 967
results with nothing filled, 236 differing from nothing only at loops, 61
blind, 1 961 with a non-zero sum around only off the filled triples, 39
results asserting nothing, 2 309 told (`summary.json`, `told_or_not`); the
three-term run: 15 667, 182, 444, 2 512, 6, 11 072.

**D6. Blind results: what no filling tells.** Call a result blind when every sum
around three different terms, both ways round, is zero (`Blind`): then it
balances every triple that can be filled (`Blind.balanced`). Going round both
ways adds up to the three two-way sums, so blind means: every sum around one way
round is zero, and every three terms' two-way sums add up to zero. What that
forces on the two-way sums:
- *three terms*: their three two-way sums add up to zero (`blind_three_iff`) —
  a two-way sum can be non-zero: `a b c; arb arc csb csa` has two-way sums one,
  minus one and zero and is blind (`blind_three_not_nothing`, `blindThree_blind`);
- *four terms*: the two-way sums are equal on the two pairs of each split of the
  four terms, and the three values add up to zero (`blind_four`); conversely,
  with such two-way sums every three terms' two-way sums add up to zero, so the
  result is blind exactly when its sums around one way round are zero (proof:
  the sum around the other way is the two-way total less it). A four-term blind
  result with no loop that is not the one asserting nothing:
  `a b c d; bra crd asc dsb` (`blind_four_not_nothing`);
- *five terms or more*: every two-way sum is zero (`blind_twoWay_five`: from
  the sums around the triples among any five terms), so a blind result whose
  loops are zero is the result asserting nothing (`blind_five`) — **what no
  filling tells, with five terms or more, lies at the loops only**.
The same count, done on the excess tables modulo raising, says how many
independent directions of the results the sums around every triple never see:
3 + 2 with three terms, 4 + 2 with four, 5 + 0 with five, 6 + 0 with six (the
first number the loops; `unseen.csv`, which also gives, for every set of filled
triples with at most four terms up to writing, the directions it leaves
unseen). Computed: on every
result of every run, blind by the sums and blind by this description agree, and
a blind result filled at every triple is not told while a result that is not
blind, so filled, is (`blind_mismatch` empty).

**D7. Which filled triples decide.** Take every loop and every two-way sum zero.
Then the excess is determined by its values `e(x, y)`, `x < y`, the moves
`g(x) − g(y)` span `n − 1` dimensions of them, and the result is the one
asserting nothing exactly when every sum around is zero (23:D2). A set of filled
triples *decides* when all of them balancing forces that. *Criterion (proof
here):* it decides exactly when the sums around the filled triples have rank
`C(n − 1, 2) = C(n, 2) − (n − 1)` on these excesses. The sums around vanish on
the moves, so the excesses balancing every filled triple form a space holding
the moves; it is the moves alone exactly when its dimension is `n − 1`, that is
when the rank is `C(n − 1, 2)`; a rational excess balancing them all that is not
a move, scaled to whole numbers, is a whole-number one, and it is not the result
asserting nothing since some sum around it is not zero. *The triples through
one term decide* (`cone_decides`: every sum around is the sum of three sums
around triples through that term, when the two-way sums are zero). *Four terms:*
three of the four triples always share a term and are all the triples through
it, so they decide; two do not (`two_triples_do_not_decide`) — the sets that
decide are exactly those holding three of the four triples. *Five terms:* up to
writing, 34 sets of triples; none of five or fewer decides, 3 of the 6 sets of
six (125 of the 210 labelled ones), 3 of the 4 sets of seven, and every set of
eight, nine or ten; the fewest triples that decide are six, `C(4, 2)`
(`decide.csv`, each non-deciding set with a witness that balances it and is not
the result asserting nothing; `summary.json`). Computed:
the rank against the witness for every set with at most five terms, and against
a search over excess tables with entries −1, 0, 1 for at most four terms
(`decide_mismatch` empty).

**D8. Fewest changes.** Let `psi` be the twenty-second's cost of a state's
assertions (`phi`, the terms plus the assertions of its plain part) plus its
filled triples. Every change raises `psi` by at most one (`Step25.psi_le`): the
four kinds raise `phi` by at most one (22:D4, `Step.phi_le`, imported), a
filling raises the triples by one, an identification never adds a triple
(`length_carry_le`). From the empty state, additions reach a state asserting the
fewest (22:D4, `reach_plainSt`, imported; carried by `embed_reach`) and the
fillings follow (`reach_fill_all`). So **the fewest changes to a result is the
twenty-third's cost of its assertions plus the number of its filled triples**
(`cost25_eq`), `n + min_g Σ |e(x, y) + g(x) − g(y)| + |F|` by 23:D5
(`cost3_iff_min`, imported), the same in every writing (`cost25_every_writing`);
with nothing filled it is the twenty-third's (`cost25_embed_iff`). Computed: in
every run the round of every result is this cost, and the round of every state
reached is its `psi` (`round_not_cost`, `plain_mismatch` empty).

**D9. How one change moves the cost, and which changes respect the sameness.**
A filling raises the cost of the result by exactly one: the assertions are not
touched. A change performed on a state asserting the fewest raises the cost by
at most one (`Step25.cost_le`), and no change returns a state to its own result
(`Step25.not_same`: a term or an identification changes the terms, an addition
or a removal the parity of the size, 23:D6 imported, a filling the number of
filled triples). **The twenty-third's parity of the cost fails:** identifying
`a` and `b` in `a b c` with `a b c` filled is one change, and the cost goes from
four to two — the filled triple is left without three different terms and
dropped (`parity_fails`). Computed, five-term run: identifications move the
cost by −1 … −5, even amounts included (−2 1 612 times, −4 357); fillings by +1
always; adding a term by +1, +3, +5 (from states not asserting the fewest, as in
the twenty-third); every change from a state asserting the fewest by at most one
(`change_mismatch` empty). *Which changes respect the sameness* (23:C-X): a
filling does — the same triple filled in two states of one result gives one
result (`Same25.fill`); adding a term does not, as in the twenty-third
(`addTerm_not_respected25`); adding and removing assertions do, and identifying
does with at most three terms (23:D4, no change: filled triples are carried the
same way from every state of a result).

**D10. Relating this seed to the earlier ones: the twenty-third maps one to one.**
A twenty-third state read with nothing filled (`embed`): two of its results are
one result here exactly when they are one result there
(`embed_same_iff`), in every writing (`embed_sameW_iff`); every change of the
twenty-third is carried to the same change here (`embed_step`, `embed_reach`);
its cost is the cost here (`cost25_embed_iff`). The other seeds of the line do
not map one to one: the seventh's pair `a b; arb arb`, `a b; arb bra` — two
seventh results, two ninth states, two twenty-second results in every writing
(23:D9, `seventh_pair_apart`, `twentysecond_pair_apart`, `ninth_pair_apart`,
imported) — is one result here (`seventh_pair_merge25`), and so is the first
seed's pair `a b c; arb arc`, `a b c; bra cra` (`first_pair_merge25`; apart:
`first_pair_apart`, imported). Computed: in every run the twenty-third's own
exploration at the same bound, run again, gives exactly the results here with
nothing filled, at the same rounds (4 973, 15 671, 7 914; `embed_mismatch`
empty).

**D11. The map back.** From this seed's results to the twenty-third's
(`readBack25`): the twenty-third result of a result with nothing filled, "none"
otherwise. It depends on the result only (`readBack25_congr`) and **returns the
original on every mapped result** — by its definition (`readBack25_embed`, true by
computation; what carries weight is that the embedding is one to one, D10). **Every result it
answers "none" on costs at least four** (`readBack25_none_cost`: a filled triple
needs three terms and a filling), and **the results it answers "none" on at cost
four are `a b c` with one triple filled and nothing asserted**
(`readBack25_none_smallest`), either way round — one result in every writing
(`oneFilled_sameW_other`, `readBack25_none_smallest_writing`), costing four
(`cost_oneFilled`). Computed: first "none" at round 4 in every run with three
terms or more; 4 600 and 14 212 results answered "none" in the five- and
three-term runs, none with two terms (`read_back_mismatch` empty).

**D12. What a merge loses.** This seed makes no two twenty-third results one
(`embed_same_iff`): nothing is lost by a merge. The other way, forgetting the
filled triples maps this seed's results onto the twenty-third's
(`forget_same`) and is not one to one: `a b c` filled at `a b c` and `a b c` with
nothing filled are two results here and one there (`forget_loses`); what it
loses is the filled triples and their record. Computed: up to 49 results here
over one twenty-third result in the five-term run, 4 in the three-term run.

**D13. Reachability: the twenty-third's criterion holds.** A result reaches
another exactly when the other has a term or the first is the empty state
(`reach25_criterion`). Path: remove every assertion (`reach25_clear`), identify
the terms down to one (`reach25_collapse`) — a well-formed state with one term
has nothing filled (`nothing_filled_of_lt_three`), so every filled triple is gone
— add terms (`reach25_grow`), add the other's plain part and fill its triples
(`reach25_fill_in`). So results with a term reach each other both ways
(`reach25_mutual`) and the empty result is never returned to
(`empty_never_returned25`). Computed: within three terms and five rounds, 90
results, 8 011 of the 8 100 ordered pairs reachable — the 89 others into the
empty result — the criterion agreeing with a search along the changes of every
state reached (`reach_mismatch` empty). Under reading C-I3 it fails (D16).

**D14. The exchange of the two relations.** Exchanging `r` and `s` in the
assertions, the filled triples kept (`FSt.swap`), carries every change to a
change of the same kind (`Step25.swap`), keeps the sameness both ways
(`same25_swap_iff`), the cost (`cost25_swap`), reachability (`reach25_swap`) and
which filled triples balance (`balanced_swap`, `told_swap`): a symmetry of
results, cost, reachability and the record. Computed: every result's exchange is
a result of the same round, told exactly when it is (`exchange_mismatch`
empty).

**D15. Counting the results.** A result is a twenty-third result `R` and a set
of filled triples up to one rewriting of both. Fix `R` on `n` terms and the
rewritings that keep it (its stabilizer); the results over `R` with `f` filled
triples are the orbits of the `f`-sets of the `2·C(n, 3)` triples under that
stabilizer. Averaging over the stabilizer the sets each rewriting keeps — a kept
set is a union of the rewriting's cycles on the triples, so a cycle of length
`L` contributes a factor `1 + x^L` — counts them (`fill_orbits`). The cost of
each is `n + w + f`, `w` the fewest assertions of `R`. The twenty-third results
are listed from every excess table of weight at most `w`, grouped by the
twenty-third's mark (its own listing, independent of the changes). With at most
two terms nothing can be filled and the twenty-third's closed form holds: the
results of round `r` with at most two terms are `2r² − 7r + 9` from `r = 3` on
(23:D14). With three terms, results with both triples filled number as the
twenty-third's results (the pair of triples is kept by every rewriting), and
results with one number as the twenty-third's results counted up to the three
rotations only: 1, 6, 50, 258, 962, 2 966 recording 0 … 5 assertions
(`counts.csv`). Computed: every count equals the exploration's, by terms, fewest
assertions and filled triples (`count_mismatch`, `two_term_mismatch` empty).

**D16. The unchosen readings** (three terms, six rounds, `readings.json`).
C-F2: 257 results, the twenty-third's, at the twenty-third's rounds (proof: §3).
C-I2 and fillings last: the chosen results at the chosen rounds (proofs: §3).
C-O2, C-O3: 291 results; C-O4: 478; C-M2: 328; C-B2: 319 — each round the
twenty-third's cost plus the filled triples, counted (same proof as D8: no
change adds more than one triple, and additions then fillings reach every
result). C-I3: 328 results, and **the cost of D8 fails**: `a b` with the triple
`a a b` kept by an identification is reached at round 5, not 3 — a triple
without three different terms cannot be filled directly, so it needs three
terms, a filling and an identification; and **reachability fails**: no change
removes a filled triple, and an identification carries each to a triple (two
may become one, never none), so a result with a filled triple reaches no result
with none — none of the 71 such results does, by search. Told results: 30
(chosen), 25 (C-O2), 7 (C-O3), 104 (C-O4), 42 (C-B2), 32 (C-M2), 34 (C-I3).

**D17. Statements about the results.** The earlier 44 statements (the ninth's 42
and the twenty-third's two about results, read as in 23:D17 on every state of a
result asserting the fewest) and four about the filled triples (some triple filled; every filled triple balances; no filling tells it;
the exchange keeps the result) are read on every result: none holds in every
result of the five- or three-term run; 21 depend on the state taken, as in the
twenty-third; with two terms "every filled triple balances" and "no filling
tells it" hold in every result, there being nothing to fill (`follows_*.csv`).

## 5. What does not follow

Each item has two witnesses, or a proof.

- **N1.** That the twenty-third's record shows which terms keep a result from
  nothing: `a b; ara` and `a b; arb` record the same and are kept by one term and
  by two (`record_pair_two_terms`); it does show whether (`record_shows_whether`).
- **N2.** That a result not asserting nothing is told: `a b c; ara` filled both
  ways round is not (`loop_unseen`); `a b c; arb bsa` filled either way round is
  (`arcThree_told`).
- **N3.** That filling both ways round sees every two-way sum:
  `a b c; arb arc csb csa` balances both ways round, with a two-way sum of one
  (`blind_three_not_nothing`); with five terms or more it does (`blind_five`).
- **N4.** That one way round tells what the other does: in `a b c; arb` the sum
  around `a b c` is one, around `a c b` zero (`arb_one_way`).
- **N5.** That two triples through one term decide: `a b c d; crd dsc`
  (`two_triples_do_not_decide`); all the triples through one term do
  (`cone_decides`).
- **N6.** That every change changes the cost by an odd number (23:D6):
  `parity_fails`; a filling does (+1).
- **N7.** That the map back answers every result: `readBack25_oneFilled`; it does
  on every mapped result (`readBack25_embed`).
- **N8.** That forgetting the filled triples is one to one (`forget_loses`); the
  embedding is (`embed_same_iff`).
- **N9.** That reachability holds under every reading: under C-I3 it fails
  (D16, by proof and search); under C-I1 it holds (`reach25_criterion`).
- **N10.** Anything about the asserting or the filling in every result (D17).
- **Refuted** (proved impossible): a told result that is the result asserting
  nothing (`told_not_nothing`); a filled triple balancing in one state of a
  result and not in another (`Same25.balanced_iff`); fewer changes to a result
  than the twenty-third's cost plus its filled triples (`cost25_eq`); a change
  from a state asserting the fewest raising the cost by more than one
  (`Step25.cost_le`); a change returning a state to its own result
  (`Step25.not_same`); a blind result with five terms or more, loops zero, that
  is not the result asserting nothing (`blind_five`); a set of triples through one
  term that balances a result with loops and two-way sums zero that is not the
  one asserting nothing (`cone_decides`); a result answered "none" costing
  fewer than four changes (`readBack25_none_cost`); two twenty-third results made
  one here (`embed_same_iff`).

## 6. The exploration

**Protocol** (reading 23:C-E, with filled triples). From the empty state, round
by round, every change of every state first reached in the round before —
each state a plain state (no pair asserted in both relations) with its filled
triples, in its least writing — fewest additions first, bounded in terms and
rounds; then the states are grouped into results by the sameness of D2. This is
the twenty-third's exploration (the twenty-second's, run as it stands) with the
filled triples carried and the fifth kind attempted; with at most two terms
nothing can be filled and it *is* the twenty-third's. Three runs: 5 terms and 8
rounds, 3 terms and 10 rounds, 2 terms and 24 rounds (the twenty-third's
bounds, above the plan's 4 terms and 7 rounds and 3 and 9, since each completed
here in minutes: about seven minutes for the whole evidence). Beside each, the
twenty-third's exploration at the same bound, computed again. A full attempt log
at 3 terms and 5 rounds (fillings first occur at round 4); reachability at 3
terms and 5 rounds; the readings at 3 terms and 6 rounds; the sets of triples up
to five terms, and every triple filled up to six. Files:
`results_*.csv`, `added_*.csv`, `frontier_*.csv`, `rounds_*.csv`,
`follows_*.csv`, `records_*.csv`, `reach_bound3_rounds5.csv`,
`attempts_bound3_rounds5.jsonl`, `counts.csv`, `decide.csv`, `unseen.csv`,
`given.json`, `readings.json`, `summary.json` (every check; the sixteen
disagreement lists of `FillingCheck`, all empty), `lean_axioms.txt`,
`MANIFEST.sha256`.

**K1. Results within the bounds.**

| run | states reached | results | by terms | with a filled triple | told | answered "none" by the map back |
|---|---|---|---|---|---|---|
| 5 terms, 8 rounds | 12 445 | 9 573 | 1 / 15 / 210 / 3 622 / 5 002 / 723 | 4 600 | 2 309 | 4 600 |
| 3 terms, 10 rounds | 68 526 | 29 883 | 1 / 19 / 453 / 29 410 | 14 212 | 11 072 | 14 212 |
| 2 terms, 24 rounds | 86 201 | 7 914 | 1 / 47 / 7 866 | 0 | 0 | 0 |

In every run: every round has a new result; the round of every result is its
cost; the counts equal the independent counts; with at most two terms the rounds
follow the twenty-third's closed form.

**K2. Completeness within the bound; the frontier.** Let the bound be `N` terms
and `R` rounds. A result with at most `N` terms and cost at most `R` has a state
asserting the fewest, plain, with its filled triples; that state has `psi` equal
to the cost, and additions then fillings reach it without ever holding more
terms, so the exploration reaches it at the round of its cost (D8). So every
such result is formed at the round of its cost; its states reached in that
round are its states asserting the fewest (with its filled triples). The
frontier: every attempt adding a term to a state with `N` terms (59, 21 203 and
71 875 entries; `frontier_*.csv` gives each state and its result), and the
results of round `R`. The independent count (D15) agrees result for result by
terms, assertions and filled triples.

**K3. The map back** (D11): first "none" `a b c` filled at `a b c`, round 4.

**K4. The twenty-third computed again** (D10): its results are the results with
nothing filled, at the same rounds, in all three runs. Reading 23:C-E′ (the
ninth's exploration of every state, grouped) is not run again: its agreement
with C-E (23:K4) rests on a state asserting the fewest being plain, which filled
triples do not change.

**K5. The twenty-third's record** (D3, `records_*.csv`). **K6. Statements**
(D17). **K7. Reachability** (D13). **K8. Readings** (D16). **K9. Changes and the
cost** (D9). **K10. The sets of triples that decide** (D7, `decide.csv`,
`unseen.csv`).

**Reproducibility.** `python code/run_twentyfifth.py` rewrites every computed
file; `--check` regenerates into a temporary folder and compares byte for byte;
`python code/lean_report_twentyfifth.py` builds `lean4_core/` and rewrites
`lean_axioms.txt`, refusing any axiom other than `propext` and `Quot.sound`.

## 7. The task's questions

- **In the twenty-third, does what is recorded for a result show which of its
  terms keep it from being the same as a result with nothing asserted on as many
  terms?** No. It shows *whether* (no assertion recorded exactly then), not
  *which*: `a b; ara` and `a b; arb` record the same and are kept by one term and
  by two; `a b c; ara bsb`, `a b c; arb bsc`, `a b c; arb bsa` record the same and
  are kept by one, two and three terms (D3).
- **Here, which results that are not the same as such a result can be told from
  one that is by filled terms that do not balance?** Exactly those with a filled
  triple that does not balance (D4). **Which cannot?** Those with every filled
  triple balancing: every result with nothing filled (all results with at most
  two terms); results differing from nothing only at loops; blind results —
  with three terms two-way sums adding up to zero and the sum around zero, with
  four two-way sums equal across each split and adding up to zero and the sums
  around zero, with five or more none beyond the loops; and results whose
  non-zero sums around lie off the filled triples, which the filled triples
  cannot exclude unless they decide — through one term, three of four, a rank
  of `C(n − 1, 2)` (D5–D7).
- **The fewest changes to each result**: the twenty-third's cost of its
  assertions plus the number of its filled triples (D8).
- **An earlier seed mapped in one to one**: the twenty-third, each change carried
  to the same change; not the twenty-second, the ninth, the seventh or the first
  (D10). **The map back** returns the original on every mapped result and answers
  "none" first on `a b c` with one triple filled, cost four (D11). **What a
  merge loses**: no twenty-third results are merged; forgetting the filled
  triples loses them and their record (D12).

## 8. What of the twenty-third holds here, and where it does not

- **Cost** (23:D5): holds exactly on the results with nothing filled; elsewhere
  the cost is the twenty-third's cost of the assertions plus the filled triples
  (D8). "A change from a state asserting the fewest raises the cost by at most
  one" holds (`Step25.cost_le`); "no change returns a state to its own result"
  holds (`Step25.not_same`); **"every change changes the cost by an odd number"
  fails** (`parity_fails`).
- **Reachability** (23:D12): holds (D13) under C-I1 and C-I2; fails under C-I3
  (D16).
- **The exchange** (23:D13): holds, the balance record included (D14).
- **The sameness and what shows a result is not the one asserting nothing**
  (23:D1, 23:D2): hold, the filled triples carried by rewriting (D2); the record
  of balance is one of 23:D2's sums, read on the filled triples (D1).
- **A change of a result depends on the state** (23:D4): as there for the four
  kinds; filling does not depend on it (D9).
- **The map from earlier seeds** (23:D9): the twenty-third itself now maps in
  one to one; the others still do not (D10). **The map back** (23:D10): now to the
  twenty-third, first "none" at cost four here too, on a different result (D11).
- **The counts** (23:D14): hold for the results with nothing filled, in
  particular for all results with at most two terms; new counts with filled
  triples (D15).
- **Nothing about the asserting holds in every result** (23:D17): holds (D17).

## 9. Alternatives: kept, or eliminated by proof

| Alternative | Kept / eliminated |
|---|---|
| C-F1 / C-F2 (filling in the state / on the change only) | C-F1 chosen; C-F2 kept, computed: the twenty-third's results (§3, D16) |
| C-O1 / C-O2 / C-O3 / C-O4 (way round) | C-O1 chosen; the others kept and computed (D16) |
| C-B1 / C-B2 (what is gone along) | C-B1 chosen; C-B2 kept and computed: same results, other record (§3, D16) |
| C-M1 / C-M2 (filled or counted) | C-M1 chosen; C-M2 kept and computed (D16) |
| C-I1 / C-I2 / C-I3 (identifying and filled triples) | C-I1 chosen; C-I2 kept, same results and rounds (§3); C-I3 kept, cost and reachability fail (D16) |
| fillings with the changes adding nothing / last | the first chosen; same results and rounds (§3) |
| C-R: filled triples not among what is added / among it | the first chosen; the second a record only |
| C-K: least keeping sets / every term in one | the first chosen; D3's witnesses answer alike |
| filling adds or removes assertions; filling fewer than three different terms | set aside: refused by "A change is exactly one of", by no assertion being named, by "three different terms" |
| C-E / C-E′ (explore plain states / every state) | C-E chosen; C-E′ not run again (K4) |
| a bound on terms alone | eliminated: infinitely many results within it (the loop excess alone) |
| every result within the bound, up to rewriting | kept; none dropped (K2) |

## 10. Open

- O1. A closed form of the cost of the assertions with four or more terms
  (23:O1): unchanged here; the filled triples add their number.
- O2. Lean statements of the rank criterion (D7) in general, of the blind
  description's converse with four terms (D6), of the counts (D15), and of the
  readings' results (D16): proved in the paper and checked by computation.
- O3. Which sets of filled triples decide, for six terms or more, in words other
  than the rank condition (D7): computed up to five terms only.
- O4. Whether some map from the twenty-second's, the ninth's, the seventh's or the
  first's states, carrying each change to some change here (not necessarily of
  the same kind), is one to one (23:O4, unchanged for those seeds).
- O5. A closed form for the number of shortest sequences to a result with
  filled triples: computed per result within the bound (`results_*.csv`).

## 11. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **Simplicial cohomology in degree one.** Read the terms as vertices, every
  pair of different terms as an edge, and the filled triples as oriented
  triangles of a 2-dimensional complex. Once every loop and two-way sum is zero
  the excess is a 1-cochain with integer values; raising adds a coboundary; a
  triple balances exactly when the coboundary of the cochain vanishes on that
  triangle. A result filled so that every triple balances is a cocycle of the
  complex, the result asserting nothing is a coboundary, and D7's "decides" says
  the first cohomology group of the complex (with integer, equivalently rational,
  coefficients here, since cohomology in degree one has no torsion) is zero: the
  filled triangles' boundaries span the cycles of the complete graph over the
  rationals. D6 is the statement that the complete 2-complex on five or more
  vertices has vanishing first cohomology, read for the non-antisymmetric part
  too. Differences: the excess here is not antisymmetric — loops and two-way
  sums are extra data the complex does not see (D5(b), D6 with three and four
  terms) — and a triangle is filled with an orientation, so an oriented filled
  triangle sees a symmetric part one way round and not the other (N4).
- **Kalai's count of simplicial spanning trees.** The 125 sets of six triangles
  on five labelled vertices that decide (`summary.json`,
  `sets_of_triples_that_decide`, among the 210 sets of six) match
  `n^{C(n−2, 2)} = 5³` — no torsion arising on five vertices; this derivation
  computes them and does not use the formula.
- **Gain graphs and balance (Harary; Zaslavsky).** As in the twenty-third, a
  result is an integer-gain graph up to switching; "balance" here is the
  seed's word for a single triangle of zero gain, which is Harary's balance
  restricted to the filled cycles. A balanced gain graph in Zaslavsky's sense is
  one where every cycle balances; filling chooses which cycles are inspected.
- **Discrete exterior calculus and lattice gauge theory.** Filled triangles are
  plaquettes, the sum around one is a discrete curl or a plaquette holonomy,
  and "told" is a non-zero field strength on an inspected plaquette; loops at a
  vertex and symmetric edge parts have no analogue there.
- **Orbit counting (Burnside's lemma).** D15 counts sets of triangles up to the
  stabilizer of each twenty-third result by averaging fixed sets, with a factor
  `1 + x^L` per cycle of triangles.

What appears to be specific to this seed: that the record the seed asks for is
exactly one of the twenty-third's sums, read only where a triple was filled, so
the record shows some terms that keep a result from nothing and never a loop;
that orientation matters once the two directions of a pair are separate; that
the earlier cost survives with the filled triples simply added while its parity
does not, identifying dropping triples; and that the twenty-third maps in one to
one, while the smallest result the map back cannot answer is a single filled
triangle on three terms with nothing asserted.
