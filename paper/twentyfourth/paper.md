# Two relations, nothing given, raising, and filled terms: what follows

Twenty-fourth derivation. Input: `prompt/twentyfourth/seed_prompt.md`. Task:
`prompt/twentyfourth/prompt.md`. Claim IDs refer to
`paper/twentyfourth/claim_ledger.md`; an ID written `23:D4` refers to the
twenty-third derivation's ledger (`paper/twentythird/claim_ledger.md`, paper
`paper/twentythird/paper.md`), `22:D4` to the twenty-second's, `9:D4` to the
ninth's, `7:D11` to the seventh's, `1:C4` to the first's — the twenty-third is
the parent, the others are cited through it; no other derivation is read, and
the twenty-fifth (a sibling) is not an input. Lean names without a namespace
are in the namespace `Twentyfourth` of the library `Twentyfourth` in
`lean4_core/` (no `require`, toolchain `leanprover/lean4:v4.33.1`); it imports
the twenty-third's library `Twentythird` (and through it `Twentysecond`) and
nothing from `lean4/`. The axiom report for every theorem of the library (142)
and for every earlier theorem this paper names (16) is
`evidence/twentyfourth/lean_axioms.txt`: all rest on `propext` and
`Quot.sound` at most. Computed files are in `evidence/twentyfourth/`, written
by `python code/run_twentyfourth.py`.

Every notion below carries one source status: **given** (said by the seed),
**chosen** (a reading fixed here where the seed is silent or ambiguous; the
unchosen readings are listed), **derived** (proved), **computed** (output of
`code/`), **refuted** (proved impossible), **open**.

Where a result of an earlier derivation is used it is cited, and the ledger's
re-check column says how its proof was checked from this seed: *no change*
(the statement is about the assertions and the four earlier kinds of change,
which this seed does not touch), *imported* (a theorem of the twenty-third's or
twenty-second's Lean library used as it stands: its statement mentions nothing
this seed changes, and Lean re-checks it when this library is built),
*re-proved* (proved afresh here or in `lean4_core/Twentyfourth/`), or *computed
again* (an earlier exploration re-run beside this one and compared).

## 0. Findings in brief

1. **The seed** is the twenty-third's with a fifth kind of change — filling
   one term — and one sentence added: a filled term `x` balances when `xrx`
   and `xsx` are asserted equally often; for every result, record which filled
   terms balance. It does not say what filling does beyond making the term
   filled; the sameness sentence says nothing of filled terms.
2. **Reading.** A state is the twenty-third's state and a set of filled terms;
   filling marks a term and changes nothing asserted (C-F1); a rewriting
   carries the filled terms, pairs asserted together and raising touch none,
   and two results differing in their filled terms are two results (C-S);
   identifying two terms fills the one term when either was (C-I1). Unchosen
   readings of filling (a count, adding the loops, adding what balances) and
   of identifying (filled only when both were, never) are kept (§3).
3. **The twenty-third's question.** Its record — terms, and the assertions in
   `r` and in `s` of a state asserting the fewest — shows *whether* a result is
   the one asserting nothing on as many terms (it records no assertion exactly
   then: `record_whether`) but **not which terms keep it from being it**:
   `a b; ara` and `a b; arb` record the same and are kept by one term and by
   two terms together; `a b c; ara asb` and `a b c; arb bsa` record the same
   and are kept by one term and only by three together
   (`record23_does_not_show_which`, `record23_does_not_show_which_three`). Among
   the twenty-third's results within three terms and six rounds, 17 of its 37
   records hold results kept by different numbers of terms.
4. **Balance belongs to the result**: a filled term balances exactly when its
   loop's excess `e(x, x) = M_r(x, x) − M_s(x, x)` is zero, and that is the same
   in every state of the result and in every writing (`Same24.balances`,
   `SameW24.balances`).
5. **Which results filled terms that do not balance tell apart from a result
   with nothing asserted on as many terms** (the same terms filled): exactly
   those with a filled term whose loop's excess is not zero (`told_iff`,
   `told_not_nothing`). **Which they cannot**: every other result that is not
   the one asserting nothing, of three kinds (`not_told_cases`) — a loop of
   non-zero excess only at unfilled terms, one filling away from being told
   (`told_after_fill`); every loop zero and a two-way sum `e(x, y) + e(y, x)`
   not zero; every loop and two-way sum zero and a sum around three terms not
   zero. For the last two kinds **no filling ever tells**
   (`never_told_of_loops_zero`): filling is a one-term probe and sees only
   loops. Witnesses: `a; ara` with `a` filled (told), `a b; brb` with `a` filled
   (one filling away), `a b; arb` and `a b c; arb bsa` with every term filled
   (never). One identification can turn the two-term kind into a told one:
   `a b; arb` both filled, `a` and `b` identified, is `a; ara` filled
   (`identify_tells`).
6. **Fewest changes** to a result: its terms, its filled terms, and the fewest
   assertions among its states — `n + |F| + min_g Σ |e(x, y) + g(x) − g(y)|`,
   the twenty-third's cost plus the number of filled terms (`cost24_eq`), the
   same in every writing (`cost24_every_writing`). A shortest sequence adds
   terms, adds assertions and fills, and nothing else (`shortest24`).
7. **Relating the seed to the earlier ones.** The twenty-third maps in one to
   one: its states read with no term filled, each of its changes a change here
   of the same kind (`same24_ofSt_iff`, `Step.toStep24`, `sameW24_ofSt_iff`); so
   no two of its results are made one, and the merge loses nothing
   (`no_merge`). **The map back** — a result with no filled term to its
   twenty-third result, "none" otherwise — returns the original on every
   mapped result (`readBack_ofSt`) and answers "none" exactly with a filled
   term (`readBack_none_iff`); **the smallest result answered "none" is one
   term, filled, nothing asserted, at cost two, the only one at that cost**
   (`smallest_none`, `smallest_none_unique`). The forgetting map answers every
   result but merges results that differ in their filled terms
   (`forget_merges`).
8. **What of the twenty-third holds here.** Its cost holds on the results
   with no filled term (`cost24_ofSt`) and gains one per filled term
   elsewhere; its parity — every change moves the cost by an odd number —
   fails exactly for identifying two filled terms, which moves it by an even
   number (`identify_two_filled_even`: `a b` both filled costs 4, identified
   costs 2). Its reachability fails under C-I1: **a filled term never goes
   away** (`Reach24.hasFilled`), and a result reaches another exactly when the
   other has a term or the first is empty, and the other has a filled term or
   the first has none (`reach24_criterion`, `twentythird_criterion_fails`);
   under C-I2 and C-I3 the twenty-third's criterion holds (`i2_unfills`,
   computed). The exchange of the two relations holds, balance included
   (`same24_swap_iff`, `balances_swap`, `told_swap`, `cost24_swap`,
   `reach24_swap`).

## 1. What the seed gives

| ID | Given |
|---|---|
| G1 | Terms are written with letters. |
| G2⁗ | An assertion is written `xry` or `xsy`, where `x` and `y` are terms and `r` and `s` are the two relations; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one. |
| G3″ | Nothing is given: to begin with there are no terms and nothing is asserted. |
| G6′ | A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion; filling one term. Nothing else is a change. |
| G7 | Identifying two terms replaces both by one term in every assertion. |
| G7a | A filled term `x` balances when `xrx` and `xsx` are asserted equally often; for every result, record which filled terms balance. |
| G11 | Attempt every change, fewest additions first. For every result, record how many terms and assertions it adds to what is given. |
| G12″ | Two results that differ only in how their terms are written, only by an `xry` and an `xsy` asserted together, or only by raising terms, are the same result. |
| G12a | Raising a term `x` adds `xry` and `ysx` once for every other term `y`. |
| G13 | Attempt 100 changes along each alternative, earlier changes on every alternative before later ones; do not invent a change; if too many, declare a finite bound, export the exact frontier, and prove what is complete within it. |
| G14 | Any outcome is valid. |

Against the twenty-third seed, G6′ replaces G6 and G7a is new; every other
sentence is the twenty-third's, character for character (`git diff --no-index
--word-diff`; `research/twentyfourth/reading_the_seed.md`).

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, letter, assertion `xry` or `xsy`, the two relations, multiplicity | given (G1, G2⁗) | the ninth's |
| the state: the twenty-third's (terms, a multiplicity per ordered pair per relation) and its filled terms | chosen (C-F1, C-S) | Lean `FSt`: the twenty-second's `St` and a filled predicate |
| the beginning: no terms, nothing asserted, nothing filled | given (G3″) | `empty24` |
| change, five kinds; what identifying does to assertions | given (G6′, G7) | `Step24` |
| what filling does | chosen (C-F1) | unchosen C-F1′, C-F2, C-F3, C-F4 |
| what identifying does to filled terms | chosen (C-I1) | unchosen C-I2, C-I3 |
| a filled term balances | given (G7a), derived (D2) | `Balances`; a mark of the result |
| the record of which filled terms balance | given (G7a), chosen (C-B) | at the result's least writing, with the two counts |
| the twenty-third's record (terms, assertions in `r`, in `s`) | given (G11), chosen (23:C-R, no change) | kept beside the new one |
| the sameness of results | given (G12″), chosen (C-S), derived (D1) | `Same24`, in every writing `SameW24` |
| a result with nothing asserted on as many terms | the task's words, chosen (C-N) | the same filled terms (`nothingOf`); C-N0 |
| the terms that keep a result from being it | the task's words, chosen (C-K) | loops, two terms, three terms (23:D2) |
| told apart by filled terms that do not balance | the task's words, derived (D4) | `Told`, `told_iff` |
| a change of a result | chosen (23:C-X, no change) | a change of one of its states |
| exploration of states, results formed afterwards | the task's words, chosen (23:C-E) | unchosen C-E′ computed |
| order of the attempts | given (G11), chosen (C-O) | fillings with the changes adding nothing |
| round of a result | chosen: the first round in which one of its states is reached | equals the cost (D8) |
| cost (fewest changes) | derived (D8) | `Cost24` |
| reachability between results | derived (D11) | `ReachR24` |
| an earlier seed mapped in; the map back; what a merge loses | the task's words, derived (D13, D14) | `ofSt`, `readBack` |
| counts of results | computed (K1), derived (D15) | two-term closed form |
| names `a`, `b`, `arb`, `bra`, what is given | — (not in the seed) | without object, as under the ninth |

## 3. Readings that had to be chosen

Inherited without change from the twenty-third (23:C-inh, 23:C-H1, 23:C-J1,
23:C-X, 23:C-E, 23:C-R): the state's assertions, no cap on letters, what a
change of the four earlier kinds is and that merged multiplicities add up,
raising and the sameness it generates, pairs asserted together, a change of a
result as a change of one of its states, the exploration of states with the
results formed afterwards, and the twenty-third's record. Each is about the
assertions, the four earlier kinds, or a clause this seed repeats word for word
(re-check: no change).

**C-F1 (chosen). Filling.** Filling `x` makes `x` filled and changes nothing
asserted (`FSt.fill`). Filling a filled term changes nothing and is not a
change, as removing what is not asserted is not (9:C5⁗). **C-F1′ (unchosen,
eliminated):** it is a change whose outcome is its start; it reaches no state
C-F1 does not, so the results and rounds are C-F1's.

**C-F2 (unchosen, kept, computed).** A term filled a number of times, each
filling raising it by one; "filled" is filled at least once, and an
identification adds the two counts, as merged multiplicities do. "A filled
term" names a property and the seed speaks of "a number of times" only for
assertions, which is why it is not chosen. It gives other results: 233
against C-F1's 175 within two terms and six rounds, every round equal to the
twenty-third's cost plus the number of fillings (`readings.json`).

**C-F3 (unchosen, eliminated by proof).** Filling `x` also asserts `xrx` and
`xsx` once each. That is a pair asserted together, so the outcome is C-F1's
result (`fillLoops_same`); computed: the same results at the same rounds.

**C-F4 (unchosen, kept, computed).** Filling `x` adds the missing `xrx` or
`xsx` until they are asserted equally often. Its outcomes differ from C-F1's
(the loop's excess is set to zero); its results and rounds are C-F1's — the
potential of D8 rises by at most one at such a filling, and a sequence reaching
a result fills before adding the loops — computed: 175 results, the same rounds.

**C-S (chosen). Filled terms and the sameness.** A rewriting carries the
filled terms with the terms; pairs asserted together and raising touch none;
two results that differ in which terms are filled are two results (no clause of
G12″ joins them). Set aside: the filled terms kept off the result, as a record
of the sequence that reached it — refused by G7a's "for every result, record
which filled terms balance", which needs the filled terms of a result.

**C-I1 (chosen). Identifying.** The one term of an identification is filled
when either term was ("replaces both by one term": it stands for both;
`idF`). **C-I2** (filled only when both were) and **C-I3** (never filled) are
unchosen, kept and computed: they give the same results and the same rounds
(the potential of D8 does not rise at any identification under any of the
three, and no shortest sequence identifies); they give other outcomes of some
identifications (41 and 46 of 113 in the readings run) and, unlike C-I1, let a
filled term go away (D11).

**C-B (chosen). The record of which filled terms balance**: for every filled
term of the result, at its least writing, whether it balances; with it the
numbers of filled terms that balance and that do not (`results_*.csv`, column
`which_filled_terms_balance`). D2 shows it is a record of the result.

**C-N (chosen). "A result with nothing asserted on as many terms"**: as many
terms, the same filled terms, nothing asserted (`nothingOf`); the question is
then about the assertions. **C-N0 (unchosen, kept):** nothing asserted and
nothing filled. Then every result with a filled term is not such a result, and
those whose assertions are the ones asserting nothing and whose filled terms
all balance are told apart by being filled, not by filled terms that do not
balance: 115 of the 175 results of the readings run are not that result and
have every filled term balancing.

**C-K (chosen). "The terms that keep a result from being the one asserting
nothing"** (the task's words, asked of the twenty-third): the smallest sets of
terms on which the result is not the one asserting nothing — a loop, two terms,
or three terms whose sum is not zero (23:D2); `keeping_size` counts the fewest,
`keeping_terms` how many terms lie in some such set.

**C-O (chosen). The order of the attempts**: identifications, removals in `r`,
in `s`, fillings (they add no term and no assertion), a term, additions in
`r`, in `s`. A round completes before the next, so the order within a round
changes no result and no round, only the attempt log.

**C-E′ (unchosen, computed).** The ninth's states (not taken to their plain
state) with filled terms, grouped: the same results at the same rounds (175
results from 482 states against 340 in the readings run).

## 4. What follows

Proofs are in Lean where a Lean name is given; otherwise the proof is here.

**D1. Sameness.** `Same24 X Y`: the twenty-third's `Same3` on the assertions and
the same filled terms; an equivalence (`Same24.refl`, `Same24.symm`,
`Same24.trans`) keeping the terms, the filled count and whether some term is
filled (`Same24.n`, `Same24.fc`, `Same24.hasFilled`). In every writing:
`SameW24` (a rewriting of the assertions, 22:D1 imported, and of the filled
terms, then `Same24`). Computed: on every state of one and two terms with at
most one assertion per relation and every set of filled terms, joining each to
its rewritings, to itself with one more pair asserted together and to itself
raised at a term, among the states of at most four per relation, gives exactly
the classes of the mark `result_key` (6 and 29; `summary.json`,
`generated_sameness`).

**D2. Balance belongs to the result.** `Balances X x`: `x` is filled and the
atoms `⟨r, x, x⟩` and `⟨s, x, x⟩` occur equally often; that is its loop's
excess being zero (`balances_iff`). The loop's excess is kept by the
twenty-third's sameness (23:D2, `Same3.loop`, imported) and the filled terms by
C-S, so `Same24.balances`; a rewriting carries each filling and each loop's
excess to the term it writes (`SameW24.pointwise`), so `SameW24.balances`.
Computed: in every run the record read from the mark agrees with the loops of
every state reached (`balance_mismatch` empty).

**D3. The twenty-third's question: its record shows whether, not which.**
*Whether*: a result costs its number of terms — its record counts no
assertion — exactly when it is the result asserting nothing on its terms
(`record_whether`; the cost of that result is its terms, `cost3_nothing`).
*Not which*: `a b; ara` and `a b; arb` each assert the fewest of their results
(`fewest_loopA`, `fewest_arbA`) and record (2, 1, 0); the first has a loop of
excess one — one term keeps it — the second has both loops zero and its two-way
sum one — no single term keeps it, the two together do
(`record23_does_not_show_which`). `a b c; ara asb` and `a b c; arb bsa` each
assert the fewest (`fewest_loopAsb`, `fewest_arcThree`: two assertions at
least, from the sums kept by the sameness) and record (3, 1, 1); the first is
kept by its loop at `a`, the second has every loop and every two-way sum zero
and its sum around `a b c` one — only the three together keep it
(`record23_does_not_show_which_three`). The record names no term at all: it is
a triple of counts, the same in every writing. Computed over the twenty-third's
own results within three terms and six rounds (`given.json`): 37 records, 17
holding results kept by different fewest numbers of terms, 23 holding results
with different numbers of keeping terms; the first in order records (2, 0, 1),
`a b; bsb` and `a b; bsa`.

**D4. Which results filled terms that do not balance tell apart.** The result
with nothing asserted on the terms of `X`, the same terms filled, is `nothingOf
X`; `X` is it exactly when its assertions are the twenty-third's result
asserting nothing (`same24_nothing_iff`; 23:D2 imported: every loop, two-way
sum and sum around three terms zero). In it every filled term balances
(`nothing_balances`). The record at a fixed writing (`balRec`: a term recorded
as filled and balancing) of `X` differs from that of `nothingOf X` exactly when
some filled term of `X` has a loop whose excess is not zero (`told_iff`) — then
`X` is not the result asserting nothing (`told_not_nothing`) — and whether it
does is a mark of the result (`Same24.told`) in every writing
(`SameW24.told`). Under C-N0 a result with a filled term differs from the
result asserting and filling nothing in any case; the answer about filled terms
that do not balance is the same.

**D5. Which they cannot tell apart.** A result that is neither the one
asserting nothing nor told is exactly one of (`not_told_cases`):
(a) a loop of non-zero excess, every one at an unfilled term — filling that
term tells it (`told_after_fill`; `awayOne_not_told`, `awayOne_fill_told`:
`a b; brb` with `a` filled); (b) every loop zero and some two-way sum not zero;
(c) every loop and two-way sum zero and some sum around three terms not zero.
In (b) and (c) **no set of filled terms tells it**
(`never_told_of_loops_zero`): `a b; arb` (`twoWayFilled_not_nothing`,
`twoWayFilled_never_told`) and `a b c; arb bsa` (`aroundFilled_never_told`) with
every term filled. By 23:D2 no longer sum is needed, so these three kinds and
the told results are all the results other than the one asserting nothing.
Computed, how the results stand (`summary.json`):

| run | the one asserting nothing | told | one filling away | two terms | three terms |
|---|---|---|---|---|---|
| 5 terms, 7 rounds | 17 | 346 | 1 176 | 504 | 9 |
| 3 terms, 9 rounds | 10 | 4 915 | 9 062 | 1 472 | 8 |
| 2 terms, 16 rounds | 6 | 4 332 | 2 489 | 78 | 0 |

the first of each kind in round order being `a; asa` with `a` filled (told),
`a; asa` (one filling away), `a b; bsa` (two terms) and `a b c; crb bsc` (three
terms) (`given.json`); in every run the class read from the mark equals the one
read from the states (`tell_mismatch` empty).

**D6. Identifying can tell, and can blind.** Identifying `u` and `v` sends the
atoms `⟨q, u, u⟩`, `⟨q, v, v⟩`, `⟨q, u, v⟩`, `⟨q, v, u⟩` onto the one term's
loop, so the merged loop's excess is the two loops plus the two-way sum
`e(u, v) + e(v, u)`. Identifying `a` and `b` in `a b; arb`, both filled, gives
`a; ara` with `a` filled: a two-term kind turned told (`identify_tells`).
Conversely identifying any two terms of `a b c; arb bsa` gives the result
asserting nothing on two terms: the merged loop is `1 − 1 + 0 = 0` or `0`, and
the two-way sum with the remaining term is the sum of two two-way sums, all
zero — the three-term witness is merged away.

**D7. Changes of a result.** Filling respects the sameness: filling one term of
two states of one result gives one result (`Same24.fill`); so do adding an
assertion and removing one from states that both assert it (23:D4, no change:
they act on the assertions and keep the filled terms). Adding a term does not,
from two terms on (23:D4, `addTerm_not_respected`, imported: its states have no
term filled, and read with none filled here they are one result and then two,
by `same24_ofSt_iff`). Computed:
on results with at most three terms, every filling and every addition of an
assertion performed on each reached state of a result lands on one result
(13 387, 273 457 and 358 040 outcomes compared; `respect_mismatch` empty).

**D8. Fewest changes.** `pot X`: the twenty-second's `phi` of the assertions
(terms plus the plain part's assertions) plus the filled terms. Every change
raises it by at most one (`Step24.pot_le`): adding a term or an assertion by
at most one (22:D4, imported) with the filled count kept (`fc_addTerm`);
removing likewise; filling by exactly one (`fc_fill`); identifying lowers `phi`
by at least one (22:D4, imported) and never raises the filled count
(`fc_identify_le`, a count through the identification map, `rsum_image_le`).
From the empty state the twenty-second's additions reach the plain state of the
assertions and fillings then fill the terms, in `phi + |F|` changes
(`reach24_upper`, `reach24_fillUpTo`). So **the cost of a result is the
twenty-third's cost of its assertions plus its number of filled terms**
(`cost24_eq`; `Cost24.unique`, `Cost24.congr`) — `n + |F| + min_g Σ |e(x, y) +
g(x) − g(y)|` by 23:D5 (`cost3_iff`, imported) — the twenty-third's cost on its
results mapped in (`cost24_ofSt`), one more after a filling (`fill_cost`), and
the fewest changes in every writing (`cost24_every_writing`, with `fc_rename`,
`pot_rename`). A shortest sequence adds terms, adds assertions and fills
(`shortest24`: the ninth's size plus the filled count rises by one at each of
those changes and falls at every other, `Step24.size24_step`,
`Reach24.raising`). Computed: in every run the round of every result, and of
every state, is its cost, and its potential (`round_not_cost` empty).

**D9. How far one change moves the cost; parity.** A change performed on a
state asserting the fewest raises the cost by at most one (`Step24.cost_le`,
`cost24_le_pot`). No change returns a state to its own result
(`Step24.not_same24`: a filling changes the filled terms, a term or an
identification the number of terms, an assertion the size's parity, 23:D6
imported). But the twenty-third's parity — every change moves the cost by an
odd number (23:D6) — **fails exactly for identifying two filled terms** under
C-I1: `a b` with both filled costs 4, identified it is `a` filled and costs 2
(`identify_two_filled_even`). The move of the assertions' cost is odd (23:D6),
the filled count falls by one exactly when both terms were filled. Under C-I2
the even moves are the identifications with at least one term filled, under
C-I3 those with exactly one (46 and 41 of 113 in the readings run, against 5
under C-I1). Computed (`summary.json`, `how_each_kind_moves_the_cost`), in the
five-term run's 15 729 changes: filling `+1` 1 536 times; identifying `−2` 33,
`−4` 5 — all of them identifications of two filled terms, and every other change
moving it by an odd number (`change_mismatch` empty).

**D10. Shortest sequences.** A shortest sequence to a one-term result adds the
term, then its loops, and fills it if it is filled, anywhere after the term:
one sequence without a filling, `t + 1` with one (`t` the loop's `|excess|`) —
the twenty-second's "one shortest sequence per one-term result" (22:D12, held
by the twenty-third) fails for the filled ones. Computed: the one-term counts
agree in every run (`sequences_mismatch` empty); with more terms the counts are
computed per result (`results_*.csv`), up to 587 059 200 in the two-term run.

**D11. Reachability.** `ReachR24 X Y`: some sequence from `X` ends at a state of
`Y`'s result. Under C-I1 **a filled term never goes away**
(`Step24.hasFilled`, `Reach24.hasFilled`: an identification fills the term a
filled term goes onto). **A result reaches another exactly when the other has a
term or the first is empty, and the other has a filled term or the first has
none** (`reach24_criterion`). Necessity: the twenty-third's (the terms never run
out, 22:D9, imported through `Reach24.forget`) and the filled term. Sufficiency:
remove every assertion (`reach24_clear`), identify the terms down to one —
filled exactly when some term was (`reach24_collapse`) — add terms, fill, add
the target's plain assertions (`reach24_from_one`); when the one term is filled
and the target's first term is not, one more term is added and identified with
the filled one, which moves the filled term onto a filled term of the target
(`idF_move`, `glue_move`). So the twenty-third's criterion (23:D12) **fails
exactly on the pairs from a result with a filled term to one without**
(`twentythird_criterion_fails`: `a` filled does not reach `a`); results with a
filled term reach each other both ways, and so do results with a term and none
filled (`reach24_mutual`). Under C-I2 a filled term goes away by identifying it
with an unfilled term (`i2_unfills`: `a` filled, a term added, the two
identified), and under C-I3 by any identification; with the path above — the
filled term merged away through one extra term — the twenty-third's criterion
holds under both (proof here; computed). Computed within two terms and four
rounds, 37 results: under C-I1 1 034 of the 1 369 ordered pairs reachable,
under C-I2 and C-I3 1 333 (all but the pairs into the empty result); the 299
missing are the 13 results with a filled term times the 23 without, with a
term; the criterion agrees with a search along the changes of every state
reached (`reach_mismatch` empty).

**D12. The exchange of the two relations.** Exchanging `r` and `s`, the filled
terms kept (`FSt.swap`), negates every excess (22:D10, imported) and keeps
zero, so it keeps the sameness both ways (`same24_swap_iff`), balance
(`balances_swap`), the told results (`told_swap`), the cost (`cost24_swap`) and
reachability (`reach24_swap`), carrying every change to a change of the same
kind (`Step24.swap`). Computed: every result's exchange is a result of the same
round with the same balance record and class, its record's relations exchanged
(`exchange_mismatch` empty).

**D13. The twenty-third mapped in, one to one.** A twenty-third state read with
no term filled (`ofSt`): two are one result here exactly when they are one
there (`same24_ofSt_iff`; in every writing `sameW24_ofSt_iff`), and each of the
twenty-third's changes is a change here of the same kind (`Step.toStep24`,
`Reach.toReach24`; an identification of unfilled terms fills nothing,
`idF_false`). So this seed makes no two of the twenty-third's results one
(`no_merge`): the merge the task asks about loses nothing. The twenty-second,
the ninth, the seventh and the first do not map in one to one (23:D9): their
witnesses have no term filled and merge here as there
(`seventh_pair_merge24`). Computed again: the twenty-third's exploration at the
same bounds gives exactly the results here with no filled term, at the same
rounds, with the same numbers of shortest sequences (1 164, 6 450, 2 182
results; `twentythird_mismatch` empty).

**D14. The maps back.** `readBack X`: the twenty-third result of `X` when no
term is filled, "none" otherwise. It returns the original on every mapped
result (`readBack_ofSt`), answers "none" exactly when a term is filled
(`readBack_none_iff`), and depends on the result only (`readBack_congr`).
Every result answered "none" costs at least two (`readBack_none_cost`: a term
and a filling); **the smallest is one term, filled, nothing asserted, at cost
two** (`smallest_none`), and it is the only one at that cost
(`smallest_none_unique`). Computed: the first "none" in round order is `a`
filled at round 2 in every run; 888, 9 017 and 4 723 results answered "none".
**The forgetting map** — a result to the twenty-third result of its states —
answers every result, returns the original on mapped results, and carries each
change to a change of the same kind or, for a filling, to no change
(`Step24.forget`); it merges results that differ only in their filled terms
(`forget_merges`), losing them and the record of which balance. Computed: it
lands on every twenty-third result of the run, up to 8, 8 and 4 results here
on one; each change, forgotten, is a twenty-third change or none
(`forget_mismatch` empty).

**D15. Counting the results.** A result is a twenty-third result and a set of
filled terms, the same rewriting acting on both. With one term: the loop's
excess and whether it is filled, one result recording no assertion and two for
every `t ≥ 1`, filled or not. With two terms: the loops `d0`, `d1`, the two-way
sum `S`, the filled terms `f0`, `f1`, up to exchanging the terms; `t = |d0| +
|d1| + |S|`; the points of `Z³` at distance `t ≥ 1` number `4t² + 2`, and the
exchange fixes the `2t` with `d0 = d1` when both or neither term is filled and
none when one is, so **the two-term results with `k` filled terms recording
`t ≥ 1` assertions number `2t² + t + 1`, `4t² + 2`, `2t² + t + 1` for `k = 0,
1, 2`** (one each for `t = 0`). The results of round `r` with at most two terms
are 1, 1, 4, 9 and then `8r² − 46r + 78` from `r = 4` on (22, 48, 90, 148, …);
within the seed's 100 rounds, 2 482 245 results. Three terms from the loops,
the two-way sums, the sum around and the filled terms up to the rewritings;
four and five terms by listing every excess table with every set of filled
terms. Without a bound on terms the results of round `r` number 1, 1, 4, 10,
28, 94, 366, 1 555 (`r ≤ 7`). Each count is independent of the explorations
and equals them (`count_mismatch`, `two_term_mismatch` empty). Not in Lean.

**D16. The unchosen readings.** C-F1′ reaches nothing new (§3). C-F3's filling
is C-F1's up to a pair asserted together (`fillLoops_same`). C-F2, C-F4, C-I2,
C-I3 and C-E′ computed within two terms and six rounds (`readings.json`):
C-F2 233 results, per round 1, 1, 4, 10, 26, 61, 130, every round its counted
cost; C-F3, C-F4, C-I2, C-I3, C-E′ exactly C-F1's 175 results at C-F1's rounds
(`readings_mismatch` empty).

**D17. Statements about the asserting.** The twenty-third's statements, read
on the states of a result asserting the fewest (23:D17), and six about filled
terms (`follows_*.csv`): none holds in every explored result; 21, 21 and 16
depend on the state in the three runs; "some term is filled", "every filled
term balances", "told apart" and "every term whose loops differ is filled"
hold in some results and fail in others.

## 5. What does not follow

Each item has two witnesses, or a proof.

- **N1.** That a result other than the one asserting nothing has a filled term
  that does not balance: `a b; arb` both filled has none
  (`twoWayFilled_never_told`); `a; ara` filled has one (`toldOne_told`).
- **N2.** That filling the right term always tells: with every loop zero no
  filling does (`aroundFilled_never_told`); with a loop not zero at an
  unfilled term one filling does (`awayOne_fill_told`).
- **N3.** That the twenty-third's record shows which terms keep a result from
  being the one asserting nothing (`record23_does_not_show_which`,
  `record23_does_not_show_which_three`); it shows whether (`record_whether`).
- **N4.** That every change moves the cost by an odd number: identifying two
  filled terms moves it by two (`identify_two_filled_even`); filling by one
  (`fill_cost`).
- **N5.** That the twenty-third's reachability criterion holds: not under C-I1
  (`twentythird_criterion_fails`); under C-I2 it does (`i2_unfills`, D11).
- **N6.** That an identification keeps a result untold (`identify_tells`); or
  keeps it told: identifying a filled term whose loop is `+1` with one whose
  loop is `−1` and nothing between them gives a balancing filled term (the
  merged loop's excess is their sum, D6).
- **N7.** That filled terms can be forgotten without loss (`forget_merges`); on
  the results with none filled they can (`readBack_ofSt`).
- **N8.** That a one-term result has one shortest sequence: `a; ara` filled has
  two (D10); unfilled it has one.
- **N9.** Anything about the asserting or the filling holding in every result
  (D17).
- **Refuted** (proved impossible): a told result that is the one asserting
  nothing (`told_not_nothing`); a told result with every loop zero
  (`never_told_of_loops_zero`); fewer changes to a result than the
  twenty-third's cost plus its filled terms (`cost24_eq`); a change from a state
  asserting the fewest raising the cost by more than one (`Step24.cost_le`); a
  change returning a state to its own result (`Step24.not_same24`); under C-I1,
  a sequence from a state with a filled term to one without
  (`Reach24.hasFilled`); a result answered "none" costing less than two
  (`readBack_none_cost`); two twenty-third results made one (`no_merge`).

## 6. The exploration

**Protocol** (reading C-E). From the empty state, round by round, every change
of every state first reached in the round before — its plain state with its
filled terms, least writing — fewest additions first (C-O), bounded in terms
and rounds; then the states are grouped by this seed's sameness; the round of
a result is the first round in which one of its states is reached. Three runs:
5 terms and 7 rounds, 3 terms and 9 rounds, 2 terms and 16 rounds (each
completed in seconds here; five terms at eight rounds took over a minute in
its listing count, so seven were kept, as planned). Beside each, the
twenty-third's exploration at the same bounds (D13). A full attempt log at 2
terms and 3 rounds; reachability at 2 terms and 4 rounds under each reading of
identifying; the generated sameness at one and two terms; the readings at 2
terms and 6 rounds. Two preconditions make the searches complete and are
checked by `Plan`: the sameness joins within three times the states'
assertions (23:D1), and reachability needs two terms and three rounds (the
filled term merged away through a second term under C-I2, C-I3). Files:
`results_*.csv`, `rounds_*.csv`, `frontier_*.csv`, `follows_*.csv`,
`reach_bound2_rounds4.csv`, `attempts_bound2_rounds3.jsonl`, `counts.csv`,
`given.json`, `readings.json`, `summary.json` (every check; the seventeen
disagreement lists of `FillCheck`, all empty), `lean_axioms.txt`,
`MANIFEST.sha256`.

**K1. Results within the bounds.**

| run | states reached | results | by terms | answered "none" | frontier entries |
|---|---|---|---|---|---|
| 5 terms, 7 rounds | 2 943 | 2 052 | 1 / 24 / 298 / 1 232 / 445 / 52 | 888 | 6 |
| 3 terms, 9 rounds | 29 898 | 15 467 | 1 / 32 / 824 / 14 610 | 9 017 | 7 304 |
| 2 terms, 16 rounds | 46 030 | 6 905 | 1 / 60 / 6 844 | 4 723 | 33 983 |

In every run: every round has a new result; the round of every result is its
cost; the counts equal the independent counts; with at most two terms the
rounds follow the closed form.

**K2. Completeness within the bound; the frontier.** Let the bound be `N` terms
and `R` rounds. A result with at most `N` terms and cost at most `R` has a state
asserting the fewest with its filled terms; the additions and fillings of D8
reach it in its cost, never with more terms, each prefix a state of the
exploration at the round of its potential (`shortest24`, and the round of a
state is its potential, checked). So every such result is formed, at the round
of its cost. The frontier is every attempt adding a term to a state with `N`
terms (6, 7 304 and 33 983 entries; `frontier_*.csv` gives each state and its
result) and the results of round `R`.

**K3. The map back** (D14): first "none" `a` filled at round 2 in every run.

**K4. The twenty-third, computed again** (D13).

**K5. The twenty-third's record question** (D3, `given.json`).

**K6. Statements** (D17). **K7. Reachability** (D11). **K8. Readings** (D16).
**K9. Changes and the cost** (D9).

**Reproducibility.** `python code/run_twentyfourth.py` rewrites every computed
file; `--check` regenerates into a temporary folder and compares byte for byte;
`python code/lean_report_twentyfourth.py` builds `lean4_core/` and rewrites
`lean_axioms.txt`, refusing any axiom other than `propext` and `Quot.sound`.

## 7. The task's questions

- **In the twenty-third, does what is recorded for a result show which of its
  terms keep it from being the same as a result with nothing asserted on as
  many terms?** No. It shows whether — it records no assertion exactly for
  that result — but not which: results with one record are kept by one term, by
  two terms together, or only by three together (D3).
- **Here, which results that are not the same as such a result can filled terms
  that do not balance tell apart from one that is?** Exactly those with a
  filled term whose loop's excess is not zero (D4).
- **Which cannot?** Those whose non-zero loops are all at unfilled terms (one
  filling away), and those with every loop zero, kept by two terms or by three:
  no filling ever tells these (D5).
- **The fewest changes to each result**: `n + |F| + min_g Σ |e(x, y) + g(x) −
  g(y)|` — the twenty-third's cost plus the filled terms (D8).
- **An earlier seed mapped in one to one**: the twenty-third, each change
  carried to a change of the same kind (D13). **The map back** returns the
  original on mapped results and answers "none" first at `a` filled, cost two,
  the only result there (D14). **What the merge loses**: nothing — no two
  twenty-third results are made one (D13).

## 8. What of the twenty-third holds here, and where it does not

- **Cost** (23:D5): holds on the results with no filled term (`cost24_ofSt`);
  elsewhere each filled term adds one (`cost24_eq`). "A shortest sequence is
  additions only" becomes additions and fillings (`shortest24`). "A change from
  a state asserting the fewest raises the cost by at most one" holds
  (`Step24.cost_le`); "no change returns a state to its own result" holds
  (`Step24.not_same24`); "every change moves the cost by an odd number" fails
  for identifying two filled terms and only there (D9).
- **Reachability** (23:D12): fails under C-I1 exactly on the pairs from a
  result with a filled term to one without (D11); holds under C-I2 and C-I3.
- **The exchange** (23:D13): holds, balance and the told results included
  (D12).
- **The result asserting nothing and its witnesses** (23:D2): hold for the
  assertions; filled terms see only the loops (D4, D5).
- **A change of a result depends on the state** (23:D4): adding a term still
  does; filling does not (D7).
- **What is recorded** (23:C-R, 23:D8): kept; the new record of which filled
  terms balance is added, and neither names which terms keep a result from
  being the one asserting nothing beyond the loops (D3, D4).
- **No earlier seed maps in one to one** (23:D9): the twenty-third itself now
  does (D13); the earlier ones still do not.
- **The counts** (23:D14): fail; new closed forms (D15). **One shortest sequence
  per one-term result**: holds for the unfilled ones only (D10).

## 9. Alternatives: kept, or eliminated by proof

| Alternative | Kept / eliminated |
|---|---|
| C-F1 / C-F1′ / C-F2 / C-F3 / C-F4 readings of filling | C-F1 chosen; C-F1′ eliminated (reaches nothing); C-F2 kept and computed (other results); C-F3 eliminated (`fillLoops_same`); C-F4 kept and computed (same results, other outcomes) |
| filled terms on the result / off it (a record of the sequence) | the first chosen (C-S); the second set aside by G7a's "for every result" |
| C-I1 / C-I2 / C-I3 readings of identifying | C-I1 chosen; C-I2, C-I3 kept and computed (same results and rounds; other reachability, other parity) |
| C-N / C-N0 | C-N chosen; C-N0 kept and answered (§3, D4) |
| C-K (smallest keeping sets) | chosen; `keeping_size` and `keeping_terms` both computed |
| C-O order of fillings | chosen; the order within a round changes no result (§3) |
| C-E / C-E′ | the same results and rounds (D16) |
| the twenty-third's readings (C-H1, C-J1, C-X, C-R) | kept, no change |
| every result within the bound, up to rewriting | kept; none dropped (K2) |

## 10. Open

- O1. A closed form of the cost with four or more terms (23:O1, unchanged: the
  filled terms add their number).
- O2. Lean statements of the counts (D15), of the C-I2 and C-I3 reachability
  criteria beyond the witness `i2_unfills` (proved in D11, computed), and of
  C-F4's results (proved in §3, computed).
- O3. A closed form for the number of shortest sequences to a result with two
  or more terms (computed per result within the bound).
- O4. Whether some map from an earlier seed other than the twenty-third,
  carrying each change to some change here, is one to one (23:O4, unchanged:
  filling gives such a map new room, and this derivation does not settle it).

## 11. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **Gain graphs, switching and balance (Harary; Zaslavsky).** As in the
  twenty-third, a result's assertions are an integer-gain graph on the
  complete directed graph with loops, up to switching and relabelling, and the
  result asserting nothing is the balanced class. A filled term that does not
  balance is a vertex whose loop carries a non-zero gain: a one-vertex
  certificate of imbalance. The finding that filled terms tell apart exactly
  the classes with an unbalanced loop at a filled vertex, and never those whose
  imbalance lies on digons or triangles, says that a vertex probe sees only the
  switching-invariant gains supported at one vertex; cycle gains through two or
  three vertices need a probe spanning them.
- **Vertex-coloured graphs and orbit counting (Burnside's lemma).** The
  results are pairs of a gain class and a two-colouring of the vertices,
  counted up to relabelling; the two-term closed forms are the count of such
  pairs, where a colouring that tells the two vertices apart breaks the
  symmetry exchanging them.
- **Monotone marks in rewriting systems.** Under C-I1 a filled term never goes
  away: an irreversible mark, like a token that can be merged but not consumed,
  which splits reachability into two classes; under C-I2 and C-I3 merging can
  consume it, and reachability is the twenty-third's.
- **Observability from partial measurements.** The twenty-third's record (a
  total count) and this seed's record (one bit per filled vertex, read on its
  loop) are two coarse observations of a class; neither determines which
  vertices witness its imbalance, and together they still miss the imbalance
  supported on digons and triangles.

What appears to be specific to this seed: that a change which only marks a term
already breaks two of the twenty-third's properties — the odd parity of every
change (identifying two marked terms moves the cost by two) and its
reachability (under C-I1 a mark never goes away) — while keeping its results
with no mark exactly, so that the twenty-third maps in one to one with a map
back that fails first at the smallest marked result; and that the record the
seed adds answers "which term" only for the imbalances that sit on a single
term.
