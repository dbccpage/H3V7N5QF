# Two relations, nothing given, pairs asserted together taken out, and raising: what follows

Twenty-third derivation. Input: `prompt/twentythird/seed_prompt.md`. Task:
`prompt/twentythird/prompt.md`. Claim IDs refer to
`paper/twentythird/claim_ledger.md`; an ID written `22:D4` refers to the
twenty-second derivation's ledger (`paper/twentysecond/claim_ledger.md`, paper
`paper/twentysecond/paper.md`), `9:D4` to the ninth's, `7:D11` to the
seventh's, `1:C4` to the first's — the twenty-second is the parent, and the
ninth, the seventh, the eighth and the first are cited through it; no other
derivation is read. Lean names without a namespace are in the namespace
`Twentythird` of the library `Twentythird` in `lean4_core/` (no `require`,
toolchain `leanprover/lean4:v4.33.1`); it imports the twenty-second's library
`Twentysecond` and nothing from `lean4/`. The axiom report for every theorem of
the library is `evidence/twentythird/lean_axioms.txt`: all 152 theorems rest on
`propext` and `Quot.sound` at most. Computed files are in
`evidence/twentythird/`, written by `python code/run_twentythird.py`.

Every notion below carries one source status: **given** (said by the seed),
**chosen** (a reading fixed here where the seed is silent or ambiguous; the
unchosen readings are listed), **derived** (proved), **computed** (output of
`code/`), **refuted** (proved impossible), **open**.

Where a result of an earlier derivation is used it is cited, and the ledger's
re-check column says how its proof was checked from this seed: *no change*
(the statement is about states and changes, which this seed does not touch),
*imported* (a theorem of the twenty-second's Lean library used as it stands:
its statement mentions nothing this seed changes, and Lean re-checks it when
this library is built), *re-proved* (proved afresh here or in
`lean4_core/Twentythird/` for this seed's results), or *computed again* (an
earlier exploration re-run beside this one and compared).

## 0. Findings in brief

1. **The seed** is the twenty-second's with its sameness sentence extended —
   two results that differ only by raising terms are also the same result — and
   one sentence added: raising a term `x` adds `xry` and `ysx` once for every
   other term `y`. Raising is not a change. States, the empty beginning and the
   four kinds of change are the twenty-second's (and the ninth's).
2. **Sameness.** Raising `x` moves the excess `e(u, v) = M_r(u, v) − M_s(u, v)`
   by `+1` at `(x, y)` and `−1` at `(y, x)` for every other `y`, and touches no
   loop (`excess_raise`). The sameness the three clauses generate is exactly:
   equally many terms and, after one rewriting, excesses differing by
   `g(x) − g(y)` at every ordered pair, for whole numbers `g(x)` (D1;
   `gen3_iff_same3`, in every writing `genW3_iff_sameW3`).
3. **The twenty-second's question.** There, a *state* asserting something can
   be the result asserting nothing on as many terms — exactly when it asserts
   every pair equally often in both relations (`a; ara asa`) — but a *result*
   whose plain state asserts something cannot: the excess is kept
   (`same22_nothing_iff`, `state_asserting_something_is_nothing22`).
4. **Which results are the result asserting nothing, here.** Exactly those whose
   loops have excess zero, whose two-way sums `e(x, y) + e(y, x)` are zero, and
   whose sums around three terms `e(x, y) + e(y, z) + e(z, x)` are zero
   (`same3_nothing_iff`, and in every writing `sameW3_nothing_iff`) —
   equivalently, whose excess is `g(x) − g(y)`. `a b; arb bsa` (raising `a`) is
   one; the twenty-second kept it apart (`raisedPair_nothing`,
   `raisedPair_not_nothing22`). For each number of terms there is exactly one
   such result, and from two terms on it holds infinitely many twenty-second
   results.
5. **Every other result carries what shows it is not**: a loop, two terms, or
   three terms whose sum is not zero, the same sum in every state of the result
   (`Same3.loop`, `Same3.twoWay`, `Same3.around`). No longer sum is ever
   needed; three terms can be: `a b c; arb bsa` has every loop and every
   two-way sum zero and its sum around `a b c` is one (`arcThree_not_nothing`).
6. **Changes of a result depend on the state taken.** Adding a term to two
   states of one result can give two results (`addTerm_not_respected`,
   `step_of_same3_fails`), from two terms on; identifying two terms can, from
   four terms on; adding an assertion never does, nor removing one from states
   that both assert it (D4). So, as the
   task says, the exploration performs changes on states and forms the results
   afterwards.
7. **Fewest changes** to a result: its terms plus the fewest assertions among its
   states, `n + min_g Σ |e(x, y) + g(x) − g(y)|` (D5; `cost3_iff`,
   `cost3_iff_min`, in every writing `cost3_every_writing`). With at most two
   terms: `n + Σ|loops| + |e(0, 1) + e(1, 0)|` (`cost3_two`); with three terms a
   closed form in the loops, the two-way sums and the sum around; in general the
   minimum is reached by raising sets of terms while the count falls, and the
   loops and two-way sums do not fix it (`loops_and_two_way_do_not_fix_the_cost`:
   costs 6 and 12 with the same loops and two-way sums). Every change changes
   the cost by an odd number (`Step.cost3_odd`); performed on a state asserting
   the fewest it raises it by at most one (`Step.cost3_le`); performed on
   another state of the same result, adding a term raises it by `2k + 1` for
   every `k` (`adding_a_term_raises_the_cost`).
8. **Which states of a result assert the fewest.** Exactly those asserting no
   pair in both relations from which raising no set of terms (then taking out
   the pairs asserted together) lowers the count (D7; `Fewest.plain`,
   `fewest_iff`; the general criterion proved in the paper, checked on every
   state explored). With two terms: no `xry` asserted together with `ysx`
   (`fewest_two_iff`). Up to three terms single terms suffice; with four they
   do not (`four_single_terms_do_not_find_the_fewest`). A result can have many
   such states — up to 22 within the two-term run.
9. **Relating the seed to the earlier ones.** None of the twenty-second, the
   ninth, the seventh or the first maps its states one to one into this seed's
   results: `a b; arb arb` and `a b; arb bra` are two seventh results, two ninth
   states and two twenty-second results in every writing, and one result here
   (`seventh_pair_apart`, `twentysecond_pair_apart`, `ninth_pair_apart`,
   `seventh_pair_merge`); for the first seed, `a b c; arb arc` and
   `a b c; bra cra` (`first_pair_apart`, `first_pair_merge`); and any map
   carrying additions to the same additions merges them
   (`carried_additions_merge3`). **The map back** goes to the twenty-second's
   results — a result's state asserting the fewest when that is one
   twenty-second result up to writing, "none" otherwise (`ReadBack3`). It
   returns `a b; arb` on itself (`readBack3_arb`), returns `a b` on
   `a b; arb bsa` (`readBack3_raisedPair`), answers "none" on `a b; arb arb`
   (`readBack3_none`), and answers on every result costing at most three
   (`readBack3_some_of_cost_le_three`): **the smallest results answered "none"
   cost four**; there are six, all with two terms, and the first in the
   explorations' order is `a b; bsa bsb`.
10. **What of the twenty-second holds here.** Reachability holds
    (`reach3_criterion`); the exchange of the two relations holds
    (`same3_swap_iff`, `cost3_swap`, `reach3_swap`); the twenty-second's cost of
    one of its results is the cost here exactly when that result asserts the
    fewest of the result it falls in, and exceeds it by an even number
    otherwise; "the results one change away do not depend on the state" fails
    (item 6); its counts fail (two-term results recording `t` assertions number
    `2t² + t + 1`).

## 1. What the seed gives

| ID | Given |
|---|---|
| G1 | Terms are written with letters. |
| G2⁗ | An assertion is written `xry` or `xsy`, where `x` and `y` are terms and `r` and `s` are the two relations; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one. |
| G3″ | Nothing is given: to begin with there are no terms and nothing is asserted. |
| G6 | A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. |
| G7 | Identifying two terms replaces both by one term in every assertion. |
| G11 | Attempt every change, fewest additions first. For every result, record how many terms and assertions it adds to what is given. |
| G12″ | Two results that differ only in how their terms are written, only by an `xry` and an `xsy` asserted together, or only by raising terms, are the same result. |
| G12a | Raising a term `x` adds `xry` and `ysx` once for every other term `y`. |
| G13 | Attempt 100 changes along each alternative, earlier changes on every alternative before later ones; do not invent a change; if too many, declare a finite bound, export the exact frontier, and prove what is complete within it. |
| G14 | Any outcome is valid. |

Against the twenty-second seed, G12″ replaces G12′ and G12a is new; every
other sentence is the twenty-second's, character for character (`git diff
--no-index --word-diff`; `research/twentythird/reading_the_seed.md`).

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| term, letter, assertion `xry` or `xsy`, the two relations, multiplicity | given (G1, G2⁗) | the ninth's |
| the state: terms and a multiplicity for each ordered pair in each relation | chosen (9:C1′, no change) | Lean `St` of the twenty-second (terms `0 … n − 1`, atoms counted) |
| the beginning: no terms, nothing asserted | given (G3″) | one beginning |
| change, four kinds; what identifying does | given (G6, G7) | on states |
| multiplicities of merged pairs add up; removing what is not asserted is not a change | chosen (9:C5⁗, no change) | |
| a pair asserted together | given (G12″), chosen (22:C-J1) | C-J2, C-J3 re-examined (D16) |
| raising a term | given (G12a), chosen (C-H1) | `raise`; unchosen C-H2, C-H3 |
| the excess `M_r(x, y) − M_s(x, y)` | derived (22:D1, imported) | `excess` |
| the sameness of results | given (G12″), derived (D1) | `Same3`, in every writing `SameW3` |
| result | given (G12″), derived (D1) | an excess function up to `g(x) − g(y)` and rewriting |
| the result asserting nothing on `n` terms | the task's words, derived (D2) | `same3_nothing_iff` |
| loop, two-way sum, sum around three terms | derived (D2) | kept by the sameness |
| a change of a result | chosen (C-X: a change of one of its states) | its outcome depends on the state (D4) |
| exploration of states, results formed afterwards | the task's words, chosen (C-E) | unchosen C-E′ computed again (K4) |
| round of a result | chosen: the first round in which one of its states is reached | equals the cost (D5) |
| cost (fewest changes) | derived (D5) | `Cost3` |
| states of a result asserting the fewest | the task's words, derived (D7) | `Fewest`, `Fewest3` |
| raising a set of terms | derived (D5, D7) | every term of the set raised once |
| what is recorded for a result | given (G11), chosen (C-R) | read on a state asserting the fewest; the same on all (D8) |
| bound, frontier | given (G13); bound on terms and rounds chosen (9:C8′) | §6 |
| an earlier seed mapped in; the map back | the task's words, derived (D9, D10) | `ReadBack3` |
| what a merge loses | the task's words, derived (D11) | `merge_loses3` |
| reachability between results | derived (D12) | `reach3_criterion` |
| the exchange of the two relations | derived (D13) | `same3_swap_iff` |
| counts of results | computed (K1), derived (D14) | two-term closed form, three-term count |
| the earlier statements, read on the states asserting the fewest | computed again (K6) | a new verdict: "depends on the state" |
| names `a`, `b`, `arb`, `bra`, what is given | — (not in the seed) | without object, as under the ninth |

## 3. Readings that had to be chosen

Inherited without change from the twenty-second (22:C-inh: 9:C1′, C3, C5⁗, C6,
C8′, C9; 22:C-J1): the state, no cap on letters, what a change is and that
merged multiplicities add up, the order of the attempts (identifications,
removals in `r`, in `s`, a term, additions in `r`, in `s`), the bound on terms
and rounds, `r` and `s` writing assertions, and what "an `xry` and an `xsy`
asserted together" means. Each is about states or changes, or about a clause
this seed repeats word for word (re-check: no change).

**C-H1 (chosen). Raising.** Raising `x` gives the state with one more `xry` and
one more `ysx` for every term `y ≠ x` of the state raised (`raise`). "Differ
only by raising terms": one state is the other with some of its terms raised,
each some number of times. "Are the same result" makes the sameness an
equivalence: the one generated by the three clauses (`Gen3`; D1 proves what it
is).

**C-H2 (unchosen, kept, computed).** "Raising terms" as raising every term at
once. Raising every term once adds, at every ordered pair of two different
terms, one `xry` (from raising `x`) and one `xsy` (from raising `y`): pairs
asserted together (`raise_all_gen`). So C-H2 adds nothing to the
twenty-second's sameness, and its results are the twenty-second's: 673 against
C-H1's 226 at two terms and eight rounds (`readings.json`).

**C-H3 (unchosen, eliminated by proof).** Each term raised at most once. Raising
a term of a state that is itself that term raised once is raising it twice, and
the sameness is transitive, so the equivalence generated is C-H1's.

Set aside, with the words that refuse them: raising also adds `xrx` and `xsx`
(refused by "every other term"); raising is a change (refused by "Nothing else
is a change").

**The twenty-second's readings of "asserted together", with raising.** C-J1 is
kept (chosen). Under C-J2 (letters as placeholders: any `xry` with any `usv`),
raising adds `n − 1` assertions in each relation, so it keeps C-J2's mark
`(n, Σ M_r − Σ M_s)` and C-J2 with raising has C-J2's results (computed:
raising keeps the mark on every state of the readings run). Under C-J3 (only
two different terms), raising touches no loop, so a result keeps both loop
multiplicities and the excess between two different terms up to `g(x) − g(y)`;
its cost is the terms, both loop multiplicities and the fewest `Σ|e|` off the
loops; computed at two terms and eight rounds: 419 results, rounds equal to
that cost (D16).

**C-X (chosen). A change of a result** is a change performed on one of its
states; its outcome is the result of the outcome state. The twenty-second
proved that under its sameness the results one change away do not depend on
the state taken (22:D2). Here they do (D4), so which state a change is
performed on matters, and the relation "one change away" between results is
the union over the states.

**C-E (chosen). The exploration.** As the task says: changes are performed on
states, as the twenty-second's exploration does, and the results are formed
afterwards. The twenty-second's exploration is run as it stands — its
alternatives are its own results, i.e. its plain states up to writing, each
change performed on that state — and the states it reaches are grouped by this
seed's sameness; the round of a result is the first round in which one of its
states is reached. **C-E′ (unchosen, computed again):** the ninth's exploration
of every state, grouped the same way. K2 proves both give every result at the
round of its cost (D5); K4 confirms it within the ninth's rounds.

**C-R (chosen). What is recorded for a result**: its terms, and the assertions
in `r` and in `s` of a state of it asserting the fewest. D8 proves these are the
same for every such state. Unchosen: the counts of the state a sequence
reached (a record of a sequence, not of a result; kept in the attempt log as
the state reached).

## 4. What follows

Proofs are in Lean where a Lean name is given; otherwise the proof is here.

**D1. Sameness: excesses differing by `g(x) − g(y)`.** Raising `x` puts one
`⟨r, x, y⟩` and one `⟨s, y, x⟩` in front of the list for every `y < n`,
`y ≠ x` (`raiseAtoms`); between terms that are there the excess moves by
`[u = x] − [v = x]` (`excess_raise`), and raising every term `x` `f(x)` times
moves it by `f(u) − f(v)` (`excess_raiseTo_all`). `Same3 G H` says: equally many
terms and `e_G(x, y) = e_H(x, y) + g(x) − g(y)` for some `g`. It is an
equivalence (`Same3.refl`, `Same3.symm`, `Same3.trans`), coarser than the
twenty-second's (`Same.same3`), and it is exactly the equivalence the three
clauses generate at a fixed writing (`gen3_iff_same3`): one way, each clause
keeps the form; the other way, `g` moved up to be at least zero is a number of
raisings of each term (`lift_eq`), after which the two states have the same
excess and are joined by pairs asserted together (22:D1, imported). With
rewriting: the excess is carried along (`excess_rename`), `Same3` too
(`Same3.rename`), and `SameW3` — some rewriting, then `Same3` — is an
equivalence (`SameW3.symm`, `SameW3.trans`) and exactly what the clauses and
rewriting generate (`genW3_iff_sameW3`). A mark of a result: the excess table
made zero at every pair `(x, 0)`, least over the rewritings (`result_key` in
`code/twentythird/state.py`). Computed: on every state of one and two terms
with at most two assertions per relation (234 states), joining each to its
rewritings, to itself with one more pair asserted together and to itself raised
at a term, among the states of at most six per relation, gives exactly the
classes of the mark (5 and 33; `summary.json`, `generated_sameness`) — with two
terms six is enough, two same states differing by raising one term at most
four times.

**D2. The result asserting nothing, and what shows a result is not it.** The
loops' excesses, the two-way sums `e(x, y) + e(y, x)` and the sums around three
terms `e(x, y) + e(y, z) + e(z, x)` are the same in every state of a result
(`Same3.loop`, `Same3.twoWay`, `Same3.around`; the moves `g(x) − g(y)` cancel
around every closed walk, and a rewriting only moves the terms). A state is the
result asserting nothing on its terms exactly when all of them are zero
(`same3_nothing_iff`): given that, `g(x) = e(x, 0)` works, since the sum around
`x, y, 0` and the two-way sum at `0, x` give `e(x, y) = e(x, 0) − e(y, 0)`. The
same holds writing included (`sameW3_nothing_iff`). So **every other result
carries a loop, two terms or three terms whose sum is not zero**, the same sum
in every state of it; `code/twentythird/state.py`'s `nothing_certificate` finds
the first. Three terms can be needed: `a b c; arb bsa` has every loop and every
two-way sum zero, and its sum around `a b c` is one (`arcThree_not_nothing`).
With `n` terms there is exactly one result asserting nothing, at the round `n`;
its states include every state raised, any number of times, at any terms — so
infinitely many twenty-second results with two terms or more. Computed: in
every run the certificate is missing exactly on the results asserting nothing,
and every state reached has the sums of its result (`nothing_mismatch` empty).

**D3. The twenty-second's question.** In the twenty-second a state is the
result asserting nothing on its terms exactly when its excess is zero at every
pair (`same22_nothing_iff`): a state asserting something can be
(`state_asserting_something_is_nothing22`: `a; ara asa`), and exactly the states
that assert every pair equally often in both relations are; a result whose
plain state asserts something cannot. Here, results the twenty-second kept
apart from it join it: `a b; arb bsa` is the result asserting nothing on two
terms here (`raisedPair_nothing`) and not there (`raisedPair_not_nothing22`).

**D4. Which changes respect the sameness.** A change of a result is performed on
a state of it (C-X). Adding an assertion moves the excess by one at one pair,
whatever state it is performed on, so the outcomes on two states of one result
are one result; so does removing an assertion from two states that both assert
it; and removing `xqy` has the result of adding the other relation at that pair
(22:D2, imported). Adding a term does not: `a b` and `a b; arb bsa` are one
result, and with a term added the second has its sum around the three terms one
(`addTerm_not_respected`); so the twenty-second's "a change of any state of a
result has the outcome of a change of any other state" fails
(`step_of_same3_fails`). With one term raising adds nothing (there is no other
term), so adding a term respects the sameness there, and only there. Identifying
two terms respects it with at most three terms and not with four: merging `u`
and `v` turns a difference `g(x) − g(y)` into one whose loops are zero (a pair
`(x, x)` receives `g(x) − g(x)`, and the merged pairs' contributions cancel two
by two) and whose two-way sums are zero; on at most two terms that is again a
difference `h(x) − h(y)`; on three terms or more the sums around three terms
can fail — `a b c d` and `a b c d; cra crb crd asc bsc dsc` (raising `c`) are
one result, and identifying `a` with `b` in each gives `a b c` and
`a b c; bra(2) brc asb(2) csb`, whose sum around the three terms is one
(`given.json`). Computed: in the five-term run, 38 379 outcomes of additions
and identifications on results with at most three terms, performed on each
state of the result reached, rewritten to one writing, agree
(`respect_mismatch` empty).

**D5. Fewest changes.** Let the cost of a result be the fewest changes from the
empty state to some state of it (`Cost3`, unique: `Cost3.unique`; a mark of the
result: `Cost3.congr`). Every state is reached, the fewest changes to a state
being the twenty-second's `phi` of its plain part (22:D4, imported), so the cost
is the least `phi` among the states of the result (`cost3_iff`). `phi` is the
terms plus `Σ |e(x, y)|` over the pairs of terms (`phi_eq_sum`), so **the cost is
`n + min_g Σ |e(x, y) + g(x) − g(y)|`** (`cost3_iff_min`), the same in every
writing (`cost3_every_writing`).
(a) *Lower bound.* Each pair of different terms `x, y` contributes at least
`|e(x, y) + e(y, x)|`, so the cost is at least `n` plus the loops' and the
two-way sums' absolute values; with at most two terms that is the cost:
`n + |e(0, 0)| + |e(1, 1)| + |e(0, 1) + e(1, 0)|` (`cost3_two`). More generally
any set of closed walks using each ordered pair at most once bounds it: the sum
along each is kept, and `|Σ| ≤ Σ| |`; with three terms both ways round
(`phi_ge_around`, `cost3_three_ge`).
(b) *Three terms, closed form.* A state of the result is fixed by
`e(0, 1) = a`, `e(1, 2) = b`, `e(2, 0) = c` with `a + b + c = T` (the sum around,
kept), the backward excesses being `S_i − a`, … (the two-way sums `S_i`, kept).
`|a| + |S − a| = |S| + 2·dist(a, [min(0, S), max(0, S)])`, and the least total
distance of three whole numbers adding up to `T` from three intervals is the
distance of `T` from the sum of the intervals. So the cost is
`3 + Σ|loops| + Σ|S_i| + 2·dist(T, [−N, P])`, `P` and `N` the positive and
negative parts of the two-way sums added up (`cost_closed`). The loops and
two-way sums alone do not fix it: `a b c; arb brc cra` and
`a b c; arb(2) brc(2) cra(2) asc bsa csb` have the same loops and two-way sums
and cost 6 and 12 (`loops_and_two_way_do_not_fix_the_cost`).
(c) *In general: raising sets of terms.* Raising every term of a set `X` once
is `g + 1_X`. **If raising no set of terms lowers `F(g) = Σ |e + g(x) − g(y)|`,
then `F(g)` is the least.** Proof. Suppose not; among the least `g*` take one
with `h = g* − g` of least spread `max h − min h` (`h` is not constant: a
constant changes nothing). Let `X` be the terms where `h` is largest (not all).
For a pair `x ∈ X`, `y ∉ X`, with `d = g(x) − g(y)` and `d* = g*(x) − g*(y)`,
`d + 1 ≤ d*`; each pair's term `ψ(d) = |e(x, y) + d| + |e(y, x) − d|` is convex
in `d`, so `ψ(d + 1) + ψ(d* − 1) ≤ ψ(d) + ψ(d*)`; pairs inside or outside `X` do
not move. Adding up, `F(g + 1_X) + F(g* − 1_X) ≤ F(g) + F(g*)`. As
`F(g* − 1_X) ≥ F(g*)`, `F(g + 1_X) ≤ F(g)`; by hypothesis equality, so
`g* − 1_X` is least too, with smaller spread — a contradiction. ∎ So raising
sets while the count falls (`descend`) ends at the fewest; the same inequality,
with both `g` and `g*` least, shows that the least tables are joined by raisings
of sets that keep the count (`least_tables`). A least `g` has no gap between two
neighbouring values larger than every excess between two terms (raising the
lower part would lower the count), which bounds a search (`search_box`).
Computed: in every run the round of every result is its cost by descent
(`round_not_cost` empty); the closed forms agree on every result of at most
three terms, and a search over every `g` in the box agrees on the 2 401 results
of at most three terms of the five-term run (`closed_form_mismatch` empty).

**D6. Parity, and how far one change moves the cost.** Raising adds `2(n − 1)`
atoms (`raise_size`) and a pair asserted together two, so the parity of the
size is a mark of the result (`Gen3.size_parity`, `Same3.size_parity`); the cost
has that parity (`Cost3.parity`); every change moves the size by one (22:D4,
imported), so **every change changes the cost of the result by an odd number**
(`Step.cost3_odd`) and none returns a state to its own result
(`Step.not_same3`). A change performed on a state asserting the fewest raises
the cost by at most one (`Step.cost3_le`). Performed on another state of the
same result, adding a term can raise it by `2k + 1` for every `k`: `a b` raised
at `a` `k` times costs 2, and with a term added costs `3 + 2k`, both sums
around the three terms being `±k` (`adding_a_term_raises_the_cost`). Computed
(`summary.json`, `how_each_kind_moves_the_cost`), in the five-term run's 44 890
changes: adding a term `+1` 1 534 times, `+3` 121, `+5` 7; adding an assertion
`+1` 26 652, `−1` 6 020; removing `+1` 260, `−1` 4 692; identifying `−1` 4 042,
`−3` 1 413, `−5` 149. In the three-term run adding a term raises it by up to
seven; in the two-term run by one only (from one term, where adding a term
respects the sameness). Every change moves it by an odd number and every
change from a state asserting the fewest by at most one (`change_mismatch`
empty).

**D7. Which states of a result assert the fewest.** A state asserting the
fewest asserts no pair in both relations (`Fewest.plain`: taking the pair out
keeps the result), and a state is one exactly when that holds and its `phi` is
the cost (`fewest_iff`). By D5(c), **a state asserts the fewest of its result
exactly when it asserts no pair in both relations and raising no set of terms
(then taking out the pairs asserted together) lowers its count**. With at most
three terms every set is a term or all the terms but one (raising those is
lowering the one, up to raising every term, which is pairs asserted together),
so single terms suffice; with two terms the condition reads: the two excesses
between the terms have the same sign — no `xry` asserted together with `ysx`
(`fewest_two_iff`). With four terms single terms do not suffice:
`a b c d; crd asb asc dsb dsc` asserts five; raising one term, or three, never
lowers that; raising `a` and `d` lowers it to three
(`four_single_terms_do_not_find_the_fewest`; `given.json` found it as the first
such table of weight at most five). A result can have several such states:
with two terms and `e(0, 1) + e(1, 0) = k`, every split `(j, k − j)` is one, so
`⌊k/2⌋ + 1` up to writing. Computed: in every run the states of a result reached
at its round are exactly those found by raising sets from one of them
(`fewest_mismatch` empty), and the criterion (sets; single terms up to three
terms; the sign rule with two terms) agrees with the rounds on every state
reached (`characterization_mismatch` empty); at most 6, 10 and 22 such states
per result in the three runs; 3 902, 7 538 and 608 results have exactly one.

**D8. What is recorded.** Reading C-R: the terms, and the assertions in `r` and
in `s` of a state asserting the fewest. All such states assert the same number
(the fewest); `Σ M_r − Σ M_s = Σ e` on a state asserting no pair in both
relations, and `Σ e` over all ordered pairs is kept by raising (`Σ (g(x) − g(y))
= 0`) and by pairs asserted together; so the split `((w + Σe)/2, (w − Σe)/2)` is
the same for all of them. Computed: every state asserting the fewest reached
agrees (`record_mismatch` empty). The sum of the record is the cost minus the
terms.

**D9. Relating this seed to the earlier ones: none maps one to one.** The
seventh's states (one relation; the twenty-second's `St7`, read as asserting
nothing with `s` by `ofR`, its changes carried to changes of the same kind:
22:D8, imported): `a b; arb arb` and `a b; arb bra` are two seventh results in
every writing (`seventh_pair_apart`: every pair of the first rewritten is one
pair, the second has two) and one result here (`seventh_pair_merge`: the second
raised at `a`, then `bra bsa` taken out). They are two twenty-second results
in every writing (`twentysecond_pair_apart`, through the twenty-second's
one-to-one map of the seventh, imported) and two ninth states
(`ninth_pair_apart`). The first seed's states (one relation, each pair at most
once, no `xrx`; 1:C4, names kept or not): `a b c; arb arc` and `a b c; bra cra`
are such states (`first_pair_states`), different in every writing — so with the
names forgotten or kept (`first_pair_apart`) — and one result here, the first
being the second raised at `a` (`first_pair_merge`). The eighth's states carry
names results here do not have, as the twenty-second found (22:D8, no change).
Moreover **no map carrying the empty state to the empty state and each addition
to the same addition** (up to the twenty-second's sameness) keeps the seventh
pair apart (`carried_additions_merge3`). Computed: the seventh's results within
each run merge (799 into 636 results in the five-term run, 2 232 into 1 291,
7 539 into 1 247); the first merge in round order is at round 4
(`a b; bra brb` and `a b; arb brb`; `seventh_mismatch` empty). Whether some
other map, carrying each change to *some* change, is one to one is left open
(O4).

**D10. The map back.** From this seed's results to the twenty-second's results:
`ReadBack3 G T` — `T` is a state of the result of `G` asserting the fewest, and
every other such state is `T` in some writing; "none" when there is no such `T`.
It answers at most one twenty-second result up to writing
(`ReadBack3.functional`) and depends on the result only (`ReadBack3.congr`).
*On mapped states* (the twenty-second's results): it returns the original
exactly when the original asserts the fewest of its result and every other such
state is it in some writing (`readBack3_self_iff`), and whatever it answers
asserts the fewest, at the result's cost (`readBack3_answer_cost`) — so on
`a b; arb` it returns `a b; arb` (`readBack3_arb`); on a twenty-second result
that does not assert the fewest it returns another one or "none" — on
`a b; arb bsa` it returns `a b` (`readBack3_raisedPair`). It answers "none" on
`a b; arb arb`, whose states `a b; arb arb` and `a b; arb bra` both assert the
fewest (`readBack3_none`). **Every result costing at most three changes has an
answer** (`readBack3_some_of_cost_le_three`: with no terms, three terms, or one
term there is one state asserting the fewest; with two terms and one
assertion the loops and the two-way sum decide the assertion up to exchanging
the two terms), so **the smallest results answered "none" cost four**. There
are six at cost four, all with two terms: `a b; bsa bsb`, `a b; bsa(2)`,
`a b; brb bsa`, `a b; bra bsb`, `a b; bra brb`, `a b; bra(2)` (written as their
first state reached); the first in the explorations' order is `a b; bsa bsb`,
whose states asserting the fewest are `a b; bsa bsb` and `a b; asb bsb`.
Computed: the map back from the exploration equals the map back from one state
by raising sets (`read_back_mismatch` empty); on the twenty-second results of
the five-term run it returns the original 3 902 times, another 419 times, and
"none" 2 847 times.

**D11. What a merge of the twenty-second's results loses.** When this seed
makes two twenty-second results one, it loses the excess at each ordered pair
beyond what the loops, the two-way sums and the sums around three terms fix —
the `g` — and with it the twenty-second's plain state, the twenty-second's cost,
and the excess at each pair: `a b; arb bsa` and `a b` are one result here and
two twenty-second results in every writing, with twenty-second costs 4 and 2
and excesses 1 and 0 at `(a, b)` (`merge_loses3`). Kept: the terms, the loops,
the two-way sums, the sums around, `Σ e`, the parity of the size, the cost and
what is recorded (D2, D6, D8). Computed: 7 168, 39 526 and 86 201 twenty-second
results merge into 4 973, 15 671 and 7 914 results; up to 7, 12 and 22 in one.

**D12. Reachability: the twenty-second's criterion holds.** A result reaches
another exactly when the other has a term or the first is the empty state
(`reach3_criterion`): the twenty-second's criterion (22:D9, imported), which is
decided by the number of terms, kept by every clause of this seed's sameness.
So it does not depend on which state of the first result the changes start
from (`reach3_of_same3`), results with a term reach each other both ways
(`reach3_mutual`), and the empty result is never returned to. Computed: within
three terms and four rounds, 29 results, 813 of the 841 ordered pairs
reachable, the 28 others into the empty result; the criterion agrees with a
search along the changes of every state reached (`reach_mismatch` empty).

**D13. The exchange of the two relations.** Exchanging `r` and `s` negates every
excess (22:D10, imported) and turns `g` into `−g`, so it keeps this seed's
sameness both ways (`same3_swap_iff`), the cost (`cost3_swap`) and reachability
(`reach3_swap`): a symmetry of results, cost and reachability, as in the
twenty-second. Computed: every result's exchange is a result of the same round
with as many states asserting the fewest, its record's relations exchanged
(`exchange_mismatch` empty).

**D14. Counting the results.** With one term raising adds nothing: one result
recording no assertion, two for every `t ≥ 1` (as in the twenty-second). With
two terms a result is the two loops' excesses and the two-way sum, up to
exchanging the loops (the exchange of the two terms); its fewest assertions is
`t = |d0| + |d1| + |S|`. The points of `Z³` at that distance number `4t² + 2`
(for `t ≥ 1`), the exchange fixes the `2t` with `d0 = d1`, so **the two-term
results recording `t` assertions number `2t² + t + 1`** (`t ≥ 1`; one for
`t = 0`): 1, 4, 11, 22, 37, 56, 79, …, and the results of round `r` with at most
two terms are `[r = 0] + [r ≥ 1]·one(r − 1) + [r ≥ 2]·two(r − 2)` = 1, 1, 3, 6,
13, 24, 39, 58, 81, … (`2r² − 7r + 9` from `r = 3` on), of order `2r²`, where
the twenty-second's were of order `(4/3)r³`; within the seed's 100 rounds,
642 248 results. With three terms a result is its three loops, its three
two-way sums and its sum around `0, 1, 2` (complete: D2's argument), up to the
rewritings, a rewriting that turns the terms around the other way sending the
sum around `T` to `ΣS − T`; counted from those numbers with D5(b)'s cost:
1, 4, 29, 136, 497, 1 508, 3 941, 9 082 recording 0 … 7 assertions
(`counts.csv`). With more terms the results are counted by listing every
excess table of weight at most `t` and grouping by the mark (a state asserting
the fewest is among them): four terms 1, 4, 35, 272, 1 916; five terms 1, 4,
35, 304. Without a bound on terms the results of round `r` number 1, 1, 3, 7,
18, 58, 215, 867 (`r ≤ 7`). Each count is independent of the explorations and
equals them (`count_mismatch`, `two_term_mismatch` empty). Not in Lean.

**D15. Undoing.** On two terms, adding `xry` and then `ysx` is raising `x`, so it
gives back the result before both (`two_additions_undo3`): two additions of
two different pairs undo each other, which the twenty-second's sameness, at a
fixed writing, allowed only for the same pair in the two relations (22:D5).
With three terms or more a single term's raising takes `2(n − 1)` additions.

**D16. The unchosen readings.** C-H2: raising every term once is pairs asserted
together (`raise_all_gen`); its results are the twenty-second's (computed: at
two terms and eight rounds, 673 against 226, per round 1, 1, 3, 6, 20, 46, 102,
182, 312 against 1, 1, 3, 6, 13, 24, 39, 58, 81). C-H3 gives C-H1's sameness
(§3). C-J2 with raising: raising keeps `(n, Σ M_r − Σ M_s)` (computed on every
state of the readings run and each raising of it). C-J3 with raising: 419
results at two terms and eight rounds, per round 1, 1, 3, 7, 16, 33, 63, 111,
184 — more than C-H1 (the loops keep both multiplicities), fewer than the
twenty-second's C-J3 (1 081, 22:D15); every round equals the cost of D16's
formula, computed by grouping the ninth's exploration of states
(`readings_mismatch` empty).

**D17. Statements about the asserting.** The earlier forty-two statements
(9:D14, read by the twenty-second on the plain state, 22:D16) are read here on
every state of a result asserting the fewest, with three verdicts: holds (on
all), fails (on all), depends on the state (on some and not others). None holds
in every explored result; twenty-one depend on the state in the five-term run
(for example "no assertion is asserted more than once", on `a b; bra(2)`, whose
states asserting the fewest are `a b; bra(2)` and `a b; arb bra`), which the
twenty-second could not show; this seed's own statements "the result asserting
nothing" and "unchanged by the exchange" do not follow either; "one state
asserting the fewest" fails first on `a b; bsa bsb` (K6).

## 5. What does not follow

Each item has two witnesses, or a proof.

- **N1.** That the twenty-second's excess, plain state or cost is kept by the
  sameness: `a b; arb bsa` and `a b` are one result, with excesses 1 and 0 at
  `(a, b)` and twenty-second costs 4 and 2 (`merge_loses3`); `a b` and
  `a b; arb` are two results.
- **N2.** That loops and two-way sums show every result other than the one
  asserting nothing: `a b c; arb bsa` has them all zero and is not it
  (`arcThree_not_nothing`); with two terms they do (D2).
- **N3.** That a change of a result has one outcome as a result: adding a term
  to `a b` and to `a b; arb bsa` (`addTerm_not_respected`); adding an assertion
  always has one (D4).
- **N4.** That one change moves the cost by at most one: adding a term to
  `a b; arb(k) bsa(k)` moves it by `2k + 1` (`adding_a_term_raises_the_cost`);
  from a state asserting the fewest, at most one (`Step.cost3_le`).
- **N5.** That the loops and two-way sums fix the cost: costs 6 and 12 with the
  same ones (`loops_and_two_way_do_not_fix_the_cost`); with two terms they do
  (`cost3_two`).
- **N6.** That raising single terms finds the fewest: with four terms it does
  not (`four_single_terms_do_not_find_the_fewest`); with at most three it does
  (D7).
- **N7.** That a result has one state asserting the fewest: `a b; arb arb` has
  two up to writing (`readBack3_none`); `a b; arb` has one (`readBack3_arb`).
- **N8.** That an earlier seed maps in one to one (D9).
- **N9.** That the map back returns the original on every mapped state: on
  `a b; arb bsa` it returns `a b` (`readBack3_raisedPair`); on `a b; arb` the
  original (`readBack3_arb`).
- **N10.** Anything about the asserting (D17); some statements do not even
  have one truth value on a result.
- **Refuted** (proved impossible): a result other than the one asserting
  nothing with every loop, two-way sum and sum around three terms zero (D2); a
  sum kept by the sameness changing between two states of one result (D2); a
  change that keeps the parity of the cost, or returns a state to its own result
  (D6); fewer changes to a result than `n + min_g Σ|e + g(x) − g(y)|` (D5); a
  change from a state asserting the fewest raising the cost by more than one
  (D6); a state asserting the fewest that asserts a pair in both relations
  (D7); a result costing at most three answered "none" by the map back (D10);
  the seventh's, ninth's, twenty-second's or first's pairs of D9 kept apart
  here (D9).

## 6. The exploration

**Protocol** (reading C-E). The twenty-second's exploration from the empty
state, as it stands: round by round, every change of every state first reached
in the round before — its plain state, least writing — fewest additions first,
bounded in terms and rounds; then its states are grouped by this seed's
sameness. Three runs: 5 terms and 8 rounds, 3 terms and 10 rounds, 2 terms and
24 rounds (the twenty-second's bounds; each completed in minutes here). Beside
each, the ninth's exploration at the same bound on terms with 8, 9 and 12 rounds
(C-E′) and the seventh's at the same bounds. A full attempt log at 2 terms and 3
rounds; reachability at 3 terms and 4 rounds; the generated sameness at one and
two terms; the readings at 2 terms and 8 rounds. Files: `results_*.csv`,
`added_*.csv`, `frontier_*.csv`, `rounds_*.csv`, `follows_*.csv`,
`reach_bound3_rounds4.csv`, `attempts_bound2_rounds3.jsonl`, `counts.csv`,
`given.json`, `readings.json`, `summary.json` (every check; the eighteen
disagreement lists of `RaisingCheck`, all empty), `lean_axioms.txt`,
`MANIFEST.sha256`.

**K1. Results within the bounds.**

| run | twenty-second states reached | results | by terms | results answered "none" | results with one state asserting the fewest |
|---|---|---|---|---|---|
| 5 terms, 8 rounds | 7 168 | 4 973 | 1 / 15 / 210 / 2 175 / 2 228 / 344 | 1 071 | 3 902 |
| 3 terms, 10 rounds | 39 526 | 15 671 | 1 / 19 / 453 / 15 198 | 8 133 | 7 538 |
| 2 terms, 24 rounds | 86 201 | 7 914 | 1 / 47 / 7 866 | 7 306 | 608 |

In every run: every round has a new result; the round of every result is its
cost; the counts equal the independent counts; with at most two terms the rounds
follow the closed form; rounds `0 … N` agree with the unbounded count.

**K2. Completeness within the bound; the frontier.** Let the bound be `N` terms
and `R` rounds. A result with at most `N` terms and cost at most `R` has a state
asserting the fewest, which asserts no pair in both relations and so is a
twenty-second result with the same terms and twenty-second cost equal to the
cost; the twenty-second's exploration reaches it at that round (22:D13,
imported). So every such result is formed, at the round of its cost, and its
states asserting the fewest are exactly its states reached in that round. The
frontier is the twenty-second's: every attempt adding a term to a state with `N`
terms (40, 12 761 and 71 875 entries; `frontier_*.csv` gives each state and its
result), and the results of round `R`.

**K3. The map back** (D10): first "none" `a b; bsa bsb` at round 4 in every
run.

**K4. The ninth and the seventh, computed again.** C-E′: the ninth's
exploration of every state, grouped, gives exactly the results here within its
rounds, at the same rounds (4 973 from 10 416 ninth states; 6 450 from 25 965;
860 from 22 021; `ninth_mismatch` empty). The seventh's results merge (D9).

**K5. The twenty-second's results merged** (D11).

**K6. Statements** (D17, `follows_*.csv`).

**K7. Reachability** (D12). **K8. Readings** (D16, `readings.json`).
**K9. Changes and the cost** (D6).

**Reproducibility.** `python code/run_twentythird.py` rewrites every computed
file; `--check` regenerates into a temporary folder and compares byte for byte;
`python code/lean_report_twentythird.py` builds `lean4_core/` and rewrites
`lean_axioms.txt`, refusing any axiom other than `propext` and `Quot.sound`.

## 7. The task's questions

- **In the twenty-second, can a result with something asserted be the same as a
  result with nothing asserted on as many terms?** A state, yes — exactly when it
  asserts every pair equally often in both relations; a result whose plain state
  asserts something, no: the excess is kept (D3).
- **Here, which results are?** Exactly those whose loops, two-way sums and sums
  around three terms are all zero — whose excess is `g(x) − g(y)` (D2).
- **Does each other result carry something that shows it is not?** Yes: a loop,
  two terms or three terms with a non-zero sum, the same in every state of it
  and in every writing; three terms are sometimes needed, never more (D2).
- **The fewest changes to each result**: `n + min_g Σ |e(x, y) + g(x) − g(y)|`;
  closed forms with at most three terms; reached by raising sets of terms (D5).
- **Which of its states assert the fewest**: those asserting no pair in both
  relations from which raising no set of terms lowers the count; with two terms,
  those with no `xry` together with `ysx`; possibly several (D7).
- **An earlier seed mapped in one to one**: none of the twenty-second, the ninth,
  the seventh or the first (D9). **The map back** to the twenty-second's results
  answers "none" first at cost four (D10). **What the merge loses**: the excess
  at each pair beyond the kept sums, with the twenty-second's plain state and
  cost (D11).

## 8. What of the twenty-second holds here, and where it does not

- **Cost** (22:D4, `n + Σ|excess|`): the twenty-second's cost of one of its
  results is the cost here of the result it falls in exactly when it asserts the
  fewest of that result; otherwise it exceeds it by an even number
  (`a b; arb bsa`: 4 against 2). In the five-term run, 4 739 of the 4 973
  results hold no reached twenty-second result of the other kind. "A shortest sequence is additions only"
  holds (it ends at a state asserting the fewest, 22:D4). "Every change moves the
  cost by an odd number" holds (`Step.cost3_odd`); "a change raises it by at most
  one" holds from a state asserting the fewest and fails from other states
  (D6).
- **Reachability** (22:D9): holds (D12).
- **The exchange** (22:D10): holds (D13).
- **The sameness and the plain state** (22:D1): coarser; the plain state is no
  longer unique to a result (D7).
- **A change of a result does not depend on the state** (22:D2): fails for
  adding a term (from two terms) and identifying (from four terms); holds for
  adding and removing assertions (D4).
- **Undoing** (22:D5): extended — two additions of different pairs undo each
  other on two terms (D15).
- **The seventh maps in one to one** (22:D8): fails (D9).
- **The counts** (22:D11): fail; new closed forms (D14). **One shortest sequence
  per one-term result** (22:D12): holds (raising adds nothing on one term; the
  one-term results are the twenty-second's).
- **Nothing about the asserting holds in every result** (22:D16): holds, and
  some statements now depend on the state (D17).

## 9. Alternatives: kept, or eliminated by proof

| Alternative | Kept / eliminated |
|---|---|
| C-H1 / C-H2 / C-H3 readings of raising | C-H1 chosen; C-H2 kept and computed (the twenty-second's results); C-H3 eliminated (same equivalence, §3) |
| raising adds loops; raising is a change | set aside: refused by "every other term", "Nothing else is a change" |
| C-J1 / C-J2 / C-J3, with raising | C-J1 chosen; C-J2 kept (C-J2's results, raising keeps its mark); C-J3 kept and computed (D16) |
| C-E / C-E′ (the twenty-second's states / the ninth's states) | the same results and rounds (K2, K4) |
| C-X: a change performed on one state of a result | chosen; which state matters (D4) |
| C-R: record on a state asserting the fewest / on the state a sequence reached | the first chosen, well defined (D8); the second in the attempt log |
| a bound on terms alone | eliminated: infinitely many results within it (the loop excess alone) |
| every result within the bound, up to rewriting | kept; none dropped (K2) |
| names, `arb`, `bra`, what is given | without object, as under the ninth |

## 10. Open

- O1. A closed form of the cost with four or more terms. The cost is computed
  by raising sets (D5(c)); the best bound from closed walks using each ordered
  pair at most once (D5(a)) is not shown here to equal it in general.
- O2. Lean statements of the set criterion (D5(c), D7 in general), of the
  three-term closed form (D5(b)), of which changes respect the sameness beyond
  the witnesses (D4), and of the counts (D14): proved in the paper and checked
  by computation.
- O3. A closed form for the number of shortest sequences to a result with two
  or more terms: computed per result within the bound (`results_*.csv`).
- O4. Whether some map from an earlier seed's states, carrying each change to
  some change here (not necessarily of the same kind), is one to one: D9 refutes
  the maps carrying additions to the same additions, not every map.

## 11. Nearest known results, and how the findings differ

References are from memory; no network was used, so they are unchecked.

- **Gain graphs and switching (Zaslavsky; for signs, Harary's balance
  theorem).** A result here is an integer-gain graph on the complete directed
  graph with loops — the excess on each arc — up to switching at vertices
  (raising a term is switching by one) and relabelling. D2 is the balance
  theorem for additive integer gains: a gain function is switching-equivalent to
  zero exactly when every cycle has gain zero, and on a complete graph the
  triangles, the digons and the loops suffice. Differences: the two directions
  of a pair are separate arcs, so a digon is a cycle with its own sum; loops
  carry gains no switching moves; and the question asked of a class is its
  least total absolute gain.
- **Coboundaries and Kirchhoff's voltage law.** Raising terms adds the
  coboundary of a whole-number function on the terms; the results are the
  functions on arcs modulo coboundaries; D2 is the discrete statement that a
  function on arcs is a coboundary (a potential difference) exactly when its sum
  around every cycle vanishes.
- **The minimum-cost tension problem, network-flow duality, and discrete
  convex analysis (Murota's L♮-convex functions).** D5's cost is an `ℓ¹`
  distance from the excess to the space of potential differences — a
  minimum-cost tension problem, dual to a minimum-cost circulation; the set
  criterion of D5(c) and D7 is the steepest-descent optimality criterion for
  L♮-convex functions, and the connectedness of the least tables is the
  L♮-convexity of the set of minimizers. The dual bound from closed walks (D5(a),
  O1) is the circulation side of that duality; with total unimodularity it is
  expected to be exact, which this derivation does not prove.
- **HodgeRank (Jiang, Lim, Yao, Ye).** The least-squares analogue: fitting
  potential differences to pairwise data, the residual being cyclic. Here the
  fit is in whole numbers and in `ℓ¹`, and the loops and the symmetric parts
  (two-way sums) are kept apart from it.
- **Orbit counting (Burnside's lemma).** D14's three-term count lists orbits of
  the invariants under the rewritings; unlike the twenty-second's, the counts are
  not a product of a factor per cycle of pairs, because the cost is not a sum
  over pairs.
- **The twenty-second's construction (integers from pairs of naturals).** It is
  kept, then divided further by the potential differences.

What appears to be specific to this seed: that the changes of the ninth, which
respected the twenty-second's sameness, stop respecting it — adding a term from
two terms on, identifying from four terms on — so that results have no changes
of their own and must be formed after exploring states; that a single change
from a state that does not assert the fewest can raise the cost by any odd
number; that no earlier seed of the line maps in one to one, the smallest
merges being `a b; arb arb` with `a b; arb bra` (one relation) and the first
seed's out-star with its in-star; and that the map back to the twenty-second's
results fails first at cost four, on the two-term results whose two-way sum can
be split two ways.
