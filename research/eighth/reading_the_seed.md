# Reading the eighth seed against the sixth

Working notes for the eighth derivation. Nothing here is cited as evidence;
what survived is in `paper/eighth/paper.md` with its source status.

## The diff

`prompt/eighth/seed_prompt.md` against `prompt/sixth/seed_prompt.md`: two
passages change, nothing is dropped.

    < Terms are written with letters. An assertion is written `xry`, where `x` and `y` are terms; it is asserted a number of times, its multiplicity. …
    > Terms are written with letters. An assertion is written `xry` or `xsy`, where `x` and `y` are terms and `r` and `s` are the two relations; it is asserted a number of times, its multiplicity. …

    < Whether `bra` is asserted is not given.
    > Whether `bra`, or anything written with `s`, is asserted is not given.

Every other sentence is identical, character for character (`diff`; the
seventh seed differs from both by its given). So the eighth seed is the sixth
seed's counted states, four kinds of change and nothing forbidden, with a
second relation between the same terms: the given lives in `r` alone, and
`s` begins used by nothing.

## What the second relation changes

### The state: two multiplicity functions on the same terms

Terms, a multiplicity for each ordered pair in `r` and one in `s`, the
names. Each *part* (the `r` part, the `s` part) is a state of the sixth seed
with the same terms and names (`fourth.state.MState`); the two-relation
state is the pair (`code/eighth/state.py` `DState`; Lean `DSt` with a
multiplicity function indexed by a relation tag, and `proj`). Sameness: a
rewriting acts on both relations at once — two states whose parts are the
same up to *separate* rewritings need not be the same result. What is given:
`a`, `b`; `arb` once; `bra` once or not at all (the sixth's two beginnings);
nothing with `s` (chosen, C2″: a beginning asserting something with `s` is a
result of this one and reaches the same results, since every well-formed
state is a result — see below; its cost formula is this one's with the given
`s` assertions counted among the givens, which the paper proves and does not
compute).

### The changes: the sixth's four kinds over two relations

Identify two terms (merges both relations: each relation's pairs that become
one pair have their multiplicities added up, separately); remove an
assertion of `r` or of `s`; add a term; add an assertion of `r` or of `s`.
A result with `n` terms and `d_r + d_s` asserted pairs has
`C(n, 2) + d_r + d_s + 1 + 2n²` changes. Fewest additions first:
identifications, removals in `r`, removals in `s`, a term, additions in `r`,
additions in `s` (C6, the order of kinds and of relations among equals). A
change of the eighth seed is a change of the sixth on one part and leaves the
other part as it is (an assertion), or is a change of the sixth on both parts
(a term; an identification). Every change of the sixth is a change of the
eighth on the states asserting nothing with `s` (`MSt.ofR`).

### The cost: additive per relation

Size = terms + Σ `r` + Σ `s`. Destroyed givens: the sixth's, read on the `r`
part (the given is in `r`). Potential `Φ = size + 2·lost`:

- add a term: size +1, lost unchanged (both parts);
- add `xry`: size +1, lost can only fall; add `xsy`: size +1, lost unchanged;
- remove `xry`: size −1, lost +1 at most; remove `xsy`: size −1, lost unchanged;
- identify: both totals kept (the sixth's `total_identify` on each part),
  terms −1, so size −1; lost +1 at most (the sixth's `lostA6_identify` on
  the `r` part).

So `Φ` rises by at most one per change; lower bound `cost ≥ n + Φ(given)`.
Upper bound: the sixth's sequence to the `r` part (removals of givens, the
identification, additions) with nothing in `s` throughout — an
identification keeps an empty relation empty — then the `s` additions. So

    fewest changes = size − size(given) + 2·lost(r part)
                   = the sixth's fewest changes to the r part + Σ s.

The `s` part costs exactly its total, as under the seventh seed (where
nothing is given): the seventh's cost on `s`, the sixth's on `r`. Under
FREE the names are placed to make the `r` part's destroyed givens least
(`lost_free` on the `r` part); the `s` part has no say. Which changes raise
the cost by exactly one: every `s` addition; no `s` removal; the rest as the
sixth's rule on the `r` part. Parity: every change moves the size by one.

### The results: every well-formed state; jointly free

From what is given every well-formed two-relation state with a term is
reached (the reachability path below), so the results are all of them. For
every well-formed `r` part and every well-formed `s` part on the same terms
and names the pair is a result: no result in one relation constrains the
other. The sixth's results are exactly the results asserting nothing with
`s`, at the same rounds (the cost agrees there) and with the same
shortest-sequence counts (a shortest sequence to such a result never touches
`s`: an `s` addition would need an `s` removal, which is not cost-raising).
The `r` part of every result is a sixth result; so is the `s` part (both are
well formed).

### Reachability: the names on the `r` part

From a well-formed state whose names, if one term, are one term in the
target: remove every `s` assertion; the sixth's path on the `r` part with
nothing in `s` (clear, collapse, move the names, add); add the target's `s`
assertions. So `t` is reachable from `s` exactly when the sixth's criterion
holds for the `r` parts (ANCHORED), always (FREE); the `s` parts impose
nothing. Mutual within the two classes, one-way between them, comparable,
the two-change cycle at every result.

### Counting: not a product

The results with `n` terms up to rewriting: the orbit method with every
cycle of the rewriting (off-diagonal and diagonal) carrying two
multiplicities: the sixth's `r` factor (by destroyed givens, capped where the
largest `xrx` matters) times the free `s` factor `Π 1/(1 − x^L)`. The count
is *not* the product of the single-relation counts for `n ≥ 2` — with two
terms and one assertion in each relation there are 8 results, not 2 × 2 = 4
(the swap of the two terms acts on both relations at once) — and equals it
for `n = 1`. This is the precise sense in which `s` is not an independent
copy of `r`: the *set* of results is a product (jointly free), the *count*
up to sameness is not, and the *cost* is a sum.

### Two terms, all rounds (names kept)

The sixth's two-term kinds of round `k` with two terms (names apart; one
term with a second) convolved with the `s` states on two terms of total
`r − k` (`C(r − k + 3, 3)`), plus the one-term states `ara^K asa^L` with
`cost(K) + L = r`: `r + [r ≥ 2]` of them without `bra`. Quartic growth in
`r` (the sixth's cubic times a linear factor... in fact `C(r+7, 7)`-like),
so far fewer rounds than 100 complete.

### Statements

Every earlier statement is tested on each part (its wording rewritten for
`s`), plus joint ones: nothing in `s`; nothing in `r`; some pair asserted in
both; the relations agree everywhere; every `s` assertion has its `r` twin
and the converse. Every well-formed state is a result, so only "at least one
term" (on either part — the same statement) holds everywhere; "nothing in
`s`" holds in what is given and fails in round 1.

## What must be checked per citation (rule 5)

| Earlier result | Expected under the eighth seed |
|---|---|
| the counted state, sameness (4:C1′, 4:C4) | survives per part; sameness rewrites both parts at once |
| `remove`, `identify`, the fourth's `perform` (5:C5″, 6:C5‴) | survive per part |
| 6:D3 (changes, `n + related` making `xrx`) | survives per relation; the total is `C(n,2) + d_r + d_s + 1 + 2n²` |
| 6:D7 (names stay merged) | survives (through the `r` part) |
| 6:D8 (cost, potential) | survives on the `r` part; the cost gains the `s` total |
| 6:D9 (results) | extends: every well-formed two-relation state; the sixth's are those with nothing in `s` |
| 6:D12, D13 (criterion; mutual, cycle) | survive as statements about the `r` part's names |
| 6:D14 (counts) | the `r` factor survives; every cycle gains an `s` factor |
| 6:D17 (two-term forms) | convolved with the `s` states |
| 7:D4 (the cost as the size, additions only) | survives for the `s` part: it costs its total, by additions |
| 6:K1–K8 | computed again: the results with nothing in `s` |
