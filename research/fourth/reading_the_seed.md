# Reading the fourth seed against the third

Working notes for the fourth derivation. Nothing here is cited as evidence;
what survived is in `paper/fourth/paper.md` with its source status.

## The diff

`prompt/fourth/seed_prompt.md` against `prompt/third/seed_prompt.md`: two
sentences differ.

    - Terms are written with letters. An assertion is written `xry`, where `x` and `y` are terms.
    + Terms are written with letters. An assertion is written `xry`, where `x` and `y` are terms; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one.

    - `arb` is asserted.
    + `arb` is asserted with multiplicity one.

Every other sentence is identical, character for character (`diff`). The
kinds of change are the third seed's two: adding a term, adding an assertion.
So every reading and every proof of the third derivation that does not
depend on an assertion being a yes or no carries over; what depends on it
must be looked at one by one. "Depends on it" is checked per claim, not
assumed, and the check has a name in the ledger: whether the claim *survives
the assertion being counted*.

## What the two sentences change

### The state

Under the earlier seeds a state was: terms, a set of asserted `xry`, names.
Now it is: terms, a *number* for each `xry` (its multiplicity), names. The
earlier reading C1 ("asserted is yes or no") was a choice, left open as O1 in
all three papers; the fourth seed decides it. An assertion "is asserted" when
its multiplicity is positive, so "for no term `x` may `xrx` be asserted" means
every `xrx` has multiplicity zero (legal), and "whether `bra` is asserted is
not given" is about `bra` having a positive multiplicity.

Two maps between the models, both needed for citations:

- the *support* of a counted state: the earlier state asserting exactly what
  has positive multiplicity;
- the *indicator* of an earlier state: the counted state asserting everything
  it asserts once.

The support of the indicator is the state itself; the indicator of the
support is the counted state exactly when nothing is asserted twice ("simple"
states, in the code).

### "`arb` is asserted with multiplicity one."

The beginning asserts `arb` once. `bra` "not given": the two beginnings are
kept as before, `bra` with multiplicity zero or one. A beginning with `bra`
asserted `k ≥ 2` times is a third reading; every such beginning is reached
from the one with `bra` once by adding `bra` `k − 1` times, so it is a result
of that beginning and its own results are among that beginning's results: the
reading moves the starting point and adds no result (the same argument as
C2's for further terms). Chosen: multiplicity one; unchosen: `k ≥ 2`, harmless.

### "Adding an assertion raises its multiplicity by one."

- Adding `xry` is now a change whether or not `xry` is asserted: the third
  seed's reading C5 ("adding what is asserted changes nothing, so it is not a
  change") no longer holds; the outcome differs from the state. So a state
  with `n` terms has `1 + n²` changes (a term; every ordered pair, `xrx`
  included), `n` of them obstructed — the third's `1 + n² − m` loses its
  `− m`.
- Obstruction: adding `xrx` raises the multiplicity of `xrx` from zero to
  one, so it "makes some `xrx` asserted"; adding `xry` with `x ≠ y` or a term
  makes no `xrx` asserted. The obstructed changes are exactly the additions
  of some `xrx`, as under the third seed.
- "Remove the obstruction": the obstruction is the assertion the change
  itself adds. No change lowers a multiplicity (both kinds add), so
  un-asserting it is impossible; not adding it is refusal. As under the third
  seed, both readings kept, one refuted, one coinciding with refusal.
- Builds: add a term `t`, then `xrt` or `trx`. With multiplicities the
  criterion "the added term read as `x` gives the would-be outcome" becomes:
  summing multiplicities over the pairs that become one pair gives exactly
  the would-be outcome's multiplicities. The would-be outcome has `xrx` once
  and everything else as in the state. So among builds that add one term `t`
  exactly two qualify: `xrt` alone, `trx` alone. Both together would give
  `xrx` twice; a copy `try` of an asserted `xry` would give `xry` one more
  time than the outcome has. The third seed had `3 · 2^d` one-term builds
  (`d` the assertions mentioning `x`); the counted seed has 2. Small, new,
  and checkable by enumeration.

### What is kept, what moves

- **Containment.** A change adds a term or raises one multiplicity by one;
  nothing is taken away. So a state is contained in its outcome: terms in
  place, names in place, every multiplicity the same or higher. Containment
  composes and is one-way (pointwise equality from pointwise ≤ both ways).
  Everything the third derivation drew from containment should carry over
  with "asserted" read as "positive multiplicity" and with a new clause: no
  multiplicity ever decreases.
- **Size.** `size = terms + sum of multiplicities` rises by exactly one per
  change (the third's `terms + assertions` counted each assertion once; with
  the multiplicity counted the same equality holds). So every sequence
  between two states has the same length, the size difference; the round of
  a result is the size difference; fewest changes is the size difference.
- **Results.** Every legal state containing what is given is reached by
  additions (add missing terms, then raise each multiplicity as many times as
  needed). So the results are the legal states containing what is given
  (`arb` with multiplicity ≥ 1; `bra` ≥ 1 too if given; names kept; up to
  rewriting under FREE). *This set is infinite even with two terms*: `arb`
  asserted `k` times, for every `k ≥ 1`. The third's results are exactly the
  results asserting nothing twice, in the same rounds (the same sequences,
  since a sequence to a simple result passes through simple states only).
- **Reachability.** A result reaches another exactly when an embedding
  carries it into the other with every multiplicity at most the image's.
  One-way as before. On simple results this is the third's criterion (an
  embedding carrying asserted pairs to asserted pairs is the same as
  multiplicity `1 ≤ 1`). New pairs: `a b; arb` reaches `a b; arb(2)`, and the
  latter reaches nothing the former does not, but not conversely.
- **The exploration.** With the terms bounded, 100 rounds cannot complete
  for 3 or more terms: the results with `n` terms and round `r` grow like a
  polynomial of degree `n(n−1) − 1` in `r`. With exactly 2 terms all 100
  rounds complete: the results at round `r` are the multiplicity pairs
  `(1 + i, j)` with `i + j = r` — `r + 1` of them (names kept, no `bra`), so
  5 151 results in 100 rounds. The bound is declared on terms and on rounds;
  the frontier has two parts: attempts that leave the term bound, and the
  results of the last round, whose changes await the next round.
- **Counting.** The independent count changes: a rewriting fixes a counted
  state when the multiplicity is constant on each cycle of the rewriting's
  action on ordered pairs; counting by total multiplicity gives a series
  `1/(1 − x^L)` per cycle of length `L` (`x/(1 − x)` for `arb`, which must be
  positive) instead of the binomial `(1 + x^L)`. The "no pair both ways"
  count for the FREE reading with `bra` uses `(1 + x^L)/(1 − x^L)` per
  unordered-pair cycle that can carry one direction, and `1` per cycle that
  turns a pair around. The simple results are counted by the third's method
  and must agree with the third's `counts.csv`.
- **Sequences.** The number of sequences reaching a two-term result
  `(1 + i, j)` is `C(i + j, i)`: choose which of the `i + j` additions are
  `arb`. Not one in general; the third's witness (two sequences to
  `a b c; arb bra`) stands, and there is a two-term witness now:
  `a b; arb(2) bra` by two sequences.
- **Statements that do not follow**: `bra`; exactly two terms; "nothing is
  asserted twice" (holds in what is given, fails after adding `arb`);
  "`arb` is asserted exactly once" (same witnesses); "some assertion is
  asserted twice"; "all asserted assertions are asserted equally often"; the
  third's N-list otherwise unchanged.

## What must be checked per citation (rule 5)

| Earlier result | Expected under the counted seed |
|---|---|
| 1:D1 `a ≠ b` | survives (about relations; multiplicity positive is a relation) |
| 1:D2 two states on the given terms | does *not* survive as stated: on `a`, `b` alone there are infinitely many legal states containing what is given (`arb` `i` times, `bra` `j` times); exactly two assert nothing twice |
| 3:D3 obstruction, `1 + n² − m` attempts | obstruction survives; the count becomes `1 + n²` |
| 3:D4 `xrx` always obstructed | survives |
| 3:D5 containment | survives, strengthened (multiplicities) |
| 3:D6 persistence, counts never decrease | survives; new: no multiplicity decreases |
| 3:D7 obstruction never cleared | survives |
| 3:D8 size, every sequence the same length | survives with size counting multiplicity |
| 3:D9 results = legal states containing the given | survives with containment counted; the set is now infinite per term bound; simple results are the third's |
| 3:D10 answers | survives; one-term builds: exactly two (new) |
| 3:D11 rename | survives if target 5 closes |
| 3:D12 reachability = containment | survives with multiplicities |
| 3:D13 one-way | survives |
| 3:D14 completeness within the bound | survives with the bound on rounds added |
| 3:D15 `bra` with passing on | survives (support) |
| 3:D16 two sequences | survives, plus a two-term witness |
| 3:K counts | the third's numbers are the simple part; computed again as such |
| 3:C5 non-changes | does not survive: re-adding is a change |
| 1:C1 / O1 | replaced by the seed |
