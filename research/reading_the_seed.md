# Reading the seed, sentence by sentence

Working notes. Nothing here is cited as evidence; what survived is in
`paper/paper.md`, with its source status.

## "Terms are written with letters."

- Terms are things that get written; the writing is not the term (later: "differ
  only in how their terms are written").
- Open points noticed: one letter per term or several? How many letters are
  there? `r` is a letter too. None of this is given. With one letter per term
  and a fixed alphabet there would be a largest number of terms. Decision: no
  cap is assumed, and every statement is checked to survive a cap (the paths
  used in proofs never have more terms than their target, or two).
- `r`: if `r` could write a term, `rrr` would still parse (middle `r`) when
  every term is one letter, and `arrb` would not parse uniquely when terms may
  have several letters. Since only sameness up to writing matters, `r` is
  simply left out of the letters used.

## "An assertion is written `xry`, where `x` and `y` are terms."

- An assertion has a first and a second term. `arb` and `bra` are treated as
  different by the seed itself (one is asserted, the other "not given"), so
  order matters. Derived, not chosen.
- "is asserted" is said of an assertion: yes or no. Multiplicity (asserted
  twice) is not excluded by any sentence, but no sentence uses it. Chosen:
  no multiplicity. The other reading is left open, not explored.

## "`arb` is asserted. For no term `x` may `xrx` be asserted."

- Immediately: `a` and `b` are two terms.
- "may": a rule about every state, not only the first.

## "Whether `bra` is asserted is not given."

- The only thing the seed flags as not given. On the terms `a`, `b` the
  possible assertions are `ara`, `arb`, `bra`, `brb`; two are forbidden, one is
  given, one is flagged. So the flag is exhaustive *if* there are no other
  terms to begin with. That is the textual support for the closed reading
  (exactly the terms `a`, `b` to begin with). It is support, not proof: chosen.
- If more were there to begin with, every such beginning is a legal state
  containing `arb`, and all of those are results of the closed beginning by
  additions alone. So the open reading moves the starting point, it does not
  add results.

## "A change is exactly one of: ..."

- Four kinds. "Nothing else is a change": so doing nothing is not a change;
  adding what is already asserted is not a change (it changes nothing);
  removing a term is not a change (!). The number of terms can only go down by
  identification, which needs two terms: there is always at least one term.
- "adding a term" and "adding an assertion" are separate, and a change is
  exactly one of them: a new term arrives with no assertion, and an added
  assertion is between terms already there.
- "replaces both by one term": whether the one term is written like the first,
  the second, or freshly, is writing only.

## "A change that makes some `xrx` asserted is obstructed."

- Which changes can? Adding `xrx` itself. Identifying `x` and `y` when `xry`
  or `yrx` is asserted. Removing and adding a term cannot. (Proved.)

## "An obstructed change must be answered: remove the obstruction, or build structure by further changes; ..."

First attempt at a reading: the change is performed, leaving `xrx`, and the
answer repairs the state. But from a state with `xrx`, only removing `xrx`
makes it legal again: identifications and additions keep it (proved). So
"build structure" could never be an alternative to removal; it could only
come on top of a removal. Dropped.

Second attempt: the answer is performed first so that the change is no longer
obstructed. For an identification that works exactly by removing the
assertions between the two terms, and by nothing else (proved: persistence).
For adding `xrx` nothing works. So under this reading "build structure" never
answers anything. Dropped as the *only* reading, kept as the reading of
"remove the obstruction".

Third attempt (kept): "build structure" does not make the obstructed change
happen; it stands in for it. What can stand in for `xrx`? A state that would
give exactly the would-be outcome if the added terms were identified back.
Fewest additions: one term `t` and one assertion, `xrt` or `trx`. For an
obstructed identification of `x`, `y` the state itself already is such a
stand-in with no addition — the two terms stay two. Under this reading:

| obstructed change | refuse | remove the obstruction | build structure |
|---|---|---|---|
| identify `x`, `y` with `xry` or `yrx` | state unchanged | remove those, then identify | state unchanged (it is the build) |
| add `xrx` | state unchanged | impossible (proved) | add `t`, add `xrt` or `trx`, … |

Whatever the reading, as long as "further changes" are changes of the four
kinds and no state may hold `xrx`, the *results* are the same set. Only the
records differ. This is why the choice is tolerable.

Noticed on the way: the one-term state, asked to add `ara`, has exactly three
one-term builds; up to writing they are the two alternatives for what is
given. What is given looks like a built answer to an obstructed `xrx`. Kept as
a computed remark (FREE sameness only; with names it does not apply, since the
given names two terms and the build names one).

## "A refused change is recorded and changes nothing."

- Refusal is always possible. It pads a sequence of changes without effect,
  so "within `k` changes" and "in exactly `k` attempts" give the same results.

## "Attempt every change, fewest additions first. ..."

- Order of attempts on a state: identifications and removals add nothing;
  adding a term and adding an assertion add one each. The seed's own order of
  kinds is used inside each group.
- "adds to what is given": what is given counts two terms and one assertion.
  The alternative with `bra` itself adds one assertion to what is given.
  Negative numbers appear (the one-term state adds −1 and −1).

## "Two results that differ only in how their terms are written are the same result."

- Literal reading: any rewriting, `a` and `b` included. Then `arb` alone and
  `bra` alone are the same result.
- But "what is given" names `a` and `b`, and "adds to what is given" compares
  with it. Conservative reading: rewritings keep the writing of `a` and `b`.
- Neither is eliminated by anything in the seed. Both kept, both computed.

## "Attempt 100 changes along each alternative, finishing earlier changes on every alternative before later ones. ..."

- Breadth first, round by round. The number of sequences explodes; the number
  of results up to sameness is what can be recorded.
- Without a bound every round has a new result (what is given plus `k` new
  terms first appears in round `k`). 100 rounds cannot be listed. Bound on the
  number of terms declared; frontier exported; completeness within the bound
  proved and certified by an independent count.

## "Any outcome is valid."

- Taken as: no particular structure is expected. Nothing was steered.
