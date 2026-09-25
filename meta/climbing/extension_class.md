# Extension class for the climbing track (frozen 2026-09-25)

**Status:** chosen, outside the seal. **Frozen** by the author's ruling of
2026-09-25 (D5 in `rulings.md`). Its SHA-256 is in `extension_class.sha256`.
The operator wrote each member's sentences out in full on that date, from
the draft of 2026-09-24. Once frozen, this file is never edited; a changed
class is a new file with a new digest and a new ruling.

Every member is one or two sentences in seed words, and each changes the
states, the steps, or which results are the same (rubric rule L4). The class
is an operator's input. A rung that installs a member derives consequences
of that member, never the member itself. A member is written against the
seed it edits. "Replaces" names the sentence it replaces; "adds" means the
sentence is new, and "joins the list" means the kind is appended to the
seed's list of changes. Where a member names both relations, a seed with one
relation reads only its `r` part.

| member | sentences, in seed words | what it adds |
|---|---|---|
| cancel | Replaces the sameness sentence: "Two results that differ only in how their terms are written, or only by an `xry` and an `xsy` asserted together, are the same result." | counts with a sign on each ordered pair |
| raise | Needs cancel. Replaces the sameness sentence: "Two results that differ only in how their terms are written, only by an `xry` and an `xsy` asserted together, or only by raising terms, are the same result." Adds: "Raising a term `x` adds `xry` and `ysx` once for every other term `y`." | moves that repair a result without changing what it is the same as; least members of a result |
| fill one | "Filling one term" joins the list. Adds: "A filled term `x` balances when `xrx` and `xsx` are asserted equally often; for every result, record which filled terms balance." | a local check on a single term |
| fill two | "Filling two different terms" joins the list. Adds: "Two filled terms `x`, `y` balance when, going from `x` to `y` and back to `x`, as many assertions are written with `r` as with `s`, each counted as often as it is asserted; for every result, record which filled terms balance." | a local check on a return between two terms |
| fill three | "Filling three different terms" joins the list. Adds: "Three filled terms `x`, `y`, `z` balance when, going from `x` to `y` to `z` and back to `x`, as many assertions are written with `r` as with `s`, each counted as often as it is asserted; for every result, record which filled terms balance." | a local check on a closed sequence of three terms |
| compose | "Composing two assertions" joins the list. Adds: "Composing `xry` and `yrz` adds `xrz`; composing `xsy` and `ysz` adds `xsz`." | counting sequences of assertions |
| divide | Adds: "A multiplicity is a fraction. Dividing is a change: it divides every multiplicity by the same whole number greater than one." "Dividing" joins the list. | fractional counts |
| stand-for | Adds: "Every asserted `xry` is also a term, written `(xry)`, and may appear in assertions like any other term." | assertions as things a change can act on |
| between | Adds: "Two sequences of changes that start at the same result and end at the same result may be filled. Filling them is a change, and a result records which pairs of sequences are filled." "Filling two sequences" joins the list. | a change acting on changes |
| typed and joined | Replaces the first sentence: "Terms are written with small or capital letters. An assertion joins two small terms, two capital terms, or a small term `x` to a capital term `Y`, written `xjY`. Every small term is joined to exactly one capital term." | two kinds of term, and a rule joining them |
| share | "Joining two results" joins the list. Adds: "Joining the current result with an earlier result keeps every term and every assertion of either, writing once each term that is written with the same letter in both." | gluing two results |
| orient | Replaces the sameness sentence: "Two results that differ only in how their terms are written, or only by an `xry` and a `yrx` asserted together, are the same result." | reversal as a sign change |
| fewest build | For a seed with an obstruction, replaces the answering sentence: "An obstructed change is answered by the fewest further changes after which no `xrx` is asserted; declare them, and record the change, the obstruction, and the answer." | a least answer |

## Excluded by the ruling

The native track does not aim at results that need division together with
further arithmetic laws a seed would have to supply outright, such as a
pairing of counts or a rule whose double is a change of sign. The earlier
estimate was eight to twelve heavy rungs for them. No member supplies those
laws, so no rung licensed by this class can reach them. Where they are wanted,
they are hosted as supplied encodings, graded as supplied, outside this
track. "Divide" stays in the class for the results that need division alone.
