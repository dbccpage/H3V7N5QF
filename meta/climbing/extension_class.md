# Extension class for the climbing track: draft, not yet frozen

**Status:** chosen, outside the seal. This is a **draft**. Rubric rule L3
needs the class frozen (its SHA-256 committed) before any rung's seed is
written. Freezing it is the author's decision (decision D5 in
`h1_cancellation/packet.md`). Until then no rung may cite it as frozen.

Every member is one or two sentences in seed words, and each changes the
states, the steps, or which results are the same (rule L4). The class is an
operator's input. A rung that installs a member derives consequences of that
member, never the member itself.

| member | sentence(s), in seed words | what it adds |
|---|---|---|
| cancel | "Two results that differ only in how their terms are written, or only by an `xry` and an `xsy` asserted together, are the same result." | signed counts on each ordered pair |
| raise | "… or only by raising terms, are the same result. Raising a term `x` adds `xry` and `ysx` once for every other term `y`." | moves that repair a result without changing its class; least members of a class |
| fill one / two / three | "A change is exactly one of: …; filling *k* different terms." plus a balance sentence recording, for every result, which filled terms balance | a local check on a closed sequence of one, two or three terms |
| compose | a change that joins `xry` and `yrz` into `xrz` | counting sequences of assertions |
| divide | counts may be divided as well as added | fractional counts |
| stand-for | a term may stand for an assertion | assertions as things a change can act on |
| between | a change that fills between two changes that start and end together | a change acting on changes |
| typed and joined | terms of two kinds, and a rule joining an assertion of one kind to the other | two sorts of term |
| share | two results joined along the terms they share | gluing two results |
| orient | reversing an assertion flips its sign | reversal as a change |
| fewest build | an obstructed change is answered by the fewest further changes | a chosen, least answer |

Sentences marked "…" or given only as a description must be written out in
full before the class is frozen. Decision D5 also settles whether the
native track aims at results that need division together with further
arithmetic laws a seed would have to supply outright (estimated at eight to
twelve heavy rungs). The recommendation is no: keep "divide" in the class,
but leave those results to supplied encodings.
