# Input

Terms are written with letters. An assertion is written `xry` or `xsy`, where `x` and `y` are terms and `r` and `s` are the two relations; it is asserted a number of times, its multiplicity. Adding an assertion raises its multiplicity by one; removing an assertion lowers it by one.

Nothing is given: to begin with there are no terms and nothing is asserted.

A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion; filling three different terms. Nothing else is a change. Identifying two terms replaces both by one term in every assertion. Three filled terms `x`, `y`, `z` balance when, going from `x` to `y` to `z` and back to `x`, as many assertions are written with `r` as with `s`, each counted as often as it is asserted; for every result, record which filled terms balance.

Attempt every change, fewest additions first. For every result, record how many terms and assertions it adds to what is given. Two results that differ only in how their terms are written, only by an `xry` and an `xsy` asserted together, or only by raising terms, are the same result. Raising a term `x` adds `xry` and `ysx` once for every other term `y`.

Attempt 100 changes along each alternative, finishing earlier changes on every alternative before later ones. Do not invent a change to reach 100. If the alternatives exceed what can be completed, declare a finite bound, export the exact frontier, and prove what is complete within it.

Any outcome is valid.
