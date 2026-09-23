# Input

Terms are written with letters. An assertion is written `xry`, where `x` and `y` are terms.

Given:

- `arb` is asserted.

Whether `bra` is asserted is not given.

A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. Identifying two terms replaces both by one term in every assertion.

A change that makes some `xrx` asserted is obstructed. An obstructed change must be answered: remove the obstruction, or build structure by further changes; declare which, and record the change, the obstruction, and the answer. A refused change is recorded and changes nothing.

Attempt every change, fewest additions first. For every result, record how many terms and assertions it adds to what is given. Two results that differ only in how their terms are written are the same result.

Attempt 100 changes along each alternative, finishing earlier changes on every alternative before later ones. Do not invent a change to reach 100. If the alternatives exceed what can be completed, declare a finite bound, export the exact frontier, and prove what is complete within it.

Any outcome is valid.
