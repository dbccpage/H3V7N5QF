# Side notes (not cited as evidence)

## 1. Identifications alone

Script: `research/identification_only.py`. For all 238 legal states with at
most 4 terms (FREE sameness): following only unobstructed identifications
until none is left, the fewest terms of an end state equals the fewest classes
into which the terms split with no two related terms in a class, and the most
terms of an end state equals the most classes of such a split whose classes
are pairwise related. Output on this machine: `238 of 238 states agree`.

An end state is one in which every identification is obstructed: any two
terms are related one way or both. What is given is such a state under either
alternative. `evidence/results_*.csv` has a column for it; the counts per
number of terms (2, 7, 42, 582 for 2–5 terms) equal the counts of states that
never assert both ways, because swapping "not related" with "related both
ways" turns one kind into the other.

Not pursued further: it concerns a restricted process (one kind of change),
and the seed asks for every change.

## 2. Counting an answered change as one

If an obstructed change together with its answer counted as one change, the
one-term state would appear in round 1 instead of round 2 (identify `a` and
`b`, answer: remove `arb`), and each build in round 1 instead of round 2.
Results are the same set (answers reach nothing new); only the round numbers
move down, by at most the number of answered changes on the way. Not computed
as a separate table.

## 3. All 100 rounds exactly

By the cost theorem the results of round `k` are the states of cost `k`, a
finite set, and its size is an orbit count. The generator does this up to
round 20. Going to 100 needs states with up to 102 terms; the direct method
sums over all cycle types of rewritings of `n` terms, which is out of reach
for `n` near 100 in plain Python. States with few assertions and many terms
are mostly unmentioned terms, so a count by "mentioned part plus unmentioned
terms" would shrink the problem to about 68 terms; still millions of cycle
types. Left open.

## 4. A tempting reading that was not taken

Reading "build structure" as a rule that *must* add a copy of `x` with all of
`x`'s assertions, including the forbidden one, would force an endless chain
`x r x' r x'' …`. Nothing in the seed says the built term inherits anything,
and "do not invent a change" speaks against it. Not taken. Under the reading
that was taken, chains are among the results like everything else, with no
special status.

## 5. Lean environment

The pinned toolchain is `leanprover/lean4:v4.33.1`. Running `lake` from the
repository root picks elan's default toolchain instead (there is no
`lean-toolchain` file at the root) and starts rebuilding the dependencies
with the wrong compiler. Always run `lake` inside `lean4/`, or as
`lake +leanprover/lean4:v4.33.1 -d lean4 build`. `code/xry/leanreport.py`
runs it inside `lean4/`.
