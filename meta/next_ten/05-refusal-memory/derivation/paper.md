# What follows when a refused change is kept with a result and performed on the next attempt

Problem 05 derivation. Input: `meta/next_ten/05-refusal-memory/seed_prompt.md`. Task:
`meta/next_ten/05-refusal-memory/prompt.md`. The parent is the seventeenth derivation
(`prompt/seventeenth/seed_prompt.md`, `paper/seventeenth/`, `code/seventeenth/`,
`lean4/Seventeenth/`). Claim IDs refer to `meta/next_ten/05-refusal-memory/derivation/claim_ledger.md`.
Lean theorems are in `meta/next_ten/05-refusal-memory/derivation/Derivation.lean`
(namespace `Problem05`). Computed files are in `meta/next_ten/05-refusal-memory/derivation/evidence/`,
written by `evidence.py`.

Every notion below carries one source status: **given** (said by the seed),
**chosen** (a reading fixed here where the seed is silent; unchosen readings are listed),
**derived** (proved), **computed** (output of `code/`), **refuted** (proved impossible),
**open**.

## 0. Findings in brief

1. The seed edits the seventeenth seed by adding one sentence to the obstruction
   paragraph: "Its written form is kept with that result; the next attempt at the same
   written change is performed even if it makes some `xrx` asserted."
2. A result is modeled as a base seventeenth state together with a refusal record:
   a set of written forms of refused changes kept with that result.
3. Under the refusal answer reading (A-replace with memory), an attempt at an
   obstructed change absent from the refusal record is refused, altering no terms
   or assertions and adding its written form to the result's record (derived).
4. When a written change present in the refusal record is attempted on that result,
   the override executes: the change is performed via `perform`, even if it makes
   some `xrx` asserted (derived).
5. In one step from what is given with an empty refusal record, no state asserting
   a loop can be reached (derived). In two steps, a refusal step followed by an
   override step reaches a state asserting a loop, including `oneLoop` (from
   identifying `a` with `b`) and `added_loop` (from adding `ara`) (derived, computed).
6. The hypothesis ("A refusal record can change later reachability") is supported in
   this model. The falsifier ("Every reached result and round agrees with the
   seventeenth under both answer readings") is refuted: seventeenth A-replace reaches
   zero loop-asserting states at every round, while seventeenth A-perform reaches
   loop states in round 1; Problem 05 under refusal memory reaches loop states at
   round 2 (computed, derived).
7. Exploration to bound 3 and 4 rounds reaches 298 results (57 asserting loops)
   under `bra_False_anchored` and 144 results (37 asserting loops) under
   `bra_False_free`. An independent census confirms 129 canonical results of
   at most 2 terms under ANCHORED sameness and 39 under FREE sameness.

## 1. What the seed gives

The diff of `meta/next_ten/05-refusal-memory/seed_prompt.md` against `prompt/seventeenth/seed_prompt.md`
adds one sentence at the end of paragraph 5:

```diff
-A change that makes some `xrx` asserted is obstructed. An obstructed change must be answered: remove the obstruction, or build structure by further changes; declare which, and record the change, the obstruction, and the answer. A refused change is recorded and changes nothing.
+A change that makes some `xrx` asserted is obstructed. An obstructed change must be answered: remove the obstruction, or build structure by further changes; declare which, and record the change, the obstruction, and the answer. A refused change is recorded and changes nothing. Its written form is kept with that result; the next attempt at the same written change is performed even if it makes some `xrx` asserted.
```

The sentences of the seed give:

| ID | Given |
|---|---|
| G1 | Terms are written with letters. |
| G2 | An assertion is written `xry`, where `x` and `y` are terms. |
| G3 | `arb` is asserted. |
| G4 | Whether `bra` is asserted is not given. |
| G5 | A change is exactly one of: identifying two terms; removing an assertion; adding a term; adding an assertion. Nothing else is a change. |
| G6 | Identifying two terms replaces both by one term in every assertion. |
| G7 | A change that makes some `xrx` asserted is obstructed. |
| G8 | An obstructed change must be answered: remove the obstruction, or build structure by further changes; declare which, and record the change, the obstruction, and the answer. |
| G9 | A refused change is recorded and changes nothing. |
| G10 | Its written form is kept with that result. |
| G11 | The next attempt at the same written change is performed even if it makes some `xrx` asserted. |
| G12 | Attempt every change, fewest additions first; for every result record how many terms and assertions it adds to what is given. |
| G13 | Two results that differ only in how their terms are written are the same result. |
| G14 | Attempt 100 changes along each alternative; do not invent a change; declare a finite bound if exceeded. |
| G15 | Any outcome is valid. |

## 2. Notions and their sources

| Notion | Source | Note |
|---|---|---|
| Term, Assertion | given | G1, G2 |
| `arb`, `bra` alternative | given | G3, G4 |
| Four kinds of change | given | G5, G6 |
| Obstruction (M1) | chosen | G7; assertions that would become `xrx` |
| Obstruction (M2) | chosen (unchosen reading) | G7; outcome asserts some `xrx` |
| Refusal record | chosen | G9, G10; set of written forms kept with a result |
| Override step | chosen | G11; performed when change is in refusal record |
| Scope LOCAL | chosen | record belongs to result; transitions to fresh terms start empty |
| Scope CARRIED | chosen (unchosen reading) | valid refused changes carry over to successors |
| Scope EXTERNAL_LOG | chosen (unchosen reading) | record kept outside results (collapses to parent) |
| Sameness ANCHORED | chosen | G13; term rewritings fixing `a` and `b` |
| Sameness FREE | chosen | G13; all term rewritings |
| Refusal state preservation | derived | D1; refusal changes no terms or assertions |
| Refusal accumulation | derived | D2; refused change stored in record |
| Loop-free beginning | derived | D3; `givenA` asserts no loop |
| One-step loop impossibility | derived | D4; no loop reached in one step from rootA |
| Two-step loop reachability | derived | D5; loop reached via refusal then override |
| Two-attempt difference | derived | D6; reachability divergence between attempts |
| Exploration counts | computed | K1; 298 results (anchored), 144 results (free) |
| Agreement with seventeenth | refuted | R1; refuted across all four configurations |

## 3. Refusal memory and state representation

A result in Problem 05 consists of a pair $(S, R)$, where:
- $S$ is a base seventeenth state with terms $0 \dots n-1$, an assertion bitmask, and optional name placements for $a$ and $b$.
- $R$ is a finite set of changes representing the written forms of refused changes kept with that result.

When terms are rewritten by a permutation $p$, the base state transforms to $p(S)$ and each change in $R$ transforms under $p$ (mapping endpoints $u, v \mapsto p(u), p(v)$). Two results are the same result if and only if there exists an allowed term permutation carrying both the base state and the refusal record simultaneously. Canonicalization finds the lexicographically minimal representative over all allowed permutations.

## 4. Override execution and two-attempt difference

When a change $c$ is attempted on a result $(S, R)$:
1. If $c$ is unobstructed:
   The change is performed: $S' = \text{perform}(S, c)$. Under the chosen LOCAL reading, the target result starts with an empty refusal record: $(S', \emptyset)$.
2. If $c$ is obstructed:
   - If $c \notin R$ (first attempt):
     The change is answered by refusal. "A refused change is recorded and changes nothing. Its written form is kept with that result."
     The target result is $(S, R \cup \{c\})$. No term or assertion is modified (Theorem `refusal_preserves_state`).
   - If $c \in R$ (repeated attempt):
     "The next attempt at the same written change is performed even if it makes some `xrx` asserted."
     The override step executes: $S' = \text{perform}(S, c)$. Even though $c$ makes some `xrx` asserted, the outcome is accepted and stands as a result (Theorem `two_step_reaches_loop`).

This establishes a formal divergence between one-step and two-step reachability from what is given:
- In one step from `rootA = (givenA, ∅)`, attempting an obstructed change (such as identifying $a$ with $b$ or adding $ara$) must result in a refusal step, leaving the underlying state identical to `givenA`, which is loop-free (Theorem `rootA_one_step_no_loop`).
- In two steps, the repeated attempt at that same change triggers the override, producing an outcome that asserts a loop (Theorem `two_attempt_difference`).

## 5. Exploration results and comparison with seventeenth

Breadth-first exploration was performed from both beginnings (`bra=False`, `bra=True`) under both sameness conventions (`ANCHORED`, `FREE`) with term bound 3 up to 4 rounds.

Summary of exploration results under refusal memory:

| Configuration | Total Results | Round 0 | Round 1 | Round 2 | Round 3 | Round 4 | First Loop Round | Frontier Cuts |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| `bra_False_anchored` | 298 | 1 | 6 | 23 | 70 | 198 | 2 | 62 |
| `bra_False_free` | 144 | 1 | 6 | 19 | 39 | 79 | 2 | 38 |
| `bra_True_anchored` | 303 | 1 | 6 | 23 | 71 | 202 | 2 | 63 |
| `bra_True_free` | 144 | 1 | 4 | 14 | 39 | 86 | 2 | 35 |

Comparison against seventeenth derivations:

| Configuration | Seventeenth A-replace (Total / Loops) | Problem 05 Refusal Memory (Total / Loops) | Seventeenth A-perform (Total / Loops) | Agreement with Seventeenth? |
|---|:---:|:---:|:---:|:---:|
| `bra_False_anchored` | 51 / 0 | 298 / 57 | 165 / 114 | Refuted |
| `bra_False_free` | 18 / 0 | 144 / 37 | 63 / 45 | Refuted |
| `bra_True_anchored` | 48 / 0 | 303 / 59 | 165 / 114 | Refuted |
| `bra_True_free` | 17 / 0 | 144 / 31 | 63 / 45 | Refuted |

In seventeenth A-replace, obstructed changes are refused without memory and never entered, so zero loop-asserting states appear. In seventeenth A-perform, obstructed changes are performed immediately in round 1. In Problem 05 under refusal memory, loop-asserting states emerge in round 2 via the override step.

## 6. Completeness certificate and independent census

An independent combinatorial census of canonical results within term bound 2 was evaluated by generating all base assertion masks and all subsets of obstructed changes:
- `anchored_bound_1`: 3 results
- `anchored_bound_2`: 129 results
- `free_bound_1`: 3 results
- `free_bound_2`: 39 results

By comparison, loop-free results without refusal memory account for only 9 results (`anchored_bound_2`) and 4 results (`free_bound_2`).

## 7. Resolution of hypothesis and falsifier

The proposed hypothesis in `why.md` states:
> "A refusal record can change later reachability."

The stated falsifier is:
> "Every reached result and round agrees with the seventeenth under both answer readings."

Findings:
1. The falsifier is refuted: across all evaluated configurations, the reached result sets and discovery rounds disagree with seventeenth A-replace (which discovers no loop states) and seventeenth A-perform (which discovers loop states in round 1 rather than round 2).
2. The hypothesis is supported: recording refused written changes directly changes subsequent reachability by enabling override transitions that perform previously obstructed changes.

## 8. Nearest known results and differences

In formal language theory and abstract rewrite systems, an obstructed transition that cannot execute on first attempt corresponds to a guarded command or conditional rewrite rule. In Petri nets and inhibitor arc systems, an inhibitor prevents a transition until a specific marking condition is met. Here, the refusal memory acts as a local accumulator: rather than testing an external state property, the history of attempted transitions on that specific result serves as the guard condition that unlocks the override transition.

In term rewriting with failure memory (such as memoized rewriting or tabling in logic programming), recorded failures typically prune search branches to avoid re-evaluating unproductive derivations. In contrast, the seed rule inverts the effect of recorded failure: a recorded refusal does not prune the branch, but serves as a prerequisite counter that converts a refusal into an unconditional execution upon the next attempt.
