# H2 "raising": launch packet

**Status:** prepared 2026-09-26. The seed and task are installed as
`prompt/twentythird/`, byte for byte. **Not launched.** The operator launches
after the install merges, using `../launch.md` with `<n>` = `twentythird`.
This packet is chosen apparatus, outside the seal.

| file | role | SHA-256 (LF bytes) |
|---|---|---|
| `seed_prompt.md` | the seed, installed as `prompt/twentythird/seed_prompt.md` | `84eda21987126db16a43261ccc98d6fef23449c9c580a1bb5cf275b4f378578f` |
| `prompt.md` | the task, installed as `prompt/twentythird/prompt.md` | `b9d8c293dec647f6c03f7712e8253d0b8360379ff9585825bf00214f1388df8a` |
| `prediction.md` | the frozen prediction, native words only | `f44817cd494ae36828c323a86acbe76b3621c81d124b9d0b83001e8e7082b3e6` (`prediction.sha256`, committed in `9209ef7` before the install) |

## 1. The edit

The parent is the twenty-second seed (`prompt/twentysecond/seed_prompt.md`,
`dd6ea130…`). The frozen member "raise" (`../extension_class.md`, digest
`6b0929a6…`) is applied verbatim. Its first sentence replaces the sameness
sentence, and its second is added after it:

```diff
-Two results that differ only in how their terms are written, or only by an `xry` and an `xsy` asserted together, are the same result.
+Two results that differ only in how their terms are written, only by an `xry` and an `xsy` asserted together, or only by raising terms, are the same result. Raising a term `x` adds `xry` and `ysx` once for every other term `y`.
```

## 2. Licence check (`../rubric.md`)

| rule | how H2 meets it |
|---|---|
| L1, one demand in the parent's words | One sentence of the task: "In the twenty-second, can a result with something asserted be the same as a result with nothing asserted on as many terms; and here, which results are, whether each other result carries something that shows it is not, what the fewest changes to each result are, and which of its states assert the fewest assertions?" It asks for the exact results, a check for each survivor, and a least member per result, without giving any of them. |
| L2, exhaustion at the parent's level | The twenty-second's D1: its sameness keeps every difference, so no result with something asserted is the same as nothing. This is an invariant, proved in Lean (`same_iff_excess`). |
| L3, the smallest member of the frozen class | Two members make an asserted result the same as nothing: "raise" (two sentences) and "orient" (one sentence). As frozen, "orient" replaces the whole sameness sentence with a text that drops the parent's own clause (`xry` and `xsy` together). On this parent it would strike the twenty-second's rung instead of extending it. So among members that keep the parent's sentences, "raise" is the smallest. **Recorded openly:** under a literal L3 that does not require keeping the parent's sentences, "orient" is smaller, and H2's record reads "not the smallest; chosen by the operator" (ruling D4 names raising for this round). The author may settle which reading of L3 holds. |
| L4, states or steps change | Two of the twenty-second's results become one result. Witness: on two terms, `xry` and `ysx` against nothing. |
| L5, Lean and the rung pair | The Lean library `Twentythird` sits in `lean4_core/`, with the small axiom set. **Expected to fail in its first form:** the prediction (Q9) says no earlier seed's states map one to one, because raising is a repair within the level, not a new level. The task asks the run to prove that with a witness if so. The author may want L5 to allow this negative form for repair rungs. |
| L6, ablation after the merge | The fixed-term-set sibling (§5), plus strikes of each changed sentence. |

## 3. The task

`prompt.md` follows H1's task, with four differences:

- The inputs are the twenty-second's line.
- The demand is one sentence.
- By ruling D4, it says to explore by changing states and to form the
  results afterwards.
- It tells the run to run its final gates in the foreground and wait for
  them. This is the lesson of H1, where the headless process exited while
  the run's background checks were pending.

The Lean library goes in the existing package, may import `Twentysecond`,
and adds "imported" as a re-check kind. The task names no outside structure
and gives no answer.

## 4. The frozen prediction

`prediction.md` holds ten predictions, Q0 to Q9, in native words:

- **Q0:** the demand is met.
- **Q1, Q2:** sameness and exactness, by the sums of closed sequences.
- **Q3:** certified survivors. Every survivor has a closed sequence of at
  most three terms with a non-zero sum.
- **Q4:** adding a term breaks the sameness, so growth creates survivors,
  and readings (S) and (X) must both be kept.
- **Q5:** identifying two terms breaks it too, once three terms remain.
- **Q6:** fewest changes differ by reading. Under (X), round 3 is infinite.
- **Q7:** members with the fewest assertions, which need not be unique.
- **Q8:** the exchange.
- **Q9:** no new level; the rung pair fails, with a witness.

Two of the round plan's earlier hand predictions are corrected here, before
any run:

- **Cost.** "Fewest changes equal terms plus the least size of a member"
  holds only under reading (S). Under (X) the three-term survivor `xry`,
  `ysx` costs 3, not 5.
- **Identification.** "Identifying two terms respects the sameness" fails
  once three terms remain (Q5's witness).

## 5. The L6 sibling: the fixed set of terms (not launched)

By ruling D4, a sibling run fixes the set of terms during repair, with a
finite-letters sentence, so that growth cannot create survivors. Any later
question about whether survivors run out needs a fixed set of terms. It is
packeted only after H2 merges, and it is not launched now.

## 6. Launch and landing

Follow `../launch.md` with `<n>` = `twentythird`, clone `C:/wt/h3-d23`,
and transcript `C:/wt/h3-twentythird.transcript.jsonl`.

Before §1 of the template, after this install merges, check the digests of
the committed blobs:

```powershell
$R = "C:/Users/a343o/source/repos/H3V7N5QF"
git -C $R fetch origin
git -C $R show origin/main:meta/climbing/h2_raising/prediction.md | sha256sum      # f44817cd…
git -C $R show origin/main:meta/climbing/extension_class.md | sha256sum            # 6b0929a6…
git -C $R show origin/main:prompt/twentythird/seed_prompt.md | sha256sum           # 84eda219…
```

## 7. After the run

1. Land the run's commits (`../launch.md` §4). Audit the transcript from
   outside: no web, server or messaging tool call, no read outside the
   clone, and no outside words in the seed, prompt or paper body.
2. Have a second model review the run, open the pull request, and list the
   run's original commit ids in it.
3. Score Q0 to Q9 in `score.md` and fill `record.md`.
