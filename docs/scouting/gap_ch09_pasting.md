# Gap Analysis: Chapter 9 / LD-Pasting

Sources read:

- `references/ldt-paper/ld-pasting.tex` (1849 lines, 84 labels)
- `blueprint/src/chapter/ch09_pasting.tex` (390 lines, 26 labels)
- `MIPStarRE/LDT/Pasting/{Defs,Statements,Sandwich,Theorems}.lean`

## Executive summary

This chapter is the widest current gap between paper and blueprint.

- The paper has 84 labels.
- The blueprint has 26 labels.
- Only 17 labels are shared verbatim.
- 67 paper labels are absent from the blueprint.
- 9 blueprint labels are blueprint-only repackagings:
  `chap:pasting`, `def:distinct-tuples`, `def:G-hat`, `def:types`, `def:pasted-measurement`, `def:outcomes-by-type`, `def:truncated-type-sums`, `lem:truncated-type-sum-recurrence`, `lem:ld-gbcon`.

The blueprint does cover almost all of the paper's top-level theorem chain, but it omits most intermediate equation labels and one important unlabeled bridge corollary:

- Omitted as labeled items: the theorem/subtheorem bullets at the start of the chapter and inside `lem:ld-pasting-sub-measurement`.
- Omitted as a standalone statement: the paper's corollary "Consistency of `H` with `A`", which is folded into the proof of the blueprint's `lem:ld-pasting-sub-measurement`.
- Repackaged by the blueprint: the paper's `eq:ld-gbcon` becomes blueprint lemma `lem:ld-gbcon`; the paper's `S_{τ_{\ge \ell}}` identities become `def:truncated-type-sums` and `lem:truncated-type-sum-recurrence`.

Lean is already organized around the blueprint theorem chain, but not yet proved:

- `MIPStarRE/LDT/Pasting/Theorems.lean` contains 16 `sorry` sites.
- `MIPStarRE/LDT/Pasting/Sandwich.lean` contains 1 additional `sorry` at the Bernoulli-tail upper bound.
- `MIPStarRE/LDT/Pasting/Defs.lean` has a stated interpolation placeholder: `interpolateCompletedSlices` currently uses a dummy coefficient `1` instead of true Lagrange interpolation.

The main blockers are not the endpoint packaging theorems. The real critical path is:

`gCompleteSelfConsistency`
-> `commutativitySwitcheroo`
-> `commutingWithGComplete`
-> `commutingWithGIncomplete`
-> `gHatFacts`
-> `commuteGHalfSandwich`
-> `ldSandwichLineOnePoint`
and then it splits:

- consistency branch: `ldDnoteq` + `ldSandwichLineOnePoint` -> `hBConsistency` -> `ldPastingSubMeas`
- completeness branch: `ldDnoteq` + `ldSandwichLineOnePoint` -> `overAllOutcomes`; `commuteGHalfSandwich` -> `fromHToG`; `bernoulliTailFromFamily.total_le_one` -> `chernoffBernoulliMatrix`; then all three -> `ldPastingNCompleteness` -> `ldPastingSubMeas` -> `ldPasting`

## Shared versus missing coverage

### Counts by major section

| Major section | Paper labels | Shared with blueprint | Missing from blueprint |
|---|---:|---:|---:|
| Construction of the pasted measurement | 22 | 4 | 18 |
| Hat-consistency (`\widehat G` facts) | 20 | 6 | 14 |
| Sandwiching lemmas | 7 | 2 | 5 |
| Consistency of `H` with `A` | 5 | 1 | 4 |
| Completeness of `H` for low-degree | 25 | 2 | 23 |
| Chernoff/Bernoulli bounds | 5 | 2 | 3 |

## 1. Construction of the pasted measurement

### Paper labels and blueprint coverage

| Paper label | Line | In blueprint? | Note |
|---|---:|---|---|
| `sec:ld-pasting` | 10 | no | section label only |
| `thm:ld-pasting` | 12 | yes | shared |
| `item:ld-pasting-completeness` | 16 | no | theorem item only |
| `item:ld-pasting-consistency` | 20 | no | theorem item only |
| `item:ld-pasting-self-consistency` | 24 | no | theorem item only |
| `item:ld-pasting-boundedness` | 28 | no | theorem item only |
| `item:ld-pasting-N-consistency` | 45 | no | theorem conclusion item only |
| `eq:ld-abcon` | 89 | no | absorbed into blueprint prose before `lem:ld-gbcon` |
| `eq:ld-gbcon` | 93 | no | repackaged as blueprint `lem:ld-gbcon` |
| `eq:ld-nu1-def` | 97 | no | folded into blueprint `lem:ld-gbcon` |
| `eq:quote-com-main` | 101 | no | cited as `thm:com-main` in blueprint |
| `lem:ld-pasting-sub-measurement` | 118 | yes | shared |
| `item:ld-pasting-N-consistency-sub-measurement` | 121 | no | lemma item only |
| `item:ld-pasting-N-completeness-sub-measurement` | 125 | no | lemma item only |
| `prop:ld-dnoteq` | 177 | yes | shared |
| `sec:construction-numba-one` | 224 | no | first construction discussion omitted from blueprint structure |
| `eq:subtract-a-G` | 271 | no | first construction heuristic |
| `eq:dumbo-bound-for-idiots` | 277 | no | first construction heuristic |
| `eq:step-one-of-grand-plan` | 296 | no | first construction heuristic |
| `eq:equivalent-way-of-writing-grand-plan` | 316 | no | first construction heuristic |
| `lem:looks-easy-but-took-me-a-while` | 330 | yes | shared |
| `sec:construction-numba-two` | 372 | no | second construction prose only |

### Missing theorem/proposition statements

These are not given standalone blueprint labels.

`item:ld-pasting-completeness`

> If `G = \E_{\bx}\sum_g G_g^{\bx}`, then `\bra{\psi} G \otimes I \ket{\psi} \geq 1 - \kappa`.

`item:ld-pasting-consistency`

> On average over `(\bu, \bx) \sim \F_q^{m+1}`, `A^{u, x}_a \otimes I \simeq_{\zeta} I \otimes G^x_{[g(u)=a]}`.

`item:ld-pasting-self-consistency`

> On average over `\bx \sim \F_q`, `G^x_g \otimes I \approx_{\zeta} I \otimes G^x_g`.

`item:ld-pasting-boundedness`

> There exists a positive-semidefinite matrix `Z^x` for each `x \in \F_q` such that
> `\E_{\bx} \bra{\psi} (I-G^{\bx})\otimes Z^{\bx} \ket{\psi} \leq \zeta`
> and for each `x \in \F_q` and `g \in \polyfunc{m}{q}{d}`,
> `Z^x \geq \left(\E_{\bu} A^{\bu, x}_{g(\bu)}\right)`.

`item:ld-pasting-N-consistency`

> On average over `\bu \sim \F_q^{m+1}`, `A^{u}_a \otimes I \simeq_{\sigma} I \otimes H_{[h(u)=a]}`.

`item:ld-pasting-N-consistency-sub-measurement`

> On average over `\bu \sim \F_q^{m+1}`, `A^{u}_a \otimes I \simeq_{\nu} I \otimes H_{[h(u)=a]}`.

`item:ld-pasting-N-completeness-sub-measurement`

> If `H =  \sum_h H_h`, then
> `\bra{\psi} H \otimes I \ket{\psi} \geq 1 - \kappa \cdot \left(1 + \frac{1}{100m}\right) - \nu - e^{- k/(80000m^2)}`.

### Lean status

Main theorem/file status:

- `ldPasting` is `sorry` in `MIPStarRE/LDT/Pasting/Theorems.lean`.
- `ldPastingSubMeas` is `sorry`.
- `ldDnoteq` is `sorry`.
- `looksEasyButTookMeAWhile` is fully proved.

Construction layer status:

- `constructedPastedSubMeas` and `constructedPastedMeasurement` already exist in `MIPStarRE/LDT/Pasting/Sandwich.lean`.
- `pastedInterpolationFamily` restricts to globally consistent tuples before postprocessing.
- `interpolateCompletedSlices` in `MIPStarRE/LDT/Pasting/Defs.lean` is not the paper's actual interpolation map yet: it explicitly uses a dummy coefficient `1` instead of Lagrange coefficients.

### Does Lean proof structure match?

Mostly yes at the theorem level, but with two important caveats.

- The theorem chain matches the blueprint, not the raw paper exposition: `lem:ld-gbcon` is blueprint-only and not a standalone Lean theorem in `Pasting`.
- The interpolation implementation is only a scaffold. The paper's second construction depends on interpolation from globally consistent tuples; Lean has the filtering predicate `IsGloballyConsistent`, but the actual map `interpolateCompletedSlices` is only structurally shaped like interpolation.

### Dependency chain

- The theorem assumptions here feed every downstream result.
- `prop:ld-dnoteq` is used later in both `hBConsistency` and `overAllOutcomes`.
- `lem:looks-easy-but-took-me-a-while` belongs to the abandoned first-construction discussion and is not on the main proof path.
- `ldPastingSubMeas` is the convergence point of the consistency and completeness branches.
- `ldPasting` is endpoint packaging once `ldPastingSubMeas` exists.

### Most important missing items for the current sorry sites

1. `prop:ld-dnoteq`
2. `item:ld-pasting-N-consistency-sub-measurement`
3. `item:ld-pasting-N-completeness-sub-measurement`

Reason:

- `ldDnoteq` is a direct blocker for both `hBConsistency` and `overAllOutcomes`.
- The omitted theorem-item labels are not separate Lean theorems, but they are exactly the fields that `ldPastingSubMeas` and `ldPasting` must eventually package.

## 2. Hat-consistency (`\widehat G` facts)

### Paper labels and blueprint coverage

| Paper label | Line | In blueprint? | Note |
|---|---:|---|---|
| `sec:hat-consistency` | 502 | no | section label only |
| `lem:g-complete-self-consistency` | 514 | yes | shared |
| `eq:ld-g-self-consistency` | 522 | no | proof equation only |
| `cor:g-bot-self-consistency` | 537 | yes | shared |
| `lem:commutativity-switcheroo` | 560 | yes | shared |
| `eq:M-self-consistent` | 563 | no | hypothesis equation |
| `eq:M-commutes-with-G` | 567 | no | hypothesis equation |
| `eq:g-commute-with-gg-error` | 583 | no | four-term expansion |
| `eq:split-G-and-commute` | 617 | no | proof step |
| `eq:move-G-for-great-justice` | 630 | no | proof step |
| `eq:move-G-for-even-greater-justice` | 650 | no | proof step |
| `eq:commute-the-G-yet-again` | 677 | no | proof step |
| `eq:term-three-for-use-right-now` | 699 | no | proof step |
| `cor:commuting-with-G-complete` | 721 | yes | shared |
| `eq:com-main-copy` | 734 | no | paper-local restatement of `thm:com-main` |
| `eq:applied-the-lemma-to-com-main-copy` | 741 | no | proof step |
| `cor:commuting-with-G-incomplete` | 775 | yes | shared |
| `cor:G-hat-facts` | 817 | yes | shared |
| `eq:gselfconall` | 821 | no | displayed part of `cor:G-hat-facts` |
| `eq:gcomall` | 823 | no | displayed part of `cor:G-hat-facts` |

### Missing theorem/proposition statements

No additional labeled theorem/proposition is missing here. The blueprint keeps all named theorem-level results in this section. What is missing are proof-driving equation labels, especially the full four-step commutator manipulation inside `lem:commutativity-switcheroo`.

### Lean status

All six theorem nodes are present in `MIPStarRE/LDT/Pasting/Theorems.lean`, and all six are still `sorry`:

- `gCompleteSelfConsistency`
- `gBotSelfConsistency`
- `commutativitySwitcheroo`
- `commutingWithGComplete`
- `commutingWithGIncomplete`
- `gHatFacts`

The statement packaging is in `MIPStarRE/LDT/Pasting/Statements.lean` and matches the blueprint well:

- `GCompleteSelfConsistencyStatement`
- `GBotSelfConsistencyStatement`
- `CommutativitySwitcherooStatement`
- `CommutingWithGCompleteStatement`
- `CommutingWithGIncompleteStatement`
- `GHatFactsStatement`

### Does Lean proof structure match?

Yes, very closely.

- `gCompleteSelfConsistency` and `gBotSelfConsistency` are exactly the paper's easy reductions from outcome-level strong self-consistency to total-complete and total-incomplete parts.
- `commutativitySwitcheroo` is set up in Lean with the same three hypotheses as the paper: self-consistency of `G`, self-consistency of `M`, and outcome-level commutation with `G_g^x`.
- `commutingWithGComplete`, `commutingWithGIncomplete`, and `gHatFacts` are packaged as corollary-style wrappers exactly as in the paper and blueprint.

### Dependency chain

- `gCompleteSelfConsistency` -> `gBotSelfConsistency`
- `gCompleteSelfConsistency` -> `commutativitySwitcheroo`
- `commutativitySwitcheroo` + `gCompleteSelfConsistency` -> `commutingWithGComplete`
- `commutingWithGComplete` -> `commutingWithGIncomplete`
- all four previous results -> `gHatFacts`

### Most important missing items for the current sorry sites

1. `lem:commutativity-switcheroo`
2. `lem:g-complete-self-consistency`
3. `cor:G-hat-facts`

Reason:

- `commutativitySwitcheroo` is the first genuinely deep technical proof and the linchpin for the whole commutation chain.
- `gCompleteSelfConsistency` is easy but prerequisite to several later results.
- Once those are done, the remaining corollaries in this section should be mostly packaging.

## 3. Sandwiching lemmas

### Paper labels and blueprint coverage

| Paper label | Line | In blueprint? | Note |
|---|---:|---|---|
| `sec:ld-sandwiching` | 863 | no | section label only |
| `lem:commute-g-half-sandwich` | 872 | yes | shared |
| `lem:ld-sandwich-line-one-point` | 918 | yes | shared |
| `eq:delete-extraneous-coordinates` | 952 | no | proof step |
| `eq:gonna-need-a-bigger-cauchy-schwarz` | 966 | no | proof step |
| `eq:add-in-the-bot` | 981 | no | proof step |
| `eq:even-bigger-CS` | 988 | no | proof step |

### Missing theorem/proposition statements

No named theorem/proposition is missing here; the blueprint includes both named lemmas. The missing paper labels are all proof-navigation equations that matter for the formal proof shape of `lem:ld-sandwich-line-one-point`.

### Lean status

Both core lemmas are present in `MIPStarRE/LDT/Pasting/Theorems.lean` and both are `sorry`:

- `commuteGHalfSandwich`
- `ldSandwichLineOnePoint`

The corresponding operator families already exist in `MIPStarRE/LDT/Pasting/Sandwich.lean`:

- `gHatHalfSandwichLeft`
- `gHatHalfSandwichRight`
- `ldSandwichLineOnePointLeftFamily`
- `ldSandwichLineOnePointRightFamily`

### Does Lean proof structure match?

Yes.

- `CommuteGHalfSandwichStatement` matches the paper's repeated-commutation estimate.
- `LdSandwichLineOnePointStatement` matches the paper's line-point comparison.
- The blueprint compresses the proof to one sentence, but Lean already has the correct families in place for the paper's actual two Cauchy-Schwarz steps and coordinate-elimination argument.

### Dependency chain

- `gHatFacts` -> `commuteGHalfSandwich`
- `commuteGHalfSandwich` + blueprint `lem:ld-gbcon` -> `ldSandwichLineOnePoint`

### Most important missing items for the current sorry sites

1. `lem:ld-sandwich-line-one-point`
2. `lem:commute-g-half-sandwich`

Reason:

- `ldSandwichLineOnePoint` is the first place the `\widehat G` commutation machinery is actually consumed in a long estimate.
- Both the later consistency and completeness branches use it, directly or indirectly.

## 4. Consistency of `H` with `A`

### Paper labels and blueprint coverage

| Paper label | Line | In blueprint? | Note |
|---|---:|---|---|
| `sec:consistency-of-h-with-a` | 1039 | no | section label only |
| `lem:h-b-consistency` | 1041 | yes | shared |
| `eq:keep-on-expandin` | 1058 | no | proof expansion |
| `eq:keep-on-contractin` | 1071 | no | proof contraction |
| `eq:h-b-consistency-at-a-point` | 1100 | no | used in final corollary |

### Missing theorem/proposition statements

The important omission here is unlabeled in the paper, so it does not appear in the paper label count, but it is a real blueprint gap:

Paper corollary immediately after `lem:h-b-consistency`:

> `H_{[h(u, x)=a]} \otimes I \simeq_{\nu} I \otimes A^{u,x}_a.`

This is the proof of `item:ld-pasting-N-consistency-sub-measurement`.

The blueprint does not state this as a separate theorem; it folds it into the proof of `lem:ld-pasting-sub-measurement`.

### Lean status

- `hBConsistency` is `sorry` in `MIPStarRE/LDT/Pasting/Theorems.lean`.
- There is no standalone Lean theorem for the paper's unlabeled corollary from `H/B` consistency to `H/A` consistency.
- Instead, `LdPastingSubMeasConclusion.pointConsistency` is the endpoint field, so the paper corollary is expected to be discharged inside `ldPastingSubMeas`.

### Does Lean proof structure match?

Mostly yes, with one organizational shift:

- The paper puts `lem:h-b-consistency` in the subsection "Consistency of `H` with `A`".
- The blueprint moves it into the preceding section "Consistency of the sandwich with the line measurement", because it is still a line-measurement statement.
- Lean follows the blueprint organization, not the paper's subsection boundary.

### Dependency chain

- `ldDnoteq` + `ldSandwichLineOnePoint` -> `hBConsistency`
- `hBConsistency` + the earlier `A/B` consistency conversion -> paper corollary `H` with `A`
- paper corollary `H` with `A` -> `ldPastingSubMeas`

### Most important missing items for the current sorry sites

1. `lem:h-b-consistency`
2. the unlabeled paper corollary `H` with `A`

Reason:

- `hBConsistency` is the final theorem on the consistency branch.
- The omitted corollary is not hard by itself, but it is a real missing bridge between the paper proof and Lean's packaged endpoint theorem `ldPastingSubMeas`.

## 5. Completeness of `H` for low-degree

### Paper labels and blueprint coverage

| Paper label | Line | In blueprint? | Note |
|---|---:|---|---|
| `sec:completeness-of-h-low-degree` | 1120 | no | section label only |
| `lem:over-all-outcomes` | 1141 | yes | shared |
| `eq:sum-restricted-to-global-polynomial` | 1162 | no | proof step |
| `eq:remove-the-restriction` | 1169 | no | proof step |
| `eq:B-appears-out-of-thin-air` | 1178 | no | proof step |
| `eq:add-in-indicator-for-f-and-g` | 1181 | no | proof step |
| `eq:about-to-swap-x-for-y` | 1188 | no | proof step |
| `eq:consistent-indicator` | 1232 | no | proof step |
| `lem:from-H-to-G` | 1295 | yes | shared |
| `eq:G-recurrence` | 1335 | no | proof step |
| `eq:split-H-into-two-Gs` | 1339 | no | proof step |
| `eq:i-think-this-is-what-i'm-supposed-to-prove` | 1352 | no | proof step |
| `eq:S-def` | 1382 | no | repackaged by blueprint definitions |
| `eq:i-think-this-is-what-i'm-supposed-to-prove-2` | 1391 | no | proof step |
| `eq:S-bound` | 1405 | no | repackaged by blueprint recurrence lemma |
| `eq:explicit-formula-for-G-expectation` | 1414 | no | repackaged by blueprint recurrence lemma |
| `eq:S-recurrence` | 1425 | no | repackaged by blueprint recurrence lemma |
| `eq:S-sandwich` | 1440 | no | repackaged by blueprint recurrence lemma |
| `eq:move-g-over-there` | 1456 | no | proof step |
| `eq:call-again-later-part-tres` | 1459 | no | proof step |
| `eq:commute-g-part-one` | 1503 | no | proof step |
| `eq:call-this-later` | 1506 | no | proof step |
| `eq:commute-g-part-two` | 1559 | no | proof step |
| `eq:call-again-later-part-dos` | 1564 | no | proof step |
| `eq:h-ot-mgg` | 1618 | no | proof step |

### Missing theorem/proposition statements

No named paper theorem/proposition is missing here. The blueprint keeps the two headline lemmas:

- `lem:over-all-outcomes`
- `lem:from-H-to-G`

But it introduces two new labels not present in the paper:

- `def:truncated-type-sums`
- `lem:truncated-type-sum-recurrence`

These blueprint labels package paper material that in the source lives only as equations:

- `eq:S-def`
- `eq:S-bound`
- `eq:explicit-formula-for-G-expectation`
- `eq:S-recurrence`
- `eq:S-sandwich`

### Lean status

Both theorem nodes are present and still `sorry`:

- `overAllOutcomes`
- `fromHToG`

The supporting construction layer is partly there:

- `IsGloballyConsistent`
- `pastedInterpolationFamily`
- `averagedEligibleSandwichSubMeas`
- `allOutcomesExpansionFamily`
- `suffixBernoulliWeightOperator`
- `fromHToGRecurrenceLeftFamily`
- `fromHToGRecurrenceRightFamily`

### Does Lean proof structure match?

Partly, but this is the section with the heaviest repackaging.

What matches:

- `overAllOutcomes` is still the paper's comparison between the actual pasted submeasurement total and the unrestricted eligible-sandwich total.
- `fromHToG` is still the Bernoulli-tail rewrite theorem.

What is reorganized:

- The blueprint extracts the `S_{τ_{\ge \ell}}` algebra into a standalone definition and lemma.
- Lean does not create that standalone theorem. Instead, `FromHToGStatement` has:
  - a `recurrenceStep` field for the per-`ℓ` recurrence, and
  - a `bernoulliPolynomialRewrite` field for the final global rewrite.

What is structurally weaker than the paper right now:

- `fromHToGRecurrence{Left,Right}Family` are collapsed to `Unit`-indexed operator families, so the rich paper proof has already been compressed before the proof begins.
- `interpolateCompletedSlices` is still placeholder interpolation, which is potentially relevant to the global-consistency side of `overAllOutcomes`.

### Dependency chain

- `ldDnoteq` + `ldSandwichLineOnePoint` -> `overAllOutcomes`
- `commuteGHalfSandwich` + the `\widehat G` facts -> `fromHToG`
- the blueprint's recurrence packaging is conceptually between `commuteGHalfSandwich` and `fromHToG`

### Most important missing items for the current sorry sites

1. `lem:from-H-to-G`
2. `lem:over-all-outcomes`
3. the `S_{τ_{\ge \ell}}` recurrence package

Reason:

- `fromHToG` is the most structurally elaborate proof in the whole chapter.
- `overAllOutcomes` is the other long completeness-side proof and also depends on the earlier consistency branch.
- The blueprint's extracted recurrence lemma is not a separate Lean theorem yet, but its content still has to be proved somewhere, and right now that burden sits inside `fromHToG`.

## 6. Chernoff/Bernoulli bounds

### Paper labels and blueprint coverage

| Paper label | Line | In blueprint? | Note |
|---|---:|---|---|
| `lem:chernoff-bernoulli-matrix` | 1671 | yes | shared |
| `eq:in-other-words` | 1712 | no | Markov step |
| `eq:by-chernoff` | 1739 | no | scalar Chernoff step |
| `eq:almost-done-with-this-giant-proof` | 1755 | no | final assembly step |
| `cor:ld-pasting-N-completeness` | 1799 | yes | shared |

### Missing theorem/proposition statements

No named paper theorem/proposition is missing here. The blueprint includes both the matrix Chernoff lemma and the final completeness corollary.

### Lean status

Theorem-level sorrys:

- `chernoffBernoulliMatrix`
- `ldPastingNCompleteness`

Additional foundational sorry:

- `bernoulliTailFromFamily.total_le_one` in `MIPStarRE/LDT/Pasting/Sandwich.lean`

This extra `sorry` matters because the statement `ChernoffBernoulliMatrixStatement` currently includes a field
`tail_le_one : bernoulliTailOperator k degree X ≤ 1`,
so the Bernoulli-tail upper bound is not merely a local lemma; it is built into the statement package used downstream.

### Does Lean proof structure match?

Yes at a high level.

- `chernoffBernoulliMatrix` matches the paper's spectral-measure-plus-scalar-Chernoff proof.
- `ldPastingNCompleteness` matches the paper's endpoint composition:
  `overAllOutcomes` + `fromHToG` + Chernoff.

The one important implementation wrinkle is that Lean also needs the operator inequality `bernoulliTailOperator ≤ 1` as part of its packaged submeasurement object, so the proof burden is slightly more explicit than in the paper prose.

### Dependency chain

- `bernoulliTailFromFamily.total_le_one` -> `chernoffBernoulliMatrix`
- `overAllOutcomes` + `fromHToG` + `chernoffBernoulliMatrix` -> `ldPastingNCompleteness`
- `ldPastingNCompleteness` -> `ldPastingSubMeas`

### Most important missing items for the current sorry sites

1. `bernoulliTailFromFamily.total_le_one`
2. `lem:chernoff-bernoulli-matrix`
3. `cor:ld-pasting-N-completeness`

Reason:

- The operator upper bound is a hidden blocker for the matrix-Chernoff package.
- `ldPastingNCompleteness` itself should be endpoint packaging once the three inputs are proved.

## Lean crosswalk by sorry site

### `Theorems.lean`

Current `sorry` sites:

- `ldPasting`
- `ldPastingSubMeas`
- `ldDnoteq`
- `gCompleteSelfConsistency`
- `gBotSelfConsistency`
- `commutativitySwitcheroo`
- `commutingWithGComplete`
- `commutingWithGIncomplete`
- `gHatFacts`
- `commuteGHalfSandwich`
- `ldSandwichLineOnePoint`
- `hBConsistency`
- `overAllOutcomes`
- `fromHToG`
- `chernoffBernoulliMatrix`
- `ldPastingNCompleteness`

Already done:

- `looksEasyButTookMeAWhile`

### `Sandwich.lean`

Current extra `sorry`:

- the `total_le_one` proof inside `bernoulliTailFromFamily`

### Structural scaffolding already present

The following are already implemented and align well with the paper/blueprint architecture:

- complete/incomplete parts and completed measurement `\widehat G`
- sandwich operator families
- global-consistency filter `IsGloballyConsistent`
- pasted submeasurement and its completion to a full measurement
- type-based helper families for the completeness proof

The biggest structural caveat remains:

- `interpolateCompletedSlices` is only a placeholder interpolation map, not the paper's genuine reconstruction.

## Recommended proof priority

### Tier 1: hardest blockers on the critical path

1. `commutativitySwitcheroo`
2. `ldSandwichLineOnePoint`
3. `overAllOutcomes`
4. `fromHToG`

### Tier 2: prerequisites and short corollaries that unlock the chain

1. `gCompleteSelfConsistency`
2. `gBotSelfConsistency`
3. `commutingWithGComplete`
4. `commutingWithGIncomplete`
5. `gHatFacts`
6. `commuteGHalfSandwich`
7. `ldDnoteq`

### Tier 3: endpoint packaging once the core exists

1. `hBConsistency`
2. `bernoulliTailFromFamily.total_le_one`
3. `chernoffBernoulliMatrix`
4. `ldPastingNCompleteness`
5. `ldPastingSubMeas`
6. `ldPasting`

## Bottom line

The blueprint is not missing the headline theorem chain of the chapter; it is missing the paper's internal navigation structure.

What is really absent from the blueprint is:

- the theorem-item labels at the start and in the submeasurement theorem,
- almost every proof-driving equation label,
- the standalone `H`-with-`A` bridge corollary,
- the paper's explicit first-construction discussion as a named subsection,
- and the full amount of intermediate recurrence bookkeeping used in `fromHToG`.

What is really absent from Lean is not chapter organization but proofs:

- the commutation chain,
- the sandwich-line comparison,
- the unrestricted-to-Bernoulli completeness rewrite,
- and the Bernoulli-tail upper bound.

Those are the items that matter most for clearing the current `sorry` sites and turning Chapter 9 from a scaffold into a real formalization.
