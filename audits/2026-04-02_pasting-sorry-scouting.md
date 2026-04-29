---
title: "Pasting sorry-site scouting"
date: 2026-04-02
author: AI research assistant
purpose: >
  Scouting report for sorry sites in the low-degree pasting theorem layer.
status: snapshot
track: paper2009ldt
kind: scouting-report
---

# Scouting report for the 17 `sorry` sites in `MIPStarRE/LDT/Pasting/Theorems.lean`

I read both:

- `MIPStarRE/LDT/Pasting/Theorems.lean`
- `references/ldt-paper/ld-pasting.tex`

and matched each `sorry` to the labeled statement in the paper.

For scouting purposes, the useful split is actually three-way, not purely binary:

- `Compose/package`: mostly an assembly theorem or short corollary once earlier lemmas exist.
- `Standalone-routine`: not a composition theorem, but also not a deep new argument.
- `Deep core`: this is where the real proof complexity lives.

## Executive summary

Critical path to the final pasting theorem:

1. `gCompleteSelfConsistency`
2. `gBotSelfConsistency`
3. `commutativitySwitcheroo`
4. `commutingWithGComplete`
5. `commutingWithGIncomplete`
6. `gHatFacts`
7. `commuteGHalfSandwich`
8. `ldSandwichLineOnePoint`
9. `ldDnoteq`
10. `hBConsistency`
11. `overAllOutcomes`
12. `fromHToG`
13. `chernoffBernoulliMatrix`
14. `ldPastingNCompleteness`
15. `ldPastingSubMeas`
16. `ldPasting`

Off the main line:

- `looksEasyButTookMeAWhile` appears only in the paper's discussion of the first construction, which the paper explicitly abandons in favor of the second construction. It is not on the critical path for the actual theorem proved in Section 12.

Hard blockers:

- `commutativitySwitcheroo`
- `ldSandwichLineOnePoint`
- `overAllOutcomes`
- `fromHToG`

Independent side lemmas that can be proved in parallel:

- `ldDnoteq`
- `chernoffBernoulliMatrix`
- `looksEasyButTookMeAWhile`

Best "easy once deps are in" endpoints:

- `ldPasting`
- `gBotSelfConsistency`
- `commutingWithGIncomplete`
- `gHatFacts`
- `ldPastingNCompleteness`

## Dependency graph among the 17 theorems

Direct internal dependencies, as they appear from the paper proofs:

- `ldPasting <- ldPastingSubMeas`
- `ldPastingSubMeas <- hBConsistency, ldPastingNCompleteness`
- `ldPastingNCompleteness <- overAllOutcomes, fromHToG, chernoffBernoulliMatrix`
- `hBConsistency <- ldDnoteq, ldSandwichLineOnePoint`
- `overAllOutcomes <- ldDnoteq, ldSandwichLineOnePoint`
- `fromHToG <- commuteGHalfSandwich`
- `ldSandwichLineOnePoint <- gHatFacts, commuteGHalfSandwich`
- `commuteGHalfSandwich <- gHatFacts`
- `gHatFacts <- gCompleteSelfConsistency, gBotSelfConsistency, commutingWithGComplete, commutingWithGIncomplete`
- `commutingWithGIncomplete <- commutingWithGComplete`
- `commutingWithGComplete <- commutativitySwitcheroo, gCompleteSelfConsistency`
- `commutativitySwitcheroo <- gCompleteSelfConsistency`
- `gBotSelfConsistency <- gCompleteSelfConsistency`

External results used but not among the 17:

- `thm:com-main` / `Commutativity.ComMainConclusion`
- the `A/B` consistency conversions around `eq:ld-abcon` and `eq:ld-gbcon`
- `prop:two-notions-of-self-consistency`
- `prop:switch-sandwich`
- triangle inequalities for `approx` / `simeq`
- Schwartz–Zippel
- additive Chernoff

Two-branch view of the overall proof:

- `Consistency branch`:
  `g...` chain -> `ldSandwichLineOnePoint` -> `hBConsistency` -> paper corollary "Consistency of H with A" -> `ldPastingSubMeas`
- `Completeness branch`:
  `g...` chain -> `ldSandwichLineOnePoint` and `ldDnoteq` -> `overAllOutcomes`
  and separately `g...` chain -> `fromHToG`
  and independently `chernoffBernoulliMatrix`
  then `ldPastingNCompleteness` -> `ldPastingSubMeas`

## Recommended proving order

If the goal is to clear the file efficiently rather than follow source order literally:

1. `ldDnoteq`
2. `gCompleteSelfConsistency`
3. `gBotSelfConsistency`
4. `commutativitySwitcheroo`
5. `commutingWithGComplete`
6. `commutingWithGIncomplete`
7. `gHatFacts`
8. `commuteGHalfSandwich`
9. `ldSandwichLineOnePoint`
10. `hBConsistency`
11. `overAllOutcomes`
12. `fromHToG`
13. `chernoffBernoulliMatrix`
14. `ldPastingNCompleteness`
15. `ldPastingSubMeas`
16. `ldPasting`
17. `looksEasyButTookMeAWhile` whenever convenient, since it is off-path

Reasoning:

- `ldDnoteq` and `chernoffBernoulliMatrix` are independent and likely easier than the middle technical lemmas.
- The entire `G` / `\widehat G` commutation chain is the main prerequisite for both the consistency and completeness analyses.
- `ldSandwichLineOnePoint` is the first really painful proof after the `G` infrastructure.
- `overAllOutcomes` and `fromHToG` are both long core lemmas needed for the completeness corollary.
- `ldPastingSubMeas`, `ldPastingNCompleteness`, and `ldPasting` are endpoint packaging theorems.

## Per-theorem scouting notes

### 1. `ldPasting`

- Lean: `MIPStarRE/LDT/Pasting/Theorems.lean:19`
- Paper label: `thm:ld-pasting` at `references/ldt-paper/ld-pasting.tex:12`
- Lean statement: from the base hypotheses on `family` (`Complete`, `ConsistentWithPoints`, `StronglySelfConsistent`, `Bounded`) and `k >= 400md`, produce a full measurement `H` together with `LdPastingConclusion`, i.e. the constructed pasted measurement and the final point-consistency bound.
- Paper proof sketch: assume the sub-measurement theorem, add the missing mass `I - H` to an arbitrary outcome `h*`, and bound the extra inconsistency by the incompleteness of `H`. This is the proof immediately after `lem:ld-pasting-sub-measurement`.
- Assessment: `Compose/package`.
- Why: the proof is short and purely endpoint packaging. Once `ldPastingSubMeas` exists, this should be straightforward.
- Direct dependencies among the 17: `ldPastingSubMeas`.
- Risk notes: low. Mostly bookkeeping around converting a sub-measurement to a measurement and carrying the final error term.

### 2. `ldPastingSubMeas`

- Lean: `MIPStarRE/LDT/Pasting/Theorems.lean:36`
- Paper label: `lem:ld-pasting-sub-measurement` at `references/ldt-paper/ld-pasting.tex:118`
- Lean statement: construct the pasted sub-measurement `H` and package both point-consistency and completeness in `LdPastingSubMeasConclusion`.
- Paper proof sketch: the paper spends the rest of the section building this. Its two outputs come from separate later results:
  consistency with `A` comes from the corollary after `lem:h-b-consistency`,
  and completeness comes from `cor:ld-pasting-N-completeness`.
- Assessment: `Compose/package`, but it is the main packaging node of the section.
- Why: conceptually this theorem is not the deep proof. It is where the two major branches rejoin.
- Direct dependencies among the 17: `hBConsistency`, `ldPastingNCompleteness`.
- Risk notes: low once both branches are formalized; impossible before then.

### 3. `ldDnoteq`

- Lean: `MIPStarRE/LDT/Pasting/Theorems.lean:53`
- Paper label: `prop:ld-dnoteq` at `references/ldt-paper/ld-pasting.tex:177`
- Lean statement: bound the total variation distance between the uniform distribution on `k`-tuples and the distinct-tuple distribution by `k^2 / q`.
- Paper proof sketch: identify TV distance with the probability that a uniform tuple has a collision, then union-bound over the first repeated coordinate. This is a birthday-paradox estimate.
- Assessment: `Standalone-routine`.
- Why: not a composition theorem, but it is an elementary probabilistic counting bound rather than a deep section-level argument.
- Direct dependencies among the 17: none.
- Downstream use: `hBConsistency`, `overAllOutcomes`.
- Risk notes: moderate only because of distribution formalization and TV distance definitions, not because the mathematics is deep.

### 4. `looksEasyButTookMeAWhile`

- Lean: `MIPStarRE/LDT/Pasting/Theorems.lean:85`
- Paper label: `lem:looks-easy-but-took-me-a-while` at `references/ldt-paper/ld-pasting.tex:330`
- Lean statement: for `0 <= lambda <= 1`, prove
  `lambda * (1 - lambda^d) <= 2 * (lambda^(d+1) * (1-lambda))^(1/(d+1))`.
- Paper proof sketch: bound
  `lambda^(d+1) * (1 - lambda^d)^(d+1) <= d * lambda^(d+1) * (1-lambda)`,
  then take `(d+1)`-st roots and use `d^(1/(d+1)) <= 2`.
- Assessment: `Standalone-routine`.
- Why: scalar inequality, short proof.
- Direct dependencies among the 17: none.
- Downstream use among the 17: none on the actual second-construction proof path.
- Risk notes: low mathematically. The only real Lean risk is `Real.rpow` manipulation and edge cases `lambda = 0,1`.
- Important scouting note: this lemma belongs to the paper's discussion of the abandoned first construction, not the actual main proof path that reaches `ldPastingSubMeas`.

### 5. `gCompleteSelfConsistency`

- Lean: `MIPStarRE/LDT/Pasting/Theorems.lean:107`
- Paper label: `lem:g-complete-self-consistency` at `references/ldt-paper/ld-pasting.tex:514`
- Lean statement: from `family.StronglySelfConsistent`, derive `GCompleteSelfConsistencyStatement`, i.e. self-consistency for the complete part `G^x`.
- Paper proof sketch: use projectivity plus the equivalence between strong self-consistency and diagonal overlap; expand
  `||(G^x ⊗ I - I ⊗ G^x) psi||^2`
  and bound it by the assumed self-consistency error.
- Assessment: `Compose/package`.
- Why: short conversion lemma from an assumed hypothesis to the aggregate `G^x` statement.
- Direct dependencies among the 17: none.
- Downstream use: `gBotSelfConsistency`, `commutativitySwitcheroo`, `commutingWithGComplete`, `gHatFacts`.
- Risk notes: low. This should be one of the earliest easy wins on the main line.

### 6. `gBotSelfConsistency`

- Lean: `MIPStarRE/LDT/Pasting/Theorems.lean:117`
- Paper label: `cor:g-bot-self-consistency` at `references/ldt-paper/ld-pasting.tex:537`
- Lean statement: from the self-consistency of the complete part, derive the corresponding statement for the incomplete part `G_bot`.
- Paper proof sketch: use `G_bot = I - G`; then
  `G_bot ⊗ I - I ⊗ G_bot = I ⊗ G - G ⊗ I`,
  so the same norm bound applies directly.
- Assessment: `Compose/package`.
- Why: immediate algebraic corollary.
- Direct dependencies among the 17: `gCompleteSelfConsistency`.
- Risk notes: very low.

### 7. `commutativitySwitcheroo`

- Lean: `MIPStarRE/LDT/Pasting/Theorems.lean:127`
- Paper label: `lem:commutativity-switcheroo` at `references/ldt-paper/ld-pasting.tex:560`
- Lean statement: assuming self-consistency of `G`, self-consistency of an auxiliary projective sub-measurement `M`, and pointwise commutation between `G_g^x` and `M_o^y`, derive aggregate commutation between `G^x` and `M_o^y`.
- Paper proof sketch: expand the commutator norm into four terms, then show each term is close to `<psi | G ⊗ M | psi>` using a sequence of projectivity simplifications, switch-sandwich arguments, and several Cauchy-Schwarz estimates. The central move is: pointwise commutation with each `G_g^x` plus self-consistency lets you pass from commutation with components to commutation with the total `G^x`.
- Assessment: `Deep core`.
- Why: this is the first genuinely technical proof in the section. It is not just chaining prior lemmas; it creates the machinery that later corollaries depend on.
- Direct dependencies among the 17: `gCompleteSelfConsistency`.
- External dependencies: `prop:switch-sandwich`, projectivity facts, triangle / norm machinery.
- Downstream use: `commutingWithGComplete`.
- Risk notes: high. Expect the formalization pain to be in the four-term expansion, managing summed indices, and making the Cauchy-Schwarz steps line up with the library.

### 8. `commutingWithGComplete`

- Lean: `MIPStarRE/LDT/Pasting/Theorems.lean:148`
- Paper label: `cor:commuting-with-G-complete` at `references/ldt-paper/ld-pasting.tex:721`
- Lean statement: from external `ComMainConclusion` and `GCompleteSelfConsistencyStatement`, derive the complete-part commutation package.
- Paper proof sketch: start from `thm:com-main`, which gives commutation of `G_g^x` with `G_h^y`. Apply `commutativitySwitcheroo` once to sum over `h`, getting `G_g^x` commuting with `G^y`; apply it a second time with single-outcome `M = G` to get `G^x` commuting with `G^y`. Then do the exponent bookkeeping.
- Assessment: `Compose/package`.
- Why: once `commutativitySwitcheroo` exists, this is basically a two-step corollary plus error management.
- Direct dependencies among the 17: `commutativitySwitcheroo`, `gCompleteSelfConsistency`.
- Risk notes: medium-low; the main annoyance is error-term simplification.

### 9. `commutingWithGIncomplete`

- Lean: `MIPStarRE/LDT/Pasting/Theorems.lean:160`
- Paper label: `cor:commuting-with-G-incomplete` at `references/ldt-paper/ld-pasting.tex:775`
- Lean statement: derive the analogous commutation package for the incomplete part `G_bot`.
- Paper proof sketch: rewrite commutators using `G_bot = I - G`:
  `G_g^x G_bot^y - G_bot^y G_g^x = G^y G_g^x - G_g^x G^y`,
  and similarly for `G_bot^x G_bot^y`. Then appeal directly to the complete-part commutation corollary.
- Assessment: `Compose/package`.
- Why: almost immediate algebra from the previous theorem.
- Direct dependencies among the 17: `commutingWithGComplete`.
- Risk notes: very low.

### 10. `gHatFacts`

- Lean: `MIPStarRE/LDT/Pasting/Theorems.lean:170`
- Paper label: `cor:G-hat-facts` at `references/ldt-paper/ld-pasting.tex:817`
- Lean statement: bundle self-consistency and commutation for the completed measurement `\widehat G`, combining the complete and incomplete parts.
- Paper proof sketch: self-consistency is the sum of the complete and incomplete cases; commutation is split into the four outcome-type cases `(poly,poly)`, `(poly,bot)`, `(bot,poly)`, `(bot,bot)`, bounded by `eq:quote-com-main` and `cor:commuting-with-G-incomplete`.
- Assessment: `Compose/package`.
- Why: essentially a case split plus summing previous bounds.
- Direct dependencies among the 17: `gCompleteSelfConsistency`, `gBotSelfConsistency`, `commutingWithGComplete`, `commutingWithGIncomplete`.
- Risk notes: low.

### 11. `commuteGHalfSandwich`

- Lean: `MIPStarRE/LDT/Pasting/Theorems.lean:183`
- Paper label: `lem:commute-g-half-sandwich` at `references/ldt-paper/ld-pasting.tex:872`
- Lean statement: move the leftmost `\widehat G` factor past the rest of a `k`-fold product, with the stated error.
- Paper proof sketch: repeatedly use `\widehat G` self-consistency to move a factor to the second tensor component and `\widehat G` commutation to swap adjacent factors. Count how many times each move occurs, then apply the triangle inequality.
- Assessment: `Compose/package`, though it is a technical iterative one.
- Why: the proof is not conceptually new; it is a repeated use of `gHatFacts` with counting.
- Direct dependencies among the 17: `gHatFacts`.
- Downstream use: `ldSandwichLineOnePoint`, `fromHToG`.
- Risk notes: medium. The mathematics is routine, but the Lean proof may need careful handling of repeated approximate-equality chaining and index bookkeeping.

### 12. `ldSandwichLineOnePoint`

- Lean: `MIPStarRE/LDT/Pasting/Theorems.lean:195`
- Paper label: `lem:ld-sandwich-line-one-point` at `references/ldt-paper/ld-pasting.tex:918`
- Lean statement: for a fixed coordinate `i < k`, prove the one-point consistency statement between the sandwiched `\widehat H` and the line measurement.
- Paper proof sketch: first eliminate the unused coordinates by summing them out of the sandwich. Then commute the `i`-th `\widehat G` into the right place using `commuteGHalfSandwich` and two Cauchy-Schwarz steps. Collapse the prefix sum to `I`, and finish with the previously derived `G/B` consistency relation `eq:ld-gbcon`.
- Assessment: `Deep core`.
- Why: this is a dense technical proof with several nested operator manipulations, two substantial Cauchy-Schwarz bounds, and nontrivial use of the sandwich structure.
- Direct dependencies among the 17: `gHatFacts`, `commuteGHalfSandwich`.
- External dependencies: the derived `eq:ld-gbcon` relation from the paper's preliminary reductions.
- Downstream use: `hBConsistency`, `overAllOutcomes`.
- Risk notes: very high. This looks like one of the nastiest formalization points in the whole file.

### 13. `hBConsistency`

- Lean: `MIPStarRE/LDT/Pasting/Theorems.lean:212`
- Paper label: `lem:h-b-consistency` at `references/ldt-paper/ld-pasting.tex:1041`
- Lean statement: from one-point line consistency for every `i < k`, derive full consistency of the pasted `H` with the line measurement `B`.
- Paper proof sketch: expand `H` by tuples and types; if `f != h|_u`, then some active slice `i` must witness disagreement. Replace distinct tuples by uniform tuples via `ldDnoteq`, use a union bound over `i`, and apply `ldSandwichLineOnePoint` to each coordinate.
- Assessment: `Compose/package`.
- Why: the main conceptual idea is already in the previous lemma; this proof is mostly expansion, union bound, and summation.
- Direct dependencies among the 17: `ldDnoteq`, `ldSandwichLineOnePoint`.
- Risk notes: medium. More bookkeeping than new ideas.

### 14. `overAllOutcomes`

- Lean: `MIPStarRE/LDT/Pasting/Theorems.lean:228`
- Paper label: `lem:over-all-outcomes` at `references/ldt-paper/ld-pasting.tex:1141`
- Lean statement: rewrite the completeness of the pasted measurement `H` as the total mass of the sandwiched outcomes of type `tau` with `|tau| >= d+1`, up to the stated error.
- Paper proof sketch:
  start from the exact expression for `H` as a sum over globally consistent tuples;
  show that dropping the global-consistency restriction only loses a small amount;
  insert the `B` measurement;
  add an indicator for line-wise consistency;
  use `ldDnoteq` and the one-point consistency bound to control the tuples that fail the indicator;
  then use a Schwartz–Zippel argument on a witness coordinate to show that a tuple that is line-wise consistent along a random `u` but not globally consistent only survives with probability `md/q`;
  finally swap back from distinct tuples to uniform tuples.
- Assessment: `Deep core`.
- Why: this is a major argument, not a corollary. The "remove the restriction" step and the Schwartz–Zippel witness argument are genuinely central.
- Direct dependencies among the 17: `ldDnoteq`, `ldSandwichLineOnePoint`.
- Risk notes: very high. This is long and structurally subtle, even if each local step is individually standard.

### 15. `fromHToG`

- Lean: `MIPStarRE/LDT/Pasting/Theorems.lean:242`
- Paper label: `lem:from-H-to-G` at `references/ldt-paper/ld-pasting.tex:1295`
- Lean statement: show that the sandwiched-outcome expression can be rewritten as a Bernoulli tail expression in the operator `G`, packaged as `FromHToGStatement`.
- Paper proof sketch:
  define auxiliary matrices `S_{tau_{>= ell}}`;
  prove a one-step recurrence that peels off the `ell`-th coordinate from the sandwich while updating the polynomial in `G` and `I-G`;
  use positivity, commutativity, and the bound `S <= I`;
  move `\widehat G` factors between tensor components using `\widehat G` self-consistency;
  commute the leftmost `\widehat G` through the remaining string using `commuteGHalfSandwich`;
  iterate for `ell = 1, ..., k`.
- Assessment: `Deep core`.
- Why: this is probably the deepest operator-manipulation proof in the section after `commutativitySwitcheroo`. It sets up new notation and runs a nontrivial recurrence argument.
- Direct dependencies among the 17: `commuteGHalfSandwich`.
- Risk notes: extremely high. This looks like the single most time-consuming formalization target besides possibly `ldSandwichLineOnePoint`.

### 16. `chernoffBernoulliMatrix`

- Lean: `MIPStarRE/LDT/Pasting/Theorems.lean:258`
- Paper label: `lem:chernoff-bernoulli-matrix` at `references/ldt-paper/ld-pasting.tex:1671`
- Lean statement: for a PSD contraction `X`, prove the Bernoulli-tail operator has the displayed completeness lower bound, assuming `CompletenessAtLeast ψ X (1-kappa)`.
- Paper proof sketch:
  diagonalize `X` against the reduced state, turning the expectation of `F(X)` into an expectation over eigenvalues;
  use Markov to show most eigenvalue weight lies above `theta`;
  for any scalar eigenvalue `p`, identify `F(p)` with a Bernoulli upper-tail probability and lower-bound it by additive Chernoff;
  combine the two bounds.
- Assessment: `Standalone-routine`.
- Why: it is an independent argument, but it is clean spectral/probabilistic analysis rather than core pasting machinery.
- Direct dependencies among the 17: none.
- Downstream use: `ldPastingNCompleteness`.
- Risk notes: medium. The main Lean work is spectral decomposition and translating the scalar Chernoff bound through the reduced state.

### 17. `ldPastingNCompleteness`

- Lean: `MIPStarRE/LDT/Pasting/Theorems.lean:280`
- Paper label: `cor:ld-pasting-N-completeness` at `references/ldt-paper/ld-pasting.tex:1799`
- Lean statement: establish the completeness lower bound for the constructed pasted sub-measurement.
- Paper proof sketch: approximate `⟨psi, H psi⟩` by the all-outcomes sum using `overAllOutcomes`, rewrite that as `⟨psi, F(G) psi⟩` using `fromHToG`, then apply `chernoffBernoulliMatrix` with `theta = 1/(200m)` and absorb the approximation error into `nu`.
- Assessment: `Compose/package`.
- Why: this is exactly the endpoint corollary of the completeness branch.
- Direct dependencies among the 17: `overAllOutcomes`, `fromHToG`, `chernoffBernoulliMatrix`.
- Risk notes: low once the three inputs exist.

## Which theorems are "easy once dependencies are proved"?

These are the best candidates for quick cleanup after the hard lemmas land:

- `ldPasting`
- `ldPastingSubMeas`
- `gBotSelfConsistency`
- `commutingWithGIncomplete`
- `gHatFacts`
- `ldPastingNCompleteness`

Second tier: not completely trivial, but still mostly compositional:

- `gCompleteSelfConsistency`
- `commutingWithGComplete`
- `commuteGHalfSandwich`
- `hBConsistency`

## Which theorems contain the real new argument?

If I had to prioritize by "this is where the proof difficulty actually lives", the list is:

1. `fromHToG`
2. `ldSandwichLineOnePoint`
3. `commutativitySwitcheroo`
4. `overAllOutcomes`

Comments:

- `fromHToG` is the most structurally elaborate.
- `ldSandwichLineOnePoint` is the nastiest local sandwich manipulation.
- `commutativitySwitcheroo` builds the key mechanism that upgrades pointwise commutation to aggregate commutation.
- `overAllOutcomes` is long and subtle because it controls the loss from dropping global consistency.

## Practical implementation advice

- Clear the easy independent lemmas first:
  `ldDnoteq`, `chernoffBernoulliMatrix`, and optionally `looksEasyButTookMeAWhile`.
- Then finish the `G` infrastructure all the way through `gHatFacts`.
- Treat `commuteGHalfSandwich`, `ldSandwichLineOnePoint`, `overAllOutcomes`, and `fromHToG` as the main project.
- Do not spend much time on `ldPasting` or `ldPastingSubMeas` before the branch endpoints exist; they are packaging, not blockers.
- If triaging for maximum theorem-count progress, `looksEasyButTookMeAWhile` is low-hanging fruit but not on the main path.
- If triaging for progress toward the final result, `looksEasyButTookMeAWhile` should be postponed.

## Bottom line

The file is not 17 equally hard theorems.

- About half are packaging or short corollaries.
- Three are independent side lemmas (`ldDnoteq`, `looksEasyButTookMeAWhile`, `chernoffBernoulliMatrix`).
- Four are the real proof bottlenecks:
  `commutativitySwitcheroo`, `ldSandwichLineOnePoint`, `overAllOutcomes`, `fromHToG`.

If those four are done, the rest of the file should collapse fairly quickly.
