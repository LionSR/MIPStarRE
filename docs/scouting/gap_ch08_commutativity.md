# Chapter 8 Gap Analysis: Commutativity

Date: 2026-04-04

## Scope

Files inspected:

- `references/ldt-paper/commutativity-G.tex`
- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
- `MIPStarRE/LDT/Commutativity/Defs.lean`
- `MIPStarRE/LDT/Commutativity/Theorems.lean`
- `MIPStarRE/LDT/CommutativityPoints/Defs.lean`
- `MIPStarRE/LDT/CommutativityPoints/Theorem.lean`

## Executive Summary

- The blueprint covers the four main statement labels from the paper chapters:
  `thm:commutativity-points`, `lem:comm-data-processed-g`,
  `lem:normalization-condition`, and `thm:com-main`.
- The two paper claims
  `clm:g-comm-stability` and `clm:g-comm-stability2`
  are not present as blueprint labels. The blueprint proof of
  `lem:comm-data-processed-g` mentions them only informally as
  "two boundedness-driven stability claims."
- Lean already has substantial scaffolding for both chapters:
  point-level product families, evaluated/full-slice product families,
  packaged conclusion structures, and a complete formal statement of
  `lem:normalization-condition`.
- The main formalization gap is not just "missing proofs." In
  `MIPStarRE/LDT/Commutativity/Defs.lean`, the current candidates for the two
  missing stability claims are explicitly marked
  `MISMATCH(#143)`: they omit the right-register factors that appear in the
  paper claims. So the current Lean scaffold is only a partial match.
- `CommutativityPoints` is closer to the paper than `Commutativity`: the first
  consistency-to-approximation bridge is proved, but the four operator-bridge
  steps and the final theorem are still `sorry`.
- `commDataProcessedG` and the final `comMain.fullSliceCommutation` are still
  mostly unproved. The exact postprocessing identity used to specialize full
  slice products to evaluated slice products is present, but the two
  Schwartz-Zippel comparison steps from the paper are not yet formalized.

## 1. Statement-Level Comparison: Paper vs Blueprint

The blueprint chapter has five labels total if one counts the chapter label
`chap:commutativity`. Among mathematical statement labels, it has four, and
those are the four main paper statements.

### `thm:commutativity-points`

Status: match

Paper:

- Good symmetric strategy for the `(m,q,d)` low individual degree test.
- Average over independent uniform `u,v : F_q^m`.
- Conclusion:
  `(A_a^u A_b^v) \ot I \approx_{32\gamma m} (A_b^v A_a^u) \ot I`.

Blueprint:

- Same strategy hypothesis.
- Same averaging.
- Same displayed error term and conclusion.

Lean status:

- Faithful theorem shell exists as
  `MIPStarRE.LDT.CommutativityPoints.commutativityPoints`.
- The proof structure mirrors the paper very closely via the fields
  `orderedLiftToMixedBridge`, `orderedLiftToLineBridge`,
  `diagonalLineProjectiveSwap`, `reversedDropFromLineBridge`,
  `reversedDropToPointsBridge`, and `pointwiseCommutation`.

Verdict:

- No statement-level mismatch worth flagging.

### `lem:comm-data-processed-g`

Status: near match, but blueprint statement is not fully self-contained

Paper:

- Explicitly quantifies a good symmetric strategy:
  `(psi, A, B, L)` is an `(\eps,\delta,\gamma)`-good symmetric strategy for
  the `(m+1,q,d)` low individual degree test.
- Then assumes three properties of the projective family `\{G^x\}`.
- Conclusion:
  `G_a^{u,x} G_b^{v,y} \ot I \approx_{48m(\gamma^{1/2}+\zeta^{1/2})}
  G_b^{v,y} G_a^{u,x} \ot I`.

Blueprint:

- Gives the three `G^x` hypotheses and the same conclusion/error term.
- Uses the same abbreviation `G_a^{u,x} = G^x_[g(u)=a]`.

Mismatches / omissions:

- The blueprint does not explicitly quantify the strategy
  `(psi,A,B,L)`, even though `A` and `\psi` appear in the hypotheses.
  So as written, the lemma is a compressed restatement, not a fully faithful
  standalone statement.
- In the boundedness bullet, the paper says:
  for each `x` and each polynomial `g`,
  `Z^x >= (E_u A^{u,x}_{g(u)})`.
  The blueprint writes
  `Z^x \ge E_u A_{g(u)}^{u,x}` without the explicit "for each `g`"
  quantifier. The intended meaning is clear, but the quantifier is omitted.

Lean status:

- The theorem shell exists as
  `MIPStarRE.LDT.Commutativity.commDataProcessedG`.
- Its hypotheses are represented by
  `strategy.IsGood`, `family.ConsistentWithPoints`,
  `family.StronglySelfConsistent`, and `family.Bounded`.
- The output package `CommDataProcessedGConclusion` already allocates slots
  for the two missing stability claims and the final commutation statement.

Verdict:

- The mathematical target is aligned with the paper.
- The blueprint statement should be treated as a compressed restatement, not a
  line-for-line faithful copy.

### `lem:normalization-condition`

Status: match

Paper:

- `P` is a submeasurement, `Q` is a projective submeasurement.
- `C_{a,b} = Q_b P_a Q_b`.
- Conclusion:
  `\sum_a (\sum_b C_{a,b})^\dagger (\sum_b C_{a,b})
   = \sum_a (\sum_b C_{a,b}) (\sum_b C_{a,b})^\dagger <= I`.

Blueprint:

- Same hypotheses.
- Same definition of `C_{a,b}`.
- Same displayed equality and bound.

Lean status:

- Fully matched by
  `MIPStarRE.LDT.Commutativity.normalizationCondition`.
- The corresponding operator families are implemented in
  `Defs.lean`, and the theorem is proved.

Verdict:

- Faithful match.

### `thm:com-main`

Status: mostly aligned, but blueprint compresses the paper's hypotheses

Paper:

- Explicitly quantifies a good symmetric strategy and the projective family
  `\{G^x\}` with the same three hypotheses as in
  `lem:comm-data-processed-g`.
- Conclusion:
  `G_g^x G_h^y \ot I \approx_{30m(\gamma^{1/4}+\zeta^{1/4}+(d/q)^{1/4})}
  G_h^y G_g^x \ot I`.

Blueprint:

- Replaces the full paper hypothesis block with:
  "Let `\{G^x\}` satisfy the same hypotheses as in
  Lemma~`lem:comm-data-processed-g`."
- Averages over independent `x,y \sim F_q`, not over sampled
  `((u,x),(v,y))`.

Comments:

- The displayed formula depends only on `x,y,g,h`, so averaging over `x,y`
  is the natural simplified form. This is a harmless compression.
- The theorem relies on the previous lemma to carry the strategy hypotheses.
  That is acceptable only if `lem:comm-data-processed-g` is itself
  self-contained. In the current blueprint it is not fully self-contained for
  the reason noted above.
- The paper theorem statement itself is slightly awkward about dimensions:
  the theorem header says strategy for `(m,q,d)`, while one hypothesis still
  averages over `(u,x) \in F_q^{m+1}`. Lean avoids restating this and instead
  packages everything through the previous lemma.

Lean status:

- The theorem shell exists as `MIPStarRE.LDT.Commutativity.comMain`.
- The exact postprocessing identity
  `evaluatedFromFullSliceProduct* = evaluatedSliceProduct*`
  is already formalized in the `evaluationSpecialization` field.
- The main final theorem field `fullSliceCommutation` is still `sorry`.

Verdict:

- The displayed conclusion matches the paper, but the blueprint is a
  compressed rather than literal restatement.

## 2. Missing Paper Labels from the Blueprint

These are the two missing theorem-like labels the user pointed out.

### 2.1 `clm:g-comm-stability`

Source:

- `references/ldt-paper/commutativity-G.tex:134-180`

Exact paper statement:

```tex
\begin{align*}
    &\E_{\bu,\bv,\bx,\by} \sum_{a,b} \bra{\psi} G^{\bu,\bx}_a  G^{\bv,\by}_b G^{\bu,\bx}_a G^{\by}  \ot A^{\bv,\by}_b \ket{\psi} \\
    \approx_{\sqrt{\zeta}}& \E_{\bu,\bv,\bx,\by} \sum_{a,b} \bra{\psi} G^{\bu,\bx}_a  G^{\bv,\by}_b G^{\bu,\bx}_a  \ot A^{\bv,\by}_b \ket{\psi}.
\end{align*}
```

Where it is used in the proof chain:

- It is invoked immediately after `eq:apply-add-an-a-once`.
- Its only purpose is to justify the step labeled `eq:gcom9`.
- Conceptually, it removes the trailing total projector `G^y` from the left
  register while keeping the Bob-side point projector `A_b^{v,y}` on the
  right register.
- This is the first of the two boundedness-driven "stability" steps inside
  `lem:comm-data-processed-g`.

Lean counterpart:

- Partial scaffold exists:
  `commDataProcessedGStabilityOneLeft`,
  `commDataProcessedGStabilityOneRight`,
  `CommDataProcessedGConclusion.stabilityOne`,
  and the `stabilityOne := by sorry` slot in `commDataProcessedG`.
- However, the current scaffold is not faithful to the paper claim.
  `Defs.lean` already says this explicitly via:
  `MISMATCH(#143): missing right-register factors per clm:g-comm-stability`.
- In the paper claim, the compared quantities carry the right-register factor
  `\ot A_b^{v,y}`.
  The current Lean families only encode the left-register operators
  `G_a^{u,x} G_b^{v,y} G_a^{u,x} G^y` and
  `G_a^{u,x} G_b^{v,y} G_a^{u,x}`
  after left tensor placement. The Bob-side factor is missing.

Estimated difficulty:

- High.
- Reason: the proof itself is not conceptually the hardest part, but the
  operator family being compared has to be refactored first. One likely needs
  new opfamily wrappers that carry both the Alice-side left tensor factor and
  the Bob-side evaluated point factor, plus bridge lemmas for `SDDOpRel` on
  those richer families.

### 2.2 `clm:g-comm-stability2`

Source:

- `references/ldt-paper/commutativity-G.tex:184-222`

Exact paper statement:

```tex
\begin{align*}
    &\E_{\bu,\bv,\bx,\by} \sum_{a,b} \bra{\psi} G^{\bu,\bx}_a  G^{\bv,\by}_b G^{\bx}  \ot A^{\bu,\bx}_a A^{\bv,\by}_b  \ket{\psi}  \\
    \approx_{\sqrt{\zeta}+6\sqrt{\gamma(m+1)}}& \E_{\bu,\bv,\bx,\by} \sum_{a,b} \bra{\psi} G^{\bu,\bx}_a  G^{\bv,\by}_b \ot A^{\bu,\bx}_a A^{\bv,\by}_b  \ket{\psi}.
\end{align*}
```

Where it is used in the proof chain:

- It is invoked immediately after the intermediate line
  `eq:dunno-what-i-should-call-this`.
- Its only purpose is to justify the step labeled `eq:gcom10`.
- Conceptually, it removes the trailing total projector `G^x` after the point
  measurements have already been commuted using
  `thm:commutativity-points`.
- This is the second boundedness-driven stability step inside
  `lem:comm-data-processed-g`.

Lean counterpart:

- Partial scaffold exists:
  `commDataProcessedGStabilityTwoLeft`,
  `commDataProcessedGStabilityTwoRight`,
  `CommDataProcessedGConclusion.stabilityTwo`,
  and the `stabilityTwo := by sorry` slot in `commDataProcessedG`.
- The error term is already packaged faithfully as
  `commDataProcessedGStabilityTwoError`.
- But again the current operator families are not faithful to the paper claim.
  `Defs.lean` marks them with the same `MISMATCH(#143)` comment.
- In the paper claim, the right register carries
  `A_a^{u,x} A_b^{v,y}`.
  The current Lean scaffold only compares left-placed operator products,
  missing the Bob-side factor entirely.

Estimated difficulty:

- High.
- Slightly harder than `clm:g-comm-stability`, because it also depends on the
  point-commutativity theorem as an internal step and not just on boundedness.

## 3. Equation Labels vs Current Lean Proof Steps

The table below focuses on labeled equations in the two paper chapters.
Status meanings:

- `present`: there is an explicit Lean theorem/field closely matching the step.
- `scaffolded`: the relevant families or theorem slots exist, but the proof is
  still missing.
- `partial/mismatch`: there is a candidate Lean object, but it does not yet
  encode the same operator expression as the paper.
- `absent`: no clear dedicated Lean counterpart in these files.

### 3.1 `commutativity-points.tex`

| Paper label | Role in paper | Lean status |
| --- | --- | --- |
| `eq:point-diagonal-line-approx` | Converts diagonal-line consistency into state-dependent distance | present: `sampledDiagonalLineApproximation` is proved in `CommutativityPoints/Theorem.lean` |

Notes:

- The four unlabeled approximation/equality steps after
  `eq:point-diagonal-line-approx` are individually scaffolded by
  `orderedLiftToMixedBridge`, `orderedLiftToLineBridge`,
  `diagonalLineProjectiveSwap`, `reversedDropFromLineBridge`, and
  `reversedDropToPointsBridge`, but all five are still `sorry`.

### 3.2 `commutativity-G.tex`

| Paper label | Role in paper | Lean status |
| --- | --- | --- |
| `eq:gcom8` | Expands the evaluated commutator norm into two quartic terms | scaffolded: target packaged by `evaluatedSliceCommutation`, but no explicit proof step yet |
| `eq:sum-of-gux` | Shows `\sum_a G_a^{u,x} = G^x` | partial: implicit in the definition of `evaluatedPointFamily`, but not exposed as a local lemma |
| `eq:add-an-a` | Uses consistency plus `cons-sub-meas` to insert `A_a^{u,x}` | absent as a dedicated theorem in these files |
| `eq:apply-add-an-a-once` | First application of `eq:add-an-a` inside the quartic term | absent |
| `eq:gcom9` | Result of `clm:g-comm-stability` | partial/mismatch: intended by `stabilityOne`, but current families omit the Bob-side factor |
| `eq:dunno-what-i-should-call-this` | Inserts `A_a^{u,x}` and then commutes point measurements | scaffolded only at a very high level through `commutativityPoints`; no dedicated Lean step |
| `eq:gcom10` | Result of `clm:g-comm-stability2` | partial/mismatch: intended by `stabilityTwo`, but current families omit the Bob-side factor |
| `eq:gonna-cite-this-in-just-a-bit` | Two more `eq:add-an-a` rewrites after `eq:gcom10` | absent |
| `eq:new-fact-that-i-derived` | Postprocessed self-consistency of `G_a^{u,x}` | scaffolded: `postprocessedSelfConsistency` field exists, proof still `sorry` |
| `eq:g-comm-stab1` | First claim's left-hand side, before bounding the gap | partial/mismatch: closest object is `commDataProcessedGStabilityOneLeft`, but it lacks `\ot A_b^{v,y}` |
| `eq:bound-this-right-now!` | Rewrites claim 1 gap using auxiliary family `R_g^y` | absent: no Lean definition of `R_g^y` or analogous family |
| `eq:just-got-commuted` | First line of claim 2 proof after commuting point measurements | absent as an explicit theorem; only the error term is packaged |
| `eq:g-comm-stab7` | Rewrites claim 2 gap by summing over polynomials `g` | absent |
| `eq:gcomterms` | Expands the full-slice commutator norm into two quartic terms | scaffolded: target packaged by `fullSliceCommutation`, but proof missing |
| `eq:gcom4` | Converts the second quartic term into a mixed overlap using `closeness-of-ip` and the normalization lemma | absent as a dedicated theorem |
| `eq:evaluate-gcom-at-points` | First Schwartz-Zippel evaluation step, replacing `g` by `g(u)` | absent: `evaluationSpecialization` proves an exact postprocess identity, not this approximate averaging step |
| `eq:gcom4-diff` | Explicit difference term for the first Schwartz-Zippel step | absent |
| `eq:don't-understand-the-numbering-system` | Two closeness-of-ip rewrites on the evaluated expression | absent |
| `eq:evaluate-gcom-at-points-part-dos` | Second Schwartz-Zippel evaluation step, replacing `h` by `h(v)` | absent |
| `eq:eq:don't-understand-the-numbering-system-diff` | Explicit difference term for the second Schwartz-Zippel step | absent |

Bottom line for the equation-level comparison:

- The point chapter has one labeled equation, and it already has a direct Lean
  counterpart.
- In the main commutativity chapter, only the global endpoints are scaffolded.
  Most of the labeled intermediate equations are not yet broken out as Lean
  lemmas.
- The two labeled stability equations are the most important missing pieces,
  because the current scaffold for them is structurally wrong, not merely
  unproved.

## 4. Lean File-by-File Readout

### `MIPStarRE/LDT/CommutativityPoints`

What already matches the paper well:

- Product-family definitions for the ordered and reversed point products.
- The sampled diagonal-line bridge families.
- Error terms:
  `restrictedDiagonalLinesConsistencyError`,
  `pointDiagonalLineApproxError`,
  `commutativityPointsError`.
- The theorem statement structure tracks the proof chain very closely.

What is still missing:

- The five operator-comparison steps from the paper proof are all still
  `sorry`.
- So `thm:commutativity-points` is statement-faithful but proof-incomplete.

Assessment:

- This chapter is in good scaffolding shape. It looks like a straightforward
  "finish the proof chain" task, not a redesign task.

### `MIPStarRE/LDT/Commutativity`

What already matches the paper well:

- Definitions of evaluated/full-slice product families.
- Postprocessing from full-slice outcomes to evaluated outcomes.
- Full formalization of `lem:normalization-condition`.
- Exact proof that postprocessing a full-slice product equals the evaluated
  product (`evaluationSpecialization` inside `comMain`).

What is still missing or mismatched:

- `commDataProcessedG` is mostly a shell:
  `postprocessedSelfConsistency`, `stabilityOne`, `stabilityTwo`, and
  `evaluatedSliceCommutation` are all `sorry`.
- The four stability operator-family definitions are already marked with
  `MISMATCH(#143)` and need redesign.
- There is no formal Lean analogue yet of the paper's auxiliary family
  `R_g^y`.
- The two Schwartz-Zippel comparison steps in `thm:com-main` are not modeled
  as dedicated lemmas.
- `fullSliceCommutation` is still `sorry`.

Assessment:

- This chapter is not just proof-incomplete; it is partially scaffolded around
  operator families that do not yet match the paper's stated claims.

## 5. Practical Formalization Order

If the goal is to close the paper/blueprint/Lean gap with minimal rework, the
best order looks like this:

1. Finish `CommutativityPoints.commutativityPoints`.
   Its proof chain is already laid out explicitly and is a dependency of the
   second stability claim.

2. Refactor the four stability opfamilies in
   `MIPStarRE/LDT/Commutativity/Defs.lean`.
   They need to carry the Bob-side factors from the paper claims, not just
   left-placed Alice-side operators.

3. Prove `postprocessedSelfConsistency`.
   This is the clean Lean counterpart of `eq:new-fact-that-i-derived` and is
   used repeatedly later.

4. Add dedicated lemmas for the two missing claims
   `clm:g-comm-stability` and `clm:g-comm-stability2`.
   They should become blueprint items or, at minimum, named Lean lemmas.

5. Use those lemmas to finish `evaluatedSliceCommutation`
   in `commDataProcessedG`.

6. Add the two Schwartz-Zippel evaluation lemmas for `comMain`.
   The current `evaluationSpecialization` identity is useful, but it does not
   replace the paper's approximate evaluation-removal steps.

7. Finish `fullSliceCommutation`.

## 6. Short Answer to the Core Question

The blueprint is missing exactly the two internal stability claims
`clm:g-comm-stability` and `clm:g-comm-stability2`, and those are also the
most important missing pieces in Lean. There is already Lean scaffolding for
them, but it is not faithful to the paper because the current candidate
operator families omit the right-register point-measurement factors. That
operator mismatch is the main gap between the paper proof and the current
formalization scaffold for Chapter 8.
