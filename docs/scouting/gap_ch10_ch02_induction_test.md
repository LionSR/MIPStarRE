# Gap Analysis: Paper vs Blueprint vs Lean for Induction Step and Test Definition

Date: 2026-04-04

## Scope Read

Paper:

- `references/ldt-paper/inductive_step.tex` (625 lines)
- `references/ldt-paper/test_definition.tex` (211 lines)
- `references/ldt-paper/introduction.tex` (read for `thm:raz-safra`, `thm:classical-test-soundness`)

Blueprint:

- `blueprint/src/chapter/ch10_induction.tex`
- `blueprint/src/chapter/ch02_test.tex`
- `blueprint/src/chapter/ch01_overview.tex`

Lean:

- `MIPStarRE/LDT/MainInductionStep/Defs.lean`
- `MIPStarRE/LDT/MainInductionStep/Statements.lean`
- `MIPStarRE/LDT/MainInductionStep/Theorems.lean`
- `MIPStarRE/LDT/Test/Defs.lean`
- `MIPStarRE/LDT/Test/Strategy.lean`
- `MIPStarRE/LDT/Test/MainTheorem.lean`

I also checked nearby dependencies when they were clearly relevant:

- `blueprint/src/chapter/ch03_preliminaries.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
- `MIPStarRE/LDT/Preliminaries/Theorems.lean`
- `MIPStarRE/LDT/SelfImprovement/Theorems.lean`
- `MIPStarRE/LDT/Pasting/Theorems.lean`
- `MIPStarRE/LDT/MakingMeasurementsProjective/Theorems.lean`

## Executive Summary

The paper-to-blueprint compression is substantial but mostly intentional:

- `ch02_test.tex` keeps the test/game definitions and `thm:main-formal`, but drops the paper's introductory classical context theorems and the paper-local notation/remark layer.
- `ch10_induction.tex` keeps the restricted-strategy definitions, the restricted-probabilities lemma, the section-local self-improvement wrapper, and the main induction theorem, but it does not keep the paper's local label `thm:ld-pasting-in-induction-section`; instead it points directly to the global pasting theorem `thm:ld-pasting` from Chapter 9.
- The blueprint also compresses almost all labeled intermediate equations in `inductive_step.tex` into prose. Those equations are exactly the proof skeleton that Lean will need to materialize as local `have`s or helper lemmas.

The Lean state is more incomplete than the blueprint alone suggests:

- `MIPStarRE.LDT.Test.mainFormal` is still `sorry`.
- `MIPStarRE.LDT.MainInductionStep.mainInduction`, `selfImprovementInInductionSection`, `ldPastingInInductionSection`, and `restrictedProbabilities` are all still `sorry`.
- The two deepest downstream dependencies of the Chapter 10 proof are also still incomplete: `SelfImprovement.selfImprovement` and `MakingMeasurementsProjective.orthonormalizationMainLemma`, and the global pasting development still has many `sorry`s.

Most important structural mismatch in the original scout (resolved in #593):

- At scout time, the paper and blueprint treated the restricted diagonal-line measurement as a genuine projective measurement for the `(m,q,d)` slice game, while Lean weakened it to a projective submeasurement `RestrictedSymStrat.diagonalMeasurement : IdxProjSubMeas ...` in `MIPStarRE/LDT/MainInductionStep/Defs.lean`.
- At scout time, `RestrictedProbabilitiesStatement` also weakened the diagonal averaging bounds to a `1/q`-weighted statement via `sliceDiagonalDirectionWeight` and `sliceDiagonalConditioningLoss`, instead of the paper/blueprint factor `((m+1)/m)`.
- Issue #593 resolves this historical mismatch by upgrading the restricted diagonal branch to a genuine measurement encoding and by using the shared paper-faithful conditioning factor `((m+1)/m)` for both the axis-parallel and diagonal branches.
- The remaining Chapter 10 blockers are the unfinished theorem proofs listed above, not this diagonal-branch packaging issue.

## Key Missing Labels

### 1. `thm:ld-pasting-in-induction-section`

Source: `references/ldt-paper/inductive_step.tex:299-338`

Exact paper statement:

> **Theorem [Pasting].** Let $(\psi, A, B, L)$ be an $(\eps, \delta, \gamma)$-good symmetric strategy for the $(m+1,q,d)$ low individual degree test.
> Let $\{G^x\}_{x \in \F_q}$ denote a set of projective sub-measurements in $\polysub{m}{q}{d}$ with the following properties:
>
> 1. **(Completeness):** If $G = \E_{\bx} \sum_g G^{\bx}_g$, then
>    \[
>    \bra{\psi} G \otimes I \ket{\psi} \geq 1 - \kappa.
>    \]
> 2. **(Consistency with~$A$):** On average over $(\bu, \bx) \sim \F_q^{m+1}$,
>    \[
>    A^{u, x}_a \otimes I \simeq_{\zeta} I \otimes G^x_{[g(u)=a]}.
>    \]
> 3. **(Strong self-consistency):** On average over~$\bx \sim \F_q$,
>    \[
>    G^x_g \otimes I \approx_{\zeta} I \otimes G^x_g.
>    \]
> 4. **(Boundedness):** There exists a positive-semidefinite matrix $Z^x$ for each $x \in \F_q$ such that
>    \[
>    \E_{\bx} \bra{\psi} (I-G^{\bx})\otimes Z^{\bx} \ket{\psi} \leq \zeta
>    \]
>    and for each $x \in \F_q$ and $g \in \polyfunc{m}{q}{d}$,
>    \[
>    Z^x \geq \left(\E_{\bu} A^{\bu, x}_{g(\bu)}\right).
>    \]
>
> Let $k \geq 400md$ be an integer. Let
> \[
> \nu = 100 k^2m \cdot \left(\eps^{1/32} + \delta^{1/32} + \gamma^{1/32} + \zeta^{1/32} + (d/q)^{1/32}\right),
> \]
> \[
> \sigma = \kappa \cdot \left(1 + \frac{1}{100m}\right)
>  + 2\nu + e^{- k/(80000m^2)}.
> \]
> Then there exists a ``pasted" measurement $H \in \polymeas{m+1}{q}{d}$ which satisfies the following property.
> 1. **(Consistency with~$A$):** On average over $\bu \sim \F_q^{m+1}$,
>    \[
>    A^{u}_a \otimes I \simeq_{\sigma} I \otimes H_{[h(u)=a]}.
>    \]

Needed for formalization?

- Yes. This is not expository.
- It is one of the three core engines of the induction chapter:
  restricted slicing -> self-improvement on each slice -> pasting back to ambient dimension.

Blueprint counterpart:

- The blueprint does not keep this source-local label in Chapter 10.
- Instead, it merges the paper-local theorem into the global Chapter 9 theorem `thm:ld-pasting` at `blueprint/src/chapter/ch09_pasting.tex:5-35`.
- `blueprint/src/chapter/ch10_induction.tex:89-99` then cites `thm:ld-pasting` directly.

Lean counterpart:

- Present as a theorem stub:
  `MIPStarRE.LDT.MainInductionStep.ldPastingInInductionSection`
  in `MIPStarRE/LDT/MainInductionStep/Theorems.lean:57-79`.
- The global pasting theorem also exists as a stub:
  `MIPStarRE.LDT.Pasting.ldPasting`
  in `MIPStarRE/LDT/Pasting/Theorems.lean:18-33`.
- The blueprint explicitly maps the same theorem label to both Lean names:
  `blueprint/src/chapter/ch09_pasting.tex:6`.

Dependencies:

- Input hypotheses package:
  completeness, consistency with points, strong self-consistency, boundedness.
- Quantitative error bookkeeping:
  `ldPastingInInductionNu` and `ldPastingInInductionError`
  in `MIPStarRE/LDT/MainInductionStep/Defs.lean:268-283`.
- Global pasting chapter:
  Chapter 9 / `MIPStarRE/LDT/Pasting/*`.
- Upstream uses of good-strategy characterization and `\simeq`/`\approx` transport.

Current blocker:

- The local wrapper is intentionally left as `sorry` because `MainInductionStep` currently sits earlier in the import graph than the global `Pasting` theorems, and the direct wrapper would create an import cycle.

Verdict:

- Needed, blueprint-compressed, Lean statement present, proof absent.

### 2. `thm:raz-safra`

Source: `references/ldt-paper/introduction.tex:43-49`

Exact paper statement:

> **Theorem [Raz-Safra~\cite{RS97}].**
> Suppose Provers~$\mathrm{A}$ and~$\mathrm{B}$ pass the $k = 2$ surface-versus-point low-degree test with probability~$1-\eps$.
> Then there exists a degree-$d$ polynomial $g:\F_q^m \rightarrow \F_q$ such that
> \[
> \Pr_{\bu \sim \F_q^m}[g(\bu) = \ba] \geq 1 - \eps - \poly(m) \cdot \poly(d/q).
> \]

Needed for formalization?

- No, not for the current Lean target.
- This is classical background in the introduction.
- It does not enter the blueprint dependency chain toward `thm:main-formal`.

Blueprint counterpart:

- None in `ch01_overview.tex`.
- The blueprint overview keeps only the informal theorem and the dependency sketch.

Lean counterpart:

- None in `MIPStarRE/LDT/MainInductionStep/` or `MIPStarRE/LDT/Test/`.
- No nearby Lean formalization of this classical theorem was found.

Dependencies:

- Only narrative context in the introduction.
- No proof dependency into Chapter 2 or Chapter 10.

Verdict:

- Expository only for this project slice.

### 3. `thm:classical-test-soundness`

Source: `references/ldt-paper/introduction.tex:69-75`

Exact paper statement:

> **Theorem [Polishchuk-Spielman~\cite{PS94}].**
> Suppose Provers~$\mathrm{A}$ and~$\mathrm{B}$ pass the low individual degree test with probability~$1-\eps$.
> Then there exists a polynomial $g:\F_q^m \rightarrow \F_q$ with individual degree~$d$ such that
> \[
> \Pr_{\bu \sim \F_q^m}[g(\bu) = \ba] \geq 1 -  \poly(m) \cdot (\poly(\eps) + \poly(d/q)).
> \]

Needed for formalization?

- No, not as a theorem to formalize inside this Lean development.
- It is a classical benchmark/result that the paper says it is extending to the quantum setting.

Blueprint counterpart:

- None in `ch01_overview.tex`.
- The omission looks intentional: the blueprint is organized around theorem ownership for the target proof, not around historical/classical context.

Lean counterpart:

- None in `MIPStarRE/LDT/MainInductionStep/` or `MIPStarRE/LDT/Test/`.

Dependencies:

- Only used in the introduction to explain the meaning of the main informal theorem.
- It is cited later in `introduction.tex:215-216`, not in the proof chain.

Verdict:

- Expository/contextual only for this project slice.

### 4. `rem:good-strat-characterization`

Source: `references/ldt-paper/test_definition.tex:137-153`

Exact paper statement:

> **Remark.**
> Using notation which will be introduced in \Cref{sec:comparing-measurements} below,
> a symmetric strategy is $(\eps, \delta, \gamma)$-good
> if and only if it satisfies the following three conditions.
> For $\bell$ and $\bu$ as in the axis-parallel lines test,
> \[
> A^u_a \ot I \simeq_{\eps} I \ot B^{\ell}_{[f(u)=a]},
> \quad
> \text{and}
> \quad
> A^u_a \ot I \simeq_{\delta} I \ot A^u_a.
> \]
> And for $\bell$ and $\bu$ as in the diagonal lines test,
> \[
> A^u_a \ot I \simeq_{\gamma} I \ot L^{\ell}_{[f(u)=a]}.
> \]

Needed for formalization?

- Yes, effectively.
- Even though it is only a remark in the paper, it is operationally a reusable lemma.
- The blueprint correctly upgrades it to a formal lemma:
  `lem:good-strategy-characterization`
  in `blueprint/src/chapter/ch03_preliminaries.tex:61-74`.
- It is used later in the blueprint's variance, commutativity, and pasting chapters.

Blueprint counterpart:

- Yes, but renamed and promoted from a remark to a lemma.

Lean counterpart:

- No direct named counterpart was found in `MIPStarRE/LDT/MainInductionStep/` or `MIPStarRE/LDT/Test/`.
- There is enough infrastructure to state and prove it:
  `SymStrat.IsGood` in `MIPStarRE/LDT/Test/Strategy.lean:142-148`
  and `Preliminaries.simeqForMeasurements` in
  `MIPStarRE/LDT/Preliminaries/Theorems.lean:17-26`.
- But the lemma itself is currently missing from Lean.

Dependencies:

- `def:good-strategy`
- `def:simeq`
- `prop:simeq-for-measurements`

Why it matters here:

- The induction chapter itself does not cite the label directly.
- But the local pasting proof chain downstream does.
- So this remark is part of the real dependency surface of the induction chapter, not optional commentary.

Verdict:

- Needed, blueprint-renamed, Lean counterpart missing.

### 5. `not:conditioned-on-last-direction`

Source: `references/ldt-paper/test_definition.tex:155-166`

Exact paper statement:

> **Notation.**
> Our proof will be via induction,
> i.e. proving soundness of the $(m+1,q,d)$-low individual degree test
> using the soundness of the $(m,q,d)$-low individual degree test.
> To do this, we will frequently use the axis-parallel line test in the specific case of $i = m+1$.
> Thus, it will be convenient to introduce the following notation.
> Let $(\psi, A, B, L)$ be a symmetric strategy for the $(m+1, q, d)$-low individual degree test,
> Then for each $u \in \F_q^m$ we will write $B^u_f$ as shorthand for $B^{\ell}_f$,
> where $\ell = \{(u, x) \mid x \in \F_q\}$.
> For a function $f:\ell \rightarrow \F_q$,
> we will also sometimes write $f(x)$ as shorthand for $f(u,x)$.

Needed for formalization?

- The notation itself is expository.
- The semantic content is needed:
  fixing the last coordinate, embedding lines into a slice, and evaluating a slice family at `(u,x)`.

Blueprint counterpart:

- No explicit notation block in `ch02_test.tex` or `ch10_induction.tex`.
- The blueprint replaces the notation by explicit definitions:
  `def:append-x` and `def:restricted-strategy`
  in `blueprint/src/chapter/ch10_induction.tex:7-21`.

Lean counterpart:

- No direct notation alias like `B^u_f`.
- Semantic counterparts do exist:
  - `appendPoint`, `truncatePoint`, `pointHeight` in `MIPStarRE/LDT/Basic/Parameters.lean:125-145`
  - `AxisParallelLine.appendAtHeight` and `DiagonalLine.appendAtHeight` in `MIPStarRE/LDT/Basic/Parameters.lean:177-202`
  - `liftAxisAnswer`, `liftDiagonalAnswer`, `xRestrictedStrategy` in `MIPStarRE/LDT/MainInductionStep/Defs.lean:20-28, 209-215`
  - `IdxPolyFamily.evaluatedAtNextPoint` in `MIPStarRE/LDT/Test/Strategy.lean:255-261`

Dependencies:

- The induction-on-dimension viewpoint.
- Slice embedding/restriction operators.
- Later use in the paper's pasting chapter:
  `references/ldt-paper/ld-pasting.tex:64-68`.

Verdict:

- Expository as notation, but semantically important.
- No missing theorem here; the real issue is whether the Lean slice encoding matches the paper. On the diagonal branch, it currently does not.

## Intermediate Equation Audit for `inductive_step.tex`

These labeled equations are the actual proof skeleton hidden by the blueprint prose. Most of them belong to the proof of `thm:main-formal`; the last two are arithmetic steps inside `thm:main-induction`.

| Label | Source lines | Exact content | Lean counterpart in target dirs? | Role / dependencies |
| --- | --- | --- | --- | --- |
| `eq:just-applied-induction` | `inductive_step.tex:77-82` | `(A_sym)^u_a ⊗ I \simeq_σ I ⊗ G_[g(u)=a]` and `G_[g(u)=a] ⊗ I \simeq_σ I ⊗ (A_sym)^u_a` | No named counterpart | First output of applying `thm:main-induction` to the symmetrized strategy. Depends on symmetrization and `mainInduction`. |
| `eq:cons-a` | `inductive_step.tex:107` | `G^{A}_{[g(u)=a]} ⊗ I \simeq_{2σ} I ⊗ A^{B,u}_a` | No named counterpart | One half of unsymmetrization. Depends on `eq:just-applied-induction`, block-diagonal role registers, and the definition of `G^A`. |
| `eq:cons-b` | `inductive_step.tex:108` | `I ⊗ G^{B}_{[g(u)=a]} \simeq_{2σ} A^{A,u}_a ⊗ I` | No named counterpart | Other half of unsymmetrization. Same dependencies as `eq:cons-a`. |
| `eq:G-self-consistency` | `inductive_step.tex:130-133` | `G^{A}_g ⊗ I \simeq_{ζ_1} I ⊗ G^{B}_g` with `ζ_1 = 2σ + 2\sqrt{3\eps + 2σ} + md/q` | No named counterpart | Converts pointwise consistency into global polynomial consistency. Depends on `eq:cons-a`, `eq:cons-b`, original point self-consistency, `prop:simeq-triangle-inequality`, and Schwartz–Zippel. |
| `eq:G-with-Q-A` | `inductive_step.tex:146-149` | `G^{A}_g ⊗ I \approx_{ζ_2} Q^{A}_g ⊗ I` | No named counterpart | Post-orthonormalization/completion approximation. Depends on `lem:orthonormalization-main-lemma` and `prop:completing-to-measurement`. There is an unlabeled symmetric partner for `G^B` to `Q^B`. |
| `eq:third-goal` | `inductive_step.tex:160-162` | `Q^{A}_g ⊗ I \simeq_{ζ_3/2} I ⊗ Q^{B}_g` | No named counterpart | Restores `\simeq` after going through `\approx`. Depends on `eq:G-self-consistency`, `eq:G-with-Q-A`, its `B`-side analogue, `prop:simeq-to-approx`, and triangle inequality for `\approx`. |
| `eq:just-data-processed-the-heck-outta-this` | `inductive_step.tex:164-166` | `Q^{A}_{[g(u)=a]} ⊗ I \simeq_{ζ_3/2} I ⊗ Q^{B}_{[g(u)=a]}` | No named counterpart | Data-processed evaluation version of `eq:third-goal`. Depends on `prop:simeq-data-processing`. |
| `eq:ok-almost-there-ok` | `inductive_step.tex:172-174` | `Q^{A}_{[g(u)=a]} ⊗ I \simeq_{ζ_1} I ⊗ G^{B}_{[g(u)=a]}` | No named counterpart | Hybrid comparison needed before the final triangle step. Depends on `eq:G-self-consistency`, `eq:G-with-Q-A`, `prop:triangle-sub`, and data processing. |
| `eq:one-goal` | `inductive_step.tex:178-181` | `A^{A,u}_a ⊗ I \simeq_{ζ_4} I ⊗ Q^{B}_{[g(u)=a]}` | No named counterpart | First final consistency conclusion of `thm:main-formal`. Depends on `eq:cons-b`, `eq:ok-almost-there-ok`, `eq:just-data-processed-the-heck-outta-this`, and `prop:simeq-triangle-inequality`. |
| `eq:another-goal` | `inductive_step.tex:183-184` | `I ⊗ A^{B,u}_a \simeq_{ζ_4} Q^{A}_{[g(u)=a]} ⊗ I` | No named counterpart | Symmetric final consistency conclusion. Same shape as `eq:one-goal`. |
| `eq:zeta-smaller-than-nu` | `inductive_step.tex:522-527` | `\zeta \le \nu` | No named counterpart | Arithmetic bridge in `thm:main-induction`. Depends on the averaged restricted bounds and the fact that exponents weaken upward on `[0,1]`. |
| `eq:gonna-bound-m-function` | `inductive_step.tex:584-592` | `σ^* \le (1 + 1/(100m))(m^2+3)(\nu + e^{-k/(80000m^2)})` | No named counterpart | Final arithmetic bound before showing the next-stage error is the required `(m+1)^2(...)`. Depends on the pasted error formula and `eq:zeta-smaller-than-nu`. |

Observations:

- The blueprint retains the error parameters `ζ_1`, `ζ_2`, `ζ_3`, `ζ_4` only in prose in `ch10_induction.tex:105-126`.
- None of these equations currently have dedicated Lean helper lemmas in the inspected target directories.
- In practice, `Test.mainFormal` will need either:
  - a direct proof script with a long chain of `have`s mirroring this table, or
  - new helper lemmas for symmetrization/unsymmetrization and for the error-propagation chain.

## Blueprint vs Lean Gap by Chapter

### Chapter 2 / Test definition

What the blueprint keeps:

- Test rules.
- Symmetric/general projective strategy definitions.
- Good strategy definition.
- Main formal theorem.

What the blueprint drops from the paper:

- The classical context theorems `thm:raz-safra` and `thm:classical-test-soundness`.
- The paper-local remark `rem:good-strat-characterization` as a Chapter 2 item.
- The paper-local notation `not:conditioned-on-last-direction`.

What Lean has:

- The test-level data structures are in place:
  `SymStrat`, `ProjStrat`, failure probabilities, `IsGood`,
  `PassesLowIndividualDegreeTest`.
- The theorem statement `Test.mainFormal` is present but unproved.

Real gap:

- The good-strategy characterization needed downstream has not been formalized as a reusable lemma, even though its ingredients exist.

### Chapter 10 / Induction

What the blueprint keeps:

- `append_x`
- restricted strategy
- restricted probabilities
- section-local self-improvement wrapper
- main induction
- a compressed proof of the final main theorem reduction

What the blueprint compresses away:

- the source-local pasting label `thm:ld-pasting-in-induction-section`
- almost all labeled intermediate equations in both proofs
- the full arithmetic sub-derivations

What Lean has:

- Slice operators and error functions are defined.
- Statement containers are in place.
- All four main Chapter 10 results are currently theorem stubs.

Real gaps:

1. The local wrapper theorems are not proved.
2. The proof-step equations from the paper are not packaged into Lean helper lemmas.

Historical note (resolved in #593): the restricted diagonal branch had been modeled differently from the paper/blueprint.

## Historical structural Lean divergence (resolved in #593)

This was the most serious technical mismatch in the original scout. It is now resolved in #593, so the discussion below is retained only as historical context.

### A. Restricted diagonal measurement was only a submeasurement in Lean

Historical scout state:

- The paper and blueprint package the restricted strategy as a symmetric strategy for the `(m,q,d)` test, so the restricted diagonal family is again a projective measurement.
- At scout time, Lean instead stored `RestrictedSymStrat.diagonalMeasurement` as `IdxProjSubMeas (DiagonalLine params) (DiagonalLinePolynomial params) ι` in `MIPStarRE/LDT/MainInductionStep/Defs.lean`.

Update — resolved in #593:

- `RestrictedSymStrat.diagonalMeasurement` is now a genuine `IdxProjMeas ...`.
- `restrictDiagonalMeasurement` now re-embeds the restricted answers into the honest slice answer space, so the restricted slice is again packaged as a strategy for the `(m,q,d)` test.

### B. The diagonal restriction probability used the wrong constants for the paper's statement

Historical scout state:

- The paper's `lem:restricted-probabilities` and the blueprint both use the diagonal average bound
  \[
  \E_x \gamma_x \le \frac{m+1}{m}\gamma.
  \]
- At scout time, Lean instead used the diagonal-only surrogates `sliceDiagonalDirectionWeight = 1 / q` and `sliceDiagonalConditioningLoss = q`, so `RestrictedProbabilitiesStatement` asked for a different weighted diagonal bound.

Update — resolved in #593:

- The diagonal-only surrogates `sliceDiagonalDirectionWeight` and `sliceDiagonalConditioningLoss` were removed.
- `RestrictedProbabilitiesStatement` now uses the shared paper/blueprint factors `sliceTransverseDirectionWeight = m / (m + 1)` and `sliceConditioningLoss = (m + 1) / m` for the diagonal branch as well.
- Consequently, this is no longer a live design blocker for the restricted-probabilities layer; the remaining blockers are the unfinished theorem proofs listed elsewhere in this file.

## Dependency Picture for the Missing Chapter 10 Work

For the Chapter 10 formalization to close in a paper-faithful way, the critical dependency chain is:

1. `lem:good-strategy-characterization`
   - blueprint present
   - Lean missing as a named reusable theorem

2. `lem:orthonormalization-main-lemma`
   - blueprint present
   - Lean statement present but still `sorry`

3. `thm:self-improvement`
   - blueprint present
   - Lean statement present but still `sorry`

4. `thm:self-improvement-in-induction-section`
   - blueprint present
   - Lean wrapper stub
   - additionally blocked on the measurement-vs-submeasurement bridge:
     `selfImprovementFromSubMeas` currently requires an explicit measurement witness

5. `thm:ld-pasting`
   - blueprint present
   - Lean statement present but still mostly unproved

6. `thm:ld-pasting-in-induction-section`
   - source-local wrapper needed by Chapter 10
   - Lean stub additionally blocked by import-cycle issues

7. `lem:restricted-probabilities`
   - paper/blueprint statement-level mismatch resolved in #593; the remaining work is the proof and downstream Chapter 10 assembly

8. `thm:main-induction`
   - depends on all of the above and on the arithmetic steps `\zeta \le \nu` and the final `σ^*` bound

9. `thm:main-formal`
   - depends on `mainInduction` plus the symmetrization/unsymmetrization proof skeleton encoded by the intermediate equations table above

## Recommended Next Actions

After the statement-level diagonal-branch fix in #593, the most efficient remaining order is:

1. Add a named Lean theorem for `lem:good-strategy-characterization`.
2. Finish `orthonormalizationMainLemma`.
3. Finish `SelfImprovement.selfImprovement`.
4. Refactor imports so the local induction wrapper can call the global pasting theorem without a cycle.
5. Only then attack `MainInductionStep.mainInduction` and `Test.mainFormal`, using the paper's labeled equations as the proof skeleton.

Without step 1, the Chapter 10 Lean development still lacks the reusable entry point that packages the paper's good-strategy hypotheses for the downstream induction wrappers.
