# Issue #930 session 47 commutativity discrepancy audit

Audit date: 2026-05-01

Base commit: `250b17af` (`origin/main` when this worktree was created)

Branch: `gpt55/session47-930-commutativity-audit`

## Executive summary

I audited the already-formalized `MIPStarRE/LDT/Commutativity/**` slice against:

- `references/ldt-paper/commutativity-G.tex:1-420`;
- `blueprint/src/chapter/ch08_commutativity.tex:50-400`;
- the existing paper-gap and closeout notes that already cover parts of this section:
  `docs/paper-gaps/issue-760-scalar-chain-alignment.tex`,
  `docs/paper-gaps/issue-713-scalar-tensor-decision.tex`,
  `docs/reports/issue-600-628-715-evaluated-slice-audit.md`, and
  `docs/reports/issue-763-session34-fullslice-sz-audit.md`.

This scope intentionally avoids `MIPStarRE/LDT/CommutativityPoints/**`, which was audited in PR #1005, and `MIPStarRE/LDT/Pasting/**`, which was audited in PR #1007. It also avoids `MIPStarRE/LDT/Test/MainTheorem.lean`, `MainInductionStep/**`, and `SelfImprovement/**` while #931 remains assigned externally.

Verdict: I found one newly documented source-text discrepancy: the paper statement of `thm:com-main` says that the ambient strategy is for the `(m,q,d)` low individual degree test, but the theorem's hypotheses and downstream use require an ambient `(m+1,q,d)` strategy together with an `m`-dimensional slice family `{G^x}`. The blueprint and Lean already use the corrected statement. I recorded this as `docs/paper-gaps/issue-930-com-main-dimension-typo.tex`.

No Lean theorem statement or proof needs to change. Apart from this harmless dimension typo and the already documented scalar/tensor bookkeeping from #713, the formalized statements and proof routes match the paper and blueprint.

## Statement audit

### `lem:comm-data-processed-g`

The paper's evaluated-commutation lemma assumes an `(eps, delta, gamma)`-good symmetric strategy for the `(m+1,q,d)` test and a slice family `{G^x}` in `PolySub(m,q,d)`. Lean expresses this by taking `strategy : SymStrat params.next ι` and `family : IdxPolyFamily params ι` in `MIPStarRE.LDT.Commutativity.commDataProcessedG` (`ScalarApproximation/ProcessedG.lean:2001-2014`). The auxiliary map `G : Fq params -> SubMeas (Polynomial params) ι` is tied to the family by `hG : forall x, G x = (family.meas x).toSubMeas`.

The three paper hypotheses are present in the formal statement:

- consistency with `A` is `family.ConsistentWithPoints strategy zeta`, whose field is the `ConsRel` over `uniformDistribution (Point params.next)` between `strategy.pointMeasurement` and the postprocessed slice family (`Test/StrategyPolynomialFamilies.lean:282-290`);
- strong self-consistency is `family.StronglySelfConsistent strategy.state zeta`, the `SDDRel` over uniformly random slice indices `x` (`Test/StrategyPolynomialFamilies.lean:308-316`);
- boundedness is `IdxPolyFamily.SliceBoundednessInput strategy family zeta`, whose fields include both the residual bound and the identification of the domination target with `E_u A^{u,x}_{g(u)}` (`Test/StrategyPolynomialFamilies.lean:338-346`).

The conclusion is the blueprint's `CommDataProcessedGConclusion`: it includes the postprocessed point consistency, the postprocessed self-consistency, and the evaluated-slice commutation `SDDOpRel` with error `commDataProcessedGError params gamma zeta = 48m(√gamma + √zeta)` (`Scaffold/Core.lean:30-76`). This matches the paper and blueprint statement at `lem:comm-data-processed-g`.

### Stability claims `clm:g-comm-stability` and `clm:g-comm-stability2`

The blueprint links the first claim to the formal boundedness helpers and the proved overlap/scalar declarations `gCommStability_overlap` and `gCommStability_scalar`; the second claim is linked similarly to `gCommStabilityTwo_overlap` and `gCommStabilityTwo_scalar` (`ch08_commutativity.tex:177-248`). This split is faithful: the paper claims are scalar Cauchy--Schwarz/boundedness estimates, while the formal development separates the operator-family overlap packaging from the scalar estimate.

The first stability family in `Defs/Stability.lean:73-108` represents the paper expression with the extra left-register total `G^y`, and the second family in `Defs/Stability.lean:110-135` represents the paper expression with the extra left-register total `G^x`. The scalar proofs in `GCommStability/Scalar/First.lean:343-362` and `GCommStability/Scalar/Second.lean:356-376` use the same boundedness witness `Z^x`, the same residual `(I-G^x) ⊗ Z^x`, and the same `√zeta` Cauchy--Schwarz bound as the paper. The second claim also accounts for the point-commutativity swap cost `6√(gamma(m+1))`, matching the paper and blueprint.

### `lem:normalization-condition`

The paper's normalization lemma takes a submeasurement `P = {P_a}`, a projective submeasurement `Q = {Q_b}`, and the sandwiched family `C_{a,b}=Q_b P_a Q_b`, then proves the square sum is bounded by the identity. The formal statement `NormalizationConditionStatement` (`Scaffold/Core.lean:185-197`) and theorem `normalizationCondition` (`Main/Results.lean:112-137`) have the same mathematical content. The formal proof packages the equality of adjoint and non-adjoint square operators plus the identity bound; this is exactly the paper's Hermitian/projective expansion.

### `thm:com-main`

The paper statement at `commutativity-G.tex:228-257` contains the newly documented dimension typo: it says the strategy is for the `(m,q,d)` low individual degree test. However, the theorem immediately quantifies over `(u,x) in F_q^{m+1}` and uses point measurements `A^{u,x}_a`, so the ambient strategy must be for the `(m+1,q,d)` test. The theorem is also used by the pasting theorem in precisely this successor-dimensional form.

The blueprint and Lean use the corrected statement. In Lean, `MIPStarRE.LDT.Commutativity.comMain` takes `strategy : SymStrat params.next ι`, an `m`-dimensional slice family `family : IdxPolyFamily params ι`, and proves `ComMainConclusion params strategy family G gamma zeta` (`Main/Results.lean:65-110`). The final field is the full-slice commutation `SDDOpRel` over uniformly random `(x,y)` with error

```text
comMainError params gamma zeta
  = 30 * m * (gamma^(1/4) + zeta^(1/4) + (d/q)^(1/4)).
```

The proof route is the paper route after the already documented scalar/tensor public-interface choice from `docs/paper-gaps/issue-713-scalar-tensor-decision.tex`: the evaluated commutation estimate is first specialized to evaluated questions (`evaluationSpecialization_sddErrorOp_eq`), then the full-slice products are transported back by the two Schwartz--Zippel marginalization steps (`Main/EvaluatedQuestions.lean:27-46`). The scalar transport bounds are `fullSlice_scalar_marginalize_x` (`Main/Auxiliary.lean:358-421`) and `fullSlice_scalar_marginalize_y` (`Main/Auxiliary.lean:468-508`), and the evaluated-side commutation bridge is `fullSlice_closenessOfIP_CAB_hEval_sqrt` (`Main/Auxiliary.lean:1016-1107`). The final arithmetic in `Main/EvaluatedQuestions.lean:92-397` absorbs these bounds into the same displayed `30m` error parameter.

## Existing documented bookkeeping

Two apparent mismatches in this section were already documented and are not new #930 discrepancies:

- `docs/paper-gaps/issue-760-scalar-chain-alignment.tex` records that the evaluated-slice scalar chain for `lem:comm-data-processed-g` matches the paper's ten-step chain and achieves the paper error `48m(√gamma + √zeta)`.
- `docs/paper-gaps/issue-713-scalar-tensor-decision.tex` records the scalar/tensor bridge used by the full-slice transport: the public formal API exposes scalar averages, while the Schwartz--Zippel positivity argument internally uses tensor endpoints. The extra `√zeta` bridges are accounted for and still absorbed by `comMainError`.

## Follow-up

I did not open a separate follow-up issue. The only newly found discrepancy is a harmless source-text typo, now documented in `docs/paper-gaps/issue-930-com-main-dimension-typo.tex`, and the formal statement already uses the corrected version.

## Validation

Validation was run after adding this report and the paper-gap note:

```text
lake env lean MIPStarRE/LDT/Commutativity/ScalarApproximation/ProcessedG.lean
lake env lean MIPStarRE/LDT/Commutativity/Main/Auxiliary.lean
lake env lean MIPStarRE/LDT/Commutativity/Main/EvaluatedQuestions.lean
lake env lean MIPStarRE/LDT/Commutativity/Main/Results.lean
lake build MIPStarRE.LDT.Commutativity.Theorems
rg -n "\b(sorry|axiom|admit)\b" MIPStarRE/LDT/Commutativity -g '*.lean' || true
cd docs/paper-gaps && latexmk -pdf -interaction=nonstopmode issue-930-com-main-dimension-typo.tex
git diff --check
```

A scratch `#check`/`#print axioms` file was also run for the audited public declarations `commDataProcessedG`, `comMain`, `normalizationCondition`, `gCommStability_overlap`, `gCommStability_scalar`, `gCommStabilityTwo_overlap`, and `gCommStabilityTwo_scalar`; the only reported axioms were the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.
