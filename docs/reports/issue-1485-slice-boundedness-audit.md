# Issue 1485: Slice Boundedness Audit

This note records the source comparison for the boundedness assumptions formerly
packaged in a helper structure and now stated explicitly in the paper-facing
theorem headers.

## Source Statement

The boundedness hypothesis occurs explicitly in the paper in two places.

- `references/ldt-paper/commutativity-G.tex:29-36`, item
  `item:data-processed-boundedness` in `lem:comm-data-processed-g`.
- `references/ldt-paper/ld-pasting.tex:28-35`, item
  `item:ld-pasting-boundedness` in `thm:ld-pasting`.

In both source statements, for each slice `x` there is a positive-semidefinite
operator `Z^x`. These witnesses satisfy the averaged residual bound
`E_x <psi| (I - G^x) tensor Z^x |psi> <= zeta` and the pointwise domination
condition `Z^x >= E_u A^{u,x}_{g(u)}` for every low-degree polynomial `g`.

Lean now states these assumptions explicitly in the paper-facing theorem
headers. The auxiliary theorems
`IdxPolyFamily.storedBoundedResidualBound` and
`IdxPolyFamily.averagedPoint_le_witness` expose the residual and domination
parts of the paper hypothesis.

After issue #1556, Lean no longer exposes the former domination-target
identification field. That identification is not part of the paper statement
and should not be exposed as a paper-facing hypothesis.

## Classification

The following paper-facing declarations carry these boundedness assumptions.
In each case they are classified as faithful boundary data, not as bridge proof
debt.

- `Commutativity.commDataProcessedG`, linked from
  `lem:comm-data-processed-g`: `item:data-processed-boundedness`.
- `IdxPolyFamily.storedBoundedResidualBound`, linked from
  `clm:g-comm-stability`: `item:data-processed-boundedness`.
- `IdxPolyFamily.averagedPoint_le_witness`, linked from
  `clm:g-comm-stability`: `item:data-processed-boundedness`.
- `Commutativity.gCommStability_scalar`, linked from
  `clm:g-comm-stability`: `item:data-processed-boundedness`.
- `IdxPolyFamily.storedBoundedResidualBound`, linked from
  `clm:g-comm-stability2`: `item:data-processed-boundedness`.
- `IdxPolyFamily.averagedPoint_le_witness`, linked from
  `clm:g-comm-stability2`: `item:data-processed-boundedness`.
- `Commutativity.gCommStabilityTwo_scalar`, linked from
  `clm:g-comm-stability2`: `item:data-processed-boundedness`.
- `Commutativity.comMain`, linked from `thm:com-main`:
  inherited from `lem:comm-data-processed-g`.
- `MainInductionStep.ldPastingInInductionSection`, linked from
  `thm:ld-pasting`: `item:ld-pasting-boundedness`.
- `Pasting.ldPasting`, linked from `thm:ld-pasting`:
  `item:ld-pasting-boundedness`.
- `Pasting.ldPastingSubMeas`, linked from `lem:ld-pasting-sub-measurement`:
  inherited from `thm:ld-pasting`.
- `Pasting.ldSandwichLineOnePoint`, linked from
  `lem:ld-sandwich-line-one-point`: inherited from `thm:ld-pasting`.
- `Pasting.hBConsistency`, linked from `lem:h-b-consistency`:
  inherited from `thm:ld-pasting`.
- `Pasting.hAConsistency_submeas`, linked from `cor:h-a-consistency`:
  inherited from `thm:ld-pasting`.
- `Pasting.overAllOutcomes`, linked from `lem:over-all-outcomes`:
  inherited from `thm:ld-pasting`.
- `Pasting.ldPastingNCompleteness`, linked from
  `cor:ld-pasting-N-completeness`: inherited from `thm:ld-pasting`.
- `MainInductionStep.ldPastingInInductionSection`, linked from
  `thm:ld-pasting-in-induction-section`: inherited from `thm:ld-pasting`.

## Verdict

These boundedness assumptions are not analogous to bridge, residual, repair,
producer, or auxiliary-input assumptions introduced to bypass missing proof.
They record hypotheses present in the cited source statements. The proof-debt
audit therefore correctly records these occurrences as faithful boundary input
findings and excludes them from proof-debt header findings.
