import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.GlobalVariance.Theorems.Results
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.Preliminaries.Triangles
import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.CommonHelpers
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperCompleteness
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUPointConsistency

/-!
# Final-fields projective-residual boundedness transport

Off-diagonal decomposition of the helper boundedness slack,
data-processing transport of the boundedness gap, and the standalone
`final_fields_bounded` producer.

## Contents

- **helperAgreementOperatorAtPoint_eq_sum_polynomial** — reindexing
  identity collapsing the fiberwise `∑_a A^u_a ⊗ H_{[h(u)=a]}` to the
  polynomial-indexed sum `∑_h A^u_{h(u)} ⊗ H_h` (paper line 612).
- **helper_agreement_average_ev_eq_polynomial_sum** — averaged scalar
  form of the reindexing.
- **helperAgreementOperatorAtPoint_off_diagonal_decomposition** —
  operator-level off-diagonal decomposition
  `I ⊗ H.total - helperAgreementOperatorAtPoint = ∑_h ∑_{a≠h(u)} A^u_a ⊗ H_h`
  (paper line 613; blueprint lines 296–300).
- **helperAgreementOperatorAtPoint_ev_slack_eq_off_diagonal_sum** —
  pointwise scalar form of the same off-diagonal decomposition.
- **helper_boundedness_slack_average_ev_eq_off_diagonal_avg** — averaged
  scalar form of the off-diagonal decomposition (LHS of
  `eq:explicit-bound-for-A-consistency`, paper line 435).
- **helper_boundedness_gap_eq_upper_gap_add_off_diagonal_avg** — rewrites the
  helper boundedness gap as the `Z`-versus-`H.total` scalar gap plus the
  off-diagonal average.
- **helper_boundedness_gap_le_selfImprovementHelperError** — combines the
  `H`-versus-`Z` scalar comparison with the off-diagonal average estimate to
  obtain the helper boundedness gap at the helper threshold.
- **helper_boundedness_gap_le_selfImprovementHelperError_of_pointConsistencyAddInU_transfer**
  — same conclusion, with the off-diagonal estimate supplied by the
  point-consistency `add-in-u` transfer.
- **helper_upper_gap_rightTensor_le_three_sqrt_delta_of_helper_outputs**
  — converts the helper-completeness `Hhat`-versus-`Z` comparison into the
  right-tensor scalar comparison required by the boundedness gap decomposition.
- **helper_boundedness_gap_le_selfImprovementHelperError_of_helper_outputs**
  — supplies the `Z`-versus-`Hhat.total` comparison from helper outputs,
  leaving only the explicit off-diagonal `add-in-u` transfer as input.
- **helper_point_consistency_error_eq_off_diagonal_avg** — identifies the
  averaged off-diagonal mass with the helper-stage `ConsRel` defect for the
  point measurement against `polynomialEvaluationFamily`.
- **helper_point_consistency_of_pointConsistencyAddInU_transfer** — packages
  the point-consistency `add-in-u` transfer as a `ConsRel` at
  `selfImprovementHelperError`.
- **final_fields_point_consistency_totalGap_natural** — transports the
  helper-stage point consistency through the projective data-processing
  comparison, with the submeasurement total-overlap displacement recorded
  explicitly.
- **helper_boundedness_gap_transport_through_data_processing** — transport
  the helper boundedness gap through the data-processing SDD approximation
  between Ĥ and H (paper lines 747–755).
- **projective_boundedness_gap_le_helper_boundedness_gap** — dual-slack
  step: the projective residual `⟨ψ|Z⊗(I−H)|ψ⟩` is bounded by the helper
  boundedness gap (paper lines 742–749).
- **final_fields_projective_residual_bound_natural** — combines the dual-slack
  comparator with the data-processing transport to bound the projective
  residual at `selfImprovementHelperError + √selfImprovementDataProcessingError`.
- **final_fields_projective_residual_bound** — literal-threshold wrapper
  absorbing the natural error into `selfImprovementError`.
- **final_fields_projective_residual_bound_of_helper_outputs**
  — final projective-residual producer from helper outputs, data processing,
  complementary slackness, and the off-diagonal `add-in-u` transfer.
- **final_fields_bounded** — standalone producer: if `1 ≤ Z` then
  any submeasurement is `BoundedByOperator` relative to `Z ⊗ I`.

## References

- `references/ldt-paper/self_improvement.tex` lines 435, 612–613, 747–755
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/


namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Final-fields projective-residual boundedness transport (issue #931)

The boundedness paragraph of `thm:self-improvement` first compares the
projective residual against the point-agreement average and then replaces the
projective family `H` by the helper family `Hhat` through the data-processing
SDD bound. The lemma below isolates the second step: it transports the scalar
helper boundedness gap across
`selfConsistencyImpliesDataProcessing`.

This is not a raw residual assumption and does not restate `FinalFieldsInput`;
it is the checked `easy-approx-from-approx-delta` part of
`references/ldt-paper/self_improvement.tex` lines 747--755, mirrored in
`blueprint/src/chapter/ch07_self_improvement.tex` lines 609--618. -/

private lemma helper_agreement_average_ev_eq_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι) :
    ev strategy.state (helperAgreementAverageOperator params strategy H) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ a : Fq params,
          ev strategy.state
            (opTensor ((strategy.pointMeasurement u).outcome a)
              ((evaluateAt params u H).outcome a))) := by
  rw [helperAgreementAverageOperator, ev_averageOperatorOverDistribution]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  simp [helperAgreementOperatorAtPoint, ev_sum]

/-- Reindexing identity for the pointwise helper-agreement operator.

The fiberwise definition `H_{[h(u)=a]} := ∑_{h : h(u)=a} H_h` collapses the
`a`-summed expression `∑_a A^u_a ⊗ H_{[h(u)=a]}` to the polynomial-indexed sum
`∑_h A^u_{h(u)} ⊗ H_h`, by expanding the tensor product fiberwise and applying
`Finset.sum_fiberwise` along `h ↦ h u`.

This is the first equality of the boundedness display in the proof of
`\ref{item:self-improvement-boundedness}`:
`references/ldt-paper/self_improvement.tex` line 612, mirrored at
`blueprint/src/chapter/ch07_self_improvement.tex` lines 274--282
("Reindexing the sum by~$h$"). It is a purely algebraic identity — no estimate,
no measurement structure used beyond the postprocess fiber decomposition built
into `evaluateAt`. -/
theorem helperAgreementOperatorAtPoint_eq_sum_polynomial
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (u : Point params) :
    helperAgreementOperatorAtPoint params strategy H u =
      ∑ h : Polynomial params,
        opTensor ((strategy.pointMeasurement u).outcome (h u))
          (H.outcome h) := by
  classical
  -- First reduce `helperAgreementOperatorAtPoint`'s `evaluateAt` to the explicit
  -- fiber sum on each summand; everything else then follows from
  -- `Finset.sum_fiberwise` along `h ↦ h u` and bilinearity of `opTensor`.
  have hexpand :
      helperAgreementOperatorAtPoint params strategy H u =
        ∑ a : Fq params,
          opTensor ((strategy.pointMeasurement u).outcome a)
            (∑ h ∈ Finset.univ.filter
                (fun h : Polynomial params => h u = a), H.outcome h) := by
    change (∑ a : Fq params,
        opTensor ((strategy.pointMeasurement u).outcome a)
          ((evaluateAt params u H).outcome a)) = _
    refine Finset.sum_congr rfl ?_
    intro a _
    have hev :
        (evaluateAt params u H).outcome a =
          ∑ h ∈ Finset.univ.filter
              (fun h : Polynomial params => h u = a), H.outcome h := by
      ext i j
      simp only [evaluateAt, postprocess]
      convert rfl
    rw [hev]
  rw [hexpand]
  calc
    ∑ a : Fq params,
        opTensor ((strategy.pointMeasurement u).outcome a)
          (∑ h ∈ Finset.univ.filter
              (fun h : Polynomial params => h u = a), H.outcome h)
        = ∑ a : Fq params, ∑ h ∈ Finset.univ.filter
              (fun h : Polynomial params => h u = a),
            opTensor ((strategy.pointMeasurement u).outcome a) (H.outcome h) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [opTensor_sum_right_finset]
      _ = ∑ a : Fq params, ∑ h ∈ Finset.univ.filter
              (fun h : Polynomial params => h u = a),
            opTensor ((strategy.pointMeasurement u).outcome (h u)) (H.outcome h) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              refine Finset.sum_congr rfl ?_
              intro h hh
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
              rw [show h u = a from hh]
      _ = ∑ h : Polynomial params,
            opTensor ((strategy.pointMeasurement u).outcome (h u)) (H.outcome h) := by
              simpa using
                Finset.sum_fiberwise (Finset.univ : Finset (Polynomial params))
                  (fun h : Polynomial params => h u)
                  (fun h =>
                    opTensor ((strategy.pointMeasurement u).outcome (h u))
                      (H.outcome h))

/-- Reindexed expansion of the averaged helper-agreement operator.

Combining the pointwise reindexing identity
`helperAgreementOperatorAtPoint_eq_sum_polynomial` with
`helper_agreement_average_ev_eq_avg`, the scalar
`⟨ψ| E_u Σ_a A^u_a ⊗ H_{[h(u)=a]} |ψ⟩` equals the polynomial-indexed expectation
`E_u Σ_h ⟨ψ| A^u_{h(u)} ⊗ H_h |ψ⟩` from the second line of the boundedness
display in the proof of `\ref{item:self-improvement-boundedness}`
(`references/ldt-paper/self_improvement.tex` line 612;
`blueprint/src/chapter/ch07_self_improvement.tex` lines 274--282). -/
theorem helper_agreement_average_ev_eq_polynomial_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι) :
    ev strategy.state (helperAgreementAverageOperator params strategy H) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((strategy.pointMeasurement u).outcome (h u))
              (H.outcome h))) := by
  rw [helper_agreement_average_ev_eq_avg]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  have hpt :
      helperAgreementOperatorAtPoint params strategy H u =
        ∑ h : Polynomial params,
          opTensor ((strategy.pointMeasurement u).outcome (h u)) (H.outcome h) :=
    helperAgreementOperatorAtPoint_eq_sum_polynomial params strategy H u
  have hpt_ev :
      ev strategy.state (helperAgreementOperatorAtPoint params strategy H u) =
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((strategy.pointMeasurement u).outcome (h u))
              (H.outcome h)) := by
    rw [hpt, ev_sum]
  -- The LHS goal is the unfolded `helperAgreementOperatorAtPoint`-summand at `u`.
  simp only [helperAgreementOperatorAtPoint, ev_sum] at hpt_ev
  exact hpt_ev

/-- Off-diagonal decomposition of the pointwise helper boundedness slack.

For each point `u`, the difference between the right-placed total
`I ⊗ H.total = ∑_h I ⊗ H_h` and the pointwise helper-agreement operator
`helperAgreementOperatorAtPoint params strategy H u = ∑_a A^u_a ⊗ H_{[h(u)=a]}`
equals the off-diagonal sum
`∑_h ∑_{a ≠ h(u)} A^u_a ⊗ H_h`,
by combining the polynomial-indexed reindexing of `helperAgreementOperatorAtPoint`
from #1124 (`helperAgreementOperatorAtPoint_eq_sum_polynomial`) with
`∑_a A^u_a = 1` (since `pointMeasurement u` is a measurement) and the bilinearity
of `opTensor`.

This is the operator-level form of the second algebraic identity in the
boundedness display in `\ref{item:self-improvement-boundedness}`
(`references/ldt-paper/self_improvement.tex` line 613, mirrored at
`blueprint/src/chapter/ch07_self_improvement.tex` lines 296--300, the step
"Combined with $\sum_a A_a^u = I$ and~\eqref{eq:explicit-bound-for-A-consistency}
this gives ..."). The averaged scalar form of the off-diagonal sum on the right
is the LHS of `eq:explicit-bound-for-A-consistency` (line 435), which the paper
bounds by `4 √ζ_variance`. -/
theorem helperAgreementOperatorAtPoint_off_diagonal_decomposition
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (u : Point params) :
    rightTensor (ι₁ := ι) H.total -
        helperAgreementOperatorAtPoint params strategy H u =
      ∑ h : Polynomial params,
        ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
          opTensor ((strategy.pointMeasurement u).outcome a) (H.outcome h) := by
  classical
  -- Step 1: rewrite `helperAgreementOperatorAtPoint` via the #1124 reindexing.
  rw [helperAgreementOperatorAtPoint_eq_sum_polynomial]
  -- Step 2: rewrite `rightTensor H.total = ∑_h opTensor 1 (H.outcome h)`.
  have hrhs_total :
      rightTensor (ι₁ := ι) H.total =
        ∑ h : Polynomial params,
          opTensor (1 : MIPStarRE.Quantum.Op ι) (H.outcome h) := by
    change opTensor (1 : MIPStarRE.Quantum.Op ι) H.total = _
    rw [← H.sum_eq_total]
    exact opTensor_sum_right_univ (1 : MIPStarRE.Quantum.Op ι) H.outcome
  rw [hrhs_total, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro h _
  -- Pull subtraction inside `opTensor`.
  rw [opTensor_sub_left]
  -- Use `∑_a A^u_a = 1` to expand `1 - A^u_{h(u)} = ∑_{a ≠ h(u)} A^u_a`.
  have htot :
      ∑ a : Fq params, (strategy.pointMeasurement u).outcome a =
        (1 : MIPStarRE.Quantum.Op ι) :=
    (strategy.pointMeasurement u).toMeasurement.sum_eq
  have hsplit :
      (strategy.pointMeasurement u).outcome (h u) +
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            (strategy.pointMeasurement u).outcome a =
        (1 : MIPStarRE.Quantum.Op ι) := by
    rw [← htot]
    exact Finset.add_sum_erase _ _ (Finset.mem_univ (h u))
  have hsubst :
      (1 : MIPStarRE.Quantum.Op ι) -
          (strategy.pointMeasurement u).outcome (h u) =
        ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
          (strategy.pointMeasurement u).outcome a := by
    rw [← hsplit]
    abel
  rw [hsubst]
  -- Pull the sum out of the left factor of `opTensor`.
  exact opTensor_sum_left_finset _ _ _

/-- Scalar form of the pointwise off-diagonal decomposition.

For each evaluation point `u`, the scalar slack
`⟨ψ, I ⊗ H.total, ψ⟩ - ⟨ψ, helperAgreementOperatorAtPoint u, ψ⟩`
is the sum of the off-diagonal masses
`⟨ψ, A^u_a ⊗ H_h, ψ⟩` over the pairs with `a ≠ h(u)`. -/
theorem helperAgreementOperatorAtPoint_ev_slack_eq_off_diagonal_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (u : Point params) :
    ev strategy.state (rightTensor (ι₁ := ι) H.total) -
        ev strategy.state (helperAgreementOperatorAtPoint params strategy H u) =
      ∑ h : Polynomial params,
        ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
          ev strategy.state
            (opTensor ((strategy.pointMeasurement u).outcome a)
              (H.outcome h)) := by
  rw [← ev_sub, helperAgreementOperatorAtPoint_off_diagonal_decomposition,
    ev_sum]
  simp only [ev_finset_sum]

private lemma opTensor_one_left_eq_rightTensor
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (B : MIPStarRE.Quantum.Op ι₂) :
    opTensor (ι₁ := ι₁) (1 : MIPStarRE.Quantum.Op ι₁) B =
      rightTensor (ι₁ := ι₁) B := by
  rfl

private lemma pointMeasurement_total_evalFamily_total_opTensor_ev_eq_rightTensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (S : SubMeas (Polynomial params) ι)
    (u : Point params) :
    ev strategy.state
        (opTensor
          (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total)
          (((polynomialEvaluationFamily params S) u).total)) =
      ev strategy.state (rightTensor (ι₁ := ι) S.total) := by
  have hA_total :
      (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) =
        (1 : MIPStarRE.Quantum.Op ι) := by
    exact (strategy.pointMeasurement u).total_eq_one
  have hS_total : (((polynomialEvaluationFamily params S) u).total) = S.total := by
    simpa [polynomialEvaluationFamily, evaluateAt] using
      postprocess_total S (fun g : Polynomial params => g u)
  rw [hA_total, hS_total, opTensor_one_left_eq_rightTensor]

private lemma pointMeasurement_total_evalFamily_total_ev_eq_rightTensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (S : SubMeas (Polynomial params) ι)
    (u : Point params) :
    ev strategy.state
        (leftTensor (ι₂ := ι)
            (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
          rightTensor (ι₁ := ι)
            (((polynomialEvaluationFamily params S) u).total)) =
      ev strategy.state (rightTensor (ι₁ := ι) S.total) := by
  rw [leftTensor_mul_rightTensor_eq_opTensor]
  exact pointMeasurement_total_evalFamily_total_opTensor_ev_eq_rightTensor
    params strategy S u

/-- Averaged scalar form of the off-diagonal decomposition.

Composed from `helperAgreementOperatorAtPoint_off_diagonal_decomposition` by
applying the bilinearity of `ev`/`avgOver` over subtraction and averaging via
`avgOver_uniform_const`.  The difference
`⟨ψ, I ⊗ H.total, ψ⟩ - ⟨ψ, helperAgreementAverageOperator, ψ⟩` equals the
averaged off-diagonal scalar sum
`E_u ∑_h ∑_{a ≠ h(u)} ⟨ψ, A^u_a ⊗ H_h, ψ⟩`,
which is the LHS of `eq:explicit-bound-for-A-consistency`
(`references/ldt-paper/self_improvement.tex` line 435; blueprint
`ch07_self_improvement.tex` lines 153--168). -/
theorem helper_boundedness_slack_average_ev_eq_off_diagonal_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι) :
    ev strategy.state (rightTensor (ι₁ := ι) H.total) -
        ev strategy.state (helperAgreementAverageOperator params strategy H) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h))) := by
  classical
  have h_ev_pointwise (u : Point params) :
      ev strategy.state (rightTensor (ι₁ := ι) H.total) -
          ev strategy.state (helperAgreementOperatorAtPoint params strategy H u) =
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h)) := by
    exact helperAgreementOperatorAtPoint_ev_slack_eq_off_diagonal_sum params strategy H u
  calc
    ev strategy.state (rightTensor (ι₁ := ι) H.total) -
          ev strategy.state (helperAgreementAverageOperator params strategy H) =
      ev strategy.state (rightTensor (ι₁ := ι) H.total) -
        avgOver (uniformDistribution (Point params))
          (fun u => ev strategy.state
            (helperAgreementOperatorAtPoint params strategy H u)) := by
      rw [helperAgreementAverageOperator, ev_averageOperatorOverDistribution]
    _ = avgOver (uniformDistribution (Point params))
          (fun _ => ev strategy.state (rightTensor (ι₁ := ι) H.total)) -
        avgOver (uniformDistribution (Point params))
          (fun u => ev strategy.state
            (helperAgreementOperatorAtPoint params strategy H u)) := by
      rw [avgOver_uniform_const]
    _ = avgOver (uniformDistribution (Point params))
          (fun u => ev strategy.state (rightTensor (ι₁ := ι) H.total) -
            ev strategy.state
              (helperAgreementOperatorAtPoint params strategy H u)) := by
      rw [avgOver_sub]
    _ = avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h))) := by
      refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
      intro u
      exact h_ev_pointwise u

/-- The helper-stage consistency defect is exactly the averaged off-diagonal
mass appearing in the point-consistency `add-in-u` calculation.

This is the same algebraic identity as
`helper_boundedness_slack_average_ev_eq_off_diagonal_avg`, read as a
`ConsRel` defect for the point measurement against the polynomial-evaluation
family of `H`. -/
theorem helper_point_consistency_error_eq_off_diagonal_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι) :
    bipartiteConsError strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h))) := by
  classical
  unfold bipartiteConsError
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  have hdiff_eq :
      ev strategy.state (rightTensor (ι₁ := ι) H.total) -
          ev strategy.state (helperAgreementOperatorAtPoint params strategy H u) =
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (H.outcome h)) := by
    exact helperAgreementOperatorAtPoint_ev_slack_eq_off_diagonal_sum params strategy H u
  have hdiff_nonneg :
      0 ≤ ev strategy.state (rightTensor (ι₁ := ι) H.total) -
          ev strategy.state (helperAgreementOperatorAtPoint params strategy H u) := by
    rw [hdiff_eq]
    exact Finset.sum_nonneg fun h _ =>
      Finset.sum_nonneg fun a _ =>
        ev_nonneg_of_psd strategy.state _
          (opTensor_nonneg ((strategy.pointMeasurement u).toMeasurement.outcome_pos a)
            (H.outcome_pos h))
  have htotal :
      ev strategy.state
          (opTensor
            (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total)
            (((polynomialEvaluationFamily params H) u).total)) =
        ev strategy.state (rightTensor (ι₁ := ι) H.total) := by
    exact pointMeasurement_total_evalFamily_total_opTensor_ev_eq_rightTensor
      params strategy H u
  have hmatch :
      qBipartiteMatchMass strategy.state
          ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
          ((polynomialEvaluationFamily params H) u) =
        ev strategy.state (helperAgreementOperatorAtPoint params strategy H u) := by
    simp [qBipartiteMatchMass, helperAgreementOperatorAtPoint,
      polynomialEvaluationFamily, evaluateAt, ev_sum, IdxProjMeas.toIdxSubMeas]
  unfold qBipartiteConsDefect
  rw [htotal, hmatch]
  rw [max_eq_right hdiff_nonneg, hdiff_eq]

/-- Helper-stage point consistency from the point-consistency `add-in-u`
transfer hypothesis.

The transfer bound controls the off-diagonal mass
`E_u ∑_h ∑_{a ≠ h(u)} ⟨ψ, A^u_a ⊗ Hhat_h ψ⟩`.  The preceding algebraic
identity identifies this mass with the `ConsRel` defect for the point
measurement and the polynomial-evaluation family of `Hhat`. -/
theorem helper_point_consistency_of_pointConsistencyAddInU_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T Hhat : SubMeas (Polynomial params) ι}
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params Hhat)
      (selfImprovementHelperError params eps delta) := by
  refine ⟨?_⟩
  rw [helper_point_consistency_error_eq_off_diagonal_avg]
  exact
    pointConsistencyAddInU_off_diagonal_avg_le_helper_error_of_transfer
      params strategy eps delta heps hdelta T Hhat htransfer

/-- Natural-error transport of point consistency from the helper output to the
projective output, with the submeasurement total-overlap displacement stated
explicitly.

The measurement-valued right-register triangle lemma has no total-overlap term:
both right-register totals are the identity.  In the present application
`polynomialEvaluationFamily params Hhat` and
`polynomialEvaluationFamily params H.toSubMeas` are only submeasurements, so
the total-overlap term
`⟨ψ, A^u_{\mathrm{tot}} ⊗ H^u_{\mathrm{tot}} ψ⟩` must also be transported.
This theorem separates that displacement as the parameter `η`; the remaining
contribution is exactly the square root of the data-processing SDD error.  The
note `docs/paper-gaps/issue-1093-submeasurement-triangle-total-overlap.tex`
records the corresponding discrepancy with the measurement-valued paper step. -/
theorem final_fields_point_consistency_totalGap_natural
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta η : Error)
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    (hhelperPoint :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta))
    (hTotal :
      avgOver (uniformDistribution (Point params)) (fun u =>
        |ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params H.toSubMeas) u).total)) -
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params Hhat) u).total))|) ≤ η) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) + η) := by
  have hdata_right :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftRight)
        ((polynomialEvaluationFamily params H.toSubMeas).liftRight)
        (selfImprovementDataProcessingError params eps delta) := by
    simpa [IdxSubMeas.liftLeft, IdxSubMeas.liftRight]
      using
        sddRel_liftRight_of_liftLeft_permInv
          strategy.permInvState (uniformDistribution (Point params))
          (polynomialEvaluationFamily params Hhat)
          (polynomialEvaluationFamily params H.toSubMeas)
          (selfImprovementDataProcessingError params eps delta) hdata
  exact
    Preliminaries.triangleSub_right_subMeas_totalGap
      strategy.state (uniformDistribution (Point params)) strategy.isNormalized
      (uniformDistribution_weight_sum_le_one (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params Hhat)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta)
      (selfImprovementDataProcessingError params eps delta) η hhelperPoint
      hdata_right hTotal

/-- Natural-error point-consistency transport when the total-overlap
displacement is supplied as a single right-register total difference.

Since the point measurement is complete and
`polynomialEvaluationFamily params H` has the same total as `H`, the averaged
total-overlap term in `final_fields_point_consistency_totalGap_natural` is
independent of the point `u`.  This theorem records the corresponding reduction
of the issue #1226 obstruction to the scalar difference between the totals of
the two right-register submeasurements. -/
theorem final_fields_point_consistency_totalGap_natural_of_total_difference
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta η : Error)
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    (hhelperPoint :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta))
    (hTotal :
      |ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) -
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)| ≤ η) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) + η) := by
  have hTotalAvg :
      avgOver (uniformDistribution (Point params)) (fun u =>
        |ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params H.toSubMeas) u).total)) -
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params Hhat) u).total))|) ≤ η := by
    have hpoint : ∀ u : Point params,
        |ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params H.toSubMeas) u).total)) -
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params Hhat) u).total))| =
        |ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) -
          ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)| := by
      intro u
      rw [pointMeasurement_total_evalFamily_total_ev_eq_rightTensor
          params strategy H.toSubMeas u,
        pointMeasurement_total_evalFamily_total_ev_eq_rightTensor
          params strategy Hhat u]
    have hconst :
        avgOver (uniformDistribution (Point params)) (fun u =>
          |ev strategy.state
              (leftTensor (ι₂ := ι)
                (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
                rightTensor (ι₁ := ι)
                  (((polynomialEvaluationFamily params H.toSubMeas) u).total)) -
            ev strategy.state
              (leftTensor (ι₂ := ι)
                (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
                rightTensor (ι₁ := ι)
                  (((polynomialEvaluationFamily params Hhat) u).total))|) =
          avgOver (uniformDistribution (Point params)) (fun _ =>
            |ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) -
              ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)|) := by
      refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
      intro u
      exact hpoint u
    rw [hconst, avgOver_uniform_const]
    exact hTotal
  exact
    final_fields_point_consistency_totalGap_natural
      params strategy eps delta η hhelperPoint hdata hTotalAvg

/-- Literal-threshold point-consistency transport from the helper output to the
projective output.

This wrapper isolates the numerical absorption needed to turn the natural
error
`selfImprovementHelperError + sqrt selfImprovementDataProcessingError + η`
into the final `selfImprovementError` threshold.  The analytic content is
contained in `final_fields_point_consistency_totalGap_natural`. -/
theorem final_fields_point_consistency_totalGap
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta η : Error)
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    (hhelperPoint :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta))
    (hTotal :
      avgOver (uniformDistribution (Point params)) (fun u =>
        |ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params H.toSubMeas) u).total)) -
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u).total) *
              rightTensor (ι₁ := ι)
                (((polynomialEvaluationFamily params Hhat) u).total))|) ≤ η)
    (habsorb :
      selfImprovementHelperError params eps delta +
          Real.sqrt (selfImprovementDataProcessingError params eps delta) + η ≤
        selfImprovementError params eps delta) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta) :=
  MIPStarRE.LDT.ConsRel.mono habsorb
    (final_fields_point_consistency_totalGap_natural params strategy eps delta η
      hhelperPoint hdata hTotal)

/-- Literal-threshold point-consistency transport from a right-register total
difference bound.

This is the `selfImprovementError`-absorbed companion to
`final_fields_point_consistency_totalGap_natural_of_total_difference`. -/
theorem final_fields_point_consistency_totalGap_of_total_difference
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta η : Error)
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    (hhelperPoint :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params Hhat)
        (selfImprovementHelperError params eps delta))
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta))
    (hTotal :
      |ev strategy.state (rightTensor (ι₁ := ι) H.toSubMeas.total) -
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)| ≤ η)
    (habsorb :
      selfImprovementHelperError params eps delta +
          Real.sqrt (selfImprovementDataProcessingError params eps delta) + η ≤
        selfImprovementError params eps delta) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementError params eps delta) :=
  MIPStarRE.LDT.ConsRel.mono habsorb
    (final_fields_point_consistency_totalGap_natural_of_total_difference
      params strategy eps delta η hhelperPoint hdata hTotal)

/-- Algebraic decomposition of the helper boundedness gap.

The scalar gap
`⟨Z ⊗ I - helperAgreementAverageOperator⟩` is the sum of
`⟨Z ⊗ I⟩ - ⟨I ⊗ H.total⟩` and the off-diagonal average produced by
`helper_boundedness_slack_average_ev_eq_off_diagonal_avg`.  This is the
formal algebraic bridge between the reindexing calculation and the final
boundedness estimate in the proof of self-improvement. -/
theorem helper_boundedness_gap_eq_upper_gap_add_off_diagonal_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) :
    helperBoundednessGap params strategy H Z =
      (ev strategy.state (helperUpperOperator params Z) -
          ev strategy.state (rightTensor (ι₁ := ι) H.total)) +
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h : Polynomial params,
            ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
              ev strategy.state
                (opTensor ((strategy.pointMeasurement u).outcome a)
                  (H.outcome h))) := by
  have hslack :=
    helper_boundedness_slack_average_ev_eq_off_diagonal_avg params strategy H
  have hgap_decomp :
      helperBoundednessGap params strategy H Z =
        (ev strategy.state (helperUpperOperator params Z) -
            ev strategy.state (rightTensor (ι₁ := ι) H.total)) +
          (ev strategy.state (rightTensor (ι₁ := ι) H.total) -
            ev strategy.state (helperAgreementAverageOperator params strategy H)) := by
    unfold helperBoundednessGap helperBoundednessOperator
    rw [ev_sub]
    ring
  rw [hgap_decomp, hslack]

/-- Helper-stage boundedness from the scalar comparison and the off-diagonal
estimate.

The helper boundedness gap decomposes as
`⟨Z ⊗ I⟩ - ⟨I ⊗ Hhat.total⟩` plus the off-diagonal average from
`helper_boundedness_slack_average_ev_eq_off_diagonal_avg`.  Thus the comparison
`⟨Z ⊗ I⟩ - ⟨I ⊗ Hhat.total⟩ ≤ 3 √δ`, together with the off-diagonal estimate
`≤ 4 √ζ_variance`, gives the helper threshold after applying
`helper_boundedness_error_le_selfImprovementHelperError`. -/
theorem helper_boundedness_gap_le_selfImprovementHelperError
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hZ_vs_H :
      ev strategy.state (helperUpperOperator params Z) -
          ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) ≤
        3 * Real.sqrt delta)
    (hoffdiag :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (Hhat.outcome h))) ≤
        4 * Real.sqrt (selfImprovementVarianceError params eps delta)) :
    helperBoundednessGap params strategy Hhat Z ≤
      selfImprovementHelperError params eps delta := by
  calc
    helperBoundednessGap params strategy Hhat Z =
        (ev strategy.state (helperUpperOperator params Z) -
            ev strategy.state (rightTensor (ι₁ := ι) Hhat.total)) +
          avgOver (uniformDistribution (Point params)) (fun u =>
            ∑ h : Polynomial params,
              ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
                ev strategy.state
                  (opTensor ((strategy.pointMeasurement u).outcome a)
                    (Hhat.outcome h))) :=
      helper_boundedness_gap_eq_upper_gap_add_off_diagonal_avg params strategy Hhat Z
    _ ≤ 3 * Real.sqrt delta +
        4 * Real.sqrt (selfImprovementVarianceError params eps delta) :=
      add_le_add hZ_vs_H hoffdiag
    _ ≤ selfImprovementHelperError params eps delta :=
      helper_boundedness_error_le_selfImprovementHelperError params eps delta heps hdelta

/-- Helper-stage boundedness from the scalar comparison and the
point-consistency `add-in-u` transfer.

This wrapper composes the off-diagonal estimate supplied by
`pointConsistencyAddInUSelection` with
`helper_boundedness_gap_le_selfImprovementHelperError`.  It is the theorem-side
form of the sentence "combined with the explicit `A`-consistency bound" in the
boundedness paragraph of the self-improvement proof. -/
theorem helper_boundedness_gap_le_selfImprovementHelperError_of_pointConsistencyAddInU_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hZ_vs_H :
      ev strategy.state (helperUpperOperator params Z) -
          ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) ≤
        3 * Real.sqrt delta)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    helperBoundednessGap params strategy Hhat Z ≤
      selfImprovementHelperError params eps delta := by
  have hoffdiag_addInU :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (Hhat.outcome h))) ≤ addInUError params eps delta :=
    pointConsistencyAddInU_off_diagonal_avg_le_of_transfer
      params strategy eps delta T Hhat htransfer
  have hoffdiag :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ∑ a ∈ (Finset.univ : Finset (Fq params)).erase (h u),
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                (Hhat.outcome h))) ≤
        4 * Real.sqrt (selfImprovementVarianceError params eps delta) := by
    simpa [addInUError, Real.sqrt_eq_rpow] using hoffdiag_addInU
  exact
    helper_boundedness_gap_le_selfImprovementHelperError
      params strategy eps delta heps hdelta hZ_vs_H hoffdiag

/-- Convert the helper-completeness `Hhat`-versus-`Z` comparison to the
right-placed total comparison used in the boundedness gap.

The helper-completeness paragraph naturally proves
`⟨ψ, Z ⊗ I⟩ - 3√δ ≤ subMeasMass ψ Hhat.liftLeft`. The boundedness decomposition,
however, uses the right-placed total `⟨ψ, I ⊗ Hhat.total⟩`. On the
permutation-invariant strategy state these scalars agree, so the comparison
becomes `⟨ψ, Z ⊗ I⟩ - ⟨ψ, I ⊗ Hhat.total⟩ ≤ 3√δ`. -/
theorem helper_upper_gap_rightTensor_le_three_sqrt_delta_of_helper_outputs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z) :
    ev strategy.state (helperUpperOperator params Z) -
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) ≤
      3 * Real.sqrt delta := by
  have hleft :
      ev strategy.state (leftTensor (ι₂ := ι) Z) - 3 * Real.sqrt delta ≤
        subMeasMass strategy.state Hhat.liftLeft :=
    helper_hhat_vs_z_of_self_consistency_and_complementary_slackness
      params strategy eps delta hhelper hssc hslack
  have hmass :
      subMeasMass strategy.state Hhat.liftLeft =
        ev strategy.state (leftTensor (ι₂ := ι) Hhat.total) := rfl
  have hswap :
      ev strategy.state (leftTensor (ι₂ := ι) Hhat.total) =
        ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) :=
    strategy.permInvState.swap_ev Hhat.total
  unfold helperUpperOperator
  rw [hmass, hswap] at hleft
  linarith

/-- Helper-stage boundedness from the actual helper comparison and the
point-consistency `add-in-u` transfer.

This theorem composes the helper-completeness comparison `Hhat`-versus-`Z`
with the boundedness off-diagonal estimate. Complementary slackness remains an
explicit hypothesis because the reduced `SelfImprovementHelperConclusion`
records only the presently formalized SDP facts. The off-diagonal transfer is
likewise explicit: it is the theorem-side form of the `add-in-u` application
with `S_u = {(a,h) : h(u) ≠ a}`. -/
theorem helper_boundedness_gap_le_selfImprovementHelperError_of_helper_outputs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T.toSubMeas
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    helperBoundednessGap params strategy Hhat Z ≤
      selfImprovementHelperError params eps delta := by
  have hZ_vs_H :
      ev strategy.state (helperUpperOperator params Z) -
          ev strategy.state (rightTensor (ι₁ := ι) Hhat.total) ≤
        3 * Real.sqrt delta :=
    helper_upper_gap_rightTensor_le_three_sqrt_delta_of_helper_outputs
      params strategy eps delta hhelper hssc hslack
  exact
    helper_boundedness_gap_le_selfImprovementHelperError_of_pointConsistencyAddInU_transfer
      params strategy eps delta heps hdelta hZ_vs_H htransfer

/-- Transport the helper boundedness gap through the data-processing
approximation between `Hhat` and `H`.

The input `hdata` is exactly the data-processing SDD bound already produced
inside `selfImprovement`. The conclusion says that replacing the helper
polynomial family in the point-agreement average by the projective family costs
at most `sqrt ε`, matching Proposition `easy-approx-from-approx-delta` in the
boundedness paragraph of the paper. -/
theorem helper_boundedness_gap_transport_through_data_processing
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (Hhat : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (ε : Error)
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        ε) :
    helperBoundednessGap params strategy H.toSubMeas Z ≤
      helperBoundednessGap params strategy Hhat Z + Real.sqrt ε := by
  have hdata_right :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftRight)
        ((polynomialEvaluationFamily params H.toSubMeas).liftRight)
        ε := by
    simpa [IdxSubMeas.liftLeft, IdxSubMeas.liftRight]
      using
        sddRel_liftRight_of_liftLeft_permInv
          strategy.permInvState (uniformDistribution (Point params))
          (polynomialEvaluationFamily params Hhat)
          (polynomialEvaluationFamily params H.toSubMeas) ε hdata
  have happrox :=
    Preliminaries.easyApproxFromApproxDelta
      strategy.state strategy.isNormalized
      (uniformDistribution (Point params))
      (uniformDistribution_weight_sum_le_one (Point params))
      ((polynomialEvaluationFamily params Hhat).liftRight)
      ((polynomialEvaluationFamily params H.toSubMeas).liftRight)
      (IdxSubMeas.liftLeft (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      ε hdata_right
  have hscalar :
      |ev strategy.state (helperAgreementAverageOperator params strategy Hhat) -
        ev strategy.state (helperAgreementAverageOperator params strategy H.toSubMeas)| ≤
        Real.sqrt ε := by
    rw [helper_agreement_average_ev_eq_avg params strategy Hhat,
      helper_agreement_average_ev_eq_avg params strategy H.toSubMeas]
    simpa [polynomialEvaluationFamily, evaluateAt, IdxSubMeas.liftRight,
      IdxSubMeas.liftLeft, IdxProjMeas.toIdxSubMeas,
      rightTensor_mul_leftTensor_eq_opTensor] using happrox
  unfold helperBoundednessGap helperBoundednessOperator
  rw [ev_sub, ev_sub]
  have hle := le_abs_self
    (ev strategy.state (helperAgreementAverageOperator params strategy Hhat) -
      ev strategy.state (helperAgreementAverageOperator params strategy H.toSubMeas))
  linarith


/-- Compare the final projective residual with the helper boundedness gap for the
same projective family.

This is the SDP dual-slack step in the projective boundedness paragraph of
`thm:self-improvement` (`references/ldt-paper/self_improvement.tex`, lines
742--749): the term `Z ⊗ H_h` in the projective residual dominates
`(E_u A^u_{h(u)}) ⊗ H_h` for each polynomial `h`, and summing these inequalities
turns `Z ⊗ (I - H)` into the helper-stage defect
`Z ⊗ I - E_u Σ_a A^u_a ⊗ H_[h(u)=a]`. -/
theorem projective_boundedness_gap_le_helper_boundedness_gap
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hdual :
      ∀ h : Polynomial params,
        0 ≤ sdpDualSlackOperator params strategy Z h) :
    projectiveBoundednessGap params strategy H Z ≤
      helperBoundednessGap params strategy H.toSubMeas Z := by
  classical
  have hprojective_eq :
      projectiveBoundednessGap params strategy H Z =
        ev strategy.state (leftTensor (ι₂ := ι) Z) -
          ∑ h : Polynomial params,
            ev strategy.state (opTensor Z (H.toSubMeas.outcome h)) := by
    have hsub_tensor :
        opTensor Z (1 - H.toSubMeas.total) =
          opTensor Z (1 : MIPStarRE.Quantum.Op ι) -
            opTensor Z H.toSubMeas.total := by
      ext x y
      simp [opTensor, sub_eq_add_neg, mul_add]
    have htotal_tensor :
        opTensor Z H.toSubMeas.total =
          ∑ h : Polynomial params, opTensor Z (H.toSubMeas.outcome h) := by
      rw [← H.toSubMeas.sum_eq_total, opTensor_sum_right_univ]
    unfold projectiveBoundednessGap projectiveResidualOperator
    calc
      ev strategy.state (leftTensor (ι₂ := ι) Z *
          rightTensor (ι₁ := ι) (1 - H.toSubMeas.total))
          = ev strategy.state (opTensor Z (1 - H.toSubMeas.total)) := by
            rw [leftTensor_mul_rightTensor_eq_opTensor]
      _ = ev strategy.state
            (opTensor Z (1 : MIPStarRE.Quantum.Op ι) -
              opTensor Z H.toSubMeas.total) := by
            rw [hsub_tensor]
      _ = ev strategy.state (opTensor Z (1 : MIPStarRE.Quantum.Op ι)) -
            ev strategy.state (opTensor Z H.toSubMeas.total) := by
            rw [ev_sub]
      _ = ev strategy.state (leftTensor (ι₂ := ι) Z) -
            ev strategy.state (opTensor Z H.toSubMeas.total) := rfl
      _ = ev strategy.state (leftTensor (ι₂ := ι) Z) -
            ∑ h : Polynomial params,
              ev strategy.state (opTensor Z (H.toSubMeas.outcome h)) := by
            rw [htotal_tensor, ev_sum]
  have hhelper_agreement_eq :
      ev strategy.state (helperAgreementAverageOperator params strategy H.toSubMeas) =
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor (averagedPointOperator params strategy h)
              (H.toSubMeas.outcome h)) := by
    rw [helper_agreement_average_ev_eq_polynomial_sum]
    rw [avgOver_sum]
    refine Finset.sum_congr rfl ?_
    intro h _
    exact (ev_opTensor_averageOperatorOverDistribution_left strategy.state
      (uniformDistribution (Point params))
      (pointConditionedOutcomeOperatorAtPolynomial params strategy h)
      (H.toSubMeas.outcome h)).symm
  have hhelper_eq :
      helperBoundednessGap params strategy H.toSubMeas Z =
        ev strategy.state (leftTensor (ι₂ := ι) Z) -
          ∑ h : Polynomial params,
            ev strategy.state
              (opTensor (averagedPointOperator params strategy h)
                (H.toSubMeas.outcome h)) := by
    unfold helperBoundednessGap helperBoundednessOperator helperUpperOperator
    rw [ev_sub, hhelper_agreement_eq]
  have hsum_le :
      (∑ h : Polynomial params,
          ev strategy.state
            (opTensor (averagedPointOperator params strategy h) (H.toSubMeas.outcome h))) ≤
        ∑ h : Polynomial params,
          ev strategy.state (opTensor Z (H.toSubMeas.outcome h)) := by
    refine Finset.sum_le_sum ?_
    intro h _
    apply ev_mono
    exact opTensor_mono_left
      (sub_nonneg.mp (by simpa [sdpDualSlackOperator] using hdual h))
      (H.toSubMeas.outcome_pos h)
  rw [hprojective_eq, hhelper_eq]
  linarith

/-- Natural-error projective-residual producer.

Given the helper-stage boundedness estimate for `Hhat`, the dual-slack
comparator above and the existing data-processing transport produce the final
projective residual at the paper's natural error
`selfImprovementHelperError + sqrt selfImprovementDataProcessingError`. The
separate numerical absorption into the literal `selfImprovementError` threshold
is intentionally not hidden in this theorem. -/
theorem final_fields_projective_residual_bound_natural
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hhelperBounded :
      helperBoundednessGap params strategy Hhat Z ≤
        selfImprovementHelperError params eps delta)
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta)) :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementHelperError params eps delta +
        Real.sqrt (selfImprovementDataProcessingError params eps delta) := by
  have hcompare :=
    projective_boundedness_gap_le_helper_boundedness_gap params strategy H Z
      hhelper.dualDominatesAveragedPoint
  have htransport :=
    helper_boundedness_gap_transport_through_data_processing params strategy Hhat H Z
      (selfImprovementDataProcessingError params eps delta) hdata
  linarith

/-- Literal-threshold projective-residual producer.

This wraps `final_fields_projective_residual_bound_natural` with a separately
named numerical absorption lemma. The analytic inputs are only the helper-stage
boundedness estimate, dual feasibility from `SelfImprovementHelperConclusion`,
and the data-processing SDD output already produced inside `selfImprovement`. -/
theorem final_fields_projective_residual_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hhelperBounded :
      helperBoundednessGap params strategy Hhat Z ≤
        selfImprovementHelperError params eps delta)
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta))
    (habsorb :
      selfImprovementHelperError params eps delta +
          Real.sqrt (selfImprovementDataProcessingError params eps delta) ≤
        selfImprovementError params eps delta) :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta :=
  le_trans
    (final_fields_projective_residual_bound_natural params strategy eps delta
      hhelper hhelperBounded hdata)
    habsorb

/-- Literal-threshold projective-residual producer under the standard
unit-interval smallness hypotheses.

This is the convenience wrapper around
`final_fields_projective_residual_bound`: the numerical absorption input is
provided by
`final_fields_projective_residual_error_le_selfImprovementError`, so callers
only need the helper-stage boundedness estimate, data-processing output, and
the usual smallness assumptions on `eps`, `delta`, and `d/q`. -/
theorem final_fields_projective_residual_bound_of_small_errors
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hhelperBounded :
      helperBoundednessGap params strategy Hhat Z ≤
        selfImprovementHelperError params eps delta)
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta)) :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta :=
  final_fields_projective_residual_bound params strategy eps delta hhelper hhelperBounded hdata
    (final_fields_projective_residual_error_le_selfImprovementError params eps delta
      heps heps_le_one hdelta hdelta_le_one hd_le_q)

/-- Final projective-residual producer from helper outputs and the
point-consistency `add-in-u` transfer.

The theorem performs the boundedness part of the final-fields assembly once the
orthonormalization data-processing estimate is available. It supplies the
helper-stage boundedness estimate from the helper comparison, complementary
slackness, point self-consistency, and the off-diagonal `add-in-u` transfer,
then applies the standard data-processing transport and numerical absorption
into `selfImprovementError`. -/
theorem final_fields_projective_residual_bound_of_helper_outputs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (heps_le_one : eps ≤ 1)
    (hdelta : 0 ≤ delta) (hdelta_le_one : delta ≤ 1)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {H : ProjSubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (htransfer :
      |addInULeftQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          Hhat
          (pointConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          T.toSubMeas
          (pointConsistencyAddInUSelection params)| ≤ addInUError params eps delta)
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta)) :
    projectiveBoundednessGap params strategy H Z ≤
      selfImprovementError params eps delta := by
  have hhelperBounded :
      helperBoundednessGap params strategy Hhat Z ≤
        selfImprovementHelperError params eps delta :=
    helper_boundedness_gap_le_selfImprovementHelperError_of_helper_outputs
      params strategy eps delta heps hdelta hhelper hssc hslack htransfer
  exact
    final_fields_projective_residual_bound_of_small_errors
      params strategy eps delta heps heps_le_one hdelta hdelta_le_one hd_le_q
      hhelper hhelperBounded hdata

/-- Final-fields producer for the `BoundedByOperator` conclusion.

If the SDP dual witness dominates the identity, then the left-placed mass of any
submeasurement is dominated by `Z ⊗ I`: the total bound `A.total ≤ 1 ≤ Z` lifts
by monotonicity to `leftTensor A.total ≤ leftTensor Z`, and evaluation against
the state preserves this order. Consequently `bndError ψ A.liftLeft (Z ⊗ I) = 0`,
so the boundedness statement holds at any nonnegative tolerance. The
`selfImprovement` assembly uses this producer instead of requiring the
boundedness field from `FinalFieldsInput`. -/
theorem final_fields_bounded
    {α : Type*} [Fintype α]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas α ι)
    {Z : MIPStarRE.Quantum.Op ι}
    (hOne : (1 : MIPStarRE.Quantum.Op ι) ≤ Z)
    {ε : Error}
    (hε : 0 ≤ ε) :
    BoundedByOperator ψ A.liftLeft (leftTensor (ι₂ := ι) Z) ε := by
  refine
    { witnessOpPSD := ?_
      upperBound := ?_ }
  · have : leftTensor (ι₂ := ι) Z = opTensor Z (1 : MIPStarRE.Quantum.Op ι) := rfl
    rw [this]
    have hPSD : 0 ≤ Z := le_trans (op_one_nonneg (d := ι)) hOne
    exact opTensor_nonneg hPSD op_one_nonneg
  · have hAle : A.total ≤ Z :=
      le_trans A.total_le_one hOne
    have hLTle :
        leftTensor (ι₂ := ι) A.total ≤ leftTensor (ι₂ := ι) Z := by
      have hopMono :
          opTensor A.total (1 : MIPStarRE.Quantum.Op ι) ≤
            opTensor Z (1 : MIPStarRE.Quantum.Op ι) :=
        opTensor_mono_left hAle op_one_nonneg
      simpa [leftTensor, opTensor] using hopMono
    have hsubmass :
        subMeasMass ψ A.liftLeft = ev ψ (leftTensor (ι₂ := ι) A.total) := rfl
    have hev_le :
        ev ψ (leftTensor (ι₂ := ι) A.total) ≤ ev ψ (leftTensor (ι₂ := ι) Z) :=
      ev_mono ψ _ _ hLTle
    have hbnd_zero :
        bndError ψ A.liftLeft (leftTensor (ι₂ := ι) Z) = 0 := by
      unfold bndError
      rw [hsubmass]
      have :
          ev ψ (leftTensor (ι₂ := ι) A.total) -
              ev ψ (leftTensor (ι₂ := ι) Z) ≤ 0 := by
        linarith
      exact max_eq_left this
    rw [hbnd_zero]
    exact hε


end MIPStarRE.LDT.SelfImprovement
