import MIPStarRE.LDT.MainInductionStep.Theorems.SourceTheorems
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Basic
import MIPStarRE.LDT.Test.MainTheorem.ProjectiveConsistency.Evaluation
import MIPStarRE.LDT.Test.MainTheorem.UnsymmetrizedTargets
import MIPStarRE.LDT.Test.StrategyBiProjRoleAverage
import MIPStarRE.LDT.Test.StrategyBiProjUnsymmetrization

/-!
# Source-Boundary Role-Register Handoff: Core Reductions

This module contains the main-induction handoff, unsymmetrization, and the first
two-space projectivization outputs for the source route toward `thm:main-formal`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.LDT.MakingMeasurementsProjective

namespace ProjStrat

/-- Apply the source-shaped main-induction theorem to the heterogeneous
role-register symmetrization of a two-space strategy.

Paper origin: `references/ldt-paper/inductive_step.tex:26-83`, where the
general projective strategy of `thm:main-formal` is symmetrized by adding role
registers and `thm:main-induction` is applied to the resulting symmetric
strategy.

This theorem is not a proof of `thm:main-formal`: it stops at the polynomial
measurement produced by source main induction on the role-register space.  It
does, however, discharge the Step 1 handoff for the paper-faithful two-space
strategy container.  The downstream unsymmetrization and two-sided
projective-submeasurement construction are now formalized later in this file;
completion, line-169 transport, and scalar absorption remain separate, together
with the still-open source range inside
`MainInductionStep.mainInduction_sourceStatement`.

**Unfaithful:** The proof calls
`MainInductionStep.mainInduction_sourceStatement`, whose proof currently relies
on the tracked source-range obligation
`MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation`.
Documented in `docs/paper-gaps/issue-906-main-formal-k-bound.tex` and issue
#1507.  Elimination: discharge the source-range obligation for
`thm:main-induction`; this two-space role-register handoff itself adds no
bridge, package, residual, repair, or generic hypothesis to the source theorem.
-/
theorem roleRegisterSymmStrategy_sourceMainInduction
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params) (RoleRegisterLocal ιA ιB),
      ConsRel (strategy.roleRegisterSymmStrategy).state
        (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas (strategy.roleRegisterSymmStrategy).pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (MainInductionStep.mainInductionError params k
          (3 * eps) (3 * eps) (3 * eps)) := by
  exact
    MainInductionStep.mainInduction_sourceStatement params
      (strategy := strategy.roleRegisterSymmStrategy)
      (eps := 3 * eps) (delta := 3 * eps) (gamma := 3 * eps) (k := k)
      (roleRegisterSymmStrategy_is_good_three_mul
        (strategy := strategy) (eps := eps) hpass)
      hk

set_option maxHeartbeats 800000 in
-- The proof compares two averaged consistency defects after expanding the
-- role-register symmetrization and polynomial-evaluation extraction maps.
/-- Unsymmetrize the two point-consistency estimates obtained from a
role-register source-induction measurement.

Paper origin: `references/ldt-paper/inductive_step.tex:84-109`.

This theorem is the quantitative part of the heterogeneous role-register
reduction before the later projectivization and completion steps.  It starts
from the consistency estimate produced on the role-register symmetrized
strategy and extracts the two occupied principal blocks of the polynomial
measurement.  The factor `2` is exactly the factor coming from the two role
sectors in the symmetrized state.

This statement is source-boundary infrastructure, not a replacement for
`thm:main-formal`: the extracted measurements are complete measurements, not
yet projective measurements, and the error has not yet been absorbed into
`mainFormalError`. -/
theorem sourceRoleRegisterPointConsistency_ofSymConsistency
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (G : Measurement (Polynomial params) (RoleRegisterLocal ιA ιB))
    (σ : Error)
    (hsym :
      ConsRel (strategy.roleRegisterSymmStrategy).state
        (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas (strategy.roleRegisterSymmStrategy).pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        σ) :
    ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
        (polynomialEvaluationFamily params
          (Measurement.extractRoleRegisterBob G).toSubMeas)
        (2 * σ) ∧
      ConsRel strategy.state (uniformDistribution (Point params))
        (polynomialEvaluationFamily params
          (Measurement.extractRoleRegisterAlice G).toSubMeas)
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
        (2 * σ) := by
  haveI : Nonempty ιA := strategy.isNormalized.nonempty.map Prod.fst
  haveI : Nonempty ιB := strategy.isNormalized.nonempty.map Prod.snd
  constructor
  · refine ⟨?_⟩
    have hmono :
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params
              (Measurement.extractRoleRegisterBob G).toSubMeas)
          ≤
        avgOver (uniformDistribution (Point params)) (fun u =>
          2 * qBipartiteConsDefect (strategy.roleRegisterSymmStrategy).state
            ((IdxProjMeas.toIdxSubMeas
              (strategy.roleRegisterSymmStrategy).pointMeasurement) u)
            ((polynomialEvaluationFamily params G.toSubMeas) u)) := by
      unfold bipartiteConsError
      apply avgOver_mono
      intro u
      have hpoint :=
        qBipartiteConsDefect_extractRoleRegisterBob_le_two_symm
          strategy.state strategy.isNormalized
          (strategy.pointMeasurementA u) (strategy.pointMeasurementB u)
          (Test.polynomialEvaluationMeasurementFamily params G u)
      rw [congrFun (polynomialEvaluationFamily_measurement_extractRoleRegisterBob G) u]
      simpa [IdxProjMeas.toIdxSubMeas, polynomialEvaluationFamily,
        roleRegisterSymmStrategy, roleRegisterPointMeasurement,
        Test.polynomialEvaluationMeasurementFamily] using hpoint
    have hscale :
        avgOver (uniformDistribution (Point params)) (fun u =>
          2 * qBipartiteConsDefect (strategy.roleRegisterSymmStrategy).state
            ((IdxProjMeas.toIdxSubMeas
              (strategy.roleRegisterSymmStrategy).pointMeasurement) u)
            ((polynomialEvaluationFamily params G.toSubMeas) u))
          =
        2 * bipartiteConsError (strategy.roleRegisterSymmStrategy).state
          (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas (strategy.roleRegisterSymmStrategy).pointMeasurement)
          (polynomialEvaluationFamily params G.toSubMeas) := by
      simp [bipartiteConsError, avgOver_const_mul]
    calc
      bipartiteConsError strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
          (polynomialEvaluationFamily params
            (Measurement.extractRoleRegisterBob G).toSubMeas)
        ≤ avgOver (uniformDistribution (Point params)) (fun u =>
            2 * qBipartiteConsDefect (strategy.roleRegisterSymmStrategy).state
              ((IdxProjMeas.toIdxSubMeas
                (strategy.roleRegisterSymmStrategy).pointMeasurement) u)
              ((polynomialEvaluationFamily params G.toSubMeas) u)) := hmono
      _ = 2 * bipartiteConsError (strategy.roleRegisterSymmStrategy).state
            (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (strategy.roleRegisterSymmStrategy).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas) := hscale
      _ ≤ 2 * σ := by
            exact mul_le_mul_of_nonneg_left hsym.offDiagonalBound (by norm_num)
  · refine ⟨?_⟩
    have hmono :
        bipartiteConsError strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params
              (Measurement.extractRoleRegisterAlice G).toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
          ≤
        avgOver (uniformDistribution (Point params)) (fun u =>
          2 * qBipartiteConsDefect (strategy.roleRegisterSymmStrategy).state
            ((IdxProjMeas.toIdxSubMeas
              (strategy.roleRegisterSymmStrategy).pointMeasurement) u)
            ((polynomialEvaluationFamily params G.toSubMeas) u)) := by
      unfold bipartiteConsError
      apply avgOver_mono
      intro u
      have hpoint :=
        qBipartiteConsDefect_extractRoleRegisterAlice_le_two_symm
          strategy.state strategy.isNormalized
          (strategy.pointMeasurementA u) (strategy.pointMeasurementB u)
          (Test.polynomialEvaluationMeasurementFamily params G u)
      rw [congrFun (polynomialEvaluationFamily_measurement_extractRoleRegisterAlice G) u]
      simpa [IdxProjMeas.toIdxSubMeas, polynomialEvaluationFamily,
        roleRegisterSymmStrategy, roleRegisterPointMeasurement,
        Test.polynomialEvaluationMeasurementFamily] using hpoint
    have hscale :
        avgOver (uniformDistribution (Point params)) (fun u =>
          2 * qBipartiteConsDefect (strategy.roleRegisterSymmStrategy).state
            ((IdxProjMeas.toIdxSubMeas
              (strategy.roleRegisterSymmStrategy).pointMeasurement) u)
            ((polynomialEvaluationFamily params G.toSubMeas) u))
          =
        2 * bipartiteConsError (strategy.roleRegisterSymmStrategy).state
          (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas (strategy.roleRegisterSymmStrategy).pointMeasurement)
          (polynomialEvaluationFamily params G.toSubMeas) := by
      simp [bipartiteConsError, avgOver_const_mul]
    calc
      bipartiteConsError strategy.state (uniformDistribution (Point params))
          (polynomialEvaluationFamily params
            (Measurement.extractRoleRegisterAlice G).toSubMeas)
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
        ≤ avgOver (uniformDistribution (Point params)) (fun u =>
            2 * qBipartiteConsDefect (strategy.roleRegisterSymmStrategy).state
              ((IdxProjMeas.toIdxSubMeas
                (strategy.roleRegisterSymmStrategy).pointMeasurement) u)
              ((polynomialEvaluationFamily params G.toSubMeas) u)) := hmono
      _ = 2 * bipartiteConsError (strategy.roleRegisterSymmStrategy).state
            (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas (strategy.roleRegisterSymmStrategy).pointMeasurement)
            (polynomialEvaluationFamily params G.toSubMeas) := hscale
      _ ≤ 2 * σ := by
            exact mul_le_mul_of_nonneg_left hsym.offDiagonalBound (by norm_num)

/-- Passing the two-space low individual degree test bounds the point-agreement
branch by `3ε`.

This is the heterogeneous analogue of
`SameSpaceProjStrat.point_agreement_le_three_mul`; it follows because the
point-agreement branch is one of the three nonnegative terms averaged in
`ProjStrat.lowIndividualDegreeFailureProbability`. -/
theorem pointAgreementFailureProbability_le_three_mul
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    {strategy : ProjStrat params ιA ιB}
    {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    strategy.pointAgreementFailureProbability ≤ 3 * eps := by
  have haxis_nonneg : 0 ≤ strategy.axisParallelRoleAverage :=
    axisParallelRoleAverage_nonneg strategy
  have hpoint_nonneg : 0 ≤ strategy.pointAgreementFailureProbability :=
    pointAgreementFailureProbability_nonneg strategy
  have hdiag_nonneg : 0 ≤ strategy.diagonalRoleAverage :=
    diagonalRoleAverage_nonneg strategy
  have hmain :
      (strategy.axisParallelRoleAverage + strategy.pointAgreementFailureProbability +
        strategy.diagonalRoleAverage) / 3 ≤ eps := by
    simpa [ProjStrat.lowIndividualDegreeFailureProbability] using
      hpass.soundnessHypothesis
  linarith

/-- The two-space Step 5 self-consistency calculation before projectivization.

Paper origin: `references/ldt-paper/inductive_step.tex:111-133`.

Starting from the two unsymmetrized estimates
`G^A_[g(u)=a] \otimes I \simeq_\sigma I \otimes A^{B,u}_a` and
`A^{A,u}_a \otimes I \simeq_\sigma I \otimes G^B_[g(u)=a]`,
the original point-agreement branch of the test gives the evaluated polynomial
consistency at error `σ + 2 sqrt(3ε + σ)`.  The heterogeneous
Schwartz--Zippel Step 5 lemma then gives full-polynomial consistency with the
additional `md/q` loss. -/
theorem sourceRoleRegisterFullPolynomialSelfConsistency_ofPointConsistency
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps σ : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (G_A : Measurement (Polynomial params) ιA)
    (G_B : Measurement (Polynomial params) ιB)
    (hpointAGB :
      ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
        (polynomialEvaluationFamily params G_B.toSubMeas)
        σ)
    (hGApointB :
      ConsRel strategy.state (uniformDistribution (Point params))
        (polynomialEvaluationFamily params G_A.toSubMeas)
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
        σ) :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas)
      (σ + 2 * Real.sqrt (3 * eps + σ) +
        (params.m * params.d : Error) / params.q) := by
  let leftEval : IdxMeas (Point params) (Fq params) ιA :=
    Test.polynomialEvaluationMeasurementFamily params G_A
  let rightEval : IdxMeas (Point params) (Fq params) ιB :=
    Test.polynomialEvaluationMeasurementFamily params G_B
  let pointA : IdxMeas (Point params) (Fq params) ιA :=
    IdxProjMeas.toIdxMeas strategy.pointMeasurementA
  let pointB : IdxMeas (Point params) (Fq params) ιB :=
    IdxProjMeas.toIdxMeas strategy.pointMeasurementB
  have hleft : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas leftEval) (IdxMeas.toIdxSubMeas pointB) σ := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params G_A.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      σ
    exact hGApointB
  have hpoint : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointA) (IdxMeas.toIdxSubMeas pointB) (3 * eps) := by
    refine ⟨?_⟩
    simpa [ProjStrat.pointAgreementFailureProbability] using
      pointAgreementFailureProbability_le_three_mul params hpass
  have hright : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointA) (IdxMeas.toIdxSubMeas rightEval) σ := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params G_B.toSubMeas)
      σ
    exact hpointAGB
  have hevaluated : ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params G_A.toSubMeas)
      (polynomialEvaluationFamily params G_B.toSubMeas)
      (σ + 2 * Real.sqrt (3 * eps + σ)) := by
    have htriangle :=
      Preliminaries.simeqTriangleInequality_heterogeneous strategy.state
        (uniformDistribution (Point params)) strategy.isNormalized
        (uniformDistribution_weight_sum_le_one (Point params))
        leftEval pointA pointB rightEval σ (3 * eps) σ hleft hpoint hright
    simpa [leftEval, rightEval, pointA, pointB,
      Test.polynomialEvaluationMeasurementFamily] using htriangle
  exact
    Test.mainFormalStep5_selfConsistency_ofExpansionBound_heterogeneous params strategy.state
      strategy.isNormalized G_A.toSubMeas G_B.toSubMeas
      (σ + 2 * Real.sqrt (3 * eps + σ)) hevaluated

/-- The two unsymmetrized polynomial measurements obtained from the
source-shaped role-register main-induction call.

Paper origin: `references/ldt-paper/inductive_step.tex:68-109`.

This theorem packages the first two quantitative conclusions of the
role-register reduction in the proof of `thm:main-formal`: after applying
source main induction to the heterogeneous role-register symmetrization, the
occupied principal blocks of the resulting polynomial measurement are
consistent with the original two-space point measurements, with the expected
factor-two loss.

It is not the final theorem.  The outputs here are complete polynomial
measurements, not projective measurements, and no self-consistency conclusion is
claimed.  Those are the later projectivization, completion, and scalar
absorption steps in `references/ldt-paper/inductive_step.tex:111-185`.

**Unfaithful:** The proof calls
`roleRegisterSymmStrategy_sourceMainInduction`, hence transitively
`MainInductionStep.mainInduction_sourceStatement`; the latter currently relies
on the tracked source-range obligation
`MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation`.
Documented in `docs/paper-gaps/issue-906-main-formal-k-bound.tex` and issue
#1507.  Elimination: discharge the source-range obligation for
`thm:main-induction`; the present theorem adds no bridge, package, residual,
repair, producer, input, or generic hypothesis to the paper theorem. -/
theorem sourceRoleRegisterUnsymmetrizedPointConsistency
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : params.m * params.d ≤ k) :
    ∃ G_A : Measurement (Polynomial params) ιA,
      ∃ G_B : Measurement (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (2 * MainInductionStep.mainInductionError params k
              (3 * eps) (3 * eps) (3 * eps)) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (2 * MainInductionStep.mainInductionError params k
              (3 * eps) (3 * eps) (3 * eps)) := by
  rcases roleRegisterSymmStrategy_sourceMainInduction
      params strategy eps hpass k hk with ⟨G, hG⟩
  refine
    ⟨Measurement.extractRoleRegisterAlice G, Measurement.extractRoleRegisterBob G, ?_⟩
  exact
    sourceRoleRegisterPointConsistency_ofSymConsistency params strategy G
      (MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps)) hG

/-- Complete polynomial measurements obtained from the two-space source
role-register route, including full-polynomial self-consistency.

Paper origin: `references/ldt-paper/inductive_step.tex:68-133`.

This is the source-boundary route through the end of the paper's
Schwartz--Zippel Step 5 calculation.  It applies source main induction to the
heterogeneous role-register symmetrization, extracts the occupied principal
blocks, proves the two factor-two point-consistency estimates, and then applies
the heterogeneous triangle and Schwartz--Zippel calculation to obtain
full-polynomial consistency.

It is still not `thm:main-formal`: the measurements are complete POVMs, not
projective measurements, and the scalar cascade has not yet been absorbed into
`mainFormalError`.

**Unfaithful:** The proof calls
`sourceRoleRegisterUnsymmetrizedPointConsistency`, hence transitively
`MainInductionStep.mainInduction_sourceStatement`; the latter currently relies
on the tracked source-range obligation
`MainInductionStep.mainInduction_sourceRangeSmallErrorPositiveNonBaseKPosObligation`.
Documented in `docs/paper-gaps/issue-906-main-formal-k-bound.tex` and issue
#1507.  Elimination: discharge the source-range obligation for
`thm:main-induction`; the present theorem adds no bridge, package, residual,
repair, producer, input, or generic hypothesis to the paper theorem. -/
theorem sourceRoleRegisterCompletePolynomialSelfConsistency
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : params.m * params.d ≤ k) :
    ∃ G_A : Measurement (Polynomial params) ιA,
      ∃ G_B : Measurement (Polynomial params) ιB,
        ConsRel strategy.state (uniformDistribution (Point params))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
            (polynomialEvaluationFamily params G_B.toSubMeas)
            (2 * MainInductionStep.mainInductionError params k
              (3 * eps) (3 * eps) (3 * eps)) ∧
          ConsRel strategy.state (uniformDistribution (Point params))
            (polynomialEvaluationFamily params G_A.toSubMeas)
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
            (2 * MainInductionStep.mainInductionError params k
              (3 * eps) (3 * eps) (3 * eps)) ∧
          ConsRel strategy.state (uniformDistribution Unit)
            (constSubMeasFamily G_A.toSubMeas)
            (constSubMeasFamily G_B.toSubMeas)
            (2 * MainInductionStep.mainInductionError params k
                (3 * eps) (3 * eps) (3 * eps) +
              2 * Real.sqrt (3 * eps +
                2 * MainInductionStep.mainInductionError params k
                  (3 * eps) (3 * eps) (3 * eps)) +
              (params.m * params.d : Error) / params.q) := by
  rcases sourceRoleRegisterUnsymmetrizedPointConsistency
      params strategy eps hpass k hk with ⟨G_A, G_B, hpointAGB, hGApointB⟩
  refine ⟨G_A, G_B, hpointAGB, hGApointB, ?_⟩
  exact
    sourceRoleRegisterFullPolynomialSelfConsistency_ofPointConsistency
      params strategy eps
      (2 * MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps))
      hpass G_A G_B hpointAGB hGApointB

/-- Alice-side projective submeasurement obtained from a two-space
complete-measurement Step 5 output.

Paper origin: `references/ldt-paper/inductive_step.tex:135-143`, applying
`lem:orthonormalization-main-lemma` to the complete polynomial measurements
whose full-polynomial consistency has just been proved.

This is a genuine two-space consequence of the source-facing orthonormalization
lemma.  It constructs the Alice-side projective submeasurement from the
complete measurement `G_A` and the cross-consistency relation with `G_B`, without
assuming permutation-invariance or identifying the two local Hilbert spaces. -/
theorem sourceRoleRegisterLeftProjectiveSubmeasurement_ofFullConsistency
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (G_A : Measurement (Polynomial params) ιA)
    (G_B : Measurement (Polynomial params) ιB)
    (ζ : Error)
    (hfull : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ) :
    ∃ P_A : ProjSubMeas (Polynomial params) ιA,
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizationError ζ) := by
  have hζ : 0 ≤ ζ := by
    have hq : qBipartiteConsDefect strategy.state G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
      simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily] using
        hfull.offDiagonalBound
    exact le_trans (qBipartiteConsDefect_nonneg strategy.state G_A.toSubMeas G_B.toSubMeas)
      hq
  exact
    orthonormalizationMeasurement_of_consistency_from_projectivizationRepair_heterogeneous
      strategy.state strategy.isNormalized G_A G_B ζ hζ hfull

/-- Bob-side projective submeasurement obtained from a two-space
complete-measurement Step 5 output.

Paper origin: `references/ldt-paper/inductive_step.tex:135-143`, applying
`lem:orthonormalization-main-lemma` to the complete polynomial measurements
whose full-polynomial consistency has just been proved.

This is the right-register counterpart of
`sourceRoleRegisterLeftProjectiveSubmeasurement_ofFullConsistency`.  It
constructs the Bob-side projective submeasurement from the complete measurement
`G_B` and the cross-consistency relation with `G_A`, without assuming
permutation-invariance or identifying the two local Hilbert spaces. -/
theorem sourceRoleRegisterRightProjectiveSubmeasurement_ofFullConsistency
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (G_A : Measurement (Polynomial params) ιA)
    (G_B : Measurement (Polynomial params) ιB)
    (ζ : Error)
    (hfull : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ) :
    ∃ P_B : ProjSubMeas (Polynomial params) ιB,
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizationError ζ) := by
  have hζ : 0 ≤ ζ := by
    have hq : qBipartiteConsDefect strategy.state G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
      simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily] using
        hfull.offDiagonalBound
    exact le_trans (qBipartiteConsDefect_nonneg strategy.state G_A.toSubMeas G_B.toSubMeas)
      hq
  exact
    orthonormalizationMeasurement_right_of_consistency_from_projectivizationRepair_heterogeneous
      strategy.state strategy.isNormalized G_A G_B ζ hζ hfull


end ProjStrat

end MIPStarRE.LDT
