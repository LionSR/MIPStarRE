import MIPStarRE.LDT.Preliminaries.ComparisonProjective
import MIPStarRE.LDT.Test.MainTheorem.UnsymmetrizedTargets

/-!
# Projective consistency evaluation

This module contains the data-processing lemmas which turn polynomial-level
projective consistency into pointwise consistency after evaluation at a sampled
point.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- A constant full-polynomial consistency statement postprocesses to pointwise
polynomial evaluation with the same error.

This is the data-processing move used after paper line 156: once
`Q^A_g \otimes I \simeq I \otimes Q^B_g` is available over the single
polynomial question, evaluating both polynomial outcomes at a point `u` preserves
consistency over the uniform point distribution. -/
theorem consRel_constPolynomialEvaluation
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    (A B : Measurement (Polynomial params) ι) {δ : Error}
    (h : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) δ) :
    ConsRel ψ (uniformDistribution (Point params))
      (polynomialEvaluationFamily params A.toSubMeas)
      (polynomialEvaluationFamily params B.toSubMeas) δ := by
  classical
  let Aconst : IdxSubMeas (Point params) (Polynomial params) ι := fun _ => A.toSubMeas
  let Bconst : IdxSubMeas (Point params) (Polynomial params) ι := fun _ => B.toSubMeas
  have hconstPoint :
      ConsRel ψ (uniformDistribution (Point params)) Aconst Bconst δ := by
    rcases h with ⟨hbound⟩
    constructor
    have hpoint_avg :
        avgOver (uniformDistribution (Point params))
            (fun _ : Point params => qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas) =
          qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
      haveI : Nonempty (Point params) := by infer_instance
      simpa using
        (avgOver_uniform_const (α := Point params)
          (qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas))
    have hunit_eq :
        bipartiteConsError ψ (uniformDistribution Unit)
            (constSubMeasFamily A.toSubMeas) (constSubMeasFamily B.toSubMeas) =
          qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
      have hunit_avg :
          avgOver (uniformDistribution Unit)
              (fun _ : Unit => qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas) =
            qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
        simpa using
          (avgOver_uniform_const (α := Unit)
            (qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas))
      simpa [bipartiteConsError, constSubMeasFamily] using hunit_avg
    calc
      bipartiteConsError ψ (uniformDistribution (Point params)) Aconst Bconst
          = avgOver (uniformDistribution (Point params))
              (fun _ : Point params => qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas) := by
            rfl
      _ = qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := hpoint_avg
      _ = bipartiteConsError ψ (uniformDistribution Unit)
            (constSubMeasFamily A.toSubMeas) (constSubMeasFamily B.toSubMeas) :=
            hunit_eq.symm
      _ ≤ δ := hbound
  have hprocessed :=
    Preliminaries.consRelDataProcessing_questionDependent ψ
      (uniformDistribution (Point params)) Aconst Bconst δ (fun u g => g u) hconstPoint
  simpa [Aconst, Bconst, polynomialEvaluationFamily, evaluateAt] using hprocessed

/-- Heterogeneous form of `consRel_constPolynomialEvaluation`.

The same data-processing argument applies when Alice's polynomial measurement
acts on `H_A` and Bob's on `H_B`. -/
theorem consRel_constPolynomialEvaluation_heterogeneous
    {params : Parameters} [FieldModel params.q]
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement (Polynomial params) ιA) (B : Measurement (Polynomial params) ιB)
    {δ : Error}
    (h : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) δ) :
    ConsRel ψ (uniformDistribution (Point params))
      (polynomialEvaluationFamily params A.toSubMeas)
      (polynomialEvaluationFamily params B.toSubMeas) δ := by
  classical
  let Aconst : IdxSubMeas (Point params) (Polynomial params) ιA := fun _ => A.toSubMeas
  let Bconst : IdxSubMeas (Point params) (Polynomial params) ιB := fun _ => B.toSubMeas
  have hconstPoint :
      ConsRel ψ (uniformDistribution (Point params)) Aconst Bconst δ := by
    rcases h with ⟨hbound⟩
    constructor
    have hpoint_avg :
        avgOver (uniformDistribution (Point params))
            (fun _ : Point params => qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas) =
          qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
      haveI : Nonempty (Point params) := by infer_instance
      simpa using
        (avgOver_uniform_const (α := Point params)
          (qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas))
    have hunit_eq :
        bipartiteConsError ψ (uniformDistribution Unit)
            (constSubMeasFamily A.toSubMeas) (constSubMeasFamily B.toSubMeas) =
          qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
      have hunit_avg :
          avgOver (uniformDistribution Unit)
              (fun _ : Unit => qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas) =
            qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
        simpa using
          (avgOver_uniform_const (α := Unit)
            (qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas))
      simpa [bipartiteConsError, constSubMeasFamily] using hunit_avg
    calc
      bipartiteConsError ψ (uniformDistribution (Point params)) Aconst Bconst
          = avgOver (uniformDistribution (Point params))
              (fun _ : Point params => qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas) := by
            rfl
      _ = qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := hpoint_avg
      _ = bipartiteConsError ψ (uniformDistribution Unit)
            (constSubMeasFamily A.toSubMeas) (constSubMeasFamily B.toSubMeas) :=
            hunit_eq.symm
      _ ≤ δ := hbound
  have hprocessed :=
    Preliminaries.consRelDataProcessing_questionDependent ψ
      (uniformDistribution (Point params)) Aconst Bconst δ (fun u g => g u) hconstPoint
  simpa [Aconst, Bconst, polynomialEvaluationFamily, evaluateAt] using hprocessed

/-- Turn a line-156 projective approximation into the evaluated consistency used
in the final point-consistency triangles.

The proof first applies the projective converse of `prop:simeq-to-approx` at the
polynomial level, then uses question-dependent data processing to evaluate both
projective polynomial measurements at each point. -/
theorem projectiveEvaluationConsistency_ofFullPolynomialConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)}
    (Q_A Q_B : ProjMeas (Polynomial params) ι) {ζ₃ : Error}
    (hline : Preliminaries.BipartiteSDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas)
      (constSubMeasFamily Q_B.toSubMeas) ζ₃) :
    ConsRel ψ (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Q_A.toSubMeas)
      (polynomialEvaluationFamily params Q_B.toSubMeas) (ζ₃ / 2) := by
  let leftConst : IdxProjMeas Unit (Polynomial params) ι := fun _ => Q_A
  let rightConst : IdxProjMeas Unit (Polynomial params) ι := fun _ => Q_B
  have happrox :
      Preliminaries.BipartiteSDDRel ψ (uniformDistribution Unit)
        (IdxProjMeas.toIdxSubMeas leftConst)
        (IdxProjMeas.toIdxSubMeas rightConst) (2 * (ζ₃ / 2)) := by
    change Preliminaries.BipartiteSDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas) (constSubMeasFamily Q_B.toSubMeas)
      (2 * (ζ₃ / 2))
    convert hline using 1
    ring
  have hcons :=
    Preliminaries.approxToSimeq ψ (uniformDistribution Unit)
      leftConst rightConst (ζ₃ / 2) happrox
  simpa [leftConst, rightConst, constSubMeasFamily, IdxProjMeas.toIdxSubMeas]
    using consRel_constPolynomialEvaluation ψ Q_A.toMeasurement Q_B.toMeasurement hcons

/-- Heterogeneous form of
`projectiveEvaluationConsistency_ofFullPolynomialConsistency`.

It first applies the two-space projective converse to the placed
state-dependent-distance relation, and then evaluates the polynomial outcomes
at the sampled point. -/
theorem projectiveEvaluationConsistency_ofFullPolynomialConsistency_heterogeneous
    {params : Parameters} [FieldModel params.q]
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    {ψ : QuantumState (ιA × ιB)}
    (Q_A : ProjMeas (Polynomial params) ιA) (Q_B : ProjMeas (Polynomial params) ιB)
    {ζ₃ : Error}
    (hline : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas)) ζ₃) :
    ConsRel ψ (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Q_A.toSubMeas)
      (polynomialEvaluationFamily params Q_B.toSubMeas) (ζ₃ / 2) := by
  let leftConst : IdxProjMeas Unit (Polynomial params) ιA := fun _ => Q_A
  let rightConst : IdxProjMeas Unit (Polynomial params) ιB := fun _ => Q_B
  have happrox :
      SDDRel ψ (uniformDistribution Unit)
        (IdxSubMeas.placeLeft (ιB := ιB) (IdxProjMeas.toIdxSubMeas leftConst))
        (IdxSubMeas.placeRight (ιA := ιA) (IdxProjMeas.toIdxSubMeas rightConst))
        (2 * (ζ₃ / 2)) := by
    change SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
      (2 * (ζ₃ / 2))
    convert hline using 1
    ring
  have hcons :=
    Preliminaries.approxToSimeq_heterogeneous ψ (uniformDistribution Unit)
      leftConst rightConst (ζ₃ / 2) happrox
  simpa [leftConst, rightConst, constSubMeasFamily, IdxProjMeas.toIdxSubMeas]
    using
      consRel_constPolynomialEvaluation_heterogeneous ψ
        Q_A.toMeasurement Q_B.toMeasurement hcons

end Test

end MIPStarRE.LDT
