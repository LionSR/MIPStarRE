import MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical.Witness
import MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical.Saturated

/-!
# Section 9 — Matrix realization

Compatibility module for the concrete finite-dimensional matrix realization of
the self-improvement SDP data.  The base SDP data, canonical block SDP layer,
canonical optimal-witness packages, and saturated zero-slack canonical interface
are re-exported from the corresponding `MatrixRealization` submodules; this
file keeps the matrix add-in-u transfer interface at the original import path.

## References

- `references/ldt-paper/self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-- A raw point-indexed matrix outcome family used in the matrix `add-in-u` transfer. -/
abbrev MatrixIndexedPointOutcomeFamily (params : Parameters) [FieldModel params.q]
    (Outcome : Type*) (H : FiniteHilbertSpace) :=
  Point params → Outcome → MatrixOperator H

/-- The concrete sandwiched operator `A^u_{h(u)} T_h A^u_{h(u)}`. -/
noncomputable def matrixSandwichedPolynomialOutcomeOperatorAt (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (u : Point params) (h : Polynomial params) : MatrixOperator model.space :=
  let Au := matrixAveragedPointOperatorContribution params model h u
  Au * (T.effect h) * Au

/-- The averaged concrete sandwiched operator `E_u A^u_{h(u)} T_h A^u_{h(u)}`. -/
noncomputable def matrixAveragedSandwichedPolynomialOutcomeOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (h : Polynomial params) : MatrixOperator model.space :=
  matrixAverageOperator (fun u : Point params =>
    matrixSandwichedPolynomialOutcomeOperatorAt params model T u h)

/-- The matrix left-hand operator in `add-in-u`. -/
noncomputable def matrixAddInULeftOperatorAtPoint {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (S : AddInUSelection params Outcome)
    (u : Point params) : MatrixOperator model.space :=
  ∑ ah ∈ addInUSelectionPairs params S u,
    (M u ah.1) * (H.effect ah.2)

/-- The matrix right-hand operator in `add-in-u`. -/
noncomputable def matrixAddInURightOperatorAtPoint {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (S : AddInUSelection params Outcome)
    (u : Point params) : MatrixOperator model.space :=
  ∑ ah ∈ addInUSelectionPairs params S u,
    let Au := matrixAveragedPointOperatorContribution params model ah.2 u
    Au * (M u ah.1) * Au * (T.effect ah.2)

private noncomputable def matrixAddInUPointAverage (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (f : Point params → MatrixOperator model.space) : Error :=
  finiteAverage (fun u : Point params => Complex.re (matrixExpectation model.state (f u)))

/-- The matrix left-hand expectation in `add-in-u`. -/
noncomputable def matrixAddInULeftQuantity {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (S : AddInUSelection params Outcome) : Error :=
  matrixAddInUPointAverage params model (matrixAddInULeftOperatorAtPoint params model M H S)

/-- The matrix right-hand expectation in `add-in-u`. -/
noncomputable def matrixAddInURightQuantity {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (S : AddInUSelection params Outcome) : Error :=
  matrixAddInUPointAverage params model (matrixAddInURightOperatorAtPoint params model M T S)

/-- The concrete evaluated polynomial family `H_[h(u)=a]`. -/
noncomputable def matrixPolynomialEvaluationOutcomeOperatorAtPoint (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (u : Point params) (a : Fq params) : MatrixOperator model.space :=
  let evalFamily :=
    MIPStarRE.Quantum.Submeasurement.postprocess (M := H) (fun h => h u)
  evalFamily.effect a

/-- The concrete matched operator `Σ_a A^u_a H_[h(u)=a]`. -/
noncomputable def matrixHelperAgreementOperatorAtPoint (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (u : Point params) : MatrixOperator model.space :=
  ∑ a : Fq params,
    (model.pointMeasurement u).effect a *
      matrixPolynomialEvaluationOutcomeOperatorAtPoint params model H u a

/-- The concrete averaged matched operator `E_u Σ_a A^u_a H_[h(u)=a]`. -/
noncomputable def matrixHelperAgreementAverageOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    MatrixOperator model.space :=
  matrixAverageOperator (fun u : Point params =>
    matrixHelperAgreementOperatorAtPoint params model H u)

/-- The concrete helper boundedness gap `Re τ(ρ (Z - E_u Σ_a A^u_a H_[h(u)=a]))`. -/
noncomputable def matrixHelperBoundednessGap (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) : Error :=
  Complex.re (matrixExpectation model.state
    (Z - matrixHelperAgreementAverageOperator params model H))

/-- The concrete projective residual gap `Re τ(ρ (Z (I - Σ_h H_h)))`. -/
noncomputable def matrixProjectiveResidualGap (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) : Error :=
  let total := MIPStarRE.Quantum.Submeasurement.total H
  Complex.re (matrixExpectation model.state (Z * (1 - total)))

/-- Paper origin: `references/ldt-paper/self_improvement.tex:238-343`
(`\label{lem:add-in-u}`).

Matrix-level version of the `add-in-u` transfer inequality: this is the matrix
realization of `AddInUStatement`, recording the `lem:add-in-u` transfer bound on
the difference between the left- and right-hand expectations evaluated at a
selection rule `S`. -/
structure MatrixAddInUTransferStatement {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (eps delta : Error) : Prop where
  transfer :
    ∀ S : AddInUSelection params Outcome,
      |matrixAddInULeftQuantity params model M H S -
          matrixAddInURightQuantity params model M T S| ≤
        addInUError params eps delta


end MIPStarRE.LDT.SelfImprovement
