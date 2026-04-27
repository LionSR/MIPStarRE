import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.Commutativity.GCommStability.OverlapOne
import MIPStarRE.LDT.Preliminaries.CauchySchwarz

/-!
# Section 11 commutativity: shared scalar stability helpers

Auxiliary positivity, order, and bounded-residual lemmas used by the scalar stability estimates.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma averagedSlicePointEvaluationOperator_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) :
    0 ≤ IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g := by
  unfold IdxPolyFamily.averagedSlicePointEvaluationOperator
  exact Finset.sum_nonneg fun u _ =>
    smul_nonneg ((uniformDistribution (Point params)).nonnegative u)
      ((strategy.pointMeasurement (appendPoint params u x)).outcome_pos (g u))

lemma averagedSlicePointEvaluationOperator_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) :
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤ 1 := by
  unfold IdxPolyFamily.averagedSlicePointEvaluationOperator
  calc
    averageOperatorOverDistribution (uniformDistribution (Point params))
        (fun u => (strategy.pointMeasurement (appendPoint params u x)).outcome (g u))
      ≤ ∑ u ∈ (uniformDistribution (Point params)).support,
          (uniformDistribution (Point params)).weight u • (1 : MIPStarRE.Quantum.Op ι) := by
            simp only [averageOperatorOverDistribution]
            exact Finset.sum_le_sum fun u _ =>
              smul_le_smul_of_nonneg_left
                ((strategy.pointMeasurement (appendPoint params u x)).outcome_le_one (g u))
                ((uniformDistribution (Point params)).nonnegative u)
    _ = (∑ u ∈ (uniformDistribution (Point params)).support,
          (uniformDistribution (Point params)).weight u) • (1 : MIPStarRE.Quantum.Op ι) := by
          rw [Finset.sum_smul]
    _ = 1 := by
          have hcard : ((Fintype.card (Point params) : Error)) ≠ 0 := by
            exact_mod_cast Fintype.card_ne_zero
          simp [uniformDistribution]

lemma averagedSlicePointEvaluationOperator_hermitian
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) :
    (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g)ᴴ =
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g := by
  exact
    (Matrix.nonneg_iff_posSemidef.mp
      (averagedSlicePointEvaluationOperator_nonneg params strategy x g)).isHermitian.eq

lemma averagedSlicePointEvaluationOperator_sq_le_self
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) :
    IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g *
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g := by
  exact MIPStarRE.Quantum.sq_le_self
    (averagedSlicePointEvaluationOperator_nonneg params strategy x g)
    (averagedSlicePointEvaluationOperator_le_one params strategy x g)

lemma storedResidual_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (zeta : Error)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ∀ x : Fq params, 0 ≤ hbound.storedResidual G x := by
  intro x
  unfold IdxPolyFamily.SliceBoundednessInput.storedResidual
  apply ev_nonneg_of_psd
  rw [leftTensor_mul_rightTensor_eq_opTensor]
  simpa [opTensor] using
    MIPStarRE.Quantum.kronecker_nonneg
      (sub_nonneg.mpr (G x).total_le_one)
      (hbound.bounded.sliceOpPSD x)

end MIPStarRE.LDT.Commutativity
