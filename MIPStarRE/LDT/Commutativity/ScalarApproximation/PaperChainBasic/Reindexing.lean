import MIPStarRE.LDT.Commutativity.ScalarApproximation.Core
import MIPStarRE.LDT.Commutativity.EvaluatedSliceCommutation.Consequences

/-!
# Reindexing and evaluation utilities for the evaluated-slice paper chain

This file contains finite-reindexing and evaluated-family identities used by
the paper-faithful scalar approximation chain.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Decompose the uniform average over a next-level point into a height and prefix average. -/
lemma avgOver_uniform_pointNext_decompose
    (params : Parameters) [FieldModel params.q]
    (f : Point params.next → Error) :
    avgOver (uniformDistribution (Point params.next)) f =
      avgOver (uniformDistribution (Fq params))
        (fun x => avgOver (uniformDistribution (Point params))
          (fun u => f (appendPoint params u x))) := by
  simpa using CommutativityPoints.avgOver_uniform_pointNext_decompose params f


/-- The evaluated point family has the same total as the underlying slice
measurement `G` at the sampled height.

This unfolds `evaluatedPointFamily` as postprocessing of `family.meas y`; the
postprocessing total is unchanged, and `hG` identifies the slice with `G y`. -/
lemma evaluatedPointFamily_total_eq_G_total
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (u : Point params.next) :
    ((evaluatedPointFamily params family u).total) =
      (G (pointHeight params u)).total := by
  simp [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
    postprocess_total, hG]

/-- Expand a finite sum in the middle factor of a left-register sandwich.

Linearity of matrix multiplication, left tensor placement, multiplication by a
fixed right-register operator, and `ev` turns
`A (∑ x, B_x) C R ⊗ D` into the corresponding sum of expectations
`∑ x, A B_x C R ⊗ D`. -/
lemma ev_leftTensor_mul_middle_finset_sum
    {α : Type*} (s : Finset α)
    (ψ : QuantumState (ι × ι))
    (A C R D : MIPStarRE.Quantum.Op ι)
    (B : α → MIPStarRE.Quantum.Op ι) :
    ev ψ
        (leftTensor (ι₂ := ι) (((A * (∑ x ∈ s, B x) * C) * R)) *
          rightTensor (ι₁ := ι) D) =
      ∑ x ∈ s,
        ev ψ
          (leftTensor (ι₂ := ι) (((A * B x * C) * R)) *
            rightTensor (ι₁ := ι) D) := by
  classical
  have hinner :
      ((A * (∑ x ∈ s, B x) * C) * R) =
        ∑ x ∈ s, ((A * B x * C) * R) := by
    simp [Matrix.mul_sum, Finset.sum_mul, mul_assoc]
  calc
    ev ψ
        (leftTensor (ι₂ := ι) (((A * (∑ x ∈ s, B x) * C) * R)) *
          rightTensor (ι₁ := ι) D)
        = ev ψ
            (leftTensor (ι₂ := ι) (∑ x ∈ s, ((A * B x * C) * R)) *
              rightTensor (ι₁ := ι) D) := by rw [hinner]
    _ = ev ψ
          ((∑ x ∈ s, leftTensor (ι₂ := ι) (((A * B x * C) * R))) *
            rightTensor (ι₁ := ι) D) := by
          rw [leftTensor_finset_sum (ι₂ := ι)]
    _ = ev ψ
          (∑ x ∈ s,
            leftTensor (ι₂ := ι) (((A * B x * C) * R) ) *
              rightTensor (ι₁ := ι) D) := by
          rw [Finset.sum_mul]
    _ = ∑ x ∈ s,
          ev ψ
            (leftTensor (ι₂ := ι) (((A * B x * C) * R)) *
              rightTensor (ι₁ := ι) D) := by
          rw [ev_finset_sum]


/-- Evaluating the slice family at an appended point is postprocessing the slice
measurement by the fiber `{g | g u = a}`. -/
lemma evaluatedPointFamily_appendPoint_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (x : Fq params) (u : Point params) (a : Fq params) :
    (evaluatedPointFamily params family (appendPoint params u x)).outcome a =
      ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
        (G x).outcome g := by
  simp [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
    postprocess, hG, truncatePoint_appendPoint, pointHeight_appendPoint]

end MIPStarRE.LDT.Commutativity
