import MIPStarRE.LDT.Pasting.Core
import MIPStarRE.LDT.Pasting.Sandwich.Switcheroo

/-!
# Section 12 pasting: commuting-with-G incomplete part

Incomplete-part commuting-with-`G` bounds.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `cor:commuting-with-G-incomplete`. -/
theorem commutingWithGIncomplete
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hcomm : CommutingWithGCompleteStatement params ψbi family gamma zeta) :
    CommutingWithGIncompleteStatement params ψbi family gamma zeta := by
  refine {
    pointWithIncompletePartCommutation := ?_
    incompletePartCommutation := ?_
  }
  · rcases hcomm.pointWithCompletePartCommutation with ⟨hcomplete_bound⟩
    refine ⟨?_⟩
    calc
      sddErrorOp ψbi
          (uniformDistribution (SlicePairQuestion params))
          (incompletePartPointProductLeft params family)
          (incompletePartPointProductRight params family)
        =
          sddErrorOp ψbi
            (uniformDistribution (SlicePairQuestion params))
            (completePartPointProductLeft params family)
            (completePartPointProductRight params family) := by
              unfold sddErrorOp
              apply avgOver_congr
              intro q
              unfold qSDDOp qSDDCore
              apply Finset.sum_congr rfl
              intro g _hg
              have hdiff :
                  (incompletePartPointProductLeft params family q).outcome g -
                      (incompletePartPointProductRight params family q).outcome g =
                    -((completePartPointProductLeft params family q).outcome g -
                      (completePartPointProductRight params family q).outcome g) := by
                let A : MIPStarRE.Quantum.Op ι := (family.meas q.1).outcome g
                let B : MIPStarRE.Quantum.Op ι :=
                  (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).total
                have hinner : A * (1 - B) - (1 - B) * A = -(A * B - B * A) := by
                  dsimp [A, B]
                  noncomm_ring
                ext i j
                rcases i with ⟨i₁, i₂⟩
                rcases j with ⟨j₁, j₂⟩
                by_cases h₂ : i₂ = j₂
                · have hentry := congrArg (fun X : MIPStarRE.Quantum.Op ι => X i₁ j₁) hinner
                  simpa [incompletePartPointProductLeft, incompletePartPointProductRight,
                    completePartPointProductLeft, completePartPointProductRight,
                    OpFamily.leftPlacedOpFamily, multiplyByTotalOnRight,
                    multiplyByTotalOnLeft, incompletePartSubMeas, completePartSubMeas,
                    sub_eq_add_neg, leftTensor, A, B, h₂] using hentry
                · simp [incompletePartPointProductLeft, incompletePartPointProductRight,
                    completePartPointProductLeft, completePartPointProductRight,
                    OpFamily.leftPlacedOpFamily, multiplyByTotalOnRight,
                    multiplyByTotalOnLeft, incompletePartSubMeas, completePartSubMeas,
                    sub_eq_add_neg, leftTensor, h₂]
              rw [hdiff]
              have hswap :
                  (((completePartPointProductRight params family q).outcome g)ᴴ -
                        ((completePartPointProductLeft params family q).outcome g)ᴴ) *
                      ((completePartPointProductRight params family q).outcome g -
                        (completePartPointProductLeft params family q).outcome g) =
                    (((completePartPointProductLeft params family q).outcome g)ᴴ -
                        ((completePartPointProductRight params family q).outcome g)ᴴ) *
                      ((completePartPointProductLeft params family q).outcome g -
                        (completePartPointProductRight params family q).outcome g) := by
                noncomm_ring
              simpa [sub_eq_add_neg] using congrArg (ev ψbi) hswap
      _ ≤ commutingWithGIncompleteError params gamma zeta := by
          simpa [commutingWithGIncompleteError] using hcomplete_bound
  · rcases hcomm.completePartCommutation with ⟨hcomplete_bound⟩
    refine ⟨?_⟩
    calc
      sddErrorOp ψbi
          (uniformDistribution (SlicePairQuestion params))
          (incompletePartTotalProductLeft params family)
          (incompletePartTotalProductRight params family)
        =
          sddErrorOp ψbi
            (uniformDistribution (SlicePairQuestion params))
            (completePartTotalProductLeft params family)
            (completePartTotalProductRight params family) := by
              unfold sddErrorOp
              apply avgOver_congr
              intro q
              unfold qSDDOp qSDDCore
              apply Finset.sum_congr rfl
              intro u _hu
              cases u
              have hq1 :
                  (postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).outcome () =
                    (family.meas q.1).total := by
                simpa [completePartSubMeas] using
                  (completePartSubMeas_outcome_unit
                    (params := params) (family := family) q.1)
              have hq2 :
                  (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).outcome () =
                    (family.meas q.2).total := by
                simpa [completePartSubMeas] using
                  (completePartSubMeas_outcome_unit
                    (params := params) (family := family) q.2)
              have hdiff :
                  (incompletePartTotalProductLeft params family q).outcome () -
                      (incompletePartTotalProductRight params family q).outcome () =
                    (completePartTotalProductLeft params family q).outcome () -
                      (completePartTotalProductRight params family q).outcome () := by
                let A : MIPStarRE.Quantum.Op ι :=
                  (postprocess ((family.meas q.1).toSubMeas) (fun _ => ())).total
                let B : MIPStarRE.Quantum.Op ι :=
                  (postprocess ((family.meas q.2).toSubMeas) (fun _ => ())).total
                have hinner : (1 - A) * (1 - B) - (1 - B) * (1 - A) = A * B - B * A := by
                  dsimp [A, B]
                  noncomm_ring
                ext i j
                rcases i with ⟨i₁, i₂⟩
                rcases j with ⟨j₁, j₂⟩
                by_cases h₂ : i₂ = j₂
                · have hentry := congrArg (fun X : MIPStarRE.Quantum.Op ι => X i₁ j₁) hinner
                  simpa [incompletePartTotalProductLeft, incompletePartTotalProductRight,
                    completePartTotalProductLeft, completePartTotalProductRight,
                    OpFamily.leftPlacedOpFamily, multiplyByTotalOnRight,
                    multiplyByTotalOnLeft, incompletePartSubMeas, completePartSubMeas,
                    sub_eq_add_neg, leftTensor, A, B, hq1, hq2, h₂,
                    (family.meas q.1).sum_eq_total,
                    (family.meas q.2).sum_eq_total] using hentry
                · simp [incompletePartTotalProductLeft, incompletePartTotalProductRight,
                    completePartTotalProductLeft, completePartTotalProductRight,
                    OpFamily.leftPlacedOpFamily, multiplyByTotalOnRight,
                    multiplyByTotalOnLeft, incompletePartSubMeas, completePartSubMeas,
                    sub_eq_add_neg, leftTensor, h₂, (family.meas q.1).sum_eq_total]
              rw [hdiff]
      _ ≤ commutingWithGIncompleteError params gamma zeta := by
          simpa [commutingWithGIncompleteError] using hcomplete_bound

end MIPStarRE.LDT.Pasting
