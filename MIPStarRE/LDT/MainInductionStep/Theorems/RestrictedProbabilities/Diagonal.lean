import MIPStarRE.LDT.MainInductionStep.Theorems.RestrictedProbabilities.Base

/-!
# Section 6 -- Diagonal Restricted Probability Bounds

This module contains the diagonal-line part of the restricted-probability
bookkeeping for the main induction step.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Equivalence repackaging a slice point `u : Point params`, a height `x : Fq params`
and an auxiliary index `β` as an ambient point `Point params.next` paired with the same
auxiliary index. This is the product-compatible form of `CommutativityPoints.pointNextEquiv`. -/
private def pointAppendProdEquiv (params : Parameters) [FieldModel params.q] (β : Type*) :
    Fq params × (Point params × β) ≃ Point params.next × β where
  toFun := fun xb => (appendPoint params xb.2.1 xb.1, xb.2.2)
  invFun := fun ub => (pointHeight params ub.1, (truncatePoint params ub.1, ub.2))
  left_inv := by
    rintro ⟨x, u, b⟩
    simp [truncatePoint_appendPoint, pointHeight_appendPoint]
  right_inv := by
    rintro ⟨u, b⟩
    exact Prod.ext ((CommutativityPoints.pointNextEquiv params).left_inv u) rfl

private lemma restrictedDiagonalSampleError_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params)
    (j : Fin params.m)
    (s : RestrictedDiagonalSample params j) :
    qBipartiteConsDefect strategy.state
      (RestrictedSymStrat.restrictedDiagonalPointAnswerFamily
        (xRestrictedStrategy params strategy x) j s)
      (RestrictedSymStrat.restrictedDiagonalLineAnswerFamily
        (xRestrictedStrategy params strategy x) j s) =
    qBipartiteConsDefect strategy.state
      (diagonalPointAnswerFamily strategy (embedCoord params j)
        (appendPoint params s.1 x, s.2))
      (diagonalLineAnswerFamily strategy (embedCoord params j)
        (appendPoint params s.1 x, s.2)) := by
  have hdir :
      appendPoint params (extendRestrictedDirection j s.2) zeroCoord =
        extendRestrictedDirection (params := params.next) (embedCoord params j) s.2 := by
    funext k
    by_cases hkm : k.1 < params.m
    · by_cases hk : k.1 ≤ j.1
      · simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hk]
      · simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hk]
        rfl
    · have hnotle : ¬ k.1 ≤ j.1 := by
          intro hk
          exact hkm (lt_of_le_of_lt hk j.2)
      simp [appendPoint, extendRestrictedDirection, embedCoord, hkm, hnotle]
      rfl
  have hline :
      DiagonalLine.appendAtHeight params
          { base := s.1, direction := extendRestrictedDirection j s.2 } x =
        ({ base := appendPoint params s.1 x,
           direction :=
             extendRestrictedDirection (params := params.next) (embedCoord params j) s.2 } :
          DiagonalLine params.next) := by
    simp [DiagonalLine.appendAtHeight, hdir]
  simp [RestrictedSymStrat.restrictedDiagonalPointAnswerFamily,
    RestrictedSymStrat.restrictedDiagonalLineAnswerFamily, diagonalPointAnswerFamily,
    diagonalLineAnswerFamily, xRestrictedStrategy]
  simp [hline]

/-- Per-index diagonal-line consistency defect of the restricted `x`-slice strategy
at embedded index `j`, averaged over the restricted diagonal sample space. -/
private noncomputable def diagonalSliceIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params)
    (j : Fin params.m) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (RestrictedDiagonalSample params j))
    (RestrictedSymStrat.restrictedDiagonalPointAnswerFamily
      (xRestrictedStrategy params strategy x) j)
    (RestrictedSymStrat.restrictedDiagonalLineAnswerFamily
      (xRestrictedStrategy params strategy x) j)

/-- Per-index diagonal-line consistency defect of the ambient `(m+1)`-dimensional
strategy at index `j`, averaged over the ambient restricted diagonal sample space. -/
private noncomputable def diagonalIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (j : Fin params.next.m) : Error :=
  bipartiteConsError strategy.state
    (uniformDistribution (RestrictedDiagonalSample params.next j))
    (diagonalPointAnswerFamily strategy j)
    (diagonalLineAnswerFamily strategy j)

private lemma diagonalIndexError_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (j : Fin params.next.m) :
    0 ≤ diagonalIndexError params strategy j := by
  unfold diagonalIndexError
  exact bipartiteConsError_nonneg strategy.state
    (uniformDistribution (RestrictedDiagonalSample params.next j))
    (diagonalPointAnswerFamily strategy j)
    (diagonalLineAnswerFamily strategy j)

private lemma diagonalSliceIndexErrorAverage_eq_diagonalIndexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (j : Fin params.m) :
    avgOver (uniformDistribution (Fq params))
      (fun x => diagonalSliceIndexError params strategy x j) =
      diagonalIndexError params strategy (embedCoord params j) := by
  let g : RestrictedDiagonalSample params.next (embedCoord params j) → Error := fun s =>
    qBipartiteConsDefect strategy.state
      (diagonalPointAnswerFamily strategy (embedCoord params j) s)
      (diagonalLineAnswerFamily strategy (embedCoord params j) s)
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => diagonalSliceIndexError params strategy x j)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (RestrictedDiagonalSample params j))
            (fun s => g (appendPoint params s.1 x, s.2))) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              unfold diagonalSliceIndexError bipartiteConsError
              refine avgOver_congr _ _ _ ?_
              intro s
              simpa [g] using restrictedDiagonalSampleError_eq params strategy x j s
    _ = avgOver (uniformDistribution (Fq params × RestrictedDiagonalSample params j))
          (fun xs => g (appendPoint params xs.2.1 xs.1, xs.2.2)) := by
            simpa using
              (avgOver_uniform_prod (α := Fq params)
                (β := RestrictedDiagonalSample params j)
                (f := fun x s => g (appendPoint params s.1 x, s.2))).symm
    _ = avgOver
          (uniformDistribution (RestrictedDiagonalSample params.next (embedCoord params j)))
          g := by
            simpa using
              (CommutativityPoints.avgOver_uniform_equiv
                (e := pointAppendProdEquiv params (Fin (j.val + 1) → Fq params))
                (f := fun xs : Fq params × RestrictedDiagonalSample params j =>
                  g ((pointAppendProdEquiv params (Fin (j.val + 1) → Fq params)) xs)))
    _ = diagonalIndexError params strategy (embedCoord params j) := by
            rfl

private lemma diagonalFailure_eq_average_indexError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fin params.next.m))
      (diagonalIndexError params strategy) =
      strategy.diagonalFailureProbability := by
  unfold diagonalIndexError SymStrat.diagonalFailureProbability
  calc
    avgOver (uniformDistribution (Fin params.next.m))
        (fun j =>
          bipartiteConsError strategy.state
            (uniformDistribution (RestrictedDiagonalSample params.next j))
            (diagonalPointAnswerFamily strategy j)
            (diagonalLineAnswerFamily strategy j))
      = ∑ j : Fin params.next.m,
          (1 / (params.next.m : Error)) *
            bipartiteConsError strategy.state
              (uniformDistribution (RestrictedDiagonalSample params.next j))
              (diagonalPointAnswerFamily strategy j)
              (diagonalLineAnswerFamily strategy j) := by
                simp [avgOver, uniformDistribution, Fintype.card_fin]
    _ = (1 / (params.next.m : Error)) *
          ∑ j : Fin params.next.m,
            bipartiteConsError strategy.state
              (uniformDistribution (RestrictedDiagonalSample params.next j))
              (diagonalPointAnswerFamily strategy j)
              (diagonalLineAnswerFamily strategy j) := by
                symm
                rw [Finset.mul_sum]
    _ = strategy.diagonalFailureProbability := by
          rfl

private lemma averageRestrictedDiagonalFailure_eq_embeddedDiagonalIndices
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
      (fun x => (xRestrictedStrategy params strategy x).diagonalFailureProbability) =
    avgOver (uniformDistribution (Fin params.m))
      (fun j => diagonalIndexError params strategy (embedCoord params j)) := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedStrategy params strategy x).diagonalFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Fin params.m))
            (fun j => diagonalSliceIndexError params strategy x j)) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              unfold RestrictedSymStrat.diagonalFailureProbability diagonalSliceIndexError
              calc
                (1 / (params.m : Error)) *
                    ∑ j : Fin params.m,
                      bipartiteConsError strategy.state
                        (uniformDistribution (RestrictedDiagonalSample params j))
                        ((xRestrictedStrategy params strategy
                          x).restrictedDiagonalPointAnswerFamily j)
                        ((xRestrictedStrategy params strategy
                          x).restrictedDiagonalLineAnswerFamily j)
                  = ∑ j : Fin params.m,
                      (1 / (params.m : Error)) *
                        bipartiteConsError strategy.state
                          (uniformDistribution (RestrictedDiagonalSample params j))
                          ((xRestrictedStrategy params strategy
                            x).restrictedDiagonalPointAnswerFamily j)
                          ((xRestrictedStrategy params strategy
                            x).restrictedDiagonalLineAnswerFamily j) := by
                              rw [Finset.mul_sum]
                _ = avgOver (uniformDistribution (Fin params.m))
                      (fun j => diagonalSliceIndexError params strategy x j) := by
                              simp [avgOver, uniformDistribution, Fintype.card_fin,
                                diagonalSliceIndexError]
    _ = avgOver (uniformDistribution (Fq params × Fin params.m))
          (fun xj => diagonalSliceIndexError params strategy xj.1 xj.2) := by
            simpa using
              (avgOver_uniform_prod (α := Fq params) (β := Fin params.m)
                (f := fun x j => diagonalSliceIndexError params strategy x j)).symm
    _ = avgOver (uniformDistribution (Fin params.m × Fq params))
          (fun jx => diagonalSliceIndexError params strategy jx.2 jx.1) := by
            simpa using
              (CommutativityPoints.avgOver_uniform_equiv
                (e := Equiv.prodComm (Fq params) (Fin params.m))
                (f := fun xj : Fq params × Fin params.m =>
                  diagonalSliceIndexError params strategy xj.1 xj.2))
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun j => avgOver (uniformDistribution (Fq params))
            (fun x => diagonalSliceIndexError params strategy x j)) := by
            simpa using
              (avgOver_uniform_prod (α := Fin params.m) (β := Fq params)
                (f := fun j x => diagonalSliceIndexError params strategy x j))
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun j => diagonalIndexError params strategy (embedCoord params j)) := by
            refine avgOver_congr _ _ _ ?_
            intro j
            exact diagonalSliceIndexErrorAverage_eq_diagonalIndexError params strategy j

/-- The weighted average of the restricted diagonal slice errors is bounded by
 the ambient diagonal-line test error. -/
lemma weighted_diagonal_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedStrategy params strategy x).diagonalFailureProbability) ≤ gamma := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedStrategy params strategy x).diagonalFailureProbability)
      = sliceTransverseDirectionWeight params *
          avgOver (uniformDistribution (Fq params))
            (fun x => (xRestrictedStrategy params strategy x).diagonalFailureProbability) := by
              rw [avgOver_const_mul]
    _ = sliceTransverseDirectionWeight params *
          avgOver (uniformDistribution (Fin params.m))
            (fun j => diagonalIndexError params strategy (embedCoord params j)) := by
              rw [averageRestrictedDiagonalFailure_eq_embeddedDiagonalIndices params strategy]
    _ ≤ avgOver (uniformDistribution (Fin params.next.m))
          (diagonalIndexError params strategy) :=
        weighted_embedded_average_le_full_average params
          (f := diagonalIndexError params strategy)
          (hf := diagonalIndexError_nonneg params strategy)
    _ = strategy.diagonalFailureProbability :=
        diagonalFailure_eq_average_indexError params strategy
    _ ≤ gamma := hgood.diagonalLineTest

end MIPStarRE.LDT.MainInductionStep
