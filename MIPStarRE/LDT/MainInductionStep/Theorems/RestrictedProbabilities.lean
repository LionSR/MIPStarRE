import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import MIPStarRE.LDT.MainInductionStep.Statements
import MIPStarRE.LDT.Test.StrategyFailures
import MIPStarRE.LDT.CommutativityPoints.Approximation
import MIPStarRE.LDT.Tactic.AvgCongr

/-!
# Section 6 — Restricted Probability Bookkeeping

Private helper lemmas for restricted-axis and restricted-diagonal sample
errors, together with the public `weighted_axisParallel_bound`,
`weighted_diagonal_bound`, `restrictedProbabilities`, and their
answer-valued analogues.

Three helpers (`answerRestricted_*FailureProbability_eq`) are exposed
because they are also used in the `PackageConstructors` leaf module.

## References

- `blueprint/src/chapter/ch10_induction.tex`
-/

namespace MIPStarRE.LDT.MainInductionStep

open MIPStarRE.LDT
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Restricted-probability bookkeeping -/

private lemma selfConsistencyRestrictedAverage_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability) =
      strategy.selfConsistencyFailureProbability := by
  let g : Point params.next → Error :=
    fun u =>
      qBipartiteSSCDefect strategy.state ((strategy.pointMeasurement u).toSubMeas)
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Point params))
            (fun u => g (appendPoint params u x))) := by
              rfl
    _ = avgOver (uniformDistribution (Point params.next)) g := by
          simpa using (CommutativityPoints.avgOver_uniform_pointNext_decompose params g).symm
    _ = strategy.selfConsistencyFailureProbability := by
          rfl

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

private lemma restrictAxisParallelMeasurement_toSubMeas_eq_transport
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params)
    (ℓ : AxisParallelLine params) :
    (restrictAxisParallelMeasurement params strategy x ℓ).toSubMeas =
      SubMeas.transport (axisLinePolynomialEquiv params x).symm
        ((strategy.axisParallelMeasurement
          (AxisParallelLine.appendAtHeight params ℓ x)).toSubMeas) := by
  refine SubMeas.ext ?_ ?_
  · intro f
    rfl
  · simpa [SubMeas.transport,
      (strategy.axisParallelMeasurement
        (AxisParallelLine.appendAtHeight params ℓ x)).total_eq_one] using
      (restrictAxisParallelMeasurement params strategy x ℓ).total_eq_one

private lemma restrictAxisParallelMeasurement_postprocess_zero
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params)
    (ℓ : AxisParallelLine params) :
    postprocess ((restrictAxisParallelMeasurement params strategy x ℓ).toSubMeas) (· zeroCoord) =
      postprocess
        ((strategy.axisParallelMeasurement (AxisParallelLine.appendAtHeight params ℓ x)).toSubMeas)
        (fun f : AxisLinePolynomial params.next => f zeroCoord) := by
  rw [restrictAxisParallelMeasurement_toSubMeas_eq_transport params strategy x ℓ]
  rw [SubMeas.postprocess_transport]
  have hreadout :
      (fun a : AxisLinePolynomial params.next =>
          ((axisLinePolynomialEquiv params x).symm a) zeroCoord) =
        (fun f : AxisLinePolynomial params.next => f zeroCoord) := by
    funext a
    cases a
    rfl
  simp [hreadout]

private lemma restrictedAxisSampleError_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params)
    (u : Point params)
    (i : Fin params.m) :
    qBipartiteConsDefect strategy.state
      (RestrictedSymStrat.axisParallelPointAnswerFamily
        (xRestrictedStrategy params strategy x) (u, i))
      (RestrictedSymStrat.axisParallelLineAnswerFamily
        (xRestrictedStrategy params strategy x) (u, i)) =
    qBipartiteConsDefect strategy.state
      (axisParallelPointAnswerFamily strategy (appendPoint params u x, embedCoord params i))
      (axisParallelLineAnswerFamily strategy (appendPoint params u x, embedCoord params i)) := by
  simp [RestrictedSymStrat.axisParallelPointAnswerFamily,
    RestrictedSymStrat.axisParallelLineAnswerFamily, axisParallelPointAnswerFamily,
    axisParallelLineAnswerFamily, xRestrictedStrategy]
  simpa [AxisParallelLine.appendAtHeight] using
    congrArg
      (fun B =>
        qBipartiteConsDefect strategy.state
          ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas) B)
      (restrictAxisParallelMeasurement_postprocess_zero params strategy x
        { base := u, direction := i })

/-- Per-direction axis-parallel consistency defect of the restricted `x`-slice
strategy at embedded direction `i`, averaged over the slice point space
`Point params`. -/
private noncomputable def sliceAxisDirectionError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (x : Fq params)
    (i : Fin params.m) : Error :=
  avgOver (uniformDistribution (Point params)) fun u =>
    qBipartiteConsDefect strategy.state
      (RestrictedSymStrat.axisParallelPointAnswerFamily
        (xRestrictedStrategy params strategy x) (u, i))
      (RestrictedSymStrat.axisParallelLineAnswerFamily
        (xRestrictedStrategy params strategy x) (u, i))

/-- Per-direction axis-parallel consistency defect of the ambient `(m+1)`-dimensional
strategy at direction `i`, averaged over the ambient point space `Point params.next`. -/
private noncomputable def axisDirectionError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (i : Fin params.next.m) : Error :=
  avgOver (uniformDistribution (Point params.next)) fun u =>
    qBipartiteConsDefect strategy.state
      (axisParallelPointAnswerFamily strategy (u, i))
      (axisParallelLineAnswerFamily strategy (u, i))

private lemma axisDirectionError_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (i : Fin params.next.m) :
    0 ≤ axisDirectionError params strategy i := by
  unfold axisDirectionError
  refine avgOver_nonneg (uniformDistribution (Point params.next)) _ ?_
  intro u
  exact qBipartiteConsDefect_nonneg strategy.state
    (axisParallelPointAnswerFamily strategy (u, i))
    (axisParallelLineAnswerFamily strategy (u, i))

private lemma sliceAxisDirectionErrorAverage_eq_axisDirectionError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (i : Fin params.m) :
    avgOver (uniformDistribution (Fq params))
      (fun x => sliceAxisDirectionError params strategy x i) =
      axisDirectionError params strategy (embedCoord params i) := by
  let g : Point params.next → Error := fun u =>
    qBipartiteConsDefect strategy.state
      (axisParallelPointAnswerFamily strategy (u, embedCoord params i))
      (axisParallelLineAnswerFamily strategy (u, embedCoord params i))
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceAxisDirectionError params strategy x i)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Point params))
            (fun u => g (appendPoint params u x))) := by
              unfold sliceAxisDirectionError
              avg_congr with x, u
              simpa [g] using restrictedAxisSampleError_eq params strategy x u i
    _ = avgOver (uniformDistribution (Point params.next)) g := by
          simpa using (CommutativityPoints.avgOver_uniform_pointNext_decompose params g).symm
    _ = axisDirectionError params strategy (embedCoord params i) := by
          rfl

private lemma axisFailure_eq_average_directionError
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fin params.next.m))
      (axisDirectionError params strategy) =
      strategy.axisParallelFailureProbability := by
  let err : Fin params.next.m × Point params.next → Error := fun iu =>
    qBipartiteConsDefect strategy.state
      (axisParallelPointAnswerFamily strategy (iu.2, iu.1))
      (axisParallelLineAnswerFamily strategy (iu.2, iu.1))
  have hprod :
      avgOver (uniformDistribution (Fin params.next.m))
          (fun i => avgOver (uniformDistribution (Point params.next))
            (fun u => err (i, u))) =
        avgOver (uniformDistribution (Fin params.next.m × Point params.next)) err := by
    simpa using
      (avgOver_uniform_prod (α := Fin params.next.m) (β := Point params.next)
        (f := fun i u => err (i, u))).symm
  have hswap :
      avgOver (uniformDistribution (Fin params.next.m × Point params.next)) err =
        avgOver (uniformDistribution (Point params.next × Fin params.next.m))
          (fun ui => err (ui.2, ui.1)) := by
    simpa using
      (CommutativityPoints.avgOver_uniform_equiv
        (e := Equiv.prodComm (Fin params.next.m) (Point params.next))
        (f := err))
  calc
    avgOver (uniformDistribution (Fin params.next.m)) (axisDirectionError params strategy)
      = avgOver (uniformDistribution (Fin params.next.m))
          (fun i => avgOver (uniformDistribution (Point params.next))
            (fun u => err (i, u))) := by
              avg_congr
    _ = avgOver (uniformDistribution (Fin params.next.m × Point params.next)) err := hprod
    _ = avgOver (uniformDistribution (Point params.next × Fin params.next.m))
          (fun ui => err (ui.2, ui.1)) := hswap
    _ = strategy.axisParallelFailureProbability := by
          rfl

private lemma averageRestrictedAxisFailure_eq_embeddedAxisDirections
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    avgOver (uniformDistribution (Fq params))
      (fun x => (xRestrictedStrategy params strategy x).axisParallelFailureProbability) =
    avgOver (uniformDistribution (Fin params.m))
      (fun i => axisDirectionError params strategy (embedCoord params i)) := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => (xRestrictedStrategy params strategy x).axisParallelFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => avgOver (uniformDistribution (Fin params.m))
            (fun i => sliceAxisDirectionError params strategy x i)) := by
              refine avgOver_congr _ _ _ ?_
              intro x
              unfold RestrictedSymStrat.axisParallelFailureProbability bipartiteConsError
              calc
                avgOver (uniformDistribution (Point params × Fin params.m))
                    (fun s =>
                      qBipartiteConsDefect strategy.state
                        (RestrictedSymStrat.axisParallelPointAnswerFamily
                          (xRestrictedStrategy params strategy x) s)
                        (RestrictedSymStrat.axisParallelLineAnswerFamily
                          (xRestrictedStrategy params strategy x) s))
                  = avgOver (uniformDistribution (Fin params.m × Point params))
                      (fun iu =>
                        qBipartiteConsDefect strategy.state
                          (RestrictedSymStrat.axisParallelPointAnswerFamily
                            (xRestrictedStrategy params strategy x) (iu.2, iu.1))
                          (RestrictedSymStrat.axisParallelLineAnswerFamily
                            (xRestrictedStrategy params strategy x) (iu.2, iu.1))) := by
                              simpa using
                                (CommutativityPoints.avgOver_uniform_equiv
                                  (e := Equiv.prodComm (Point params) (Fin params.m))
                                  (f := fun s : Point params × Fin params.m =>
                                    qBipartiteConsDefect strategy.state
                                      (RestrictedSymStrat.axisParallelPointAnswerFamily
                                        (xRestrictedStrategy params strategy x) s)
                                      (RestrictedSymStrat.axisParallelLineAnswerFamily
                                        (xRestrictedStrategy params strategy x) s)))
                _ = avgOver (uniformDistribution (Fin params.m))
                      (fun i => avgOver (uniformDistribution (Point params))
                        (fun u =>
                          qBipartiteConsDefect strategy.state
                            (RestrictedSymStrat.axisParallelPointAnswerFamily
                              (xRestrictedStrategy params strategy x) (u, i))
                            (RestrictedSymStrat.axisParallelLineAnswerFamily
                              (xRestrictedStrategy params strategy x) (u, i)))) := by
                                simpa using
                                  (avgOver_uniform_prod (α := Fin params.m) (β := Point params)
                                    (f := fun i u =>
                                      qBipartiteConsDefect strategy.state
                                        (RestrictedSymStrat.axisParallelPointAnswerFamily
                                          (xRestrictedStrategy params strategy x) (u, i))
                                        (RestrictedSymStrat.axisParallelLineAnswerFamily
                                          (xRestrictedStrategy params strategy x) (u, i))))
                _ = avgOver (uniformDistribution (Fin params.m))
                      (fun i => sliceAxisDirectionError params strategy x i) := by
                                rfl
    _ = avgOver (uniformDistribution (Fq params × Fin params.m))
          (fun xi => sliceAxisDirectionError params strategy xi.1 xi.2) := by
            simpa using
              (avgOver_uniform_prod (α := Fq params) (β := Fin params.m)
                (f := fun x i => sliceAxisDirectionError params strategy x i)).symm
    _ = avgOver (uniformDistribution (Fin params.m × Fq params))
          (fun ix => sliceAxisDirectionError params strategy ix.2 ix.1) := by
            simpa using
              (CommutativityPoints.avgOver_uniform_equiv
                (e := Equiv.prodComm (Fq params) (Fin params.m))
                (f := fun xi : Fq params × Fin params.m =>
                  sliceAxisDirectionError params strategy xi.1 xi.2))
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun i => avgOver (uniformDistribution (Fq params))
            (fun x => sliceAxisDirectionError params strategy x i)) := by
            simpa using
              (avgOver_uniform_prod (α := Fin params.m) (β := Fq params)
                (f := fun i x => sliceAxisDirectionError params strategy x i))
    _ = avgOver (uniformDistribution (Fin params.m))
          (fun i => axisDirectionError params strategy (embedCoord params i)) := by
            refine avgOver_congr _ _ _ ?_
            intro i
            exact sliceAxisDirectionErrorAverage_eq_axisDirectionError params strategy i

private lemma weighted_embedded_average_le_full_average
    (params : Parameters)
    (f : Fin params.next.m → Error)
    (hf : ∀ i, 0 ≤ f i) :
    sliceTransverseDirectionWeight params *
        avgOver (uniformDistribution (Fin params.m)) (fun i => f (embedCoord params i)) ≤
      avgOver (uniformDistribution (Fin params.next.m)) f := by
  have hm : (params.m : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.hm)
  have hnextm : (params.next.m : Error) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt params.next.hm)
  have hsum_le :
      ∑ i : Fin params.m, f (embedCoord params i) ≤ ∑ j : Fin params.next.m, f j := by
    classical
    calc
      ∑ i : Fin params.m, f (embedCoord params i)
        = Finset.sum
            (((Finset.univ : Finset (Fin params.m)).image (embedCoord params)))
            (fun j => f j) := by
            symm
            refine Finset.sum_image ?_
            intro a _ b _ hab
            exact embedCoord_injective params hab
      _ ≤ ∑ j : Fin params.next.m, f j := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (by simp) ?_
            intro j _ _
            exact hf j
  calc
    sliceTransverseDirectionWeight params *
        avgOver (uniformDistribution (Fin params.m)) (fun i => f (embedCoord params i))
      = sliceTransverseDirectionWeight params *
          ∑ i : Fin params.m, (1 / (params.m : Error)) * f (embedCoord params i) := by
            simp [avgOver, uniformDistribution, Fintype.card_fin]
    _ = ∑ i : Fin params.m,
          (sliceTransverseDirectionWeight params * (1 / (params.m : Error)))
              * f (embedCoord params i) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
    _ = ∑ i : Fin params.m, (1 / (params.next.m : Error)) * f (embedCoord params i) := by
            have hnext : (params.next.m : Error) = (params.m : Error) + 1 := by
              simp [Parameters.next]
            have hplus_ne : (params.m : Error) + 1 ≠ 0 := hnext ▸ hnextm
            have hweight :
                sliceTransverseDirectionWeight params =
                  (params.m : Error) / ((params.m : Error) + 1) := by
              unfold sliceTransverseDirectionWeight
              push_cast
              ring
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hweight, hnext]
            field_simp
    _ = (1 / (params.next.m : Error)) * ∑ i : Fin params.m, f (embedCoord params i) := by
            symm
            rw [Finset.mul_sum]
    _ ≤ (1 / (params.next.m : Error)) * ∑ j : Fin params.next.m, f j := by
            exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = ∑ j : Fin params.next.m, (1 / (params.next.m : Error)) * f j := by
            rw [Finset.mul_sum]
    _ = avgOver (uniformDistribution (Fin params.next.m)) f := by
            simp [avgOver, uniformDistribution, Fintype.card_fin]

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

/-- The weighted average of the restricted axis-parallel slice errors is bounded
by the ambient axis-parallel test error. -/
lemma weighted_axisParallel_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedStrategy params strategy x).axisParallelFailureProbability) ≤ eps := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedStrategy params strategy x).axisParallelFailureProbability)
      = sliceTransverseDirectionWeight params *
          avgOver (uniformDistribution (Fq params))
            (fun x => (xRestrictedStrategy params strategy x).axisParallelFailureProbability) := by
              rw [avgOver_const_mul]
    _ = sliceTransverseDirectionWeight params *
          avgOver (uniformDistribution (Fin params.m))
            (fun i => axisDirectionError params strategy (embedCoord params i)) := by
              rw [averageRestrictedAxisFailure_eq_embeddedAxisDirections params strategy]
    _ ≤ avgOver (uniformDistribution (Fin params.next.m))
          (axisDirectionError params strategy) :=
        weighted_embedded_average_le_full_average params
          (f := axisDirectionError params strategy)
          (hf := axisDirectionError_nonneg params strategy)
    _ = strategy.axisParallelFailureProbability :=
        axisFailure_eq_average_directionError params strategy
    _ ≤ eps := hgood.axisParallelTest

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

private lemma weighted_bound_to_average
    (params : Parameters)
    {a b : Error}
    (h : sliceTransverseDirectionWeight params * a ≤ b) :
    a ≤ sliceConditioningLoss params * b := by
  have hmul :
      sliceConditioningLoss params * (sliceTransverseDirectionWeight params * a) ≤
        sliceConditioningLoss params * b :=
    mul_le_mul_of_nonneg_left h (by
      unfold sliceConditioningLoss
      positivity)
  have hcancel :
      sliceConditioningLoss params * (sliceTransverseDirectionWeight params * a) = a := by
    unfold sliceConditioningLoss sliceTransverseDirectionWeight
    have hm : (params.m : Error) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt params.hm)
    have hms : (((params.m + 1 : ℕ) : Error)) ≠ 0 := by
      exact_mod_cast (Nat.succ_ne_zero params.m)
    field_simp [hm, hms]
  calc
    a = sliceConditioningLoss params * (sliceTransverseDirectionWeight params * a) := by
          symm
          exact hcancel
    _ ≤ sliceConditioningLoss params * b := hmul

/-- Package weighted restricted axis/diagonal bounds into the public
`RestrictedProbabilitiesStatement`. -/
lemma RestrictedProbabilitiesStatement.ofWeightedBounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).axisParallelFailureProbability) ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).diagonalFailureProbability) ≤ gamma) :
    RestrictedProbabilitiesStatement params strategy eps delta gamma := by
  let profile : RestrictedFailureProfile params strategy :=
    { axisParallel := fun x =>
        (xRestrictedStrategy params strategy x).axisParallelFailureProbability
      selfConsistency := fun x =>
        (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability
      diagonal := fun x =>
        (xRestrictedStrategy params strategy x).diagonalFailureProbability
      restrictedGood := by
        intro x
        exact ⟨le_rfl, le_rfl, le_rfl⟩ }
  have haxis_weighted_avg :
      sliceTransverseDirectionWeight params *
          averageRestrictedAxisParallelError params profile ≤ eps := by
    simpa [profile, averageRestrictedAxisParallelError, avgOver_const_mul] using
      haxisWeightedBound
  have hdiag_weighted_avg :
      sliceTransverseDirectionWeight params *
          averageRestrictedDiagonalError params profile ≤ gamma := by
    simpa [profile, averageRestrictedDiagonalError, avgOver_const_mul] using
      hdiagonalWeightedBound
  refine ⟨profile, ?_⟩
  refine ⟨weighted_bound_to_average params haxis_weighted_avg, ?_, ?_⟩
  · calc
      averageRestrictedSelfConsistencyError params profile
        = strategy.selfConsistencyFailureProbability := by
            simpa [profile, averageRestrictedSelfConsistencyError] using
              selfConsistencyRestrictedAverage_eq params strategy
      _ ≤ delta := hgood.selfConsistencyTest
  · exact weighted_bound_to_average params hdiag_weighted_avg

/-- `lem:restricted-probabilities`. -/
lemma restrictedProbabilities
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    RestrictedProbabilitiesStatement params strategy eps delta gamma := by
  exact RestrictedProbabilitiesStatement.ofWeightedBounds params strategy eps delta gamma hgood
    (weighted_axisParallel_bound params strategy eps delta gamma hgood)
    (weighted_diagonal_bound params strategy eps delta gamma hgood)

/-- The answer-valued slice has the same axis-parallel failure probability as the
legacy restricted slice. -/
lemma answerRestricted_axisParallelFailureProbability_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability =
      (xRestrictedStrategy params strategy x).axisParallelFailureProbability := by
  rfl

/-- The answer-valued slice has the same self-consistency failure probability as
the legacy restricted slice. -/
lemma answerRestricted_selfConsistencyFailureProbability_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).selfConsistencyFailureProbability =
      (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability := by
  rfl

/-- The answer-valued slice has the same verifier-visible diagonal failure
probability as the legacy restricted slice after evaluating line answers at the
base point. -/
lemma answerRestricted_diagonalFailureProbability_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability =
      (xRestrictedStrategy params strategy x).diagonalFailureProbability := by
  unfold AnswerSymStrat.diagonalFailureProbability RestrictedSymStrat.diagonalFailureProbability
  apply congrArg (fun s => (1 / (params.m : Error)) * s)
  refine Finset.sum_congr rfl ?_
  intro j _hj
  apply congrArg
  funext s
  let ℓ : DiagonalLine params :=
    { base := s.1, direction := extendRestrictedDirection j s.2 }
  change
    postprocess ((restrictDiagonalAnswerMeasurement params strategy x ℓ).toSubMeas)
        (fun f : DiagonalLineAnswer params => f zeroCoord) =
      postprocess ((restrictDiagonalMeasurement params strategy x ℓ).toSubMeas)
        (fun f : DiagonalLinePolynomial params => f zeroCoord)
  rw [restrictDiagonalAnswerMeasurement_postprocess_zero,
    restrictDiagonalMeasurement_postprocess_zero]

/-- The weighted average of the answer-valued restricted axis-parallel slice errors
is bounded by the ambient axis-parallel test error. -/
lemma answer_weighted_axisParallel_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability) ≤ eps := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).axisParallelFailureProbability) := by
            refine avgOver_congr _ _ _ ?_
            intro x
            rw [answerRestricted_axisParallelFailureProbability_eq]
    _ ≤ eps := weighted_axisParallel_bound params strategy eps delta gamma hgood

/-- The weighted average of the answer-valued restricted diagonal slice errors is
bounded by the ambient diagonal-line test error. -/
lemma answer_weighted_diagonal_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability) ≤ gamma := by
  calc
    avgOver (uniformDistribution (Fq params))
        (fun x => sliceTransverseDirectionWeight params *
          (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability)
      = avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedStrategy params strategy x).diagonalFailureProbability) := by
            refine avgOver_congr _ _ _ ?_
            intro x
            rw [answerRestricted_diagonalFailureProbability_eq]
    _ ≤ gamma := weighted_diagonal_bound params strategy eps delta gamma hgood

/-- Package answer-valued weighted restricted axis/diagonal bounds into the public
answer-valued restricted-probabilities statement. -/
lemma AnswerRestrictedProbabilitiesStatement.ofWeightedBounds
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (haxisWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability) ≤ eps)
    (hdiagonalWeightedBound :
      avgOver (uniformDistribution (Fq params))
          (fun x => sliceTransverseDirectionWeight params *
            (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability) ≤ gamma) :
    AnswerRestrictedProbabilitiesStatement params strategy eps delta gamma := by
  let profile : AnswerRestrictedFailureProfile params strategy :=
    { axisParallel := fun x =>
        (xRestrictedAnswerSymStrat params strategy x).axisParallelFailureProbability
      selfConsistency := fun x =>
        (xRestrictedAnswerSymStrat params strategy x).selfConsistencyFailureProbability
      diagonal := fun x =>
        (xRestrictedAnswerSymStrat params strategy x).diagonalFailureProbability
      restrictedGood := by
        intro x
        exact ⟨le_rfl, le_rfl, le_rfl⟩ }
  have haxis_weighted_avg :
      sliceTransverseDirectionWeight params *
          averageAnswerRestrictedAxisParallelError params profile ≤ eps := by
    simpa [profile, averageAnswerRestrictedAxisParallelError, avgOver_const_mul] using
      haxisWeightedBound
  have hdiag_weighted_avg :
      sliceTransverseDirectionWeight params *
          averageAnswerRestrictedDiagonalError params profile ≤ gamma := by
    simpa [profile, averageAnswerRestrictedDiagonalError, avgOver_const_mul] using
      hdiagonalWeightedBound
  refine ⟨profile, ?_⟩
  refine ⟨weighted_bound_to_average params haxis_weighted_avg, ?_, ?_⟩
  · calc
      averageAnswerRestrictedSelfConsistencyError params profile
        = avgOver (uniformDistribution (Fq params))
            (fun x =>
              (xRestrictedStrategy params strategy x).selfConsistencyFailureProbability) := by
            refine avgOver_congr _ _ _ ?_
            intro x
            simp [profile,
              answerRestricted_selfConsistencyFailureProbability_eq]
      _ = strategy.selfConsistencyFailureProbability := by
            exact selfConsistencyRestrictedAverage_eq params strategy
      _ ≤ delta := hgood.selfConsistencyTest
  · exact weighted_bound_to_average params hdiag_weighted_avg

/-- Answer-valued version of `lem:restricted-probabilities`. -/
lemma answerRestrictedProbabilities
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    AnswerRestrictedProbabilitiesStatement params strategy eps delta gamma := by
  exact AnswerRestrictedProbabilitiesStatement.ofWeightedBounds
    params strategy eps delta gamma hgood
    (answer_weighted_axisParallel_bound params strategy eps delta gamma hgood)
    (answer_weighted_diagonal_bound params strategy eps delta gamma hgood)



end MIPStarRE.LDT.MainInductionStep
