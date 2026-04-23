import MIPStarRE.LDT.Basic.Parameters
import MIPStarRE.LDT.CommutativityPoints.Defs
import MIPStarRE.LDT.Preliminaries.Theorems

/-!
# Section 10 — commutativity points approximation layer

Restricted-diagonal approximation infrastructure for commutativity at points.
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix MatrixOrder ComplexOrder BigOperators

/-- The final restriction index, corresponding to the paper's `m`-restricted
diagonal-lines test. -/
private def lastRestrictionIndex (params : Parameters) : Fin params.m :=
  ⟨params.m - 1, Nat.sub_lt params.hm Nat.zero_lt_one⟩

/-- Reindexing a uniform average along an equivalence preserves its value. -/
lemma avgOver_uniform_equiv
    {α β : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (e : α ≃ β) (f : α → Error) :
    avgOver (uniformDistribution α) f =
      avgOver (uniformDistribution β) (fun b => f (e.symm b)) := by
  simpa using MIPStarRE.LDT.avgOver_uniform_equiv e f

/-- Decompose a point in `Point params.next` into its truncated point and final coordinate. -/
def pointNextEquiv (params : Parameters) [FieldModel params.q] :
    Point params.next ≃ Point params × Fq params where
  toFun := fun u => (truncatePoint params u, pointHeight params u)
  invFun := fun ux => appendPoint params ux.1 ux.2
  left_inv := by
    intro u
    funext i
    by_cases h : i.1 < params.m
    · simp [appendPoint, truncatePoint, h]
    · have hi : i.1 = params.m := by
        have hi_lt : i.1 < params.m + 1 := by
          simpa [Parameters.next] using i.2
        omega
      have hlast : i = lastCoord params := by
        apply Fin.ext
        simp [lastCoord, hi]
      simp [appendPoint, truncatePoint, pointHeight, hlast]
  right_inv := by
    rintro ⟨u, x⟩
    simp [truncatePoint_appendPoint, pointHeight_appendPoint]

/-- Build an operator family from its outcomes, taking the total to be their sum. -/
noncomputable def opFamilyOfOutcome {Outcome : Type*} [Fintype Outcome]
    (outcome : Outcome → MIPStarRE.Quantum.Op ι) :
    OpFamily Outcome ι where
  outcome := outcome
  total := ∑ a : Outcome, outcome a

abbrev pointPairOutcomeSwapEquiv (params : Parameters) :
    PointPairOutcome params ≃ PointPairOutcome params :=
  Equiv.prodComm _ _

private lemma lastRestrictionIndex_val_succ
    (params : Parameters) :
    (lastRestrictionIndex params).val + 1 = params.m := by
  have hm := params.hm
  dsimp [lastRestrictionIndex]
  omega

/-- At the final restriction index, a restricted diagonal direction records all
`m` coordinates, so it is equivalent to an unrestricted point of `Point params`. -/
private noncomputable def lastRestrictedDirectionEquiv
    (params : Parameters)
    [FieldModel params.q] :
    (Fin ((lastRestrictionIndex params).val + 1) → Fq params) ≃ Point params where
  toFun := extendRestrictedDirection (lastRestrictionIndex params)
  invFun := fun direction i =>
    direction ⟨i.val, by
      have h := lastRestrictionIndex_val_succ params
      omega⟩
  left_inv := by
    intro free
    funext i
    have hlt : i.val < params.m := by
      have h := lastRestrictionIndex_val_succ params
      omega
    have hle : (⟨i.val, hlt⟩ : Fin params.m).val ≤ (lastRestrictionIndex params).val := by
      dsimp [lastRestrictionIndex]
      omega
    have hidx :
        (⟨i.val, Nat.lt_succ_of_le hle⟩ : Fin ((lastRestrictionIndex params).val + 1)) = i := by
      ext
      rfl
    rw [← hidx]
    simp [extendRestrictedDirection, hle]
  right_inv := by
    intro direction
    funext k
    have hk : k.val ≤ (lastRestrictionIndex params).val := by
      dsimp [lastRestrictionIndex]
      omega
    have hidx :
        (⟨k.val, by
            have h := lastRestrictionIndex_val_succ params
            omega⟩ : Fin params.m) = k := by
      ext
      rfl
    rw [← hidx]
    simp [extendRestrictedDirection, hk]

/-- At the final restriction index, a restricted diagonal sample is exactly a
full diagonal line: the sample point becomes the base point and the restricted
direction determines all line coefficients. -/
private noncomputable def lastRestrictedSampleEquivDiagonalLine
    (params : Parameters)
    [FieldModel params.q] :
    RestrictedDiagonalSample params (lastRestrictionIndex params) ≃ DiagonalLine params where
  toFun := fun s =>
    { base := s.1
      direction := lastRestrictedDirectionEquiv params s.2 }
  invFun := fun ℓ =>
    (ℓ.base, (lastRestrictedDirectionEquiv params).symm ℓ.direction)
  left_inv := by
    rintro ⟨base, free⟩
    refine Prod.ext rfl ?_
    funext i
    have hlt : i.val < params.m := by
      have h := lastRestrictionIndex_val_succ params
      omega
    have hle : (⟨i.val, hlt⟩ : Fin params.m).val ≤ (lastRestrictionIndex params).val := by
      dsimp [lastRestrictionIndex]
      omega
    have hidx :
        (⟨i.val, Nat.lt_succ_of_le hle⟩ : Fin ((lastRestrictionIndex params).val + 1)) = i := by
      ext
      rfl
    rw [← hidx]
    simp [lastRestrictedDirectionEquiv, extendRestrictedDirection, hle]
  right_inv := by
    rintro ⟨base, direction⟩
    change
      ({ base := base,
         direction := extendRestrictedDirection (lastRestrictionIndex params)
           (fun i => direction ⟨i.val, by
             have h := lastRestrictionIndex_val_succ params
             omega⟩) } : DiagonalLine params) =
      ({ base := base, direction := direction } : DiagonalLine params)
    congr
    funext k
    have hk : k.val ≤ (lastRestrictionIndex params).val := by
      dsimp [lastRestrictionIndex]
      omega
    have hidx :
        (⟨k.val, by
            have h := lastRestrictionIndex_val_succ params
            omega⟩ : Fin params.m) = k := by
      ext
      rfl
    rw [← hidx]
    simp [extendRestrictedDirection, hk]

/-- Rebase the last restricted diagonal sample so that its distinguished base
point appears at the queried parameter. This identifies the corrected diagonal
test sample space with the shared point-with-diagonal-line questions used in
the commutativity-at-points argument. -/
private noncomputable def rebasedLastRestrictedQuestionEquiv
    (params : Parameters)
    [FieldModel params.q] :
    (RestrictedDiagonalSample params (lastRestrictionIndex params) × Fq params) ≃
      PointDiagonalLineQuestion params where
  toFun := fun st =>
    let ℓ := lastRestrictedSampleEquivDiagonalLine params st.1
    (DiagonalLine.rebaseAt ℓ (subCoord zeroCoord st.2), st.2)
  invFun := fun q =>
    let ℓ := DiagonalLine.rebaseAt q.1 q.2
    ((lastRestrictedSampleEquivDiagonalLine params).symm ℓ, q.2)
  left_inv := by
    rintro ⟨s, t⟩
    simp [DiagonalLine.rebaseAt_rebase, addCoord_subCoord_left]
  right_inv := by
    rintro ⟨ℓ, t⟩
    simp [DiagonalLine.rebaseAt_rebase, addCoord_subCoord_right]

/-- Evaluate each restricted diagonal measurement at the distinguished base
parameter `zeroCoord`, matching the corrected paper definition of the diagonal
branch. -/
private noncomputable def rawDiagonalLineAnswerFamily
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (j : Fin params.m) :
    IdxSubMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
  fun s =>
    let v := extendRestrictedDirection j s.2
    postprocess
      ((strategy.diagonalMeasurement { base := s.1, direction := v }).toSubMeas)
      (· zeroCoord)

/-- Consistency transfer for the corrected diagonal branch at the final
restriction index.

The corrected test samples a restricted diagonal line and compares the point
measurement at its distinguished base point with the diagonal measurement
postprocessed by evaluation at `zeroCoord`. The global diagonal-line test bound
therefore controls this last restricted slice in particular. -/
private lemma sampledDiagonalLineConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    ConsRel strategy.state
      (uniformDistribution
        (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (diagonalPointAnswerFamily strategy (lastRestrictionIndex params))
      (rawDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params))
      (restrictedDiagonalLinesConsistencyError
        params gamma) := by
  let j := lastRestrictionIndex params
  let err : Fin params.m → Error := fun j =>
    bipartiteConsError strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j))
      (diagonalPointAnswerFamily strategy j)
      (rawDiagonalLineAnswerFamily params strategy j)
  have herr_nonneg : ∀ j : Fin params.m, 0 ≤ err j := by
    intro j'
    exact bipartiteConsError_nonneg strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j'))
      (diagonalPointAnswerFamily strategy j')
      (rawDiagonalLineAnswerFamily params strategy j')
  have hsum_bound : ∑ j' : Fin params.m, err j' ≤ gamma * (params.m : Error) := by
    have hm_nonneg : 0 ≤ (params.m : Error) := by
      positivity
    have hm_ne : (params.m : Error) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt params.hm
    have hdiag := hgood.diagonalLineTest
    dsimp [SymStrat.diagonalFailureProbability, err] at hdiag
    calc
      ∑ j' : Fin params.m, err j'
        = (params.m : Error) * ((1 / (params.m : Error)) * ∑ j' : Fin params.m, err j') := by
            field_simp [hm_ne]
      _ ≤ (params.m : Error) * gamma := by
            exact mul_le_mul_of_nonneg_left hdiag hm_nonneg
      _ = gamma * (params.m : Error) := by ring
  have hj_le : err j ≤ gamma * (params.m : Error) := by
    calc
      err j ≤ ∑ j' : Fin params.m, err j' := by
        exact Finset.single_le_sum (fun j' _ => herr_nonneg j') (Finset.mem_univ j)
      _ ≤ gamma * (params.m : Error) := hsum_bound
  refine ⟨?_⟩
  simpa [j, err, restrictedDiagonalLinesConsistencyError] using hj_le

/-- Convert the corrected restricted diagonal consistency estimate into the
corresponding SDD approximation bound.

This is the final-slice version of the diagonal branch that feeds the
commutativity-at-points argument. It packages the consistency estimate through
`Preliminaries.simeqToApprox`. -/
private lemma sampledDiagonalLineApproximation
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDRel strategy.state
      (uniformDistribution
        (RestrictedDiagonalSample params (lastRestrictionIndex params)))
      (IdxSubMeas.liftLeft
        (diagonalPointAnswerFamily strategy (lastRestrictionIndex params)))
      (IdxSubMeas.liftRight
        (rawDiagonalLineAnswerFamily params strategy (lastRestrictionIndex params)))
      (pointDiagonalLineApproxError params gamma) := by
  let j := lastRestrictionIndex params
  let pointFamily : IdxMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
    fun s => (strategy.pointMeasurement s.1).toMeasurement
  let lineFamily : IdxMeas (RestrictedDiagonalSample params j) (Fq params) ι :=
    fun s =>
      { toSubMeas := rawDiagonalLineAnswerFamily params strategy j s
        total_eq_one := by
          dsimp [rawDiagonalLineAnswerFamily]
          rw [postprocess_total]
          exact
            (strategy.diagonalMeasurement
              { base := s.1
                direction := extendRestrictedDirection j s.2 }).total_eq_one }
  have hcons := sampledDiagonalLineConsistency params strategy eps delta gamma hgood
  have hcons' :
      ConsRel strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (IdxMeas.toIdxSubMeas pointFamily)
        (IdxMeas.toIdxSubMeas lineFamily)
        (restrictedDiagonalLinesConsistencyError params gamma) := by
    simpa [j, pointFamily, lineFamily, diagonalPointAnswerFamily,
      diagonalLineAnswerFamily, IdxMeas.toIdxSubMeas] using hcons
  have happrox :
      Preliminaries.BipartiteSDDRel strategy.state
        (uniformDistribution (RestrictedDiagonalSample params j))
        (IdxMeas.toIdxSubMeas pointFamily)
        (IdxMeas.toIdxSubMeas lineFamily)
        (2 * restrictedDiagonalLinesConsistencyError params gamma) :=
    Preliminaries.simeqToApprox strategy.state
      (uniformDistribution (RestrictedDiagonalSample params j))
      pointFamily lineFamily
      (restrictedDiagonalLinesConsistencyError params gamma) hcons'
  refine ⟨?_⟩
  simpa [j, pointFamily, lineFamily, diagonalPointAnswerFamily,
    pointDiagonalLineApproxError, restrictedDiagonalLinesConsistencyError,
    Preliminaries.BipartiteSDDRel, sddError, IdxMeas.toIdxSubMeas,
    IdxSubMeas.liftLeft, IdxSubMeas.liftRight] using
    happrox.leftRightSquaredDistanceBound

/-- Transport the corrected restricted-diagonal approximation bound to the
shared point-with-diagonal-line distribution used downstream.

The reindexing runs through `rebasedLastRestrictedQuestionEquiv`, which turns a
restricted sample together with an evaluation parameter into the corresponding
rebased diagonal-line question. -/
lemma sampledDiagonalLineApproximation_pointWithDiagonalLine
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDRel strategy.state
      (pointWithDiagonalLineDistribution params)
      (IdxSubMeas.liftLeft
        (sampledPointMeasurement params strategy))
      (IdxSubMeas.liftRight
        (sampledDiagonalLineEvaluation params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  let j := lastRestrictionIndex params
  let e := rebasedLastRestrictedQuestionEquiv params
  rcases sampledDiagonalLineApproximation params strategy eps delta gamma hgood with ⟨hbase⟩
  let f : PointDiagonalLineQuestion params → Error := fun q =>
    qSDD strategy.state
      ((IdxSubMeas.liftLeft (sampledPointMeasurement params strategy)) q)
      ((IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy)) q)
  have hreindex :
      avgOver (pointWithDiagonalLineDistribution params) f =
        avgOver
          (uniformDistribution
            (RestrictedDiagonalSample params j × Fq params))
          (fun st => f (e st)) := by
    symm
    simpa [pointWithDiagonalLineDistribution, f] using
      (avgOver_uniform_equiv e (fun st => f (e st)))
  let g : RestrictedDiagonalSample params j → Error := fun s =>
    qSDD strategy.state
      ((IdxSubMeas.liftLeft (diagonalPointAnswerFamily strategy j)) s)
      ((IdxSubMeas.liftRight (rawDiagonalLineAnswerFamily params strategy j)) s)
  have hignore :
      avgOver
          (uniformDistribution
            (RestrictedDiagonalSample params j × Fq params))
          (fun st => g st.1) =
        avgOver (uniformDistribution (RestrictedDiagonalSample params j)) g := by
    exact avgOver_uniform_fst g
  refine ⟨?_⟩
  calc
    sddError strategy.state
        (pointWithDiagonalLineDistribution params)
        (IdxSubMeas.liftLeft (sampledPointMeasurement params strategy))
        (IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy))
      = avgOver (pointWithDiagonalLineDistribution params) f := by
          rfl
    _ = avgOver
          (uniformDistribution
            (RestrictedDiagonalSample params j × Fq params))
          (fun st => f (e st)) := hreindex
    _ = avgOver
          (uniformDistribution
            (RestrictedDiagonalSample params j × Fq params))
          (fun st =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (diagonalPointAnswerFamily strategy j)) st.1)
              ((IdxSubMeas.liftRight (rawDiagonalLineAnswerFamily params strategy j)) st.1)) := by
            apply avgOver_congr
            rintro ⟨s, t⟩
            let ℓ₀ : DiagonalLine params := lastRestrictedSampleEquivDiagonalLine params s
            have hpoint : sampledPointFromDiagonalQuestion params (e (s, t)) = s.1 := by
              change (DiagonalLine.rebaseAt ℓ₀ (subCoord zeroCoord t)).pointAt t = s.1
              calc
                (DiagonalLine.rebaseAt ℓ₀ (subCoord zeroCoord t)).pointAt t
                  = ℓ₀.pointAt (addCoord (subCoord zeroCoord t) t) := by
                      simpa using DiagonalLine.rebaseAt_pointAt ℓ₀ (subCoord zeroCoord t) t
                _ = ℓ₀.pointAt zeroCoord := by simp
                _ = s.1 := by
                      rcases s with ⟨u, free⟩
                      funext i
                      simp [ℓ₀, lastRestrictedSampleEquivDiagonalLine, DiagonalLine.pointAt,
                        addPoint, smulPoint, zeroCoord, addCoord, mulCoord]
            have hA : ∀ a,
                (((IdxSubMeas.liftLeft
                    (sampledPointMeasurement params strategy)) (e (s, t))).outcome a) =
                  (((IdxSubMeas.liftLeft (diagonalPointAnswerFamily strategy j)) s).outcome a) := by
              intro a
              simp [IdxSubMeas.liftLeft, sampledPointMeasurement, diagonalPointAnswerFamily,
                hpoint]
            have hB : ∀ a,
                (((IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy))
                    (e (s, t))).outcome a) =
                  (((IdxSubMeas.liftRight
                      (rawDiagonalLineAnswerFamily params strategy j)) s).outcome a) := by
              intro a
              have hreparam :=
                (DiagonalCovariantMeasurement.reparamInvariant
                  strategy.diagonalMeasurement)
                  (DiagonalLine.rebaseAt ℓ₀ (subCoord zeroCoord t)) t a
              have hline :
                  ((sampledDiagonalLineEvaluation params strategy) (e (s, t))).outcome a =
                    (rawDiagonalLineAnswerFamily params strategy j s).outcome a := by
                calc
                  ((sampledDiagonalLineEvaluation params strategy) (e (s, t))).outcome a
                    = (postprocess
                        ((strategy.diagonalMeasurement
                          (DiagonalLine.rebaseAt ℓ₀ (subCoord zeroCoord t))).toSubMeas)
                        (fun f => f t)).outcome a := by
                            simp [sampledDiagonalLineEvaluation, e,
                              rebasedLastRestrictedQuestionEquiv, ℓ₀]
                  _ = (postprocess
                        ((strategy.diagonalMeasurement
                          (DiagonalLine.rebaseAt
                            (DiagonalLine.rebaseAt ℓ₀ (subCoord zeroCoord t)) t)).toSubMeas)
                        (fun f => f zeroCoord)).outcome a := by
                            symm
                            exact hreparam
                  _ = (postprocess
                        ((strategy.diagonalMeasurement ℓ₀).toSubMeas)
                        (fun f => f zeroCoord)).outcome a := by
                            simp [DiagonalLine.rebaseAt_rebase, addCoord_subCoord_left]
                  _ = (rawDiagonalLineAnswerFamily params strategy j s).outcome a := by
                            rcases s with ⟨u, free⟩
                            change
                              (postprocess
                                ((strategy.diagonalMeasurement
                                  { base := u,
                                    direction :=
                                      lastRestrictedDirectionEquiv params free
                                  }).toSubMeas)
                                (fun f => f zeroCoord)).outcome a =
                              (postprocess
                                ((strategy.diagonalMeasurement
                                  { base := u,
                                    direction :=
                                      extendRestrictedDirection
                                        (lastRestrictionIndex params) free
                                  }).toSubMeas)
                                (fun f => f zeroCoord)).outcome a
                            simp [lastRestrictedDirectionEquiv]
              simpa [IdxSubMeas.liftRight] using
                congrArg (fun X => rightTensor (ι₁ := ι) X) hline
            unfold f qSDD qSDDCore
            apply Finset.sum_congr rfl
            intro a _
            rw [hA a, hB a]
    _ = avgOver (uniformDistribution (RestrictedDiagonalSample params j))
          g := by
            exact hignore
    _ = sddError strategy.state
          (uniformDistribution (RestrictedDiagonalSample params j))
          (IdxSubMeas.liftLeft (diagonalPointAnswerFamily strategy j))
          (IdxSubMeas.liftRight (rawDiagonalLineAnswerFamily params strategy j)) := by
            rfl
    _ ≤ pointDiagonalLineApproxError params gamma := hbase


end MIPStarRE.LDT.CommutativityPoints
