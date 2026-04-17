import MIPStarRE.LDT.Basic.Parameters
import MIPStarRE.LDT.CommutativityPoints.Defs
import MIPStarRE.LDT.Preliminaries.Theorems

/-!
# Section 10 — Theorems

The main theorem in this file proves commutativity of the point measurements by transporting the
paper's diagonal-line approximation through a sequence of operator-valued bridge families.
The strategy state is bipartite (`QuantumState (ι × ι)`), so all state-dependent distances are
measured against `strategy.state` directly.

## References

- `references/ldt-paper/commutativity-points.tex`
- `blueprint/src/chapter/ch08_commutativity.tex`
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix MatrixOrder ComplexOrder BigOperators

-- pointDiagonalLineQuestionEquiv removed: the diagonal test now uses
-- RestrictedDiagonalSample (indexed by restriction index j) instead
-- of the old DiagonalTestSample.
-- TODO(#306): Rebuild the equivalence for the restricted diagonal test.

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
      avgOver (uniformDistribution β) (fun b => f (e.symm b)) :=
  MIPStarRE.LDT.avgOver_uniform_equiv e f

/-- Swapping the two coordinates reindexes point-pair outcomes. -/
private def pointPairOutcomeSwapEquiv (params : Parameters) :
    PointPairOutcome params ≃ PointPairOutcome params :=
  Equiv.prodComm (Fq params) (Fq params)

/-- Build an operator family from its outcomes, taking the total to be their sum. -/
private noncomputable def opFamilyOfOutcome {Outcome : Type*} [Fintype Outcome]
    (outcome : Outcome → MIPStarRE.Quantum.Op ι) :
    OpFamily Outcome ι where
  outcome := outcome
  total := ∑ a : Outcome, outcome a

private lemma avgOver_uniform_prod_fst
    {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    (f : α → Error) :
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.1) =
      avgOver (uniformDistribution α) f := by
  have hα : ((Fintype.card α : ℕ) : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hβ : ((Fintype.card β : ℕ) : Error) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  calc
    avgOver (uniformDistribution (α × β)) (fun ab => f ab.1)
      = (1 / (Fintype.card (α × β) : Error)) * ∑ ab : α × β, f ab.1 := by
          simp [avgOver, uniformDistribution, Finset.mul_sum]
    _ = (1 / ((Fintype.card α : Error) * (Fintype.card β : Error))) *
          ∑ a : α, ∑ b : β, f a := by
          rw [Fintype.card_prod]
          simpa using
            (Fintype.sum_prod_type' (f := fun (a : α) (_b : β) => f a))
    _ = (1 / ((Fintype.card α : Error) * (Fintype.card β : Error))) *
          ((Fintype.card β : Error) * ∑ a : α, f a) := by
          congr 1
          simp [Finset.mul_sum]
    _ = (1 / (Fintype.card α : Error)) * ∑ a : α, f a := by
          field_simp [hα, hβ]
    _ = avgOver (uniformDistribution α) f := by
          simp [avgOver, uniformDistribution, Finset.mul_sum]

private lemma lastRestrictionIndex_val_succ
    (params : Parameters) :
    (lastRestrictionIndex params).val + 1 = params.m := by
  have hm := params.hm
  dsimp [lastRestrictionIndex]
  omega

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
    simpa [extendRestrictedDirection, hle] using congrArg free hidx
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
    simpa [extendRestrictedDirection, hk] using congrArg direction hidx

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
    simpa [lastRestrictedDirectionEquiv, extendRestrictedDirection, hle] using congrArg free hidx
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
    simpa [lastRestrictedDirectionEquiv, extendRestrictedDirection, hk] using
      congrArg direction hidx

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

/-- TODO(#306): Consistency transfer for the corrected restricted diagonal test.

This proof gap is intentional tracking for the diagonal-test definition fix:
the old proof used `DiagonalTestSample` with unrestricted directions, while the
corrected statement uses `RestrictedDiagonalSample` with restricted directions
and base-point evaluation. The previous proof therefore established the wrong
sample space for the paper-corrected test. -/
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

/-- TODO(#306): SDD approximation transfer for the corrected restricted diagonal test.

This proof gap is intentional tracking for the diagonal-test definition fix:
the old proof used `DiagonalTestSample` with unrestricted directions, while the
corrected statement uses `RestrictedDiagonalSample` with restricted directions
and base-point evaluation. The previous proof therefore established the wrong
sample space for the paper-corrected test. -/
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

/-- TODO(#306): Transport the corrected restricted diagonal approximation to
the shared line-plus-parameter distribution used by the commutativity proof. -/
private lemma sampledDiagonalLineApproximation_pointWithDiagonalLine
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
    exact avgOver_uniform_prod_fst g
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
                  (((IdxSubMeas.liftRight (rawDiagonalLineAnswerFamily params strategy j)) s).outcome a) := by
              intro a
              have hreparam :=
                strategy.diagonalReparamInvariant
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
                            simpa [lastRestrictedDirectionEquiv]
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

private lemma qSDDOp_symm
    {Outcome : Type*}
    (ψ : QuantumState ι) [Fintype Outcome]
    (A B : OpFamily Outcome ι) :
    qSDDOp ψ A B = qSDDOp ψ B A := by
  let F : Outcome → MIPStarRE.Quantum.Op ι := fun a => A.outcome a - B.outcome a
  let G : Outcome → MIPStarRE.Quantum.Op ι := fun a => B.outcome a - A.outcome a
  have hFG : F = fun a => -G a := by
    funext a
    dsimp [F, G]
    abel
  unfold qSDDOp qSDDCore
  change ∑ a : Outcome, ev ψ ((F a)ᴴ * F a) = ∑ a : Outcome, ev ψ ((G a)ᴴ * G a)
  rw [hFG]
  refine Finset.sum_congr rfl ?_
  intro a _
  change ev ψ ((-G a)ᴴ * (-G a)) = ev ψ ((G a)ᴴ * G a)
  simp

private lemma sddOpRel_symm
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ : Error) :
    SDDOpRel ψ 𝒟 A B δ →
      SDDOpRel ψ 𝒟 B A δ := by
  intro ⟨h⟩
  constructor
  simpa [sddErrorOp, qSDDOp_symm] using h

private lemma qSDDOp_reindex
    {Outcome Outcome' : Type*}
    [Fintype Outcome] [Fintype Outcome']
    (e : Outcome ≃ Outcome')
    (ψ : QuantumState ι)
    (A B : OpFamily Outcome ι) :
    qSDDOp ψ A B =
      qSDDOp ψ
        ({ outcome := fun a' => A.outcome (e.symm a')
           total := A.total } : OpFamily Outcome' ι)
        ({ outcome := fun a' => B.outcome (e.symm a')
           total := B.total } : OpFamily Outcome' ι) := by
  unfold qSDDOp qSDDCore
  calc
    ∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))
      = ∑ a' : Outcome',
          ev ψ
            ((A.outcome (e.symm a') - B.outcome (e.symm a'))ᴴ *
              (A.outcome (e.symm a') - B.outcome (e.symm a'))) := by
          exact Fintype.sum_equiv e
            (fun a =>
              ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a)))
            (fun a' =>
              ev ψ
                ((A.outcome (e.symm a') - B.outcome (e.symm a'))ᴴ *
                  (A.outcome (e.symm a') - B.outcome (e.symm a'))))
            (by
              intro a
              simp)
    _ = qSDDOp ψ
          ({ outcome := fun a' => A.outcome (e.symm a')
             total := A.total } : OpFamily Outcome' ι)
          ({ outcome := fun a' => B.outcome (e.symm a')
             total := B.total } : OpFamily Outcome' ι) := by
          rfl

private lemma sddOpRel_reindex
    {Question Outcome Outcome' : Type*}
    [Fintype Outcome] [Fintype Outcome']
    (e : Outcome ≃ Outcome')
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ : Error) :
    SDDOpRel ψ 𝒟 A B δ →
      SDDOpRel ψ 𝒟
        (fun q =>
          ({ outcome := fun a' => (A q).outcome (e.symm a')
             total := (A q).total } : OpFamily Outcome' ι))
        (fun q =>
          ({ outcome := fun a' => (B q).outcome (e.symm a')
             total := (B q).total } : OpFamily Outcome' ι))
        δ := by
  intro ⟨h⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver 𝒟
        (fun q =>
          qSDDOp ψ
            ({ outcome := fun a' => (A q).outcome (e.symm a')
               total := (A q).total } : OpFamily Outcome' ι)
            ({ outcome := fun a' => (B q).outcome (e.symm a')
               total := (B q).total } : OpFamily Outcome' ι))
      = avgOver 𝒟 (fun q => qSDDOp ψ (A q) (B q)) := by
          apply avgOver_congr
          intro q
          rw [qSDDOp_reindex e ψ (A q) (B q)]
    _ ≤ δ := h

private lemma sddOpRel_congr_outcome
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B A' B' : IdxOpFamily Question Outcome ι) (δ : Error)
    (hA : ∀ q a, (A q).outcome a = (A' q).outcome a)
    (hB : ∀ q a, (B q).outcome a = (B' q).outcome a) :
    SDDOpRel ψ 𝒟 A B δ →
      SDDOpRel ψ 𝒟 A' B' δ := by
  intro ⟨h⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver 𝒟 (fun q => qSDDOp ψ (A' q) (B' q))
      = avgOver 𝒟 (fun q => qSDDOp ψ (A q) (B q)) := by
          apply avgOver_congr
          intro q
          unfold qSDDOp qSDDCore
          apply Finset.sum_congr rfl
          intro a _
          rw [hA q a, hB q a]
    _ ≤ δ := h

private lemma subMeas_sum_adjoint_mul_le_one
    {Outcome : Type*}
    [Fintype Outcome]
    (A : SubMeas Outcome ι) :
    ∑ a : Outcome, (A.outcome a)ᴴ * A.outcome a ≤ 1 := by
  calc
    ∑ a : Outcome, (A.outcome a)ᴴ * A.outcome a
      = ∑ a : Outcome, A.outcome a * A.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [SubMeas.outcome_hermitian]
    _ ≤ ∑ a : Outcome, A.outcome a := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact MIPStarRE.Quantum.sq_le_self (A.outcome_pos a) (A.outcome_le_one a)
    _ = A.total := A.sum_eq_total
    _ ≤ 1 := A.total_le_one

private lemma liftLeft_mul_leftPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftLeft).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b =
      leftTensor (A.outcome a * B.outcome b) := by
  simp [SubMeas.liftLeft, OpFamily.leftPlacedOpFamily, SubMeas.toOpFamily,
    leftTensor_mul_leftTensor]

private lemma liftLeft_mul_rightPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftLeft).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b =
      opTensor (A.outcome a) (B.outcome b) := by
  simp [SubMeas.liftLeft, OpFamily.rightPlacedOpFamily, SubMeas.toOpFamily,
    leftTensor_mul_rightTensor_eq_opTensor]

private lemma liftRight_mul_leftPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftRight).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b =
      opTensor (B.outcome b) (A.outcome a) := by
  simp [SubMeas.liftRight, OpFamily.leftPlacedOpFamily, SubMeas.toOpFamily,
    rightTensor_mul_leftTensor_eq_opTensor]

private lemma liftRight_mul_rightPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftRight).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b =
      rightTensor (A.outcome a * B.outcome b) := by
  simp [SubMeas.liftRight, OpFamily.rightPlacedOpFamily, SubMeas.toOpFamily,
    rightTensor_mul_rightTensor]

private theorem sharedDiagonalLineQuestionOfPointPair_sampledPointPair
    (params : Parameters)
    [FieldModel params.q]
    (s : PointPairQuestion params × Fq params) :
    sampledPointPairFromSharedDiagonalQuestion params
      (sharedDiagonalLineQuestionOfPointPair params s) = s.1 := by
  rcases s with ⟨⟨u, v⟩, t⟩
  refine Prod.ext ?_ ?_
  · funext i
    simp [sampledPointPairFromSharedDiagonalQuestion, sharedDiagonalLineQuestionOfPointPair,
      DiagonalLine.pointAt, addPoint, smulPoint, addCoord, subCoord, mulCoord]
  · funext i
    simp [sampledPointPairFromSharedDiagonalQuestion, sharedDiagonalLineQuestionOfPointPair,
      DiagonalLine.pointAt, addPoint, smulPoint, addCoord, subCoord, mulCoord]
    rw [← encode_decodeScalar (v i)]
    congr 1
    ring_nf
    simpa using (decode_encodeScalar (params := params) (decodeScalar (v i)))

private theorem sharedDiagonalLineQuestionOfPointPair_of_line
    (params : Parameters)
    [FieldModel params.q]
    (ℓ : DiagonalLine params)
    (t : Fq params) :
    sharedDiagonalLineQuestionOfPointPair params
      (((ℓ.pointAt t, ℓ.pointAt (addCoord t (encodeScalar 1))), t)) =
      (ℓ, (t, addCoord t (encodeScalar 1))) := by
  cases ℓ with
  | mk base direction =>
      change
        (({ base := fun i => _, direction := fun i => _ } : DiagonalLine params),
          (t, addCoord t (encodeScalar 1))) =
        ({ base := base, direction := direction }, (t, addCoord t (encodeScalar 1)))
      congr
      · funext i
        simp [DiagonalLine.pointAt, addPoint, smulPoint, addCoord, subCoord, mulCoord]
        rw [← encode_decodeScalar (base i)]
        congr 1
        ring_nf
        simpa using (decode_encodeScalar (params := params) (decodeScalar (base i)))
      · funext i
        simp [DiagonalLine.pointAt, addPoint, smulPoint, addCoord, subCoord, mulCoord]
        rw [← encode_decodeScalar (direction i)]
        congr 1
        ring_nf
        simpa using (decode_encodeScalar (params := params) (decodeScalar (direction i)))

private theorem sharedDiagonalLineQuestionOfPointPair_injective
    (params : Parameters)
    [FieldModel params.q] :
    Function.Injective (sharedDiagonalLineQuestionOfPointPair params) := by
  intro s₁ s₂ hs
  have hs' := congrArg
    (fun q => (sampledPointPairFromSharedDiagonalQuestion params q, q.2.1)) hs
  rcases Prod.mk.inj (by
    simpa [sharedDiagonalLineQuestionOfPointPair_sampledPointPair] using hs') with ⟨hpair, ht⟩
  exact Prod.ext hpair ht

private lemma avgOver_pointPairSharedDiagonalLine_eq_uniform_seed
    (params : Parameters)
    [FieldModel params.q]
    (f : PointPairDiagonalLineQuestion params → Error) :
    avgOver (pointPairSharedDiagonalLineDistribution params) f =
      avgOver (uniformDistribution (PointPairQuestion params × Fq params))
        (fun s => f (sharedDiagonalLineQuestionOfPointPair params s)) := by
  let e : PointPairQuestion params × Fq params → PointPairDiagonalLineQuestion params :=
    sharedDiagonalLineQuestionOfPointPair params
  have hinj : Function.Injective e := sharedDiagonalLineQuestionOfPointPair_injective params
  unfold avgOver pointPairSharedDiagonalLineDistribution uniformDistribution
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro s _
    have hs : e s ∈ Finset.univ.image e := by
      exact Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩
    simp [e, hs]
  · intro s₁ _ s₂ _ hs
    exact hinj hs

private noncomputable def pointPairSharedDiagonalLine_ignore_first_equiv
    (params : Parameters)
    [FieldModel params.q] :
    (PointPairQuestion params × Fq params) ≃ PointDiagonalLineQuestion params where
  toFun := fun s =>
    let q := sharedDiagonalLineQuestionOfPointPair params s
    (q.1, q.2.2)
  invFun := fun r =>
    let ℓ := r.1
    let tv := r.2
    (((ℓ.pointAt (subCoord tv (encodeScalar 1)), ℓ.pointAt tv)),
      subCoord tv (encodeScalar 1))
  left_inv := by
    rintro ⟨⟨u, v⟩, t⟩
    refine Prod.ext ?_ ?_
    · simpa [Prod.ext_iff, sharedDiagonalLineQuestionOfPointPair, addCoord, subCoord] using
        sharedDiagonalLineQuestionOfPointPair_sampledPointPair params ((u, v), t)
    · simp [sharedDiagonalLineQuestionOfPointPair, addCoord, subCoord]
  right_inv := by
    rintro ⟨ℓ, tv⟩
    simpa [addCoord, subCoord] using
      congrArg (fun q => (q.1, q.2.2))
        (sharedDiagonalLineQuestionOfPointPair_of_line params ℓ
          (subCoord tv (encodeScalar 1)))

private noncomputable def pointPairSharedDiagonalLine_ignore_second_equiv
    (params : Parameters)
    [FieldModel params.q] :
    (PointPairQuestion params × Fq params) ≃ PointDiagonalLineQuestion params where
  toFun := fun s =>
    let q := sharedDiagonalLineQuestionOfPointPair params s
    (q.1, q.2.1)
  invFun := fun r =>
    let ℓ := r.1
    let t := r.2
    (((ℓ.pointAt t, ℓ.pointAt (addCoord t (encodeScalar 1))), t))
  left_inv := by
    rintro ⟨⟨u, v⟩, t⟩
    refine Prod.ext ?_ ?_
    · simpa [Prod.ext_iff, sharedDiagonalLineQuestionOfPointPair] using
        sharedDiagonalLineQuestionOfPointPair_sampledPointPair params ((u, v), t)
    · simp [sharedDiagonalLineQuestionOfPointPair]
  right_inv := by
    rintro ⟨ℓ, t⟩
    simpa using
      congrArg (fun q => (q.1, q.2.1))
        (sharedDiagonalLineQuestionOfPointPair_of_line params ℓ t)

private lemma avgOver_pointPairSharedDiagonalLine_ignore_first
    (params : Parameters)
    [FieldModel params.q]
    (f : PointDiagonalLineQuestion params → Error) :
    avgOver (pointPairSharedDiagonalLineDistribution params)
      (fun q => f (q.1, q.2.2)) =
      avgOver (pointWithDiagonalLineDistribution params) f := by
  calc
    avgOver (pointPairSharedDiagonalLineDistribution params)
        (fun q => f (q.1, q.2.2))
      = avgOver (uniformDistribution (PointPairQuestion params × Fq params))
          (fun s => f ((pointPairSharedDiagonalLine_ignore_first_equiv params) s)) := by
            simpa [pointPairSharedDiagonalLine_ignore_first_equiv] using
              avgOver_pointPairSharedDiagonalLine_eq_uniform_seed params
                (fun q => f (q.1, q.2.2))
    _ = avgOver (uniformDistribution (PointDiagonalLineQuestion params)) f := by
          simpa using
            (avgOver_uniform_equiv (pointPairSharedDiagonalLine_ignore_first_equiv params)
              (fun s => f ((pointPairSharedDiagonalLine_ignore_first_equiv params) s)))
    _ = avgOver (pointWithDiagonalLineDistribution params) f := by
          simp [pointWithDiagonalLineDistribution]

private lemma avgOver_pointPairSharedDiagonalLine_ignore_second
    (params : Parameters)
    [FieldModel params.q]
    (f : PointDiagonalLineQuestion params → Error) :
    avgOver (pointPairSharedDiagonalLineDistribution params)
      (fun q => f (q.1, q.2.1)) =
      avgOver (pointWithDiagonalLineDistribution params) f := by
  calc
    avgOver (pointPairSharedDiagonalLineDistribution params)
        (fun q => f (q.1, q.2.1))
      = avgOver (uniformDistribution (PointPairQuestion params × Fq params))
          (fun s => f ((pointPairSharedDiagonalLine_ignore_second_equiv params) s)) := by
            simpa [pointPairSharedDiagonalLine_ignore_second_equiv] using
              avgOver_pointPairSharedDiagonalLine_eq_uniform_seed params
                (fun q => f (q.1, q.2.1))
    _ = avgOver (uniformDistribution (PointDiagonalLineQuestion params)) f := by
          simpa using
            (avgOver_uniform_equiv (pointPairSharedDiagonalLine_ignore_second_equiv params)
              (fun s => f ((pointPairSharedDiagonalLine_ignore_second_equiv params) s)))
    _ = avgOver (pointWithDiagonalLineDistribution params) f := by
          simp [pointWithDiagonalLineDistribution]

private lemma avgOver_pointPairSharedDiagonalLine_sampled_pair
    (params : Parameters)
    [FieldModel params.q]
    (f : PointPairQuestion params → Error) :
    avgOver (pointPairSharedDiagonalLineDistribution params)
      (fun q => f (sampledPointPairFromSharedDiagonalQuestion params q)) =
      avgOver (uniformDistribution (PointPairQuestion params)) f := by
  calc
    avgOver (pointPairSharedDiagonalLineDistribution params)
        (fun q => f (sampledPointPairFromSharedDiagonalQuestion params q))
      = avgOver (uniformDistribution (PointPairQuestion params × Fq params))
          (fun s => f s.1) := by
            simpa [sharedDiagonalLineQuestionOfPointPair_sampledPointPair] using
              avgOver_pointPairSharedDiagonalLine_eq_uniform_seed params
                (fun q => f (sampledPointPairFromSharedDiagonalQuestion params q))
    _ = avgOver (uniformDistribution (PointPairQuestion params)) f := by
          exact avgOver_uniform_prod_fst f

private lemma pointMeasurementProductAlongSharedLine_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (pointMeasurementProductAlongSharedLine params strategy q).outcome (a, b) =
      leftTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a *
          (strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b) := by
  simp [pointMeasurementProductAlongSharedLine, pointMeasurementProductLeft,
    orderedProductOpFamily, sampledPointPairFromSharedDiagonalQuestion,
    OpFamily.leftPlacedOpFamily]

private lemma pointMeasurementProductAlongSharedLineReversed_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (pointMeasurementProductAlongSharedLineReversed params strategy q).outcome (a, b) =
      leftTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b *
          (strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a) := by
  simp [pointMeasurementProductAlongSharedLineReversed, pointMeasurementProductRight,
    reversedProductOpFamily, sampledPointPairFromSharedDiagonalQuestion,
    OpFamily.leftPlacedOpFamily]

private lemma pointDiagonalLineMixedProductLeft_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    ((IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy) q).outcome
      (a, b)) =
      opTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
  simp [pointDiagonalLineMixedProductLeft, tensorProductSubMeas,
    sampledDiagonalLineEvaluation, IdxSubMeas.toIdxOpFamily, SubMeas.toOpFamily,
    leftTensor_mul_rightTensor_eq_opTensor]

private lemma pointDiagonalLineMixedProductRight_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    ((IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy) q).outcome
      (a, b)) =
      opTensor
        ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
  classical
  simp [pointDiagonalLineMixedProductRight, tensorProductSubMeas, sampledDiagonalLineEvaluation,
    postprocess, Prod.swap, IdxSubMeas.toIdxOpFamily, SubMeas.toOpFamily,
    leftTensor_mul_rightTensor_eq_opTensor]
  have hfilter :
      (Finset.univ.filter (fun ab : Fq params × Fq params => ab.2 = a ∧ ab.1 = b)) =
        {(b, a)} := by
    ext ab
    rcases ab with ⟨a', b'⟩
    simp [and_comm]
  rw [hfilter]
  simp

private lemma diagonalLineProductOrdered_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (diagonalLineProductOrdered params strategy q).outcome (a, b) =
      rightTensor
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b *
          (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
  simp [diagonalLineProductOrdered, sampledDiagonalLineEvaluation,
    OpFamily.rightPlacedOpFamily, reversedProductOpFamily]

private lemma diagonalLineProductReversed_outcome
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (q : PointPairDiagonalLineQuestion params)
    (a b : Fq params) :
    (diagonalLineProductReversed params strategy q).outcome (a, b) =
      rightTensor
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a *
          (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
  simp [diagonalLineProductReversed, sampledDiagonalLineEvaluation,
    OpFamily.rightPlacedOpFamily, orderedProductOpFamily]

private lemma sampledDiagonalLineApproximation_ignore_first
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (pointDiagonalLineApproxError params gamma) := by
  rcases sampledDiagonalLineApproximation_pointWithDiagonalLine
    params strategy eps delta gamma hgood with ⟨happrox⟩
  constructor
  calc
    sddErrorOp strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (fun q =>
          OpFamily.leftPlacedOpFamily (ιB := ι)
            ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
        (fun q =>
          OpFamily.rightPlacedOpFamily (ιA := ι)
            (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      = avgOver (pointPairSharedDiagonalLineDistribution params)
          (fun q =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (sampledPointMeasurement params strategy)) (q.1, q.2.2))
              ((IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy))
                (q.1, q.2.2))) := by
            unfold sddErrorOp
            apply avgOver_congr
            intro q
            simp [qSDDOp, qSDD, qSDDCore, IdxSubMeas.liftLeft, IdxSubMeas.liftRight,
              OpFamily.leftPlacedOpFamily, OpFamily.rightPlacedOpFamily, sampledPointMeasurement,
              sampledPointFromDiagonalQuestion, SubMeas.liftLeft, SubMeas.liftRight,
              SubMeas.toOpFamily]
    _ = avgOver (pointWithDiagonalLineDistribution params)
          (fun q =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (sampledPointMeasurement params strategy)) q)
              ((IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy)) q)) := by
            exact avgOver_pointPairSharedDiagonalLine_ignore_first params
              (fun q =>
                qSDD strategy.state
                  ((IdxSubMeas.liftLeft (sampledPointMeasurement params strategy)) q)
                  ((IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy)) q))
    _ = sddError strategy.state
          (pointWithDiagonalLineDistribution params)
          (IdxSubMeas.liftLeft (sampledPointMeasurement params strategy))
          (IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy)) := by
            rfl
    _ ≤ pointDiagonalLineApproxError params gamma := happrox

private lemma sampledDiagonalLineApproximation_ignore_second
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (pointDiagonalLineApproxError params gamma) := by
  rcases sampledDiagonalLineApproximation_pointWithDiagonalLine
    params strategy eps delta gamma hgood with ⟨happrox⟩
  constructor
  calc
    sddErrorOp strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (fun q =>
          OpFamily.leftPlacedOpFamily (ιB := ι)
            ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
        (fun q =>
          OpFamily.rightPlacedOpFamily (ιA := ι)
            (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      = avgOver (pointPairSharedDiagonalLineDistribution params)
          (fun q =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (sampledPointMeasurement params strategy)) (q.1, q.2.1))
              ((IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy))
                (q.1, q.2.1))) := by
            unfold sddErrorOp
            apply avgOver_congr
            intro q
            simp [qSDDOp, qSDD, qSDDCore, IdxSubMeas.liftLeft, IdxSubMeas.liftRight,
              OpFamily.leftPlacedOpFamily, OpFamily.rightPlacedOpFamily, sampledPointMeasurement,
              sampledPointFromDiagonalQuestion, SubMeas.liftLeft, SubMeas.liftRight,
              SubMeas.toOpFamily]
    _ = avgOver (pointWithDiagonalLineDistribution params)
          (fun q =>
            qSDD strategy.state
              ((IdxSubMeas.liftLeft (sampledPointMeasurement params strategy)) q)
              ((IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy)) q)) := by
            exact avgOver_pointPairSharedDiagonalLine_ignore_second params
              (fun q =>
                qSDD strategy.state
                  ((IdxSubMeas.liftLeft (sampledPointMeasurement params strategy)) q)
                  ((IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy)) q))
    _ = sddError strategy.state
          (pointWithDiagonalLineDistribution params)
          (IdxSubMeas.liftLeft (sampledPointMeasurement params strategy))
          (IdxSubMeas.liftRight (sampledDiagonalLineEvaluation params strategy)) := by
            rfl
    _ ≤ pointDiagonalLineApproxError params gamma := happrox

private lemma orderedLiftToMixedBridge
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  /-
  First replacement step in the paper:
  `(A^u_a A^v_b) ⊗ I ≈ A^u_a ⊗ L^ℓ_[f(v)=b]`.
  -/
  let e : PointPairOutcome params ≃ PointPairOutcome params :=
    pointPairOutcomeSwapEquiv params
  let Araw : IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Au.liftLeft).outcome ab.2 *
          (OpFamily.leftPlacedOpFamily (ιB := ι) Av).outcome ab.1
  let Braw : IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Lv := sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Au.liftLeft).outcome ab.2 *
          (OpFamily.rightPlacedOpFamily (ιA := ι) Lv.toOpFamily).outcome ab.1
  let hbase :=
    sampledDiagonalLineApproximation_ignore_first params strategy eps delta gamma hgood
  let hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (fun q _b a =>
        (((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas).liftLeft).outcome a)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q b
        exact subMeas_sum_adjoint_mul_le_one
          (((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas).liftLeft))
  have hreindexed :=
    sddOpRel_reindex e strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      Araw
      Braw
      (pointDiagonalLineApproxError params gamma)
      hcab
  let Astep :
      IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : PointPairOutcome params => (Araw q).outcome (e.symm ab)
         total := (Araw q).total } : OpFamily (PointPairOutcome params) (ι × ι))
  let Bstep :
      IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : PointPairOutcome params => (Braw q).outcome (e.symm ab)
         total := (Braw q).total } : OpFamily (PointPairOutcome params) (ι × ι))
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (pointMeasurementProductAlongSharedLine params strategy)
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = leftTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a *
                (strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b) := by
                  simpa [Astep, Araw, e] using
                    liftLeft_mul_leftPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      a b
        _ = (pointMeasurementProductAlongSharedLine params strategy q).outcome (a, b) := by
              symm
              exact pointMeasurementProductAlongSharedLine_outcome params strategy q a b)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
                  simpa [Bstep, Braw, e] using
                    liftLeft_mul_rightPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      a b
        _ =
              ((IdxSubMeas.toIdxOpFamily
                (pointDiagonalLineMixedProductLeft params strategy) q).outcome
                (a, b)) := by
              symm
              exact pointDiagonalLineMixedProductLeft_outcome params strategy q a b)
    hreindexed

private lemma orderedLiftToLineBridge
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
      (diagonalLineProductOrdered params strategy)
      (pointDiagonalLineApproxError params gamma) := by
  /-
  Second replacement step:
  `A^u_a ⊗ L^ℓ_[f(v)=b] ≈ I ⊗ (L^ℓ_[f(v)=b] L^ℓ_[f(u)=a])`.
  -/
  let Araw : IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      let Au := strategy.pointMeasurement (q.1.pointAt q.2.1)
      let Lv := postprocess (strategy.diagonalMeasurement q.1).toSubMeas fun f => f q.2.2
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        opTensor (Au.outcome ab.1) (Lv.outcome ab.2)
  let Braw : IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      let Lu := postprocess (strategy.diagonalMeasurement q.1).toSubMeas fun f => f q.2.1
      let Lv := postprocess (strategy.diagonalMeasurement q.1).toSubMeas fun f => f q.2.2
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        rightTensor (Lv.outcome ab.2 * Lu.outcome ab.1)
  let hbase :=
    sampledDiagonalLineApproximation_ignore_second params strategy eps delta gamma hgood
  have hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (fun q _a b =>
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).liftRight).outcome b)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q a
        exact subMeas_sum_adjoint_mul_le_one
          ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).liftRight))
  let Astep :
      IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Lv := sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Lv.liftRight).outcome ab.2 *
          (OpFamily.leftPlacedOpFamily (ιB := ι) Au).outcome ab.1
  let Bstep :
      IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      let Lu := sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      let Lv := sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Lv.liftRight).outcome ab.2 *
          (OpFamily.rightPlacedOpFamily (ιA := ι) Lu.toOpFamily).outcome ab.1
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
    (diagonalLineProductOrdered params strategy)
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a)
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
                  simpa [Astep] using
                    liftRight_mul_leftPlaced_outcome
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      b a
        _ =
              ((IdxSubMeas.toIdxOpFamily
                (pointDiagonalLineMixedProductLeft params strategy) q).outcome
                (a, b)) := by
              symm
              exact pointDiagonalLineMixedProductLeft_outcome params strategy q a b)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = rightTensor
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b *
                (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
                  simpa [Bstep] using
                    liftRight_mul_rightPlaced_outcome
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      b a
        _ = (diagonalLineProductOrdered params strategy q).outcome (a, b) := by
              symm
              exact diagonalLineProductOrdered_outcome params strategy q a b)
    hcab

private lemma diagonalLineProduct_outcome_swap
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    ∀ q ab,
      (diagonalLineProductOrdered params strategy q).outcome ab =
        (diagonalLineProductReversed params strategy q).outcome ab := by
  intro q ⟨a, b⟩
  simp only [diagonalLineProductOrdered,
    diagonalLineProductReversed,
    OpFamily.rightPlacedOpFamily,
    reversedProductOpFamily,
    orderedProductOpFamily,
    sampledDiagonalLineEvaluation]
  congr 1
  exact (strategy.diagonalMeasurement
    q.1).postprocess_outcome_commute
    (fun f => f q.2.2)
    (fun f => f q.2.1) b a

set_option maxHeartbeats 1000000 in
-- Reindexing and outcome-congruence for this bridge create a large elaboration problem.
private lemma reversedDropFromLineBridge
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductReversed params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  /-
  Third replacement step:
  `I ⊗ (L^ℓ_[f(u)=a] L^ℓ_[f(v)=b]) ≈ A^v_b ⊗ L^ℓ_[f(u)=a]`.
  -/
  let e : PointPairOutcome params ≃ PointPairOutcome params :=
    pointPairOutcomeSwapEquiv params
  let Araw : IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      let Lu := sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      let Lv := sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Lu.liftRight).outcome ab.2 *
          (OpFamily.rightPlacedOpFamily (ιA := ι) Lv.toOpFamily).outcome ab.1
  let Braw : IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      let Lu := sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Lu.liftRight).outcome ab.2 *
          (OpFamily.leftPlacedOpFamily (ιB := ι) Av).outcome ab.1
  let hbase :=
    sddOpRel_symm strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (pointDiagonalLineApproxError params gamma)
      (sampledDiagonalLineApproximation_ignore_first params strategy eps delta gamma hgood)
  let hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily
            (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))))
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas))
      (fun q _b a =>
        ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).liftRight).outcome a)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q b
        exact subMeas_sum_adjoint_mul_le_one
          ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).liftRight))
  have hreindexed :=
    sddOpRel_reindex e strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      Araw
      Braw
      (pointDiagonalLineApproxError params gamma)
      hcab
  let Astep :
      IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : PointPairOutcome params => (Araw q).outcome (e.symm ab)
         total := (Araw q).total } : OpFamily (PointPairOutcome params) (ι × ι))
  let Bstep :
      IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      ({ outcome := fun ab : PointPairOutcome params => (Braw q).outcome (e.symm ab)
         total := (Braw q).total } : OpFamily (PointPairOutcome params) (ι × ι))
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (diagonalLineProductReversed params strategy)
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = rightTensor
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a *
                (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2)).outcome b) := by
                  simpa [Astep, Araw, e] using
                    liftRight_mul_rightPlaced_outcome
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.2))
                      a b
        _ = (diagonalLineProductReversed params strategy q).outcome (a, b) := by
              symm
              exact diagonalLineProductReversed_outcome params strategy q a b)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
                  simpa [Bstep, Braw, e] using
                    liftRight_mul_leftPlaced_outcome
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      a b
        _ =
              ((IdxSubMeas.toIdxOpFamily
                (pointDiagonalLineMixedProductRight params strategy) q).outcome
                (a, b)) := by
              symm
              exact pointDiagonalLineMixedProductRight_outcome params strategy q a b)
    hreindexed

private lemma orderedDropFromLineBridge
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductOrdered params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointDiagonalLineApproxError params gamma) := by
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    (diagonalLineProductReversed params strategy)
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (diagonalLineProductOrdered params strategy)
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      symm
      exact diagonalLineProduct_outcome_swap params strategy q ab)
    (by intro q ab; rfl)
    (reversedDropFromLineBridge params strategy eps delta gamma hgood)

private lemma reversedDropToPointsBridge
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      (pointDiagonalLineApproxError params gamma) := by
  /-
  Final replacement step:
  `A^v_b ⊗ L^ℓ_[f(u)=a] ≈ (A^v_b A^u_a) ⊗ I`.
  -/
  let Astep :
      IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      let Lu := sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Av.liftLeft).outcome ab.2 *
          (OpFamily.rightPlacedOpFamily (ιA := ι) Lu.toOpFamily).outcome ab.1
  let Bstep :
      IdxOpFamily (PointPairDiagonalLineQuestion params) (PointPairOutcome params) (ι × ι) :=
    fun q =>
      let Au := (strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas
      let Av := (strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas
      opFamilyOfOutcome fun ab : PointPairOutcome params =>
        (Av.liftLeft).outcome ab.2 *
          (OpFamily.leftPlacedOpFamily (ιB := ι) Au).outcome ab.1
  let hbase :=
    sddOpRel_symm strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (pointDiagonalLineApproxError params gamma)
      (sampledDiagonalLineApproximation_ignore_second params strategy eps delta gamma hgood)
  have hcab :=
    MIPStarRE.LDT.Preliminaries.cabApproxDelta_raw
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (fun q =>
        OpFamily.rightPlacedOpFamily (ιA := ι)
          (SubMeas.toOpFamily (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))))
      (fun q =>
        OpFamily.leftPlacedOpFamily (ιB := ι)
          ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas))
      (fun q _a b =>
        (((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas).liftLeft).outcome b)
      (pointDiagonalLineApproxError params gamma)
      hbase
      (by
        intro q a
        exact subMeas_sum_adjoint_mul_le_one
          (((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas).liftLeft))
  exact sddOpRel_congr_outcome strategy.state
    (pointPairSharedDiagonalLineDistribution params)
    Astep Bstep
    (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
    (pointMeasurementProductAlongSharedLineReversed params strategy)
    (pointDiagonalLineApproxError params gamma)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Astep q).outcome (a, b)
          = opTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b)
              ((sampledDiagonalLineEvaluation params strategy (q.1, q.2.1)).outcome a) := by
                  simpa [Astep] using
                    liftLeft_mul_rightPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      (sampledDiagonalLineEvaluation params strategy (q.1, q.2.1))
                      b a
        _ =
              ((IdxSubMeas.toIdxOpFamily
                (pointDiagonalLineMixedProductRight params strategy) q).outcome
                (a, b)) := by
              symm
              exact pointDiagonalLineMixedProductRight_outcome params strategy q a b)
    (by
      intro q ab
      rcases ab with ⟨a, b⟩
      calc
        (Bstep q).outcome (a, b)
          = leftTensor
              ((strategy.pointMeasurement (q.1.pointAt q.2.2)).outcome b *
                (strategy.pointMeasurement (q.1.pointAt q.2.1)).outcome a) := by
                  simpa [Bstep] using
                    liftLeft_mul_leftPlaced_outcome
                      ((strategy.pointMeasurement (q.1.pointAt q.2.2)).toSubMeas)
                      ((strategy.pointMeasurement (q.1.pointAt q.2.1)).toSubMeas)
                      b a
        _ = (pointMeasurementProductAlongSharedLineReversed params strategy q).outcome (a, b) := by
              symm
              exact pointMeasurementProductAlongSharedLineReversed_outcome params strategy q a b)
    hcab

/-- `thm:commutativity-points`. -/
theorem commutativityPoints
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    SDDOpRel strategy.state
      (uniformDistribution (PointPairQuestion params))
      (pointMeasurementProductLeft params strategy)
      (pointMeasurementProductRight params strategy)
      (commutativityPointsError params gamma) := by
  let δ := pointDiagonalLineApproxError params gamma
  have hleft :
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (pointMeasurementProductAlongSharedLine params strategy)
        (diagonalLineProductOrdered params strategy)
        (2 * (δ + δ)) := by
    exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductLeft params strategy))
      (diagonalLineProductOrdered params strategy)
      δ δ
      (orderedLiftToMixedBridge params strategy eps delta gamma hgood)
      (orderedLiftToLineBridge params strategy eps delta gamma hgood)
  have hright :
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (diagonalLineProductOrdered params strategy)
        (pointMeasurementProductAlongSharedLineReversed params strategy)
        (2 * (δ + δ)) := by
    exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (diagonalLineProductOrdered params strategy)
      (IdxSubMeas.toIdxOpFamily (pointDiagonalLineMixedProductRight params strategy))
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      δ δ
      (orderedDropFromLineBridge params strategy eps delta gamma hgood)
      (reversedDropToPointsBridge params strategy eps delta gamma hgood)
  have hshared :
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (pointMeasurementProductAlongSharedLine params strategy)
        (pointMeasurementProductAlongSharedLineReversed params strategy)
        (2 * (2 * (δ + δ) + 2 * (δ + δ))) := by
    exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_triangle
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (diagonalLineProductOrdered params strategy)
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      (2 * (δ + δ)) (2 * (δ + δ))
      hleft hright
  have hshared' :
      SDDOpRel strategy.state
        (pointPairSharedDiagonalLineDistribution params)
        (pointMeasurementProductAlongSharedLine params strategy)
        (pointMeasurementProductAlongSharedLineReversed params strategy)
        (commutativityPointsError params gamma) := by
    refine MIPStarRE.LDT.Preliminaries.stateDependentDistanceOpRel_mono
      strategy.state
      (pointPairSharedDiagonalLineDistribution params)
      (pointMeasurementProductAlongSharedLine params strategy)
      (pointMeasurementProductAlongSharedLineReversed params strategy)
      (2 * (2 * (δ + δ) + 2 * (δ + δ)))
      (commutativityPointsError params gamma)
      ?_ hshared
    dsimp [δ, pointDiagonalLineApproxError, restrictedDiagonalLinesConsistencyError,
      commutativityPointsError]
    ring_nf
    linarith
  rcases hshared' with ⟨hshared'⟩
  constructor
  calc
    sddErrorOp strategy.state
        (uniformDistribution (PointPairQuestion params))
        (pointMeasurementProductLeft params strategy)
        (pointMeasurementProductRight params strategy)
      = avgOver (pointPairSharedDiagonalLineDistribution params)
          (fun q =>
            qSDDOp strategy.state
              (pointMeasurementProductAlongSharedLine params strategy q)
              (pointMeasurementProductAlongSharedLineReversed params strategy q)) := by
            symm
            simpa [sddErrorOp, pointMeasurementProductAlongSharedLine,
              pointMeasurementProductAlongSharedLineReversed] using
              avgOver_pointPairSharedDiagonalLine_sampled_pair params
                (fun uv =>
                  qSDDOp strategy.state
                    (pointMeasurementProductLeft params strategy uv)
                    (pointMeasurementProductRight params strategy uv))
    _ = sddErrorOp strategy.state
          (pointPairSharedDiagonalLineDistribution params)
          (pointMeasurementProductAlongSharedLine params strategy)
          (pointMeasurementProductAlongSharedLineReversed params strategy) := by
            rfl
    _ ≤ commutativityPointsError params gamma := hshared'

end MIPStarRE.LDT.CommutativityPoints
