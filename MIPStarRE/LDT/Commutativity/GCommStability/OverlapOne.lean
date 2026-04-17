import MIPStarRE.LDT.Commutativity.ScalarApproximation.Pointwise

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 2000000 in
/-- Averaging the common overlap term over `Point params.next` depends only on
the final coordinate `x : F_q`. -/
private lemma gCommOverlap_avgOver_point
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (G : Fq params → SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params.next))
      (fun w => gCommOverlapTerm params strategy G (pointHeight params w)) =
    avgOver (uniformDistribution (Fq params))
      (fun x => gCommOverlapTerm params strategy G x) := by
  let e := CommutativityPoints.pointNextEquiv params
  calc
    avgOver (uniformDistribution (Point params.next))
        (fun w => gCommOverlapTerm params strategy G (pointHeight params w))
      = avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => gCommOverlapTerm params strategy G (pointHeight params (e.symm ux))) :=
          avgOver_uniform_equiv e _
    _ = avgOver (uniformDistribution (Point params × Fq params))
          (fun ux => gCommOverlapTerm params strategy G ux.2) := by
          apply avgOver_congr
          intro ux
          rcases ux with ⟨u, x⟩
          simp [e, CommutativityPoints.pointNextEquiv, pointHeight_appendPoint]
    _ = avgOver (uniformDistribution (Fq params))
          (fun x => gCommOverlapTerm params strategy G x) := by
          exact avgOver_uniform_snd
            (α := Point params)
            (β := Fq params)
            (f := fun x => gCommOverlapTerm params strategy G x)

/-- Averaging the overlap term over evaluated-slice questions through the
second point coordinate marginalizes to the uniform `x : F_q` average. -/
private lemma gCommOverlap_avgOver_snd
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (G : Fq params → SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => gCommOverlapTerm params strategy G (pointHeight params q.2)) =
    avgOver (uniformDistribution (Fq params))
      (fun x => gCommOverlapTerm params strategy G x) := by
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => gCommOverlapTerm params strategy G (pointHeight params q.2))
      = avgOver (uniformDistribution (Point params.next))
          (fun w => gCommOverlapTerm params strategy G (pointHeight params w)) := by
            exact avgOver_uniform_snd
              (f := fun w => gCommOverlapTerm params strategy G (pointHeight params w))
    _ = avgOver (uniformDistribution (Fq params))
          (fun x => gCommOverlapTerm params strategy G x) :=
          gCommOverlap_avgOver_point params strategy G

/-- Averaging the overlap term over evaluated-slice questions through the
first point coordinate marginalizes to the uniform `x : F_q` average. -/
lemma gCommOverlap_avgOver_fst
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (G : Fq params → SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
      (fun q => gCommOverlapTerm params strategy G (pointHeight params q.1)) =
    avgOver (uniformDistribution (Fq params))
      (fun x => gCommOverlapTerm params strategy G x) := by
  calc
    avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => gCommOverlapTerm params strategy G (pointHeight params q.1))
      = avgOver (uniformDistribution (Point params.next))
          (fun w => gCommOverlapTerm params strategy G (pointHeight params w)) := by
            exact avgOver_uniform_fst
              (f := fun w => gCommOverlapTerm params strategy G (pointHeight params w))
    _ = avgOver (uniformDistribution (Fq params))
          (fun x => gCommOverlapTerm params strategy G x) :=
          gCommOverlap_avgOver_point params strategy G

/-- The common overlap term is always at most `1`. -/
private lemma gCommOverlapTerm_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (hnorm : strategy.state.IsNormalized)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (x : Fq params) :
    gCommOverlapTerm params strategy G x ≤ 1 := by
  unfold gCommOverlapTerm
  have hmono :
      opTensor (1 - (G x).total) ((G x).total) ≤
        leftTensor (ι₂ := ι) (1 - (G x).total) := by
    exact opTensor_le_leftTensor
      (sub_nonneg.mpr (G x).total_le_one)
      (G x).total_le_one
  calc
    ev strategy.state
        (leftTensor (ι₂ := ι) (1 - (G x).total) *
          rightTensor (ι₁ := ι) ((G x).total))
      = ev strategy.state
          (opTensor (1 - (G x).total) ((G x).total)) := by
            rw [leftTensor_mul_rightTensor_eq_opTensor]
    _ ≤ ev strategy.state
          (leftTensor (ι₂ := ι) (1 - (G x).total)) := by
            exact ev_mono strategy.state _ _ hmono
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
            exact ev_mono strategy.state _ _ <|
              leftTensor_le_one (ι₂ := ι)
                (sub_le_self (1 : MIPStarRE.Quantum.Op ι) (G x).total_nonneg)
    _ = 1 := ev_one_of_isNormalized strategy.state hnorm

set_option maxHeartbeats 2000000 in
/-- Any pointwise defect bound by the common overlap term inherits a raw
`zeta / 2` estimate after marginalizing to the slice SSC defect of `G`. -/
lemma gCommStability_raw_le_half_of
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    {Outcome : Type*} [Fintype Outcome]
    (A B : IdxOpFamily (EvaluatedSliceQuestion params) Outcome (ι × ι))
    (point : EvaluatedSliceQuestion params → Point params.next)
    (hmarg :
      avgOver (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => gCommOverlapTerm params strategy G (pointHeight params (point q))) =
      avgOver (uniformDistribution (Fq params))
        (fun x => gCommOverlapTerm params strategy G x))
    (hpointwise : ∀ q,
      qSDDOp strategy.state (A q) (B q) ≤
        gCommOverlapTerm params strategy G (pointHeight params (point q))) :
    sddErrorOp strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      A B ≤
    zeta / 2 := by
  have hsliceSSC := gCommStability_sliceSSC params strategy zeta family G hG hself
  have hssc_point := gCommStability_ssc_point params strategy G
  calc
    sddErrorOp strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        A B
      ≤ avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => gCommOverlapTerm params strategy G (pointHeight params (point q))) := by
            unfold sddErrorOp
            exact avgOver_mono _ _ _ hpointwise
    _ = avgOver (uniformDistribution (Fq params))
          (fun x => gCommOverlapTerm params strategy G x) := hmarg
    _ ≤ avgOver (uniformDistribution (Fq params))
          (fun x => qBipartiteSSCDefect strategy.state (G x)) := by
            exact avgOver_mono _ _ _ hssc_point
    _ = bipartiteSSCError strategy.state (uniformDistribution (Fq params)) G := by
          rfl
    _ ≤ zeta / 2 := hsliceSSC.overlapBound

set_option maxHeartbeats 2000000 in
/-- Any pointwise defect bound by the common overlap term is trivially at most
`1`. -/
lemma gCommStability_raw_le_one_of
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (hnorm : strategy.state.IsNormalized)
    (G : Fq params → SubMeas (Polynomial params) ι)
    {Outcome : Type*} [Fintype Outcome]
    (A B : IdxOpFamily (EvaluatedSliceQuestion params) Outcome (ι × ι))
    (point : EvaluatedSliceQuestion params → Point params.next)
    (hpointwise : ∀ q,
      qSDDOp strategy.state (A q) (B q) ≤
        gCommOverlapTerm params strategy G (pointHeight params (point q))) :
    sddErrorOp strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      A B ≤
    1 := by
  calc
    sddErrorOp strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        A B
      ≤ avgOver (uniformDistribution (EvaluatedSliceQuestion params))
          (fun q => gCommOverlapTerm params strategy G (pointHeight params (point q))) := by
            unfold sddErrorOp
            exact avgOver_mono _ _ _ hpointwise
    _ ≤ avgOver (uniformDistribution (EvaluatedSliceQuestion params)) (fun _ => 1) := by
          apply avgOver_mono
          intro q
          exact gCommOverlapTerm_le_one
            params strategy hnorm G (pointHeight params (point q))
    _ = ∑ q ∈ (uniformDistribution (EvaluatedSliceQuestion params)).support,
          (uniformDistribution (EvaluatedSliceQuestion params)).weight q := by
          simp [avgOver]
    _ ≤ 1 := by
          simpa using
            uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)

set_option maxHeartbeats 2000000 in
/-- Upgrade raw `zeta / 2` and `1` bounds to the displayed `sqrt zeta` relation. -/
lemma sddOpRel_of_sqrt_bound_from_half_one
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι)
    (zeta : Error)
    (hz_nonneg : 0 ≤ zeta)
    (hhalf : sddErrorOp ψ 𝒟 A B ≤ zeta / 2)
    (hone : sddErrorOp ψ 𝒟 A B ≤ 1) :
    SDDOpRel ψ 𝒟 A B (Real.sqrt zeta) := by
  constructor
  by_cases hz1 : zeta ≤ 1
  · have hsmall : zeta / 2 ≤ Real.sqrt zeta := by
      have hsqrt_nonneg : 0 ≤ Real.sqrt zeta := Real.sqrt_nonneg _
      nlinarith [Real.sq_sqrt hz_nonneg]
    exact le_trans hhalf hsmall
  · have hbig : 1 ≤ Real.sqrt zeta := by
      have hz_one : 1 ≤ zeta := by linarith
      have hsqrt_nonneg : 0 ≤ Real.sqrt zeta := Real.sqrt_nonneg _
      nlinarith [Real.sq_sqrt hz_nonneg]
    exact le_trans hone hbig

set_option maxHeartbeats 2000000 in
/-- The first stability family has raw defect at most `zeta / 2`. -/
private lemma gCommStability_raw_le_half
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    sddErrorOp strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityOneLeft params strategy family G)
      (commDataProcessedGStabilityOneRight params strategy family G) ≤
    zeta / 2 := by
  exact
    gCommStability_raw_le_half_of params strategy zeta family G hG hself
      (commDataProcessedGStabilityOneLeft params strategy family G)
      (commDataProcessedGStabilityOneRight params strategy family G)
      Prod.snd
      (gCommOverlap_avgOver_snd params strategy G)
      (gCommStability_pointwise_bound params strategy family G hG)

set_option maxHeartbeats 2000000 in
/-- The first stability family has raw defect at most `1`. -/
private lemma gCommStability_raw_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (_zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    sddErrorOp strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityOneLeft params strategy family G)
      (commDataProcessedGStabilityOneRight params strategy family G) ≤
    1 := by
  exact
    gCommStability_raw_le_one_of params strategy hnorm G
      (commDataProcessedGStabilityOneLeft params strategy family G)
      (commDataProcessedGStabilityOneRight params strategy family G)
      Prod.snd
      (gCommStability_pointwise_bound params strategy family G hG)

/-- The boundedness residual currently stored by `IdxPolyFamily.Bounded`.

This is the induction-oriented `Z^x ⊗ (I - G^x)` term after replacing the
abstract slice family by the concrete `G` supplied to the commutativity theorem.
The paper's commutativity stability claims use the swapped
`(I - G^x) ⊗ Z^x` orientation, so this lemma records the currently available
boundedness input rather than completing the paper's scalar argument. -/
noncomputable def gCommStabilityBoundedResidual
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (x : Fq params) : Error :=
  ev strategy.state
    (leftTensor (ι₂ := ι) (family.witness x) *
      rightTensor (ι₁ := ι) (1 - (G x).total))

/-- Stored residual half of the boundedness hypothesis.

This is the line currently available from `IdxPolyFamily.Bounded`.  It is
swapped relative to `references/ldt-paper/commutativity-G.tex`, where the
residual appears as `(I-G^x) ⊗ Z^x`. -/
theorem gCommStability_storedBoundedResidualBound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    avgOver (uniformDistribution (Fq params))
      (fun x => gCommStabilityBoundedResidual params strategy family G x) ≤ zeta := by
  simpa [gCommStabilityBoundedResidual, hG] using hbound.bounded.sliceBoundedness

/-- Paper-faithful domination half of the boundedness hypothesis.

This is the line `Z^x ≥ E_u A^{u,x}_{g(u)}` from
`references/ldt-paper/commutativity-G.tex`. -/
theorem gCommStability_averagedPoint_le_witness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (family : IdxPolyFamily params ι)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ∀ x : Fq params, ∀ g : Polynomial params,
      IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤ family.witness x := by
  intro x g
  have hdom : family.dominationTarget x g ≤ family.witness x :=
    sub_nonneg.mp (hbound.bounded.sliceDominatesTarget x g)
  simpa [hbound.dominationTargetAgrees x g] using hdom

set_option maxHeartbeats 2000000 in
/-- Overlap-only version of the first stability estimate.

This is not the paper's boundedness-driven scalar proof of
`clm:g-comm-stability`: it bounds the current SDD package through the slice SSC
overlap term `⟨ψ,(I-G^y)⊗G^y ψ⟩`. It remains useful as an internal overlap
lemma while the scalar-chain API is being completed. -/
theorem gCommStability_overlap
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    SDDOpRel strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityOneLeft params strategy family G)
      (commDataProcessedGStabilityOneRight params strategy family G)
      (Real.sqrt zeta) := by
  have hz_nonneg : 0 ≤ zeta := by
    exact le_trans
      (sddError_nonneg strategy.state
        (uniformDistribution (Fq params))
        (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
        (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas)))
      hself.sliceSelfConsistency.squaredDistanceBound
  have hraw_le_half :=
    gCommStability_raw_le_half params strategy zeta family G hG hself
  have hraw_le_one :=
    gCommStability_raw_le_one params strategy zeta hnorm family G hG
  exact
    sddOpRel_of_sqrt_bound_from_half_one
      strategy.state
      (uniformDistribution (EvaluatedSliceQuestion params))
      (commDataProcessedGStabilityOneLeft params strategy family G)
      (commDataProcessedGStabilityOneRight params strategy family G)
      zeta hz_nonneg hraw_le_half hraw_le_one


end MIPStarRE.LDT.Commutativity
