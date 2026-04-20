import MIPStarRE.LDT.Test.StrategyRoleAverage

/-!
# Polynomial-family interfaces for the low individual degree test

Packaged slice-indexed polynomial-family interfaces extracted from
`MIPStarRE.LDT.Test.Strategy`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Polynomial-family interfaces -/

/-- A packaged family `x ↦ G^x` together with its witness operators and domination targets.

The `witness` and `dominationTarget` fields store the per-slice PSD operator
`Z^x` and per-slice, per-polynomial operator `E_u A^{u,x}_{g(u)}` appearing in
the paper's boundedness hypothesis (`references/ldt-paper/commutativity-G.tex`,
item `data-processed-boundedness`). Their stored defaults use the slice
submeasurement itself — `total` dominates every per-polynomial outcome — which
is PSD, non-vacuous, and satisfies `sliceOpPSD` and `sliceDominatesTarget`
without any additional hypothesis.

Callers with access to a symmetric strategy should prefer the paper-faithful
smart constructor `ofSymStrat`, which ties `dominationTarget` to the averaged
slice-point evaluation operator `E_u A^{u,x}_{g(u)}` from the paper. -/
structure IdxPolyFamily (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  meas : IdxProjSubMeas (Fq params) (Polynomial params) ι
  witness : Fq params → MIPStarRE.Quantum.Op ι := fun x => (meas x).toSubMeas.total
  dominationTarget : Fq params → Polynomial params → MIPStarRE.Quantum.Op ι :=
    fun x g => (meas x).toSubMeas.outcome g
  deriving Inhabited

namespace IdxPolyFamily

/-- The averaged submeasurement `G = E_x G^x`: average the slice
measurements over the uniform distribution on slice heights `x ∈ F_q`. -/
noncomputable def averagedSubMeas {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι) :
    SubMeas (Polynomial params) ι where
  outcome := fun g =>
    let 𝒟 := uniformDistribution (Fq params)
    ∑ x ∈ 𝒟.support, 𝒟.weight x • (family.meas x).toSubMeas.outcome g
  total :=
    let 𝒟 := uniformDistribution (Fq params)
    ∑ x ∈ 𝒟.support, 𝒟.weight x • (family.meas x).toSubMeas.total
  outcome_pos := by
    intro g
    let 𝒟 := uniformDistribution (Fq params)
    exact Finset.sum_nonneg fun x _ =>
      smul_nonneg (𝒟.nonnegative x) ((family.meas x).outcome_pos g)
  sum_eq_total := by
    classical
    let 𝒟 := uniformDistribution (Fq params)
    calc
      ∑ g, ∑ x ∈ 𝒟.support, 𝒟.weight x • (family.meas x).toSubMeas.outcome g
          = ∑ x ∈ 𝒟.support, ∑ g, 𝒟.weight x • (family.meas x).toSubMeas.outcome g := by
              rw [Finset.sum_comm]
      _ = ∑ x ∈ 𝒟.support, 𝒟.weight x • ∑ g, (family.meas x).toSubMeas.outcome g := by
            apply Finset.sum_congr rfl
            intro x _
            rw [← Finset.smul_sum]
      _ = ∑ x ∈ 𝒟.support, 𝒟.weight x • (family.meas x).toSubMeas.total := by
            apply Finset.sum_congr rfl
            intro x _
            rw [(family.meas x).toSubMeas.sum_eq_total]
  total_le_one := by
    let 𝒟 := uniformDistribution (Fq params)
    calc
      ∑ x ∈ 𝒟.support, 𝒟.weight x • (family.meas x).toSubMeas.total
        ≤ ∑ x ∈ 𝒟.support, 𝒟.weight x • (1 : MIPStarRE.Quantum.Op ι) := by
            exact Finset.sum_le_sum fun x _ =>
              smul_le_smul_of_nonneg_left (family.meas x).toSubMeas.total_le_one (𝒟.nonnegative x)
      _ = (∑ x ∈ 𝒟.support, 𝒟.weight x) • (1 : MIPStarRE.Quantum.Op ι) := by
            rw [Finset.sum_smul]
      _ ≤ (1 : Error) • (1 : MIPStarRE.Quantum.Op ι) := by
            exact smul_le_smul_of_nonneg_right
              (uniformDistribution_weight_sum_le_one (Fq params)) zero_le_one
      _ = 1 := by simp

/-- Evaluate the slice family at a point `(u, x)` in `F_q^{m+1}`. -/
noncomputable def evaluatedAtNextPoint {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  fun u =>
    evaluateAt params (truncatePoint params u)
      ((family.meas (pointHeight params u)).toSubMeas)

/-- Weighted sum of operators over a distribution's finite support. -/
private noncomputable def averageOperatorOverDistribution' {α : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (f : α → MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.Op ι :=
  ∑ a ∈ 𝒟.support, 𝒟.weight a • f a

/-- Averaged point operator `E_u A^u_{h(u)}` appearing in source-style
boundedness assumptions. -/
noncomputable def averagedPointEvaluationOperator {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) (h : Polynomial params) :
    MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution' (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement u).toSubMeas.outcome (h u))

/-- Slice-wise averaged point operator `E_u A^{u,x}_{g(u)}` from the paper's
boundedness hypothesis. -/
noncomputable def averagedSlicePointEvaluationOperator {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution' (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u))

/-- Paper-faithful smart constructor: bundle a slice submeasurement with a
symmetric strategy to obtain the `IdxPolyFamily` whose `dominationTarget` is the
averaged slice-point evaluation operator `E_u A^{u,x}_{g(u)}` from
`references/ldt-paper/commutativity-G.tex`. The `witness` field is set to the
identity operator, which is a valid PSD upper bound on every `dominationTarget`
slice (the paper only requires such a `Z^x` to exist). -/
noncomputable def ofSymStrat {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι) :
    IdxPolyFamily params ι where
  meas := meas
  witness := fun _ => 1
  dominationTarget := fun x g => averagedSlicePointEvaluationOperator strategy x g

@[simp] lemma ofSymStrat_meas {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι) :
    (ofSymStrat strategy meas).meas = meas := rfl

@[simp] lemma ofSymStrat_witness {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (x : Fq params) :
    (ofSymStrat strategy meas).witness x = 1 := rfl

@[simp] lemma ofSymStrat_dominationTarget {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (x : Fq params) (g : Polynomial params) :
    (ofSymStrat strategy meas).dominationTarget x g =
      averagedSlicePointEvaluationOperator strategy x g := rfl

structure Complete {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (ψ : QuantumState (ι × ι)) (kappa : Error) : Prop where
  averageCompleteness :
    CompletenessAtLeast ψ family.averagedSubMeas.liftLeft (1 - kappa)

structure ConsistentWithPoints {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (strategy : SymStrat params.next ι) (zeta : Error) : Prop where
  pointConsistency :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      family.evaluatedAtNextPoint
      zeta

structure StronglySelfConsistent {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (ψ : QuantumState (ι × ι)) (zeta : Error) : Prop where
  sliceSelfConsistency :
    SDDRel ψ (uniformDistribution (Fq params))
      (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas family.meas))
      (IdxSubMeas.liftRight (IdxProjSubMeas.toIdxSubMeas family.meas))
      zeta

structure Bounded {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : IdxPolyFamily params ι)
    (ψ : QuantumState (ι × ι)) (zeta : Error) : Prop where
  sliceOpPSD : ∀ x, 0 ≤ family.witness x
  sliceBoundedness :
    avgOver (uniformDistribution (Fq params))
      (fun x =>
        ev ψ <|
          leftTensor (ι₂ := ι) (1 - (family.meas x).toSubMeas.total) *
            rightTensor (ι₁ := ι) (family.witness x)) ≤ zeta
  sliceDominatesTarget :
    ∀ x : Fq params, ∀ g : Polynomial params,
      0 ≤ family.witness x - family.dominationTarget x g

/-- Paper-faithful boundedness input for slice-indexed polynomial families.

This extends `IdxPolyFamily.Bounded` with the missing source-side identification
between the abstract domination target and the averaged point operator
`E_u A^{u,x}_{g(u)}`. -/
structure SliceBoundednessInput {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (zeta : Error) : Prop where
  bounded : family.Bounded strategy.state zeta
  dominationTargetAgrees :
    ∀ x : Fq params, ∀ g : Polynomial params,
      family.dominationTarget x g =
        averagedSlicePointEvaluationOperator strategy x g

namespace SliceBoundednessInput

/-- The boundedness residual obtained from a concrete slice family `G`.

This is the induction-oriented `Z^x ⊗ (I - G^x)` term after replacing the
abstract slice family by the concrete `G`, written in the paper's
`(I - G^x) ⊗ Z^x` orientation. -/
noncomputable def storedResidual {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SymStrat params.next ι}
    {family : IdxPolyFamily params ι} {zeta : Error}
    (_hbound : SliceBoundednessInput strategy family zeta)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (x : Fq params) : Error :=
  ev strategy.state
    (leftTensor (ι₂ := ι) (1 - (G x).total) *
      rightTensor (ι₁ := ι) (family.witness x))

/-- Stored residual half of the boundedness hypothesis.

This is exactly the paper's `(I-G^x) ⊗ Z^x` residual bound from
`references/ldt-paper/commutativity-G.tex`. -/
theorem storedBoundedResidualBound {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SymStrat params.next ι}
    {family : IdxPolyFamily params ι} {zeta : Error}
    (hbound : SliceBoundednessInput strategy family zeta)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas) :
    avgOver (uniformDistribution (Fq params))
      (fun x => hbound.storedResidual G x) ≤ zeta := by
  simpa [storedResidual, hG] using hbound.bounded.sliceBoundedness

/-- Paper-faithful domination half of the boundedness hypothesis.

This is the line `Z^x ≥ E_u A^{u,x}_{g(u)}` from
`references/ldt-paper/commutativity-G.tex`. -/
theorem averagedPoint_le_witness {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SymStrat params.next ι}
    {family : IdxPolyFamily params ι} {zeta : Error}
    (hbound : SliceBoundednessInput strategy family zeta) :
    ∀ x : Fq params, ∀ g : Polynomial params,
      averagedSlicePointEvaluationOperator strategy x g ≤ family.witness x := by
  intro x g
  have hdom : family.dominationTarget x g ≤ family.witness x :=
    sub_nonneg.mp (hbound.bounded.sliceDominatesTarget x g)
  simpa [hbound.dominationTargetAgrees x g] using hdom

end SliceBoundednessInput

end IdxPolyFamily

end MIPStarRE.LDT
