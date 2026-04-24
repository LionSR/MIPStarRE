import MIPStarRE.LDT.Test.StrategySymmetrized

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
item `data-processed-boundedness`). We store these operators explicitly rather
than hiding them behind ambient defaults, so each constructor must choose an
honest witness/target pair.

Callers without access to an ambient strategy can use `ofSliceMeas`, which takes
`Z^x := ∑_g G^x_g` and `dominationTarget x g := G^x_g`. Callers with access to a
symmetric strategy should prefer the paper-facing constructor `ofSymStrat`,
which derives both fields from the strategy itself. -/
structure IdxPolyFamily (params : Parameters) [FieldModel params.q]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  meas : IdxProjSubMeas (Fq params) (Polynomial params) ι
  witness : Fq params → MIPStarRE.Quantum.Op ι
  dominationTarget : Fq params → Polynomial params → MIPStarRE.Quantum.Op ι

-- NOTE: no global `Inhabited` instance for `IdxPolyFamily`; without an actual
-- slice family, any default would be a degenerate zero-family placeholder.

namespace IdxPolyFamily

/-- Honest local constructor when only the slice family `x ↦ G^x` is available.

This uses the slice total `∑_g G^x_g` as the witness operator and the concrete
outcome `G^x_g` as the domination target. -/
def ofSliceMeas {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι) :
    IdxPolyFamily params ι where
  meas := meas
  witness := fun x => (meas x).toSubMeas.total
  dominationTarget := fun x g => (meas x).toSubMeas.outcome g

@[simp] lemma ofSliceMeas_meas {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι) :
    (ofSliceMeas meas).meas = meas := rfl

@[simp] lemma ofSliceMeas_witness {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (x : Fq params) :
    (ofSliceMeas meas).witness x = (meas x).toSubMeas.total := rfl

@[simp] lemma ofSliceMeas_dominationTarget {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (x : Fq params) (g : Polynomial params) :
    (ofSliceMeas meas).dominationTarget x g = (meas x).toSubMeas.outcome g := rfl

theorem ofSliceMeas_dominationTarget_le_witness {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (x : Fq params) (g : Polynomial params) :
    (ofSliceMeas meas).dominationTarget x g ≤ (ofSliceMeas meas).witness x := by
  simpa using ((meas x).toSubMeas.outcome_le_total g)

theorem ofSliceMeas_sliceDominatesTarget {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (x : Fq params) (g : Polynomial params) :
    0 ≤ (ofSliceMeas meas).witness x - (ofSliceMeas meas).dominationTarget x g := by
  exact sub_nonneg.mpr (ofSliceMeas_dominationTarget_le_witness meas x g)

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

/-- Averaged point operator `E_u A^u_{h(u)}` appearing in source-style
boundedness assumptions. -/
noncomputable def averagedPointEvaluationOperator {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι) (h : Polynomial params) :
    MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement u).toSubMeas.outcome (h u))

/-- Slice-wise averaged point operator `E_u A^{u,x}_{g(u)}` from the paper's
boundedness hypothesis. -/
noncomputable def averagedSlicePointEvaluationOperator {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (x : Fq params) (g : Polynomial params) : MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome (g u))

/-- Slice-wise averaged total operator `E_u \sum_a A^{u,x}_a`.

For a genuine symmetric strategy this simplifies to `1`, but keeping the
strategy-shaped formula explicit records where the witness comes from. -/
noncomputable def averagedSliceTotalOperator {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι) (x : Fq params) : MIPStarRE.Quantum.Op ι :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (fun u => (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.total)

theorem averagedSliceTotalOperator_nonneg {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    0 ≤ averagedSliceTotalOperator strategy x := by
  unfold averagedSliceTotalOperator averageOperatorOverDistribution
  exact Finset.sum_nonneg fun u _ =>
    smul_nonneg ((uniformDistribution (Point params)).nonnegative u)
      ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.total_nonneg)

@[simp] theorem averagedSliceTotalOperator_eq_one {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι) (x : Fq params) :
    averagedSliceTotalOperator strategy x = 1 := by
  unfold averagedSliceTotalOperator averageOperatorOverDistribution
  calc
    ∑ u ∈ (uniformDistribution (Point params)).support,
        (uniformDistribution (Point params)).weight u •
          (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.total
      = ∑ u ∈ (uniformDistribution (Point params)).support,
          (uniformDistribution (Point params)).weight u • (1 : MIPStarRE.Quantum.Op ι) := by
            apply Finset.sum_congr rfl
            intro u _
            have htotal :
                (strategy.pointMeasurement (appendPoint params u x)).toSubMeas.total =
                  (1 : MIPStarRE.Quantum.Op ι) := by
              simpa using (strategy.pointMeasurement (appendPoint params u x)).total_eq_one
            rw [htotal]
    _ = (∑ u ∈ (uniformDistribution (Point params)).support,
          (uniformDistribution (Point params)).weight u) • (1 : MIPStarRE.Quantum.Op ι) := by
          rw [Finset.sum_smul]
    _ = 1 := by
          rw [uniformDistribution_weight_sum_eq_one (Point params), one_smul]

theorem averagedSlicePointEvaluationOperator_le_averagedSliceTotalOperator
    {params : Parameters} [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι) (x : Fq params) (g : Polynomial params) :
    averagedSlicePointEvaluationOperator strategy x g ≤ averagedSliceTotalOperator strategy x := by
  unfold averagedSlicePointEvaluationOperator averagedSliceTotalOperator
    averageOperatorOverDistribution
  exact Finset.sum_le_sum fun u _ =>
    smul_le_smul_of_nonneg_left
      ((strategy.pointMeasurement (appendPoint params u x)).toSubMeas.outcome_le_total (g u))
      ((uniformDistribution (Point params)).nonnegative u)

/-- Paper-facing constructor: bundle a slice submeasurement with a symmetric
strategy so that both the domination target and the witness are derived from the
strategy itself.

Concretely, `dominationTarget x g` is the averaged slice-point evaluation
operator `E_u A^{u,x}_{g(u)}` from `references/ldt-paper/commutativity-G.tex`,
and `witness x` is the corresponding averaged slice-total operator
`E_u \sum_a A^{u,x}_a`. Since point measurements are genuine measurements, this
witness simplifies to `1`, but its stored definition keeps the provenance
explicit. -/
noncomputable def ofSymStrat {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι) :
    IdxPolyFamily params ι where
  meas := meas
  witness := averagedSliceTotalOperator strategy
  dominationTarget := fun x g => averagedSlicePointEvaluationOperator strategy x g

@[simp] lemma ofSymStrat_meas {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι) :
    (ofSymStrat strategy meas).meas = meas := rfl

theorem ofSymStrat_witness_eq_averagedSliceTotalOperator {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (x : Fq params) :
    (ofSymStrat strategy meas).witness x = averagedSliceTotalOperator strategy x := rfl

@[simp] lemma ofSymStrat_witness {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (x : Fq params) :
    (ofSymStrat strategy meas).witness x = 1 := by
  simp [ofSymStrat_witness_eq_averagedSliceTotalOperator]

@[simp] lemma ofSymStrat_dominationTarget {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (x : Fq params) (g : Polynomial params) :
    (ofSymStrat strategy meas).dominationTarget x g =
      averagedSlicePointEvaluationOperator strategy x g := rfl

theorem ofSymStrat_dominationTarget_le_witness {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (x : Fq params) (g : Polynomial params) :
    (ofSymStrat strategy meas).dominationTarget x g ≤ (ofSymStrat strategy meas).witness x := by
  simpa [ofSymStrat_witness_eq_averagedSliceTotalOperator] using
    averagedSlicePointEvaluationOperator_le_averagedSliceTotalOperator strategy x g

theorem ofSymStrat_sliceDominatesTarget {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params.next ι)
    (meas : IdxProjSubMeas (Fq params) (Polynomial params) ι)
    (x : Fq params) (g : Polynomial params) :
    0 ≤ (ofSymStrat strategy meas).witness x - (ofSymStrat strategy meas).dominationTarget x g := by
  exact sub_nonneg.mpr (ofSymStrat_dominationTarget_le_witness strategy meas x g)

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
