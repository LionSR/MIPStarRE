import MIPStarRE.LDT.Commutativity.GCommStability.Scalar.Common

/-!
# Section 11 commutativity: first scalar stability bound

The first scalar stability defect and its Cauchy--Schwarz boundedness proof.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open GCommStability.Scalar
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The paper's slice submeasurement `R^y_g = E_{u,x} \sum_a G^{u,x}_a G^y_g G^{u,x}_a`. -/
noncomputable def gCommStabilityR
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (y : Fq params) :
    SubMeas (Polynomial params) ι :=
  averageIdxSubMeas
    (uniformDistribution (Point params.next))
    (fun ux =>
      postprocess
        (sandwichByOuterSubMeas
          (evaluatedPointFamily params family ux)
          ((family.meas y).toSubMeas))
        Prod.snd)
    (uniformDistribution_weight_sum_le_one (Point params.next))

private lemma gCommStabilityR_first_factor_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι) (y : Fq params) :
    ∑ g : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι) ((gCommStabilityR params family y).outcome g)) ≤ 1 := by
  calc
    ∑ g : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι) ((gCommStabilityR params family y).outcome g))
      = ev strategy.state
          (leftTensor (ι₂ := ι) ((gCommStabilityR params family y).total)) := by
            rw [← ev_sum strategy.state]
            rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ
              (fun g : Polynomial params => (gCommStabilityR params family y).outcome g)]
            rw [(gCommStabilityR params family y).sum_eq_total]
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          exact ev_mono strategy.state _ _ <|
            leftTensor_le_one (ι₂ := ι) (gCommStabilityR params family y).total_le_one
    _ = 1 := ev_one_of_isNormalized strategy.state hnorm

/-- Named scalar defect for the first paper stability claim.

For fixed `y`, this is the collapsed scalar from `commutativity-G.tex`,
equation `eq:bound-this-right-now!`: `gCommStabilityR` contains the averaged
left-register sandwich `R_g^y = E_{u,x} \sum_a G_a^{u,x} G_g^y G_a^{u,x}`,
the factor `(1 - (G y).total)` is the paper's left-register `(I - G^y)`, and
`IdxPolyFamily.averagedSlicePointEvaluationOperator` is the right-register
average `E_v A^{v,y}_{g(v)}`.  Thus each summand has tensor placement
`(R_g^y (I-G^y)) ⊗ E_v A^{v,y}_{g(v)}`.  This is the scalar expression bounded
by `gCommStability_scalar`, not the overlap `SDDOpRel` package. -/
noncomputable def gCommStabilityScalarDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (y : Fq params) : Error :=
  ∑ g : Polynomial params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          ((gCommStabilityR params family y).outcome g * (1 - (G y).total)) *
        rightTensor (ι₁ := ι)
          (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy y g))

private lemma gCommStability_scalar_pointwise_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    ∀ y : Fq params,
      |gCommStabilityScalarDefect params strategy family G y| ≤
        Real.sqrt (hbound.storedResidual G y) := by
  intro y
  simpa [gCommStabilityScalarDefect] using
    scalar_pointwise_cauchy_schwarz_bound
      params strategy zeta family G hG hbound
      (gCommStabilityR params family y) y
      (gCommStabilityR_first_factor_le_one params strategy hnorm family y)

/-- Direct boundedness proof for the first paper scalar stability estimate.

This is the Cauchy--Schwarz/`Z^y` part of
`references/ldt-paper/commutativity-G.tex`, `clm:g-comm-stability` (lines
135--179).  It is intentionally separate from the overlap-style
`gCommStability_overlap` theorem: the overlap theorem bounds an internal
`SDDOpRel` package, while this theorem uses `SliceBoundednessInput` to control
the paper scalar defect after the finite marginalization/reindexing step. -/
theorem gCommStability_scalar
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta) :
    |avgOver (uniformDistribution (Fq params))
      (gCommStabilityScalarDefect params strategy family G)| ≤ Real.sqrt zeta := by
  have h𝒟 :
      ∑ y ∈ (uniformDistribution (Fq params)).support,
        (uniformDistribution (Fq params)).weight y ≤ 1 := by
    simpa using uniformDistribution_weight_sum_le_one (Fq params)
  calc
    |avgOver (uniformDistribution (Fq params))
        (gCommStabilityScalarDefect params strategy family G)|
      ≤ Real.sqrt
          (avgOver (uniformDistribution (Fq params))
            (fun y => hbound.storedResidual G y)) := by
          exact
            MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise
              (uniformDistribution (Fq params))
              (gCommStabilityScalarDefect params strategy family G)
              (fun y => hbound.storedResidual G y)
              (gCommStability_scalar_pointwise_bound
                params strategy zeta hnorm family G hG hbound)
              (storedResidual_nonneg
                params strategy family G zeta hbound)
              h𝒟
    _ ≤ Real.sqrt zeta := by
          exact Real.sqrt_le_sqrt <|
            hbound.storedBoundedResidualBound G hG

end MIPStarRE.LDT.Commutativity
