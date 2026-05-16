import MIPStarRE.LDT.Commutativity.GCommStability.Scalar.Common

/-!
# Section 11 commutativity: second scalar stability bound

The mirrored scalar stability defect and its Cauchy--Schwarz boundedness proof.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open GCommStability.Scalar
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The paper's mirrored slice submeasurement
`R'^x_g = E_{v,y} \sum_b G^{v,y}_b G^x_g G^{v,y}_b`. -/
noncomputable def gCommStabilityTwoR
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (x : Fq params) :
    SubMeas (Polynomial params) ι :=
  averageIdxSubMeas
    (uniformDistribution (Point params.next))
    (fun vy =>
      postprocess
        (sandwichByOuterSubMeas
          (evaluatedPointFamily params family vy)
          (G x))
        Prod.snd)
    (uniformDistribution_weight_sum_le_one (Point params.next))

private lemma gCommStabilityTwoR_first_factor_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (x : Fq params) :
    ∑ g : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι) ((gCommStabilityTwoR params family G x).outcome g)) ≤ 1 := by
  calc
    ∑ g : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι) ((gCommStabilityTwoR params family G x).outcome g))
      = ev strategy.state
          (leftTensor (ι₂ := ι) ((gCommStabilityTwoR params family G x).total)) := by
            rw [← ev_sum strategy.state]
            rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ
              (fun g : Polynomial params => (gCommStabilityTwoR params family G x).outcome g)]
            rw [(gCommStabilityTwoR params family G x).sum_eq_total]
    _ ≤ ev strategy.state (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          exact ev_mono strategy.state _ _ <|
            leftTensor_le_one (ι₂ := ι) (gCommStabilityTwoR params family G x).total_le_one
    _ = 1 := ev_one_of_isNormalized strategy.state hnorm

/-- Named scalar defect for the boundedness half of the second paper stability claim.

For fixed `x`, this is the post-transport mirror analogue of
`commutativity-G.tex`, equation `eq:bound-this-right-now!`, with the slice
sandwich `R'^x_g` in place of `R^y_g`.  It is the scalar after the
`commutativityPoints` transport and after collapsing the `b`-indexed
left-register sandwich into `R'^x_g`; it is not literally the uncollapsed
paper expression `eq:g-comm-stab7`.  Concretely,
`gCommStabilityTwoR` averages the left-register sandwich
`E_{v,y} \sum_b G_b^{v,y} G_g^x G_b^{v,y}`, the factor
`(1 - (G x).total)` is the paper's left-register `(I-G^x)`, and
`IdxPolyFamily.averagedSlicePointEvaluationOperator` is the right-register
average `E_u A^{u,x}_{g(u)}`.  Thus each summand has tensor placement
`(R'_g{}^x (I-G^x)) ⊗ E_u A^{u,x}_{g(u)}`.  The `6√(γ(m+1))` transport loss is
a separate estimate. -/
noncomputable def gCommStabilityTwoScalarDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (x : Fq params) : Error :=
  ∑ g : Polynomial params,
    ev strategy.state
      (leftTensor (ι₂ := ι)
          ((gCommStabilityTwoR params family G x).outcome g * (1 - (G x).total)) *
        rightTensor (ι₁ := ι)
          (IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g))

private lemma gCommStabilityTwo_scalar_pointwise_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound_psd : ∀ x : Fq params, 0 ≤ family.witness x)
    (hbound_dom :
      ∀ x : Fq params, ∀ g : Polynomial params,
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤ family.witness x) :
    ∀ x : Fq params,
      |gCommStabilityTwoScalarDefect params strategy family G x| ≤
        Real.sqrt (IdxPolyFamily.storedResidual strategy family G x) := by
  intro x
  simpa [gCommStabilityTwoScalarDefect] using
    scalar_pointwise_cauchy_schwarz_bound
      params strategy family G hG hbound_psd hbound_dom
      (gCommStabilityTwoR params family G x) x
      (gCommStabilityTwoR_first_factor_le_one params strategy hnorm family G x)

/-- Direct boundedness proof for the second paper scalar stability estimate.

This is the `Z^x` boundedness half of
`references/ldt-paper/commutativity-G.tex`, `clm:g-comm-stability2` (lines
185--221), after the right-register point-commutation transport and after the
`b`-indexed left-register sandwich is collapsed into
`gCommStabilityTwoScalarDefect`.  It bounds the post-transport mirror scalar by
`√ζ`.  The separate `6√(γ(m+1))` transport loss is not proved here; a full
paper-budget theorem must combine this post-transport bound with the distinct
`commutativityPoints` transport estimate. -/
theorem gCommStabilityTwo_scalar
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (hbound_psd : ∀ x : Fq params, 0 ≤ family.witness x)
    (hbound_residual :
      avgOver (uniformDistribution (Fq params))
        (fun x => IdxPolyFamily.storedResidual strategy family G x) ≤ zeta)
    (hbound_dom :
      ∀ x : Fq params, ∀ g : Polynomial params,
        IdxPolyFamily.averagedSlicePointEvaluationOperator strategy x g ≤ family.witness x) :
    |avgOver (uniformDistribution (Fq params))
      (gCommStabilityTwoScalarDefect params strategy family G)| ≤ Real.sqrt zeta := by
  have h𝒟 :
      ∑ x ∈ (uniformDistribution (Fq params)).support,
        (uniformDistribution (Fq params)).weight x ≤ 1 := by
    simpa using uniformDistribution_weight_sum_le_one (Fq params)
  calc
    |avgOver (uniformDistribution (Fq params))
        (gCommStabilityTwoScalarDefect params strategy family G)|
      ≤ Real.sqrt
          (avgOver (uniformDistribution (Fq params))
            (fun x => IdxPolyFamily.storedResidual strategy family G x)) := by
          exact
            MIPStarRE.LDT.Preliminaries.avgOver_abs_le_sqrt_of_pointwise
              (uniformDistribution (Fq params))
              (gCommStabilityTwoScalarDefect params strategy family G)
              (fun x => IdxPolyFamily.storedResidual strategy family G x)
              (gCommStabilityTwo_scalar_pointwise_bound
                params strategy hnorm family G hG hbound_psd hbound_dom)
              (storedResidual_nonneg
                params strategy family G hbound_psd)
              h𝒟
    _ ≤ Real.sqrt zeta := by
          exact Real.sqrt_le_sqrt hbound_residual

end MIPStarRE.LDT.Commutativity
