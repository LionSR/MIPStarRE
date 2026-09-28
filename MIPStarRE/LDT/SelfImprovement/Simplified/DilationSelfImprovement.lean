import MIPStarRE.LDT.SelfImprovement.Simplified.Residual
import MIPStarRE.LDT.Preliminaries.BipartiteSelfConsistency.Core

/-!
# Simplified self-improvement through simultaneous dilation

The filtered SDP output is dilated directly to a projective
submeasurement. Its completeness, point consistency, strong
self-consistency, and residual estimates transfer to the enlarged
register without a rounding loss.

## References

- `blueprint/src/low_degree_simplified.tex`,
  `thm:self-improvement-in-induction-section`.
- `references/ldt-paper/self_improvement.tex`, `thm:self-improvement`.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

universe u

/-- The projective Naimark dilation of one filtered polynomial
submeasurement, using `Option (Polynomial params)` as a fixed ancilla. -/
noncomputable def filteredProjectiveDilation
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (H : SubMeas (Polynomial params) ι) :
    ProjSubMeas (Polynomial params) (ι × Option (Polynomial params)) :=
  simultaneousDilationFamily (fun _ : Unit => H) ()

/-- The filtered mass is exactly the mass of its projective dilation
on the enlarged bipartite state. -/
theorem filteredProjectiveDilation_mass
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (H : SubMeas (Polynomial params) ι) :
    subMeasMass ψ H.liftLeft =
      subMeasMass
        (simultaneousDilationState (Outcome := Polynomial params) ψ)
        (filteredProjectiveDilation params H).toSubMeas.liftLeft := by
  exact dilated_slice_total_mass ψ (fun _ : Unit => H) ()

/-- Point-answer consistency survives the projective dilation of the
filtered polynomial submeasurement. -/
theorem filteredProjectiveDilation_pointConsistency
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (A : IdxSubMeas (Point params) (Fq params) ι)
    (H : SubMeas (Polynomial params) ι)
    (δ : Error)
    (hcons : ConsRel ψ (uniformDistribution (Point params)) A
      (polynomialEvaluationFamily params H) δ) :
    ConsRel
      (simultaneousDilationState (Outcome := Polynomial params) ψ)
      (uniformDistribution (Point params))
      (fun u => leftPlacedSubMeas (ιB := Option (Polynomial params)) (A u))
      (polynomialEvaluationFamily params
        (filteredProjectiveDilation params H).toSubMeas) δ := by
  have h := dilated_postprocessed_consistency
    ψ (uniformDistribution (Point params)) A
    (fun _ : Unit => H) (fun _ => ()) (fun u g => g u)
  constructor
  change bipartiteConsError
      (simultaneousDilationState (Outcome := Polynomial params) ψ)
      (uniformDistribution (Point params))
      (fun u => leftPlacedSubMeas (ιB := Option (Polynomial params)) (A u))
      (fun u => postprocess (filteredProjectiveDilation params H).toSubMeas
        (fun g => g u)) ≤ δ
  have hbound : bipartiteConsError ψ (uniformDistribution (Point params)) A
      (fun u => postprocess H (fun g => g u)) ≤ δ :=
    hcons.offDiagonalBound
  simpa [filteredProjectiveDilation] using (h ▸ hbound)

/-- The filtered strong self-consistency bound becomes a mirror-distance
bound after dilation because the dilated effects are projective. -/
theorem filteredProjectiveDilation_selfConsistency
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (H : SubMeas (Polynomial params) ι)
    (δ : Error)
    (hssc : BipartiteSSCRel ψ (uniformDistribution Unit)
      (constSubMeasFamily H) δ) :
    SDDRel
      (simultaneousDilationState (Outcome := Polynomial params) ψ)
      (uniformDistribution Unit)
      (IdxSubMeas.liftLeft
        (constSubMeasFamily (filteredProjectiveDilation params H).toSubMeas))
      (IdxSubMeas.liftRight
        (constSubMeasFamily (filteredProjectiveDilation params H).toSubMeas))
      (2 * δ) := by
  have hssc' : BipartiteSSCRel
      (simultaneousDilationState (Outcome := Polynomial params) ψ)
      (uniformDistribution Unit)
      (constSubMeasFamily (filteredProjectiveDilation params H).toSubMeas)
      δ := by
    constructor
    have heq : bipartiteSSCError ψ (uniformDistribution Unit)
        (constSubMeasFamily H) =
      bipartiteSSCError
        (simultaneousDilationState (Outcome := Polynomial params) ψ)
        (uniformDistribution Unit)
        (constSubMeasFamily (filteredProjectiveDilation params H).toSubMeas) := by
      unfold bipartiteSSCError
      apply avgOver_congr
      intro _
      exact dilated_qBipartiteSSCDefect ψ (fun _ : Unit => H) ()
    rw [← heq]
    exact hssc.overlapBound
  exact MIPStarRE.LDT.Preliminaries.twoNotionsOfSelfConsistency
    (simultaneousDilationState (Outcome := Polynomial params) ψ)
    (uniformDistribution Unit)
    (constSubMeasFamily (filteredProjectiveDilation params H).toSubMeas)
    δ ⟨simultaneousDilationState_permInvState ψ hfix, hssc'⟩

/-- The filtered helper gap bounds the dilated projective residual at
the same error parameter. -/
theorem filteredProjectiveDilation_residual
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (δ : Error)
    (hdual : ∀ h : Polynomial params,
      0 ≤ sdpDualSlackOperator params strategy Z h)
    (hgap : helperBoundednessGap params strategy H Z ≤ δ) :
    ev (simultaneousDilationState (Outcome := Polynomial params) strategy.state)
      (opTensor (leftTensor (ι₂ := Option (Polynomial params)) Z)
        (1 - (filteredProjectiveDilation params H).toSubMeas.total)) ≤ δ := by
  have hres := filtered_residual_le_helper_gap params strategy H Z hdual
  have hpres := dilated_filtered_residual
    strategy.state (fun _ : Unit => H) () Z
  calc
    ev (simultaneousDilationState (Outcome := Polynomial params) strategy.state)
        (opTensor (leftTensor (ι₂ := Option (Polynomial params)) Z)
          (1 - (filteredProjectiveDilation params H).toSubMeas.total)) =
      ev strategy.state (opTensor Z (1 - H.total)) := hpres.symm
    _ ≤ helperBoundednessGap params strategy H Z := hres
    _ ≤ δ := hgap

/-- The averaged point operator is extended by the auxiliary identity
when the strategy is extended. -/
theorem extendSymStrat_averagedPointOperator
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    (g : Polynomial params) :
    averagedPointOperator params
      (extendSymStrat params strategy (Polynomial params)) g =
      leftTensor (ι₂ := Option (Polynomial params))
        (averagedPointOperator params strategy g) := by
  unfold averagedPointOperator
  rw [leftTensor_averageOperatorOverDistribution]
  apply averageOperatorOverDistribution_congr
  intro x
  rfl

/-- The simplified self-improvement error
`200 m (√ε + √δ + √(d/q))`. -/
noncomputable def selfImprovementDilationError
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error) : Error :=
  200 * (params.m : Error) *
    (Real.rpow eps (1 / (2 : Error)) +
      Real.rpow delta (1 / (2 : Error)) +
      Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (2 : Error)))

/-- The dilation error is twice the filtered helper error. -/
theorem selfImprovementDilationError_eq_two_helper
    (params : Parameters) [FieldModel params.q]
    (eps delta : Error) :
    selfImprovementDilationError params eps delta =
      2 * selfImprovementHelperError params eps delta := by
  unfold selfImprovementDilationError selfImprovementHelperError
  ring

/-- The four conclusions of self-improvement with dilation. The
ancilla and the projective polynomial submeasurement are concrete:
the ancilla is indexed by `Option (Polynomial params)`. -/
structure DilationSelfImprovementConclusion
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    (H : ProjSubMeas (Polynomial params) (ι × Option (Polynomial params)))
    (Z : MIPStarRE.Quantum.Op (ι × Option (Polynomial params)))
    (eps delta nu : Error) : Prop where
  /-- The seed consistency error moves into incompleteness. -/
  completeness :
    CompletenessAtLeast
      (extendSymStrat params strategy (Polynomial params)).state
      H.toSubMeas.liftLeft
      ((1 - nu) - selfImprovementDilationError params eps delta)
  /-- The projective output remains consistent with the point
  measurements extended by the auxiliary identity. -/
  pointConsistency :
    ConsRel (extendSymStrat params strategy (Polynomial params)).state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas
        (extendSymStrat params strategy (Polynomial params)).pointMeasurement)
      (polynomialEvaluationFamily params H.toSubMeas)
      (selfImprovementDilationError params eps delta)
  /-- The projective output has the required mirror-distance bound. -/
  strongSelfConsistency :
    SDDRel (extendSymStrat params strategy (Polynomial params)).state
      (uniformDistribution Unit)
      (IdxSubMeas.liftLeft (constSubMeasFamily H.toSubMeas))
      (IdxSubMeas.liftRight (constSubMeasFamily H.toSubMeas))
      (selfImprovementDilationError params eps delta)
  /-- The dual witness is positive semidefinite. -/
  witness_nonneg : 0 ≤ Z
  /-- The dual witness is a contraction. -/
  witness_le_one : Z ≤ 1
  /-- The dual witness dominates every averaged point effect. -/
  witness_domination : ∀ g : Polynomial params,
    averagedPointOperator params
      (extendSymStrat params strategy (Polynomial params)) g ≤ Z
  /-- The witness has small residual against the projective output. -/
  residual :
    ev (extendSymStrat params strategy (Polynomial params)).state
      (opTensor Z (1 - H.toSubMeas.total)) ≤
      selfImprovementDilationError params eps delta

/-- Self-improvement with one common Naimark ancilla, at the
`200 m (√ε + √δ + √(d/q))` error of the simplified proof.

Paper origin: `blueprint/src/low_degree_simplified.tex`,
`thm:self-improvement-in-induction-section`; the filtered construction
uses `references/ldt-paper/self_improvement.tex`, `thm:self-improvement`.
The seed consistency parameter occurs only in the completeness bound. -/
theorem selfImprovementWithDilation
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    ∃ H : ProjSubMeas (Polynomial params) (ι × Option (Polynomial params)),
      ∃ Z : MIPStarRE.Quantum.Op (ι × Option (Polynomial params)),
        DilationSelfImprovementConclusion params strategy H Z eps delta nu := by
  letI : Nonempty ι := strategy.isNormalized.nonempty.map Prod.fst
  obtain ⟨H₀, Z₀, hhelper, hZle, _hZsq⟩ :=
    self_improvement_helper_with_contraction
      params strategy eps delta gamma hgood nu G hcons
  let P := filteredProjectiveDilation params H₀
  let Z := leftTensor (ι₂ := Option (Polynomial params)) Z₀
  have hζ : 0 ≤ selfImprovementHelperError params eps delta :=
    selfImprovementHelperError_nonneg params eps delta
  have hζtwo : selfImprovementHelperError params eps delta ≤
      selfImprovementDilationError params eps delta := by
    rw [selfImprovementDilationError_eq_two_helper]
    linarith
  refine ⟨P, Z, ?_⟩
  refine {
    completeness := ?_
    pointConsistency := ?_
    strongSelfConsistency := ?_
    witness_nonneg := ?_
    witness_le_one := ?_
    witness_domination := ?_
    residual := ?_ }
  · constructor
    have hmass := filteredProjectiveDilation_mass params strategy.state H₀
    have hsource := hhelper.completeness.lowerBound
    change subMeasMass strategy.state H₀.liftLeft ≥
      (1 - nu) - selfImprovementHelperError params eps delta at hsource
    change subMeasMass
      (simultaneousDilationState (Outcome := Polynomial params) strategy.state)
      P.toSubMeas.liftLeft ≥
        (1 - nu) - selfImprovementDilationError params eps delta
    rw [← hmass]
    linarith
  · have hpoint := filteredProjectiveDilation_pointConsistency
      params strategy.state
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      H₀ (selfImprovementHelperError params eps delta)
      hhelper.pointConsistency
    change ConsRel
      (simultaneousDilationState (Outcome := Polynomial params) strategy.state)
      (uniformDistribution (Point params))
      (fun u => leftPlacedSubMeas (ιB := Option (Polynomial params))
        ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u))
      (polynomialEvaluationFamily params P.toSubMeas)
      (selfImprovementDilationError params eps delta)
    exact ConsRel.mono hζtwo hpoint
  · have hself := filteredProjectiveDilation_selfConsistency
      params strategy.state strategy.densityFixed H₀
      (selfImprovementHelperError params eps delta)
      hhelper.strongSelfConsistency
    change SDDRel
      (simultaneousDilationState (Outcome := Polynomial params) strategy.state)
      (uniformDistribution Unit)
      (IdxSubMeas.liftLeft (constSubMeasFamily P.toSubMeas))
      (IdxSubMeas.liftRight (constSubMeasFamily P.toSubMeas))
      (selfImprovementDilationError params eps delta)
    rw [selfImprovementDilationError_eq_two_helper]
    exact hself
  · exact leftTensor_nonneg hhelper.positiveSemidefiniteWitness
  · simpa [Z, leftTensor_one] using
      (leftTensor_mono (ι₂ := Option (Polynomial params)) hZle)
  · intro g
    have hdual : averagedPointOperator params strategy g ≤ Z₀ := by
      exact sub_nonneg.mp (by
        simpa [sdpDualSlackOperator] using
          hhelper.dualDominatesAveragedPoint g)
    rw [extendSymStrat_averagedPointOperator]
    exact leftTensor_mono hdual
  · have hres := filteredProjectiveDilation_residual
      params strategy H₀ Z₀ (selfImprovementHelperError params eps delta)
      hhelper.dualDominatesAveragedPoint hhelper.boundednessGap
    exact le_trans hres hζtwo

/-- The dilation construction only uses the axis-parallel and point
self-consistency tests. This form supports answer-valued restricted
strategies, whose diagonal measurement is carried separately. -/
theorem selfImprovementWithDilation_of_axisParallel_selfConsistency
    (params : Parameters) [FieldModel params.q]
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (strategy : SymStrat params ι)
    (eps delta nu : Error)
    (haxis : strategy.axisParallelFailureProbability ≤ eps)
    (hself : strategy.selfConsistencyFailureProbability ≤ delta)
    (G : Measurement (Polynomial params) ι)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    ∃ H : ProjSubMeas (Polynomial params) (ι × Option (Polynomial params)),
      ∃ Z : MIPStarRE.Quantum.Op (ι × Option (Polynomial params)),
        DilationSelfImprovementConclusion params strategy H Z eps delta nu := by
  let gamma₀ : Error := strategy.diagonalFailureProbability
  have hgood₀ : strategy.IsGood eps delta gamma₀ :=
    { axisParallelTest := haxis
      selfConsistencyTest := hself
      diagonalLineTest := le_rfl }
  exact selfImprovementWithDilation params strategy eps delta gamma₀ nu hgood₀ G hcons

end MIPStarRE.LDT.SelfImprovement
