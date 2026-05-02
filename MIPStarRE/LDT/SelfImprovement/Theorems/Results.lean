import MIPStarRE.LDT.GlobalVariance.Theorems.Results
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements

/-!
# Section 9 — Self-improvement theorem wrappers

Reduced theorem wrappers for the self-improvement pipeline.

## References

- `references/ldt-paper/self_improvement.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Reduced theorem wrappers -/

private lemma averagedPointOperator_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (g : Polynomial params) :
    averagedPointOperator params strategy g ≤ 1 := by
  let A : SubMeas Unit ι :=
    averageUnitSubMeas (ι := ι)
      (pointConditionedOutcomeOperatorAtPolynomial params strategy g)
      (fun u => by
        simpa [pointConditionedOutcomeOperatorAtPolynomial] using
          (strategy.pointMeasurement u).outcome_pos (g u))
      (fun u => by
        simpa [pointConditionedOutcomeOperatorAtPolynomial] using
          Measurement.outcome_le_one (strategy.pointMeasurement u).toMeasurement (g u))
  simpa [A, averagedPointOperator, averageUnitSubMeas_outcome] using A.outcome_le_one ()

private lemma bipartiteSSCRel_uniform_const
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas Outcome ι) (δ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit) (constSubMeasFamily A) δ →
      BipartiteSSCRel ψ (uniformDistribution Question) (fun _ : Question => A) δ := by
  intro hssc
  rcases hssc with ⟨hssc⟩
  constructor
  simpa [bipartiteSSCError, avgOver, uniformDistribution, constSubMeasFamily] using hssc

private lemma sddRel_uniform_const
    {κ Question Outcome : Type*}
    [Fintype κ] [DecidableEq κ]
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (ψ : QuantumState κ)
    (A B : SubMeas Outcome κ) (δ : Error) :
    SDDRel ψ (uniformDistribution Unit) (constSubMeasFamily A) (constSubMeasFamily B) δ →
      SDDRel ψ (uniformDistribution Question) (fun _ : Question => A)
        (fun _ : Question => B) δ := by
  intro hsdd
  rcases hsdd with ⟨hsdd⟩
  constructor
  simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily] using hsdd

private lemma ev_opTensor_averageOperatorOverDistribution_left {α : Type*}
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution α)
    (A : α → MIPStarRE.Quantum.Op ι) (B : MIPStarRE.Quantum.Op ι) :
    ev ψ (opTensor (averageOperatorOverDistribution 𝒟 A) B) =
      avgOver 𝒟 (fun a => ev ψ (opTensor (A a) B)) := by
  classical
  unfold averageOperatorOverDistribution avgOver
  rw [opTensor_sum_left_finset]
  rw [ev_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [opTensor_smul_left_error]
  exact ev_real_smul ψ (𝒟.weight a) (opTensor (A a) B)

/-- Reduced version of `lem:sdp`.

This reduced wrapper now instantiates the paper's explicit Slater witnesses: the
primal uses the uniform strict-feasible submeasurement
`T_g = (2 |\polyfunc{m}{q}{d}|)^{-1} I`, canonically completed at the zero
polynomial to fit the downstream `Measurement` interface, and the dual uses
`Z = 2I`. The paper's strong-duality and complementary-slackness conclusions are
still omitted from the current Lean statement. -/
lemma sdp
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    SdpStatement params strategy := by
  let T : Measurement (Polynomial params) ι := sdpPrimalWitness (ι := ι) params
  let Z : MIPStarRE.Quantum.Op ι := sdpStrictDualWitness (ι := ι)
  refine ⟨T.toSubMeas, Z, ?_⟩
  refine
    { primalTotalOperator := T.total_eq_one
      dualPositive := by
        simp [Z]
      dualFeasible := ?_ }
  intro g
  simpa [Z, sdpDualSlackOperator] using
    sub_nonneg.mpr
      (le_trans (averagedPointOperator_le_one params strategy g)
        (one_le_sdpStrictDualWitness (ι := ι)))

/-- Reduced version of `lem:add-in-u`.

This currently keeps only the global-variance consequence used downstream. It
now derives that consequence from the post-triangle six-step edge-transport
chain bound via `globalVarianceOfPointsFromTransportChainBound`. The `gamma` and
`hgood` arguments are intentionally retained so this reduced wrapper still
matches the surrounding self-improvement API and can be strengthened back to the
full paper statement without another caller-wide signature change. The
selection-dependent transfer inequality from the paper, together with its
dependence on an auxiliary family `M` and the averaged family `H`, is not yet
formalized here. -/
lemma addInU
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (T : Measurement (Polynomial params) ι) :
    AddInUStatement params strategy T eps delta := by
  refine
    { varianceBound := ?_ }
  let hglobalVariance :=
    globalVarianceOfPointsFromTransportChainBound params strategy eps delta gamma hgood
      T.toSubMeas
      (localVarianceTransportChainBound params strategy eps delta gamma hgood T.toSubMeas)
  simpa [selfImprovementVarianceError] using
    hglobalVariance.averagedGlobalVarianceBound

/-- The diagonal selection used in the strong-self-consistency application of
`lem:add-in-u` in the proof of `lem:self-improvement-helper`.

At every point `u`, this selects exactly the pairs `(h, h)` of polynomial
outcomes, matching `self_improvement.tex`, lines 459--468. -/
noncomputable def selfConsistencyAddInUSelection (params : Parameters)
    [FieldModel params.q] : AddInUSelection params (Polynomial params) :=
  fun _ => {hh | hh.1 = hh.2}

private lemma addInULeftOperatorAtPoint_selfConsistencySelection
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) (Polynomial params) ι)
    (H : SubMeas (Polynomial params) ι)
    (u : Point params) :
    addInULeftOperatorAtPoint params strategy M H (selfConsistencyAddInUSelection params) u =
      ∑ h : Polynomial params, opTensor ((M u).outcome h) (H.outcome h) := by
  classical
  unfold addInULeftOperatorAtPoint selfConsistencyAddInUSelection addInUSelectionPairs
  symm
  refine Finset.sum_bij (fun h _ => (h, h)) ?_ ?_ ?_ ?_
  · intro h _
    simp
  · intro a _ _ _ hab
    exact congrArg Prod.fst hab
  · intro ah hah
    refine ⟨ah.1, Finset.mem_univ _, ?_⟩
    simp at hah
    ext <;> simp [hah]
  · intro h _
    simp

private lemma addInURightOperatorAtPoint_selfConsistencySelection
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) (Polynomial params) ι)
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) :
    addInURightOperatorAtPoint params strategy M T (selfConsistencyAddInUSelection params) u =
      ∑ h : Polynomial params,
        let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
        opTensor (Au * (M u).outcome h * Au) (T.outcome h) := by
  classical
  unfold addInURightOperatorAtPoint selfConsistencyAddInUSelection addInUSelectionPairs
  symm
  refine Finset.sum_bij (fun h _ => (h, h)) ?_ ?_ ?_ ?_
  · intro h _
    simp
  · intro a _ _ _ hab
    exact congrArg Prod.fst hab
  · intro ah hah
    refine ⟨ah.1, Finset.mem_univ _, ?_⟩
    simp at hah
    ext <;> simp [hah]
  · intro h _
    simp

/-- The left side of the diagonal `add-in-u` application in the helper
strong-self-consistency proof is exactly the diagonal bipartite match mass of
`Hhat = E_u H^u`.

This formalizes the paper's identity
`∑_h ⟪H_h, H_h⟫ = E_u ∑_h ⟪H^u_h, H_h⟫` used at
`self_improvement.tex`, lines 455--468. -/
lemma addInULeftQuantity_selfConsistencySelection_eq_matchMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInULeftQuantity params strategy
        (sandwichedPolynomialSubMeasAt params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (selfConsistencyAddInUSelection params) =
      qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) := by
  classical
  change avgOver (uniformDistribution (Point params)) (fun u =>
      ev strategy.state (addInULeftOperatorAtPoint params strategy
        (sandwichedPolynomialSubMeasAt params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (selfConsistencyAddInUSelection params) u)) = _
  rw [avgOver_congr (uniformDistribution (Point params)) _
    (fun u => ∑ h : Polynomial params,
      ev strategy.state (opTensor
        ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
        ((averagedSandwichedPolynomialSubMeas params strategy T).outcome h))) ?_]
  · rw [avgOver_sum]
    unfold qBipartiteMatchMass averagedSandwichedPolynomialSubMeas
    refine Finset.sum_congr rfl ?_
    intro h _
    rw [ev_opTensor_averageOperatorOverDistribution_left]
    simp [sandwichedPolynomialSubMeasAt]
  · intro u
    rw [addInULeftOperatorAtPoint_selfConsistencySelection]
    exact ev_sum strategy.state _

/-- The right side of the diagonal `add-in-u` application is the paper's
"release-the-kraken" expression, with the two copies of
`A^u_{h(u)}` placed around the pointwise helper submeasurement `H^u_h`. -/
lemma addInURightQuantity_selfConsistencySelection_eq_release
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInURightQuantity params strategy
        (sandwichedPolynomialSubMeasAt params strategy T)
        T
        (selfConsistencyAddInUSelection params) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
          ev strategy.state
            (opTensor (Au * (sandwichedPolynomialSubMeasAt params strategy T u).outcome h * Au)
              (T.outcome h))) := by
  classical
  change avgOver (uniformDistribution (Point params)) (fun u =>
      ev strategy.state (addInURightOperatorAtPoint params strategy
        (sandwichedPolynomialSubMeasAt params strategy T)
        T
        (selfConsistencyAddInUSelection params) u)) = _
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  rw [addInURightOperatorAtPoint_selfConsistencySelection]
  exact ev_sum strategy.state _

/-- Specialization of the missing full `add-in-u` transfer to the diagonal
selection needed for helper strong self-consistency.

The hypothesis is exactly the scalar transfer inequality supplied by the paper's
`lem:add-in-u` after choosing `M^u = H^u` and
`S_u = {(h,h) : h ∈ \polyfunc{m}{q}{d}}`. The conclusion rewrites that
transfer into the paper's displayed step `eq:release-the-kraken`; the remaining
work for #931 is to prove the hypothesis from the full Cauchy--Schwarz/global
variance argument, not to assume `HelperStrongSelfConsistencyInput`. -/
lemma selfConsistencyDiagonalAddInU_of_transfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (htransfer :
      |addInULeftQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T)
          (averagedSandwichedPolynomialSubMeas params strategy T)
          (selfConsistencyAddInUSelection params) -
        addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T)
          T
          (selfConsistencyAddInUSelection params)| ≤ addInUError params eps delta) :
    |qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
          ev strategy.state
            (opTensor (Au * (sandwichedPolynomialSubMeasAt params strategy T u).outcome h * Au)
              (T.outcome h)))| ≤ addInUError params eps delta := by
  simpa [addInULeftQuantity_selfConsistencySelection_eq_matchMass,
    addInURightQuantity_selfConsistencySelection_eq_release] using htransfer

/-- Projective sandwich collapse: if `A * A = A`, then `A * (A * X * A) * A = A * X * A`.

This is the operator-algebra fact used to simplify the diagonal `add-in-u`
right-hand side: the outer `A^u_{h(u)}` factors collapse into the inner
sandwich `A^u_{h(u)} T_h A^u_{h(u)}` because
`(strategy.pointMeasurement u).proj` makes every point-measurement outcome a
projection. -/
private lemma proj_outer_sandwich_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A X : MIPStarRE.Quantum.Op ι) (hA : A * A = A) :
    A * (A * X * A) * A = A * X * A := by
  have h1 : A * (A * X * A) * A = (A * A) * X * (A * A) := by noncomm_ring
  rw [h1, hA]

/-- Projective simplification of the diagonal `add-in-u` right operator at a point.

Combining `addInURightOperatorAtPoint_selfConsistencySelection` with the
projectivity of `strategy.pointMeasurement` (each `A^u_a * A^u_a = A^u_a`),
the at-point operator collapses to the simpler tensor sum
`Σ_h H^u_h ⊗ T_h` where `H^u_h = sandwichedPolynomialSubMeasAt T u h`. -/
private lemma addInURightOperatorAtPoint_selfConsistencySelection_proj_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) :
    addInURightOperatorAtPoint params strategy
        (sandwichedPolynomialSubMeasAt params strategy T)
        T
        (selfConsistencyAddInUSelection params) u =
      ∑ h : Polynomial params,
        opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
          (T.outcome h) := by
  classical
  rw [addInURightOperatorAtPoint_selfConsistencySelection]
  refine Finset.sum_congr rfl ?_
  intro h _
  -- Unfold the `let Au := ...` binder produced by
  -- `addInURightOperatorAtPoint_selfConsistencySelection` so that we can
  -- expand the inner sandwich `(M u).outcome h = Au * T_h * Au`.
  show opTensor
      (pointConditionedOutcomeOperatorAtPolynomial params strategy h u *
        ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h) *
        pointConditionedOutcomeOperatorAtPolynomial params strategy h u)
      (T.outcome h) = _
  have hproj :
      pointConditionedOutcomeOperatorAtPolynomial params strategy h u *
        pointConditionedOutcomeOperatorAtPolynomial params strategy h u =
      pointConditionedOutcomeOperatorAtPolynomial params strategy h u := by
    simpa [pointConditionedOutcomeOperatorAtPolynomial] using
      (strategy.pointMeasurement u).proj (h u)
  have hsandwich :
      (sandwichedPolynomialSubMeasAt params strategy T u).outcome h =
        pointConditionedOutcomeOperatorAtPolynomial params strategy h u *
          T.outcome h *
          pointConditionedOutcomeOperatorAtPolynomial params strategy h u := by
    rfl
  rw [hsandwich]
  congr 1
  exact proj_outer_sandwich_eq _ _ hproj

/-- Projective simplification of the diagonal `add-in-u` right quantity.

This is the projection-collapsed paper expression: the two outer
`A^u_{h(u)}` factors absorb into the inner sandwich `H^u_h = A^u_{h(u)}
T_h A^u_{h(u)}`, leaving the cleaner form
`E_u Σ_h ⟨ψ, H^u_h ⊗ T_h ψ⟩` used in the simplified scalar transfer. -/
lemma addInURightQuantity_selfConsistencySelection_eq_simplified
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInURightQuantity params strategy
        (sandwichedPolynomialSubMeasAt params strategy T)
        T
        (selfConsistencyAddInUSelection params) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h))) := by
  classical
  change avgOver (uniformDistribution (Point params)) (fun u =>
      ev strategy.state (addInURightOperatorAtPoint params strategy
        (sandwichedPolynomialSubMeasAt params strategy T)
        T
        (selfConsistencyAddInUSelection params) u)) = _
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  rw [addInURightOperatorAtPoint_selfConsistencySelection_proj_eq]
  exact ev_sum strategy.state _

/-- Specialization of `selfConsistencyDiagonalAddInU_of_transfer` to the
projection-simplified scalar transfer hypothesis.

Compared to `selfConsistencyDiagonalAddInU_of_transfer`, the hypothesis is
stated against the cleaner right-hand side `E_u Σ_h ⟨ψ, H^u_h ⊗ T_h ψ⟩`
obtained after collapsing the outer projection factors of
`eq:release-the-kraken` via `proj_outer_sandwich_eq`. The conclusion is
identical and can therefore feed the same diagonal helper-SSC application;
the simplification reduces the remaining Cauchy--Schwarz/global-variance
proof obligation (`self_improvement.tex:247--343`) to a transfer in the
simpler shape. -/
lemma selfConsistencyDiagonalAddInU_of_simplifiedTransfer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (htransfer :
      |qBipartiteMatchMass strategy.state
          (averagedSandwichedPolynomialSubMeas params strategy T)
          (averagedSandwichedPolynomialSubMeas params strategy T) -
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h : Polynomial params,
            ev strategy.state
              (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                (T.outcome h)))| ≤ addInUError params eps delta) :
    |qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
          ev strategy.state
            (opTensor (Au * (sandwichedPolynomialSubMeasAt params strategy T u).outcome h * Au)
              (T.outcome h)))| ≤ addInUError params eps delta := by
  -- Both RHS shapes are equal to the underlying `addInURightQuantity`, so the
  -- full paper RHS (`eq:release-the-kraken`) equals the projection-collapsed
  -- RHS used in `htransfer`.
  have hRHS_eq :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h u
          ev strategy.state
            (opTensor (Au * (sandwichedPolynomialSubMeasAt params strategy T u).outcome h * Au)
              (T.outcome h)))
        = avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h : Polynomial params,
            ev strategy.state
              (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                (T.outcome h))) :=
    (addInURightQuantity_selfConsistencySelection_eq_release
        params strategy T).symm.trans
      (addInURightQuantity_selfConsistencySelection_eq_simplified
        params strategy T)
  rw [hRHS_eq]
  exact htransfer

/-- Reduced version of `lem:self-improvement-helper`.

Unlike the paper helper lemma, this theorem does not yet take the consistency
error `nu` or a hypothesis `hcons`. The current
`SelfImprovementHelperConclusion` only packages the outputs produced directly by
the reduced `sdp` + `addInU` pipeline, and those facts do not depend on the
consistency hypothesis. The `nu`-dependent consistency information will be
threaded back in when the full pipeline is assembled in `selfImprovement`. -/
lemma selfImprovementHelper
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (_nu : Error)
    -- Kept for API compatibility with the full helper statement, where future
    -- proof obligations will depend on the incoming polynomial measurement.
    (_G : Measurement (Polynomial params) ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ H : SubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
        SelfImprovementHelperConclusion params strategy T H Z eps delta := by
  obtain ⟨Tsub, Z, hsdp⟩ := (sdp params strategy).witness
  let T : Measurement (Polynomial params) ι :=
    { toSubMeas := Tsub
      total_eq_one := hsdp.primalTotalOperator }
  let Hhat : SubMeas (Polynomial params) ι :=
    averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas
  refine ⟨T, Hhat, Z, ?_⟩
  refine
    { sdpWitness := ?_
      averagedConstruction := rfl
      addInUVarianceBound := ?_
      positiveSemidefiniteWitness := hsdp.dualPositive
      dualDominatesAveragedPoint := hsdp.dualFeasible }
  · simpa [T] using hsdp
  · exact addInU params strategy eps delta gamma hgood T

/-- `thm:self-improvement`.

The remaining Section 5/8/9 obligations are exposed as explicit theorem
hypotheses, rather than bundled behind a dedicated bridge-package structure. The
evaluation-map data-processing step is now discharged internally using the
question-dependent preliminaries theorem. -/
theorem selfImprovement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hhelperStrongSelfConsistency :
      HelperStrongSelfConsistencyInput params strategy eps delta)
    (horthonormalization : OrthonormalizationInput params strategy eps delta)
    (hfinalFields : FinalFieldsInput params strategy eps delta nu)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu := by
  rcases selfImprovementHelper params strategy eps delta gamma hgood nu
      G with
    ⟨T, Hhat, Z, hhelper⟩
  have hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta) :=
    hhelperStrongSelfConsistency hhelper
  have horthBridge :
      MakingMeasurementsProjective.OrthonormalizationInput strategy.state Hhat
        (selfImprovementHelperError params eps delta) :=
    horthonormalization hssc
  rcases orthonormalization strategy.state strategy.permInvState strategy.isNormalized
      Hhat
      (selfImprovementHelperError params eps delta)
      hssc horthBridge with ⟨H, horth⟩
  have hsscPoint :
      BipartiteSSCRel strategy.state
        (uniformDistribution (Point params))
        (fun _ : Point params => Hhat)
        (selfImprovementHelperError params eps delta) :=
    bipartiteSSCRel_uniform_const strategy.state Hhat
      (selfImprovementHelperError params eps delta) hssc
  have horthPoint :
      SDDRel strategy.state
        (uniformDistribution (Point params))
        (fun _ : Point params => H.toSubMeas.liftLeft)
        (fun _ : Point params => Hhat.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta) := by
    apply sddRel_uniform_const (ψ := strategy.state)
    exact Preliminaries.sddRel_symm strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Hhat.liftLeft)
      (constSubMeasFamily H.toSubMeas.liftLeft)
      (selfImprovementOrthogonalizationError params eps delta) horth
  have hdata' :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        (selfImprovementDataProcessingError params eps delta) := by
    change SDDRel strategy.state (uniformDistribution (Point params))
      (IdxSubMeas.liftLeft (fun q => postprocess H.toSubMeas (fun h => h q)))
      (IdxSubMeas.liftLeft (fun q => postprocess Hhat (fun h => h q)))
      (8 * selfImprovementHelperError params eps delta +
        8 * Real.rpow (selfImprovementOrthogonalizationError params eps delta)
          (1 / (2 : Error)))
    simpa [Real.sqrt_eq_rpow] using
      Preliminaries.selfConsistencyImpliesDataProcessing
        strategy.state strategy.permInvState strategy.isNormalized
        (uniformDistribution (Point params))
        (uniformDistribution_weight_sum_le_one (Point params))
        (fun _ : Point params => Hhat)
        (fun _ : Point params => H)
        (selfImprovementHelperError params eps delta)
        (selfImprovementOrthogonalizationError params eps delta)
        (fun (u : Point params) (h : Polynomial params) => h u)
        hsscPoint horthPoint
  have hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        (selfImprovementDataProcessingError params eps delta) :=
    Preliminaries.sddRel_symm strategy.state (uniformDistribution (Point params))
      ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
      ((polynomialEvaluationFamily params Hhat).liftLeft)
      (selfImprovementDataProcessingError params eps delta) hdata'
  have hfinal :
      SelfImprovementFinalFields params strategy H Z eps delta nu :=
    hfinalFields hhelper horth hdata
  refine ⟨H, Z, ?_⟩
  exact
    { witness := ⟨T, Hhat, hhelper, horth, hdata⟩
      completeness := hfinal.completeness
      pointConsistency := hfinal.pointConsistency
      selfCloseness := hfinal.selfCloseness
      positiveSemidefiniteWitness := hhelper.positiveSemidefiniteWitness
      dualDominatesAveragedPoint := hhelper.dualDominatesAveragedPoint
      projectiveResidualBound := hfinal.projectiveResidualBound
      bounded := hfinal.bounded }

/--
Bridge from the measurement-input version in `self_improvement.tex` to the
submeasurement-input version used in `inductive_step.tex`.
-/
theorem selfImprovementFromSubMeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hhelperStrongSelfConsistency :
      HelperStrongSelfConsistencyInput params strategy eps delta)
    (horthonormalization : OrthonormalizationInput params strategy eps delta)
    (hfinalFields : FinalFieldsInput params strategy eps delta nu)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (Gmeas : Measurement (Polynomial params) ι)
    (hbridge : Gmeas.toSubMeas = G) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementSubMeasConclusion params strategy G H Z
        eps delta gamma nu := by
  rcases selfImprovement params strategy eps delta gamma nu
      hhelperStrongSelfConsistency
      horthonormalization hfinalFields hgood Gmeas
      with ⟨H, Z, hH⟩
  refine ⟨H, Z, ?_⟩
  exact
    { measurementBridge := ⟨Gmeas, hbridge, hH⟩ }

/-- `SelfImprovementBridgeInputs` + `IsGood` is sufficient to call
`selfImprovement` and obtain the full `SelfImprovementConclusion`. -/
theorem selfImprovementFromBridgeInputs
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hbridge : SelfImprovementBridgeInputs params strategy eps delta nu)
    (hgood : strategy.IsGood eps delta gamma)
    (G : Measurement (Polynomial params) ι) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementConclusion params strategy G H Z eps delta gamma nu :=
  selfImprovement params strategy eps delta gamma nu
    hbridge.helperStrongSelfConsistency
    hbridge.orthonormalization hbridge.finalFields hgood G

/-- `SelfImprovementBridgeInputs` + `IsGood` also suffice for the
submeasurement-input interface used by Section 6, once a measurement completion
of the input submeasurement is supplied explicitly. -/
theorem selfImprovementFromBridgeInputsSubMeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma nu : Error)
    (hinputs : SelfImprovementBridgeInputs params strategy eps delta nu)
    (hgood : strategy.IsGood eps delta gamma)
    (G : SubMeas (Polynomial params) ι)
    (Gmeas : Measurement (Polynomial params) ι)
    (hbridge : Gmeas.toSubMeas = G) :
    ∃ H : ProjSubMeas (Polynomial params) ι, ∃ Z : MIPStarRE.Quantum.Op ι,
      SelfImprovementSubMeasConclusion params strategy G H Z
        eps delta gamma nu :=
  selfImprovementFromSubMeas params strategy eps delta gamma nu
    hinputs.helperStrongSelfConsistency
    hinputs.orthonormalization hinputs.finalFields hgood G Gmeas hbridge

end MIPStarRE.LDT.SelfImprovement
