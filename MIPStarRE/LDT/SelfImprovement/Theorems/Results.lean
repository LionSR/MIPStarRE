import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.GlobalVariance.Theorems.Results
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds
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

private lemma ev_opTensor_averageOperatorOverDistribution_right {α : Type*}
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution α)
    (A : MIPStarRE.Quantum.Op ι) (B : α → MIPStarRE.Quantum.Op ι) :
    ev ψ (opTensor A (averageOperatorOverDistribution 𝒟 B)) =
      avgOver 𝒟 (fun a => ev ψ (opTensor A (B a))) := by
  unfold averageOperatorOverDistribution avgOver
  rw [opTensor_sum_right_finset]
  rw [ev_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [opTensor_smul_right_error]
  exact ev_real_smul ψ (𝒟.weight a) (opTensor A (B a))

private lemma ev_averageOperatorOverDistribution {α κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (ψ : QuantumState κ) (𝒟 : Distribution α)
    (A : α → MIPStarRE.Quantum.Op κ) :
    ev ψ (averageOperatorOverDistribution 𝒟 A) =
      avgOver 𝒟 (fun a => ev ψ (A a)) := by
  unfold averageOperatorOverDistribution avgOver
  rw [ev_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro a _
  exact ev_real_smul ψ (𝒟.weight a) (A a)

private lemma cons_rel_uniform_full_total_match_mass_lower_bound
    {Question Outcome : Type*}
    [Fintype Question] [DecidableEq Question] [Nonempty Question]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (A B : IdxSubMeas Question Outcome ι)
    (δ : Error)
    (hA_total : ∀ q : Question, (A q).total = 1)
    (hB_total : ∀ q : Question, (B q).total = 1)
    (hcons : ConsRel ψ (uniformDistribution Question) A B δ) :
    1 - δ ≤ avgOver (uniformDistribution Question)
      (fun q => qBipartiteMatchMass ψ (A q) (B q)) := by
  let 𝒟 := uniformDistribution Question
  let matchMass : Question → Error := fun q => qBipartiteMatchMass ψ (A q) (B q)
  have hdefect_point :
      ∀ q : Question,
        1 - matchMass q ≤ qBipartiteConsDefect ψ (A q) (B q) := by
    intro q
    unfold matchMass qBipartiteConsDefect
    have htotal :
        ev ψ (opTensor (A q).total (B q).total) = 1 := by
      simp [hA_total q, hB_total q, opTensor, ev_one_of_isNormalized ψ hψ]
    have hle :
        1 - qBipartiteMatchMass ψ (A q) (B q) ≤
          max 0 (1 - qBipartiteMatchMass ψ (A q) (B q)) :=
      le_max_right 0 _
    simp [htotal, hle]
  have havg_defect :
      avgOver 𝒟 (fun q => 1 - matchMass q) ≤ δ := by
    calc
      avgOver 𝒟 (fun q => 1 - matchMass q)
          ≤ avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q) (B q)) := by
            exact avgOver_mono 𝒟 _ _ hdefect_point
      _ = bipartiteConsError ψ 𝒟 A B := by rfl
      _ ≤ δ := hcons.offDiagonalBound
  have hconst : avgOver 𝒟 (fun _ : Question => (1 : Error)) = 1 := by
    simpa [𝒟] using (avgOver_uniform_const (α := Question) (c := (1 : Error)))
  have hneg :
      avgOver 𝒟 (fun q => -matchMass q) =
        -avgOver 𝒟 matchMass := by
    simpa [avgOver_const_mul, matchMass] using
      (avgOver_const_mul 𝒟 (-1) matchMass)
  have hsplit :
      avgOver 𝒟 (fun q => 1 - matchMass q) =
        1 - avgOver 𝒟 matchMass := by
    calc
      avgOver 𝒟 (fun q => 1 - matchMass q)
          = avgOver 𝒟 (fun q => (1 : Error) + (-matchMass q)) := by
            simp [sub_eq_add_neg]
      _ = avgOver 𝒟 (fun _ : Question => (1 : Error)) +
            avgOver 𝒟 (fun q => -matchMass q) := by
            rw [avgOver_add]
      _ = 1 - avgOver 𝒟 matchMass := by
            rw [hconst, hneg]
            ring
  rw [hsplit] at havg_defect
  linarith

/-- The incoming consistency of the original polynomial measurement gives the
matching-mass lower bound used in the helper-stage completeness proof.

This is the last step of the proof of
`references/ldt-paper/self_improvement.tex`, lines 407--414: after evaluating
the original input measurement `G` at a random point, `ConsRel ... nu` says the
off-diagonal mass is at most `nu`, hence the diagonal matching mass is at least
`1 - nu`. The blueprint mirror is
`blueprint/src/chapter/ch07_self_improvement.tex`, lines 137--142. -/
theorem input_consistency_match_mass_lower_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : Measurement (Polynomial params) ι)
    (nu : Error)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    1 - nu ≤
      avgOver (uniformDistribution (Point params)) (fun u =>
        qBipartiteMatchMass strategy.state
          ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
          ((polynomialEvaluationFamily params G.toSubMeas) u)) := by
  refine cons_rel_uniform_full_total_match_mass_lower_bound
    strategy.state strategy.isNormalized
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    (polynomialEvaluationFamily params G.toSubMeas) nu ?_ ?_ hcons
  · intro u
    exact (strategy.pointMeasurement u).total_eq_one
  · intro u
    simpa [polynomialEvaluationFamily, evaluateAt, postprocess_total] using G.total_eq_one

/-- Reindex the averaged input-consistency overlap as the SDP overlap
`Σ_g ⟨ψ, A_g ⊗ G_g⟩`.

This is the algebraic content of `references/ldt-paper/self_improvement.tex`,
lines 410--411: the pointwise match mass
`E_u Σ_a ⟨ψ, A^u_a ⊗ G_[g(u)=a] ψ⟩` is the same expression as
`Σ_g ⟨ψ, (E_u A^u_{g(u)}) ⊗ G_g ψ⟩`, after reindexing by the value of `g` at
`u`. The blueprint mirror is
`blueprint/src/chapter/ch07_self_improvement.tex`, lines 137--141. -/
theorem input_match_mass_eq_sdp_overlap
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        qBipartiteMatchMass strategy.state
          ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
          ((polynomialEvaluationFamily params G) u)) =
      ∑ g : Polynomial params,
        ev strategy.state
          (opTensor (averagedPointOperator params strategy g) (G.outcome g)) := by
  classical
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
        qBipartiteMatchMass strategy.state
          ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
          ((polynomialEvaluationFamily params G) u))
        =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ g : Polynomial params,
          ev strategy.state
            (opTensor (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
              (G.outcome g))) := by
        refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
        intro u
        symm
        calc
          ∑ g : Polynomial params,
              ev strategy.state
                (opTensor (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
                  (G.outcome g))
            =
          ∑ a : Fq params,
              ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
                ev strategy.state
                  (opTensor ((strategy.pointMeasurement u).outcome a) (G.outcome g)) := by
              rw [show ∑ g : Polynomial params,
                    ev strategy.state
                      (opTensor (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
                        (G.outcome g)) =
                  ∑ a : Fq params,
                    ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
                      ev strategy.state
                        (opTensor (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
                          (G.outcome g)) from by
                simpa using (Finset.sum_fiberwise Finset.univ
                  (fun g : Polynomial params => g u)
                  (fun g =>
                    ev strategy.state
                      (opTensor (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
                        (G.outcome g)))).symm]
              refine Finset.sum_congr rfl ?_
              intro a _
              refine Finset.sum_congr rfl ?_
              intro g hg
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
              simp [pointConditionedOutcomeOperatorAtPolynomial, hg]
          _ =
          ∑ a : Fq params,
              ev strategy.state
                (opTensor ((strategy.pointMeasurement u).outcome a)
                  (∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
                    G.outcome g)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [opTensor_sum_right_finset]
              exact (ev_finset_sum strategy.state _ _).symm
          _ =
          qBipartiteMatchMass strategy.state
            ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
            ((polynomialEvaluationFamily params G) u) := by
              unfold qBipartiteMatchMass polynomialEvaluationFamily evaluateAt postprocess
              refine Finset.sum_congr rfl ?_
              intro a _
              simp [IdxProjMeas.toIdxSubMeas]
              congr 4
    _ =
      ∑ g : Polynomial params,
        ev strategy.state
          (opTensor (averagedPointOperator params strategy g) (G.outcome g)) := by
        rw [avgOver_sum]
        refine Finset.sum_congr rfl ?_
        intro g _
        exact (ev_opTensor_averageOperatorOverDistribution_left strategy.state
          (uniformDistribution (Point params))
          (pointConditionedOutcomeOperatorAtPolynomial params strategy g)
          (G.outcome g)).symm

/-- Dual feasibility upper-bounds the SDP overlap by the dual mass
`⟨ψ, Z ⊗ I ψ⟩`.

This formalizes `references/ldt-paper/self_improvement.tex`, lines 408--410:
since `G` is a submeasurement, `Z ⊗ I` dominates `Z ⊗ G`, and since the SDP
dual is feasible, each `Z` dominates the averaged point operator
`E_u A^u_{g(u)}`. -/
theorem sdp_overlap_le_dual_mass
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hZ : 0 ≤ Z)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ sdpDualSlackOperator params strategy Z g) :
    (∑ g : Polynomial params,
        ev strategy.state
          (opTensor (averagedPointOperator params strategy g) (G.outcome g))) ≤
      ev strategy.state (leftTensor (ι₂ := ι) Z) := by
  classical
  calc
    (∑ g : Polynomial params,
        ev strategy.state
          (opTensor (averagedPointOperator params strategy g) (G.outcome g)))
        ≤
      ∑ g : Polynomial params,
        ev strategy.state (opTensor Z (G.outcome g)) := by
        refine Finset.sum_le_sum ?_
        intro g _
        apply ev_mono
        exact opTensor_mono_left
          (sub_nonneg.mp (by simpa [sdpDualSlackOperator] using hdual g))
          (G.outcome_pos g)
    _ = ev strategy.state (opTensor Z G.total) := by
        rw [← G.sum_eq_total]
        rw [opTensor_sum_right_univ]
        exact (ev_sum strategy.state _).symm
    _ ≤ ev strategy.state (leftTensor (ι₂ := ι) Z) := by
        exact ev_mono strategy.state _ _
          (opTensor_le_leftTensor hZ G.total_le_one)

/-- The input-consistency lower bound, after the SDP reindexing and dual
feasibility steps, gives the lower bound on the dual mass used in helper
completeness.

This packages `references/ldt-paper/self_improvement.tex`, lines 406--412,
without asserting the later Cauchy--Schwarz comparison from `Hhat` to `Z` or any
of the projective final-fields transport handled by PR #1071. -/
theorem input_consistency_dual_mass_lower_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : Measurement (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (nu : Error)
    (hZ : 0 ≤ Z)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ sdpDualSlackOperator params strategy Z g)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    1 - nu ≤ ev strategy.state (leftTensor (ι₂ := ι) Z) := by
  calc
    1 - nu
        ≤ avgOver (uniformDistribution (Point params)) (fun u =>
            qBipartiteMatchMass strategy.state
              ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
              ((polynomialEvaluationFamily params G.toSubMeas) u)) :=
          input_consistency_match_mass_lower_bound params strategy G nu hcons
    _ =
      ∑ g : Polynomial params,
        ev strategy.state
          (opTensor (averagedPointOperator params strategy g) (G.outcome g)) :=
          input_match_mass_eq_sdp_overlap params strategy G.toSubMeas
    _ ≤ ev strategy.state (leftTensor (ι₂ := ι) Z) :=
          sdp_overlap_le_dual_mass params strategy G.toSubMeas Z hZ hdual

/-- Exact `Hhat` reindexing for the helper-stage left-tensor mass.

Expanding `Hhat = E_u H^u` through `subMeasMass ψ Hhat.liftLeft = ev ψ (Hhat.total ⊗ I)`,
swapping the leftTensor through the polynomial sum, and pulling the `ev` through
the per-outcome point average gives the paper identity

  `⟨ψ| Hhat ⊗ I |ψ⟩ = E_u Σ_h ⟨ψ| H^u_h ⊗ I |ψ⟩`,

where `H^u_h = A^u_{h(u)} · T_h · A^u_{h(u)}` is
`sandwichedPolynomialOutcomeOperatorAt`. This is the algebraic opening of the
helper-stage completeness chain at
`references/ldt-paper/self_improvement.tex`, lines 354--356, mirrored at
`blueprint/src/chapter/ch07_self_improvement.tex`, lines 103--106.

The conclusion is exact (not approximate) and depends on no input-consistency
or SDP hypotheses. The remaining helper-completeness ingredients --- the
Cauchy--Schwarz reductions
(`self_improvement.tex:360--403`) onto a `Z ⊗ I`-shaped expression, and the
input-consistency dual-mass bound already supplied by
`input_consistency_dual_mass_lower_bound` --- compose against this identity. -/
theorem helper_mass_eq_avg_pointwise_sandwich_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    subMeasMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T).liftLeft =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (sandwichedPolynomialOutcomeOperatorAt params strategy T u h))) := by
  -- Per-outcome scalar identity: `ev (leftTensor (Hhat.outcome h)) = E_u ev (leftTensor H^u_h)`.
  -- `Hhat.outcome h` is by definition the per-point average of
  -- `sandwichedPolynomialOutcomeOperatorAt`; pulling `ev (leftTensor _)` through
  -- the average is `ev_opTensor_averageOperatorOverDistribution_left` with `B = 1`.
  have hev_each :
      ∀ h : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            ((averagedSandwichedPolynomialSubMeas params strategy T).outcome h)) =
          avgOver (uniformDistribution (Point params)) (fun u =>
            ev strategy.state
              (leftTensor (ι₂ := ι)
                (sandwichedPolynomialOutcomeOperatorAt params strategy T u h))) := by
    intro h
    exact ev_opTensor_averageOperatorOverDistribution_left strategy.state
      (uniformDistribution (Point params))
      (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u h)
      (1 : MIPStarRE.Quantum.Op ι)
  -- Open the LHS as a polynomial-indexed sum via the generic
  -- `ev_leftTensor_total_eq_sum_outcome`, replace each summand by its per-point
  -- average via `hev_each`, and swap sum/avgOver via `avgOver_sum`.
  calc
    subMeasMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T).liftLeft
        =
      ∑ h : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            ((averagedSandwichedPolynomialSubMeas params strategy T).outcome h)) :=
        ev_leftTensor_total_eq_sum_outcome strategy.state _
    _ =
      ∑ h : Polynomial params,
        avgOver (uniformDistribution (Point params)) (fun u =>
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (sandwichedPolynomialOutcomeOperatorAt params strategy T u h))) :=
        Finset.sum_congr rfl (fun h _ => hev_each h)
    _ =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (sandwichedPolynomialOutcomeOperatorAt params strategy T u h))) := by
        rw [← avgOver_sum (uniformDistribution (Point params))
              (fun u h =>
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                    (sandwichedPolynomialOutcomeOperatorAt params strategy T u h)))]

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
private lemma proj_outer_sandwich_eq {ι : Type*} [Fintype ι]
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
  change opTensor
      (pointConditionedOutcomeOperatorAtPolynomial params strategy h u *
        ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h) *
        pointConditionedOutcomeOperatorAtPolynomial params strategy h u)
      (T.outcome h) =
    opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
      (T.outcome h)
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

/-! ### Scalar chain for the projection-simplified diagonal add-in-u transfer -/

/-- Strong self-consistency for the point measurement, pulled back to the second
coordinate of the independent `(u, v)` average used by the add-in-`u` scalar
chain.

This is the distributional self-consistency input for the `A^v_{h(v)}` moves in
`self_improvement.tex`, lines 255--297: the point measurement sampled at `v`
has the same `2δ` left/right state-dependent distance after the product average
over `(u, v)`. -/
lemma addInU_pointMeasurement_snd_selfConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (delta : Error)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    SDDRel strategy.state (uniformDistribution (Point params × Point params))
      (IdxSubMeas.liftLeft
        (fun uv : Point params × Point params =>
          (strategy.pointMeasurement uv.2).toSubMeas))
      (IdxSubMeas.liftRight
        (fun uv : Point params × Point params =>
          (strategy.pointMeasurement uv.2).toSubMeas))
      (2 * delta) := by
  classical
  have hssc_pair :
      BipartiteSSCRel strategy.state
        (uniformDistribution (Point params × Point params))
        (fun uv : Point params × Point params =>
          (strategy.pointMeasurement uv.2).toSubMeas)
        delta := by
    rcases hssc with ⟨hssc⟩
    constructor
    calc
      avgOver (uniformDistribution (Point params × Point params))
          (fun uv : Point params × Point params =>
            qBipartiteSSCDefect strategy.state
              ((strategy.pointMeasurement uv.2).toSubMeas))
        =
          avgOver (uniformDistribution (Point params))
            (fun v : Point params =>
              qBipartiteSSCDefect strategy.state
                ((strategy.pointMeasurement v).toSubMeas)) := by
            exact avgOver_uniform_snd
              (α := Point params) (β := Point params)
              (fun v : Point params =>
                qBipartiteSSCDefect strategy.state
                  ((strategy.pointMeasurement v).toSubMeas))
      _ ≤ delta := by
            simpa [bipartiteSSCError, IdxProjMeas.toIdxSubMeas] using hssc
  have hraw :=
    Preliminaries.twoNotionsOfSelfConsistencyAfterEvaluation
      strategy.state strategy.permInvState
      (uniformDistribution (Point params × Point params))
      (fun uv : Point params × Point params =>
        (strategy.pointMeasurement uv.2).toSubMeas)
      delta
      (fun _uv (a : Fq params) => a)
      hssc_pair
  have hleft :
      IdxSubMeas.liftLeft
          (fun uv : Point params × Point params =>
            postprocess ((strategy.pointMeasurement uv.2).toSubMeas)
              (fun a : Fq params => a)) =
        IdxSubMeas.liftLeft
          (fun uv : Point params × Point params =>
            (strategy.pointMeasurement uv.2).toSubMeas) := by
    funext uv
    simp [IdxSubMeas.liftLeft]
  have hright :
      IdxSubMeas.liftRight
          (fun uv : Point params × Point params =>
            postprocess ((strategy.pointMeasurement uv.2).toSubMeas)
              (fun a : Fq params => a)) =
        IdxSubMeas.liftRight
          (fun uv : Point params × Point params =>
            (strategy.pointMeasurement uv.2).toSubMeas) := by
    funext uv
    simp [IdxSubMeas.liftRight]
  simpa [hleft, hright] using hraw

/-- The grouped tensor mass over a fiber `h(v)=a` is a contraction.

This is the submeasurement bound used inside the first Cauchy--Schwarz square
root in `self_improvement.tex`, lines 267--272: after grouping by the value
`a = h(v)`, the selected operators
`H^u_h ⊗ T_h` are dominated by the total mass of the sandwiched polynomial
submeasurement at `u`, hence by `I`. -/
lemma addInU_filtered_sandwiched_tensor_sum_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (u v : Point params) (a : Fq params) :
    ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h v = a),
        opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
          (T.outcome h) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  exact SubMeas.opTensor_sum_filter_le_one
    (sandwichedPolynomialSubMeasAt params strategy T u)
    T
    (fun h : Polynomial params => h v = a)

/-- The expanded left endpoint `Q₀` of the four-step scalar chain in
`self_improvement.tex`, lines 247--252, after setting `M^u = H^u` and averaging
the second tensor factor `H = E_v H^v`. -/
noncomputable def addInUCSChainQ0
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : Polynomial params,
      ev strategy.state
        (opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
          ((sandwichedPolynomialSubMeasAt params strategy T uv.2).outcome h)))

/-- The scalar `Q₁` obtained from `Q₀` by moving the right point projection
`A^v_{h(v)}` to the left tensor factor; this is the target of
`eq:move-one`. -/
noncomputable def addInUCSChainQ1
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : Polynomial params,
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      ev strategy.state
        (opTensor (Av * (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
          (T.outcome h * Av)))

/-- The scalar `Q₂` obtained from `Q₁` by moving the second right point
projection to the left tensor factor; this is the target of `eq:move-another`. -/
noncomputable def addInUCSChainQ2
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : Polynomial params,
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      ev strategy.state
        (opTensor (Av * (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h *
            Av)
          (T.outcome h)))

/-- The scalar `Q₃` obtained from `Q₂` by replacing the first point projection
`A^v_{h(v)}` by `A^u_{h(u)}`; this is the target of `eq:change-one`. -/
noncomputable def addInUCSChainQ3
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : Polynomial params,
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
      ev strategy.state
        (opTensor (Au * (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h *
            Av)
          (T.outcome h)))

/-- The scalar `Q₄` obtained from `Q₃` by replacing the second point projection
`A^v_{h(v)}` by `A^u_{h(u)}`; after the projection collapse, this is the
projection-simplified right endpoint of the diagonal add-in-u transfer. -/
noncomputable def addInUCSChainQ4
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
    ∑ h : Polynomial params,
      let Au := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
      ev strategy.state
        (opTensor (Au * (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h *
            Au)
          (T.outcome h)))

/-- The expanded chain endpoint `Q₀` is the existing diagonal match-mass left
side used by `selfConsistencyDiagonalAddInU_of_simplifiedTransfer`. -/
lemma add_in_u_cs_chain_q0_eq_match_mass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) =
      addInUCSChainQ0 params strategy T := by
  classical
  calc
    qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T)
        =
      ∑ h : Polynomial params,
        avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (uniformDistribution (Point params)) (fun v =>
            ev strategy.state
              (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                ((sandwichedPolynomialSubMeasAt params strategy T v).outcome h)))) := by
        unfold qBipartiteMatchMass averagedSandwichedPolynomialSubMeas
        refine Finset.sum_congr rfl ?_
        intro h _
        rw [ev_opTensor_averageOperatorOverDistribution_left]
        refine avgOver_congr _ _ _ ?_
        intro u
        simpa [sandwichedPolynomialSubMeasAt] using
          ev_opTensor_averageOperatorOverDistribution_right strategy.state
            (uniformDistribution (Point params))
            ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
            (fun v => (sandwichedPolynomialSubMeasAt params strategy T v).outcome h)
    _ = addInUCSChainQ0 params strategy T := by
        symm
        unfold addInUCSChainQ0
        rw [avgOver_uniform_prod (α := Point params) (β := Point params)
          (f := fun u v =>
            ∑ h : Polynomial params,
              ev strategy.state
                (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                  ((sandwichedPolynomialSubMeasAt params strategy T v).outcome h)))]
        calc
          avgOver (uniformDistribution (Point params)) (fun u =>
              avgOver (uniformDistribution (Point params)) (fun v =>
                ∑ h : Polynomial params,
                  ev strategy.state
                    (opTensor
                      ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                      ((sandwichedPolynomialSubMeasAt params strategy T v).outcome h))))
              =
            avgOver (uniformDistribution (Point params)) (fun u =>
              ∑ h : Polynomial params,
                avgOver (uniformDistribution (Point params)) (fun v =>
                  ev strategy.state
                    (opTensor
                      ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                      ((sandwichedPolynomialSubMeasAt params strategy T v).outcome h)))) := by
              refine avgOver_congr _ _ _ ?_
              intro u
              rw [avgOver_sum]
          _ =
            ∑ h : Polynomial params,
              avgOver (uniformDistribution (Point params)) (fun u =>
                avgOver (uniformDistribution (Point params)) (fun v =>
                  ev strategy.state
                    (opTensor
                      ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                      ((sandwichedPolynomialSubMeasAt params strategy T v).outcome h)))) := by
              rw [avgOver_sum]

/-- The raw chain endpoint `Q₄` collapses to the projection-simplified scalar
right side used by `selfConsistencyDiagonalAddInU_of_simplifiedTransfer`. -/
lemma add_in_u_cs_chain_q4_eq_simplified_rhs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUCSChainQ4 params strategy T =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h))) := by
  classical
  calc
    addInUCSChainQ4 params strategy T =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h)
              (T.outcome h))) := by
        unfold addInUCSChainQ4
        refine avgOver_congr _ _ _ ?_
        intro uv
        refine Finset.sum_congr rfl ?_
        intro h _
        have hproj :
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
              pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 =
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 := by
          simpa [pointConditionedOutcomeOperatorAtPolynomial] using
            (strategy.pointMeasurement uv.1).proj (h uv.1)
        have hcollapse :
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
                (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 =
              (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h := by
          change
            pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
                (pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
                  T.outcome h *
                  pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1) *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 =
              pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1 *
                T.outcome h *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.1
          exact proj_outer_sandwich_eq _ _ hproj
        simp [hcollapse]
    _ =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h))) := by
        exact avgOver_uniform_fst (α := Point params) (β := Point params)
          (fun u =>
            ∑ h : Polynomial params,
              ev strategy.state
                (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
                  (T.outcome h)))

/-! ### Algebraic CS-alignment for the add-in-u Step 1/2 differences

This section records pure operator-algebra rewrites that bring the differences
`addInUCSChainQ1 - addInUCSChainQ0` and `addInUCSChainQ2 - addInUCSChainQ1`
into the shapes required by the paper's Cauchy--Schwarz steps
`eq:move-one-cauchy-schwarz` and `eq:move-another-cauchy-schwarz`
(`references/ldt-paper/self_improvement.tex`, lines 261--266 and 285--289).
The reverse-difference companions give the downstream orientation
`Q₀ - Q₁` and `Q₁ - Q₂` without repeating subtraction bookkeeping.

They do **not** discharge the Cauchy--Schwarz estimate itself; they reduce the
raw `|Q₁ - Q₀| ≤ √(2δ)` and `|Q₁ - Q₂| ≤ √(2δ)` bounds to (a) a
sandwich-form Cauchy--Schwarz on the resulting `D · (M^u_h ⊗ T_h) · D'`-style
expression, plus (b) the two square-root inputs available via
`addInU_pointMeasurement_snd_selfConsistency` and
`addInU_filtered_sandwiched_tensor_sum_le_one`.

Names are deliberately suffixed `_diff_eq` to keep them honest as intermediate
algebraic identities rather than as the final scalar bounds. -/

private lemma addInU_step1_pointwise_op_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M Av Th : MIPStarRE.Quantum.Op κ) :
    opTensor (Av * M) (Th * Av) - opTensor M (Av * Th * Av) =
      (leftTensor (ι₂ := κ) Av - rightTensor (ι₁ := κ) Av) *
        (opTensor M Th * rightTensor (ι₁ := κ) Av) := by
  have hLeft :
      leftTensor (ι₂ := κ) Av * (opTensor M Th * rightTensor (ι₁ := κ) Av) =
        opTensor (Av * M) (Th * Av) := by
    change opTensor Av 1 * (opTensor M Th * opTensor 1 Av) =
        opTensor (Av * M) (Th * Av)
    rw [opTensor_mul, opTensor_mul]
    simp
  have hRight :
      rightTensor (ι₁ := κ) Av * (opTensor M Th * rightTensor (ι₁ := κ) Av) =
        opTensor M (Av * Th * Av) := by
    change opTensor 1 Av * (opTensor M Th * opTensor 1 Av) =
        opTensor M (Av * Th * Av)
    rw [opTensor_mul, opTensor_mul]
    simp [Matrix.mul_assoc]
  rw [sub_mul, hLeft, hRight]

private lemma addInU_step2_pointwise_op_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M Av Th : MIPStarRE.Quantum.Op κ) :
    opTensor (Av * M * Av) Th - opTensor (Av * M) (Th * Av) =
      leftTensor (ι₂ := κ) Av *
        (opTensor M Th * (leftTensor (ι₂ := κ) Av - rightTensor (ι₁ := κ) Av)) := by
  have hLeft :
      leftTensor (ι₂ := κ) Av * (opTensor M Th * leftTensor (ι₂ := κ) Av) =
        opTensor (Av * M * Av) Th := by
    change opTensor Av 1 * (opTensor M Th * opTensor Av 1) =
        opTensor (Av * M * Av) Th
    rw [opTensor_mul, opTensor_mul]
    simp [Matrix.mul_assoc]
  have hRight :
      leftTensor (ι₂ := κ) Av * (opTensor M Th * rightTensor (ι₁ := κ) Av) =
        opTensor (Av * M) (Th * Av) := by
    change opTensor Av 1 * (opTensor M Th * opTensor 1 Av) =
        opTensor (Av * M) (Th * Av)
    rw [opTensor_mul, opTensor_mul]
    simp
  rw [mul_sub, mul_sub, hLeft, hRight]

/-- Algebraic CS-alignment for the `Q₀ → Q₁` step.

Rewrites the difference `addInUCSChainQ1 - addInUCSChainQ0` in the exact form
appearing on the LHS of `eq:move-one-cauchy-schwarz` (paper lines 261--266):
the inner-product of the commutator
`A^v_{h(v)} ⊗ I − I ⊗ A^v_{h(v)}` with `M^u_h ⊗ T_h · (I ⊗ A^v_{h(v)})`,
averaged over `(u, v)` and summed over `h`.

This identity is purely algebraic; the actual `√(2δ)` bound still requires
the operator Cauchy--Schwarz step plus
`addInU_pointMeasurement_snd_selfConsistency`. -/
lemma addInU_cs_chain_step1_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUCSChainQ1 params strategy T - addInUCSChainQ0 params strategy T =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          ev strategy.state
            ((leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av) *
              (opTensor Mh (T.outcome h) * rightTensor (ι₁ := ι) Av))) := by
  classical
  unfold addInUCSChainQ0 addInUCSChainQ1
  rw [← avgOver_sub]
  refine avgOver_congr _ _ _ ?_
  intro uv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro h _
  set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
  set Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
  rw [← ev_sub]
  congr 1
  exact addInU_step1_pointwise_op_eq Mh Av (T.outcome h)

/-- Algebraic CS-alignment for the `Q₁ → Q₂` step.

Rewrites the difference `addInUCSChainQ2 - addInUCSChainQ1` in the exact form
appearing on the LHS of `eq:move-another-cauchy-schwarz` (paper lines 285--289):
the inner-product of `(A^v_{h(v)} · M^u_h) ⊗ T_h` with the commutator
`A^v_{h(v)} ⊗ I − I ⊗ A^v_{h(v)}`, averaged over `(u, v)` and summed over `h`.
The Lean statement keeps the equivalent factored form
`(A^v_{h(v)} ⊗ I) · (M^u_h ⊗ T_h)` before the commutator.

This identity is purely algebraic; the actual `√(2δ)` bound still requires
the operator Cauchy--Schwarz step plus
`addInU_pointMeasurement_snd_selfConsistency` and
`addInU_filtered_sandwiched_tensor_sum_le_one`. -/
lemma addInU_cs_chain_step2_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUCSChainQ2 params strategy T - addInUCSChainQ1 params strategy T =
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          ev strategy.state
            (leftTensor (ι₂ := ι) Av *
              (opTensor Mh (T.outcome h) *
                (leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av)))) := by
  classical
  unfold addInUCSChainQ1 addInUCSChainQ2
  rw [← avgOver_sub]
  refine avgOver_congr _ _ _ ?_
  intro uv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro h _
  set Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
  set Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
  rw [← ev_sub]
  congr 1
  exact addInU_step2_pointwise_op_eq Mh Av (T.outcome h)

/-- Reverse-orientation form of `addInU_cs_chain_step1_diff_eq`.

This is the same algebraic identity as the `Q₀ → Q₁` rewrite, stated in the
`Q₀ - Q₁` orientation used by the later absolute-value chain. -/
lemma addInU_cs_chain_step1_reverse_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUCSChainQ0 params strategy T - addInUCSChainQ1 params strategy T =
      -avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          ev strategy.state
            ((leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av) *
              (opTensor Mh (T.outcome h) * rightTensor (ι₁ := ι) Av))) := by
  rw [← addInU_cs_chain_step1_diff_eq params strategy T]
  ring

/-- Reverse-orientation form of `addInU_cs_chain_step2_diff_eq`.

This is the same algebraic identity as the `Q₁ → Q₂` rewrite, stated in the
`Q₁ - Q₂` orientation used by the later absolute-value chain. -/
lemma addInU_cs_chain_step2_reverse_diff_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    addInUCSChainQ1 params strategy T - addInUCSChainQ2 params strategy T =
      -avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ h : Polynomial params,
          let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy h uv.2
          let Mh := (sandwichedPolynomialSubMeasAt params strategy T uv.1).outcome h
          ev strategy.state
            (leftTensor (ι₂ := ι) Av *
              (opTensor Mh (T.outcome h) *
                (leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av)))) := by
  rw [← addInU_cs_chain_step2_diff_eq params strategy T]
  ring

/-! ### Add-in-u variance-bound conversions

The following four lemmas are conditional real-valued conversions for the
`Q₂ → Q₃` and `Q₃ → Q₄` add-in-u steps.  They do not prove the
operator-theoretic Cauchy--Schwarz estimates from
`references/ldt-paper/self_improvement.tex`, lines 299--340.  Instead, they
convert either a squared real bound or a factored product of square-root bounds
into the absolute-value square-root shape used by the surrounding scalar chain.

The hypotheses `hsq`, `hCS`, and `hD*_le*` are the places where future
operator-level arguments must supply the Cauchy--Schwarz, submeasurement
contraction, and total-mass estimates.  In particular, `T` is a submeasurement
in these statements; any `≤ 1` input corresponds to a `total_le_one`-style
bound rather than a measurement equality. -/

/-- Convert a squared `Q₂ → Q₃` real bound to an absolute-value sqrt bound.

This lemma is only the `Real.abs_le_sqrt` conversion.  The hypothesis `hsq`
must already contain any operator Cauchy--Schwarz and submeasurement estimates
needed to prove the squared bound. -/
lemma add_in_u_cs_chain_q2_q3_abs_le_sqrt_of_sq_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (hsq :
      (addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T) ^ 2 ≤
        ∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
      Real.sqrt
        (∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
  Real.abs_le_sqrt hsq

/-- Convert factored `Q₂ → Q₃` sqrt bounds to the summed-deviation sqrt bound.

This lemma assumes the Cauchy--Schwarz product bound as `hCS`, a bound on the
first factor by the summed independent-points deviation, and a `≤ 1` bound on
the second factor.  The proof is purely real-valued; the submeasurement and
operator content belongs in the hypotheses. -/
lemma add_in_u_cs_chain_q2_q3_le_sqrt_of_factor_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (D₁ D₂ : Error)
    (hCS :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt D₁ * Real.sqrt D₂)
    (hD₁_le :
      D₁ ≤ ∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g)
    (hD₂_le_one : D₂ ≤ 1) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
      Real.sqrt
        (∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) := by
  have hsqrt_D₂ : Real.sqrt D₂ ≤ 1 := Real.sqrt_le_one.mpr hD₂_le_one
  have hsqrt_D₁ :
      Real.sqrt D₁ ≤ Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
    Real.sqrt_le_sqrt hD₁_le
  calc
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T|
        ≤ Real.sqrt D₁ * Real.sqrt D₂ := hCS
    _ ≤ Real.sqrt D₁ * 1 :=
          mul_le_mul_of_nonneg_left hsqrt_D₂ (Real.sqrt_nonneg _)
    _ = Real.sqrt D₁ := mul_one _
    _ ≤ Real.sqrt
            (∑ g : Polynomial params,
              globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
          hsqrt_D₁

/-- Convert a squared `Q₃ → Q₄` real bound to an absolute-value sqrt bound.

This lemma is only the `Real.abs_le_sqrt` conversion.  The hypothesis `hsq`
must already contain any operator Cauchy--Schwarz and submeasurement estimates
needed to prove the squared bound. -/
lemma add_in_u_cs_chain_q3_q4_abs_le_sqrt_of_sq_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (hsq :
      (addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T) ^ 2 ≤
        ∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
      Real.sqrt
        (∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
  Real.abs_le_sqrt hsq

/-- Convert factored `Q₃ → Q₄` sqrt bounds to the summed-deviation sqrt bound.

This lemma assumes the Cauchy--Schwarz product bound as `hCS`, a `≤ 1` bound
on the first factor, and a bound on the second factor by the summed
independent-points deviation.  The proof is purely real-valued; the
submeasurement and operator content belongs in the hypotheses. -/
lemma add_in_u_cs_chain_q3_q4_le_sqrt_of_factor_bounds
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (D₁ D₂ : Error)
    (hCS :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt D₁ * Real.sqrt D₂)
    (hD₁_le_one : D₁ ≤ 1)
    (hD₂_le :
      D₂ ≤ ∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
      Real.sqrt
        (∑ g : Polynomial params,
          globalVarianceDeviationAtPolynomial params strategy strategy.state T g) := by
  have hsqrt_D₁ : Real.sqrt D₁ ≤ 1 := Real.sqrt_le_one.mpr hD₁_le_one
  have hsqrt_D₂ :
      Real.sqrt D₂ ≤ Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
    Real.sqrt_le_sqrt hD₂_le
  calc
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T|
        ≤ Real.sqrt D₁ * Real.sqrt D₂ := hCS
    _ ≤ 1 * Real.sqrt D₂ :=
          mul_le_mul_of_nonneg_right hsqrt_D₁ (Real.sqrt_nonneg _)
    _ = Real.sqrt D₂ := one_mul _
    _ ≤ Real.sqrt
            (∑ g : Polynomial params,
              globalVarianceDeviationAtPolynomial params strategy strategy.state T g) :=
          hsqrt_D₂

/-- Sqrt-monotonicity transit lemma used by the two GlobalVariance endpoint
bridges below: a real bounded by `Real.sqrt s` is bounded by `Real.sqrt ζ`
whenever `s ≤ ζ`. Both `Q₂→Q₃` and `Q₃→Q₄` apply this fact with the same `s`
(the summed `globalVarianceDeviationAtPolynomial`). -/
private lemma le_sqrt_of_le_sqrt_of_le {a : ℝ} {s ζ : Error}
    (hcs : a ≤ Real.sqrt s) (hsum : s ≤ ζ) : a ≤ Real.sqrt ζ :=
  le_trans hcs (Real.sqrt_le_sqrt hsum)

/-- The global-variance sum bound upgrades the raw Cauchy--Schwarz estimate for
the first global-variance replacement step into the displayed `sqrt ζ` bound.

This is the variance-use fragment of `eq:change-one` in
`references/ldt-paper/self_improvement.tex`, lines 299--318. The hypothesis
`hcs` is the Cauchy--Schwarz estimate `eq:change-one-cauchy-schwarz`
(lines 306--311) **after** the second-square-root has been bounded by `1`
using `(A^v_{h(v)})² ≤ I` and the fact that `T` is a measurement
(lines 312--316, 318); concretely, the right-hand side is the summed
`globalVarianceDeviationAtPolynomial` (the displayed first-square-root
content). This lemma applies only the remaining `≤ ζ_variance` step from
`lem:global-variance-of-points` (line 317) via sqrt-monotonicity. -/
lemma add_in_u_cs_chain_q2_q3_le_sqrt_of_globalVarianceDeviation_sum_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    {ζ : Error}
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ)
    (hcs :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g)) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
      Real.sqrt ζ :=
  le_sqrt_of_le_sqrt_of_le hcs hglobal

/-- The global-variance sum bound upgrades the raw Cauchy--Schwarz estimate for
the second global-variance replacement step into the displayed `sqrt ζ` bound.

This is the variance-use fragment of `eq:change-another` in
`references/ldt-paper/self_improvement.tex`, lines 319--340. The hypothesis
`hcs` is the Cauchy--Schwarz estimate of lines 326--332 **after** the
first-square-root has been bounded by `1` using `(A^u_{h(u)})² ≤ I` and the
fact that `T` is a measurement (lines 333--338); concretely, the right-hand
side is the summed `globalVarianceDeviationAtPolynomial` (the displayed
second-square-root content, equal to the first-square-root term of
`eq:change-one-cauchy-schwarz` per line 340). This lemma applies only the
remaining `≤ ζ_variance` step (line 340) via sqrt-monotonicity. -/
lemma add_in_u_cs_chain_q3_q4_le_sqrt_of_globalVarianceDeviation_sum_le
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    {ζ : Error}
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ)
    (hcs :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g)) :
    |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
      Real.sqrt ζ :=
  le_sqrt_of_le_sqrt_of_le hcs hglobal

/-- Combined Step 3/4 variance bridge for the projection-simplified add-in-u
Cauchy--Schwarz chain.

Given the two raw Cauchy--Schwarz estimates against the summed
independent-points deviation and a GlobalVariance sum bound, this produces the
two `sqrt ζ` absolute-difference bounds needed by
`add_in_u_simplified_transfer_of_cs_chain`. It deliberately does not assemble
the final transfer, so the remaining self-consistency steps and arithmetic
absorption stay separate. -/
lemma add_in_u_cs_chain_global_variance_steps_of_sum_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    {ζ : Error}
    (hglobal :
      (∑ g : Polynomial params,
        globalVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤ ζ)
    (h23cs :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g))
    (h34cs :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g)) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt ζ ∧
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt ζ := by
  exact
    ⟨add_in_u_cs_chain_q2_q3_le_sqrt_of_globalVarianceDeviation_sum_le
        params strategy T hglobal h23cs,
      add_in_u_cs_chain_q3_q4_le_sqrt_of_globalVarianceDeviation_sum_le
        params strategy T hglobal h34cs⟩

/-- Local-variance-sum version of the combined Step 3/4 variance bridge.

This consumes the expected output of the local-variance normalization step
(`expansion.tex`, lines 317--321) through
`globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le`, then applies
the combined Step 3/4 bridge above. -/
lemma add_in_u_cs_chain_global_variance_steps_of_local_sum_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (hlocal :
      (∑ g : Polynomial params,
        localVarianceDeviationAtPolynomial params strategy strategy.state T g) ≤
        localVarianceOfPointsError params eps delta)
    (h23cs :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g))
    (h34cs :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt
          (∑ g : Polynomial params,
            globalVarianceDeviationAtPolynomial params strategy strategy.state T g)) :
    |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt (globalVarianceOfPointsError params eps delta) ∧
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt (globalVarianceOfPointsError params eps delta) := by
  exact add_in_u_cs_chain_global_variance_steps_of_sum_bound
    params strategy T
    (globalVarianceDeviation_sum_le_of_localVarianceDeviation_sum_le
      params strategy eps delta T hlocal)
    h23cs h34cs

/-- Assemble the projection-simplified scalar transfer from the four scalar
chain moves. The analytic work remains exactly the four bounds
`Q₀ ≈ Q₁`, `Q₁ ≈ Q₂`, `Q₂ ≈ Q₃`, and `Q₃ ≈ Q₄`, plus the final arithmetic
absorption into `addInUError`. -/
lemma add_in_u_simplified_transfer_of_cs_chain
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (T : SubMeas (Polynomial params) ι)
    (η01 η12 η23 η34 : Error)
    (h01 :
      |addInUCSChainQ0 params strategy T - addInUCSChainQ1 params strategy T| ≤ η01)
    (h12 :
      |addInUCSChainQ1 params strategy T - addInUCSChainQ2 params strategy T| ≤ η12)
    (h23 :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤ η23)
    (h34 :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤ η34)
    (hsum : η01 + η12 + η23 + η34 ≤ addInUError params eps delta) :
    |qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h)))| ≤ addInUError params eps delta := by
  let Q0 := addInUCSChainQ0 params strategy T
  let Q1 := addInUCSChainQ1 params strategy T
  let Q2 := addInUCSChainQ2 params strategy T
  let Q3 := addInUCSChainQ3 params strategy T
  let Q4 := addInUCSChainQ4 params strategy T
  have htriangle :
      |Q0 - Q4| ≤ |Q0 - Q1| + |Q1 - Q2| + |Q2 - Q3| + |Q3 - Q4| := by
    calc
      |Q0 - Q4| = |(Q0 - Q1) + (Q1 - Q2) + (Q2 - Q3) + (Q3 - Q4)| := by
        ring_nf
      _ ≤ |Q0 - Q1| + |Q1 - Q2| + |Q2 - Q3| + |Q3 - Q4| := by
        have h1 := abs_add_le ((Q0 - Q1) + (Q1 - Q2) + (Q2 - Q3)) (Q3 - Q4)
        have h2 := abs_add_le ((Q0 - Q1) + (Q1 - Q2)) (Q2 - Q3)
        have h3 := abs_add_le (Q0 - Q1) (Q1 - Q2)
        nlinarith
  have h01' : |Q0 - Q1| ≤ η01 := by
    simpa [Q0, Q1] using h01
  have h12' : |Q1 - Q2| ≤ η12 := by
    simpa [Q1, Q2] using h12
  have h23' : |Q2 - Q3| ≤ η23 := by
    simpa [Q2, Q3] using h23
  have h34' : |Q3 - Q4| ≤ η34 := by
    simpa [Q3, Q4] using h34
  calc
    |qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h)))|
        = |Q0 - Q4| := by
          rw [add_in_u_cs_chain_q0_eq_match_mass,
            ← add_in_u_cs_chain_q4_eq_simplified_rhs]
    _ ≤ |Q0 - Q1| + |Q1 - Q2| + |Q2 - Q3| + |Q3 - Q4| := htriangle
    _ ≤ η01 + η12 + η23 + η34 := by
      nlinarith
    _ ≤ addInUError params eps delta := hsum

/-- Reusable numerical absorption: whenever `2 a ≤ b`, the four-term sum
`2 √(2 a) + 2 √b` collapses into `4 √b`. This is the schematic shape of the
paper's closing absorption step in the proof of `lem:add-in-u`
(`self_improvement.tex:341--342`). -/
lemma two_sqrt_two_mul_add_two_sqrt_le_four_sqrt
    {a b : Error} (hab : 2 * a ≤ b) :
    2 * Real.sqrt (2 * a) + 2 * Real.sqrt b ≤ 4 * Real.sqrt b := by
  have hsqrt : Real.sqrt (2 * a) ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
  linarith

/-- Paper-side comparison `2 δ ≤ ζ_variance` from the closing line of the proof
of `lem:add-in-u` (`self_improvement.tex:342`,
`blueprint/src/chapter/ch07_self_improvement.tex:494`). Since
`ζ_variance = 24 m (ε + δ + m d / q)` and `m ≥ 1`, the term `24 m δ` already
exceeds `2 δ` whenever `eps, delta ≥ 0`. -/
lemma two_mul_delta_le_selfImprovementVarianceError
    (params : Parameters)
    [FieldModel params.q]
    (eps delta : Error)
    (hε : 0 ≤ eps) (hδ : 0 ≤ delta) :
    2 * delta ≤ selfImprovementVarianceError params eps delta := by
  have hm : (1 : Error) ≤ (params.m : Error) := by
    have hm_nat : (1 : ℕ) ≤ params.m := params.hm
    exact_mod_cast hm_nat
  have hm_nonneg : (0 : Error) ≤ (params.m : Error) := by linarith
  have hB : 0 ≤ generalizeBError params := by
    dsimp [generalizeBError]; positivity
  unfold selfImprovementVarianceError globalVarianceOfPointsError
  calc
    2 * delta
        ≤ 24 * delta := by linarith
    _ = 24 * (1 : Error) * delta := by ring
    _ ≤ 24 * (params.m : Error) * delta := by
        have : (0 : Error) ≤ ((params.m : Error) - 1) * delta :=
          mul_nonneg (by linarith) hδ
        nlinarith
    _ ≤ 24 * (params.m : Error) * (eps + delta + generalizeBError params) := by
        have h24m : (0 : Error) ≤ 24 * (params.m : Error) := by nlinarith
        nlinarith [mul_nonneg h24m hε, mul_nonneg h24m hB]

/-- Arithmetic absorption used by `add_in_u_simplified_transfer_of_cs_chain`:
the four step-bound sum `2 √(2 δ) + 2 √(ζ_variance)` is dominated by
`addInUError = 4 ζ_variance^{1/2}` (`self_improvement.tex:341--342`,
`blueprint/src/chapter/ch07_self_improvement.tex:492--494`). This is the
arithmetic side condition that lets the step bounds with the paper-faithful
`Real.sqrt` shape (companion issues #1089 and #1090) discharge the `hsum`
hypothesis of `add_in_u_simplified_transfer_of_cs_chain`. -/
lemma two_sqrt_two_delta_add_two_sqrt_selfImprovementVarianceError_le_addInUError
    (params : Parameters)
    [FieldModel params.q]
    (eps delta : Error)
    (hε : 0 ≤ eps) (hδ : 0 ≤ delta) :
    2 * Real.sqrt (2 * delta) +
        2 * Real.sqrt (selfImprovementVarianceError params eps delta) ≤
      addInUError params eps delta := by
  have hbase :=
    two_sqrt_two_mul_add_two_sqrt_le_four_sqrt
      (two_mul_delta_le_selfImprovementVarianceError params eps delta hε hδ)
  simpa [addInUError, Real.sqrt_eq_rpow] using hbase

/-- Wrapper composing `add_in_u_simplified_transfer_of_cs_chain` with the
arithmetic absorption: when the four chain step bounds have the paper-faithful
shapes `√(2 δ)`, `√(2 δ)`, `√(ζ_variance)`, `√(ζ_variance)`, the
projection-simplified transfer holds with the displayed
`addInUError = 4 ζ_variance^{1/2}`. The four hypotheses match the targets of
companion issues #1089 (Step 1/2) and #1083/#1088/#1090 (Step 3/4). -/
lemma add_in_u_simplified_transfer_of_cs_chain_sqrt_form
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (hε : 0 ≤ eps) (hδ : 0 ≤ delta)
    (T : SubMeas (Polynomial params) ι)
    (h01 :
      |addInUCSChainQ0 params strategy T - addInUCSChainQ1 params strategy T| ≤
        Real.sqrt (2 * delta))
    (h12 :
      |addInUCSChainQ1 params strategy T - addInUCSChainQ2 params strategy T| ≤
        Real.sqrt (2 * delta))
    (h23 :
      |addInUCSChainQ2 params strategy T - addInUCSChainQ3 params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta))
    (h34 :
      |addInUCSChainQ3 params strategy T - addInUCSChainQ4 params strategy T| ≤
        Real.sqrt (selfImprovementVarianceError params eps delta)) :
    |qBipartiteMatchMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T)
        (averagedSandwichedPolynomialSubMeas params strategy T) -
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((sandwichedPolynomialSubMeasAt params strategy T u).outcome h)
              (T.outcome h)))| ≤ addInUError params eps delta := by
  have hsum :
      Real.sqrt (2 * delta) + Real.sqrt (2 * delta) +
          Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (selfImprovementVarianceError params eps delta) ≤
        addInUError params eps delta := by
    have htwo :=
      two_sqrt_two_delta_add_two_sqrt_selfImprovementVarianceError_le_addInUError
        params eps delta hε hδ
    linarith
  exact add_in_u_simplified_transfer_of_cs_chain params strategy eps delta T
    (Real.sqrt (2 * delta)) (Real.sqrt (2 * delta))
    (Real.sqrt (selfImprovementVarianceError params eps delta))
    (Real.sqrt (selfImprovementVarianceError params eps delta))
    h01 h12 h23 h34 hsum

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

/-- Producer-shaped inputs for the helper-stage strong self-consistency proof.

These fields isolate the remaining paper-side obligations in the proof of
`item:self-improvement-self` once the reduced helper conclusion is fixed:

1. the four scalar transport bounds along the chain
   `Q₀ \to Q₁ \to Q₂ \to Q₃ \to Q₄`, and
2. the final lower bound on the released right-hand side before the arithmetic
   absorption into `selfImprovementHelperError`.

This structure is intentionally narrower than
`HelperStrongSelfConsistencyInput`: it records the actual intermediate estimates
still needed from the add-in-`u`, self-consistency, and variance calculations,
rather than restating the final `BipartiteSSCRel` conclusion. -/
structure HelperStrongSelfConsistencyProducerInputs
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι)
    (Hhat : SubMeas (Polynomial params) ι)
    (eps delta : Error) : Prop where
  /-- Paper `eq:move-one`: the `Q₀ \to Q₁` transport bound. -/
  step01Bound :
    |addInUCSChainQ0 params strategy T.toSubMeas -
        addInUCSChainQ1 params strategy T.toSubMeas| ≤
      Real.sqrt (2 * delta)
  /-- Paper `eq:move-another`: the `Q₁ \to Q₂` transport bound. -/
  step12Bound :
    |addInUCSChainQ1 params strategy T.toSubMeas -
        addInUCSChainQ2 params strategy T.toSubMeas| ≤
      Real.sqrt (2 * delta)
  /-- Paper `eq:change-one`: the `Q₂ \to Q₃` variance transport bound. -/
  step23Bound :
    |addInUCSChainQ2 params strategy T.toSubMeas -
        addInUCSChainQ3 params strategy T.toSubMeas| ≤
      Real.sqrt (selfImprovementVarianceError params eps delta)
  /-- Paper `eq:change-another`: the `Q₃ \to Q₄` variance transport bound. -/
  step34Bound :
    |addInUCSChainQ3 params strategy T.toSubMeas -
        addInUCSChainQ4 params strategy T.toSubMeas| ≤
      Real.sqrt (selfImprovementVarianceError params eps delta)
  /-- The released right-hand side is within the paper's pre-absorption helper
  SSC error of the helper mass. -/
  residualLowerBound :
    subMeasMass strategy.state Hhat.liftLeft -
        addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
          T.toSubMeas
          (selfConsistencyAddInUSelection params) ≤
      (11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : Error) * (params.d : Error) / (params.q : Error))) -
        addInUError params eps delta

/-- Produce the helper-stage strong self-consistency conclusion from the actual
helper construction together with the named add-in-`u`/variance transports.

The theorem consumes the reduced helper output
`SelfImprovementHelperConclusion params strategy T Hhat Z eps delta` and a
producer-shaped package of the four scalar chain bounds plus the final lower
bound on the released right-hand side. It then assembles the diagonal transfer
using `add_in_u_simplified_transfer_of_cs_chain_sqrt_form`, upgrades it to the
paper's released right-hand side via
`selfConsistencyDiagonalAddInU_of_simplifiedTransfer`, and applies the closing
arithmetic absorption
`helper_strong_self_consistency_error_le_selfImprovementHelperError`.

This is the first no-`sorry` route from the actual helper construction to the
`HelperStrongSelfConsistencyInput` surface. The remaining analytic work is
therefore pushed into the producer package, rather than left as a raw
`BipartiteSSCRel` assumption. -/
theorem helper_strong_self_consistency_of_helper_conclusion
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hproducer : HelperStrongSelfConsistencyProducerInputs
      params strategy T Hhat eps delta) :
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Hhat)
      (selfImprovementHelperError params eps delta) := by
  have htransfer_simplified :
      |qBipartiteMatchMass strategy.state
          (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas)
          (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas) -
        avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ h : Polynomial params,
            ev strategy.state
              (opTensor
                ((sandwichedPolynomialSubMeasAt params strategy T.toSubMeas u).outcome h)
                (T.toSubMeas.outcome h)))| ≤
        addInUError params eps delta :=
    add_in_u_simplified_transfer_of_cs_chain_sqrt_form
      params strategy eps delta heps hdelta T.toSubMeas
      hproducer.step01Bound hproducer.step12Bound
      hproducer.step23Bound hproducer.step34Bound
  have htransfer_release :
      |qBipartiteMatchMass strategy.state
          (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas)
          (averagedSandwichedPolynomialSubMeas params strategy T.toSubMeas) -
        addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
          T.toSubMeas
          (selfConsistencyAddInUSelection params)| ≤
        addInUError params eps delta := by
    simpa [addInURightQuantity_selfConsistencySelection_eq_release] using
      selfConsistencyDiagonalAddInU_of_simplifiedTransfer
        params strategy eps delta T.toSubMeas htransfer_simplified
  have htransfer_release_hhat :
      |qBipartiteMatchMass strategy.state Hhat Hhat -
        addInURightQuantity params strategy
          (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
          T.toSubMeas
          (selfConsistencyAddInUSelection params)| ≤
        addInUError params eps delta := by
    simpa [hhelper.averagedConstruction] using htransfer_release
  have hhelperGap :
      subMeasMass strategy.state Hhat.liftLeft -
          qBipartiteMatchMass strategy.state Hhat Hhat ≤
        11 * Real.sqrt (selfImprovementVarianceError params eps delta) +
          Real.sqrt (2 * delta) +
          ((params.m : Error) * (params.d : Error) / (params.q : Error)) := by
    have hreleaseGap :
        addInURightQuantity params strategy
            (sandwichedPolynomialSubMeasAt params strategy T.toSubMeas)
            T.toSubMeas
            (selfConsistencyAddInUSelection params) -
          qBipartiteMatchMass strategy.state Hhat Hhat ≤
        addInUError params eps delta := by
      linarith [(abs_le.mp htransfer_release_hhat).1]
    linarith [hproducer.residualLowerBound, hreleaseGap]
  have hhelperGap_absorbed :
      subMeasMass strategy.state Hhat.liftLeft -
          qBipartiteMatchMass strategy.state Hhat Hhat ≤
        selfImprovementHelperError params eps delta := by
    have habsorb :=
      helper_strong_self_consistency_error_le_selfImprovementHelperError
        params eps delta heps hdelta hd_le_q
    linarith
  have hhelperErr_nonneg :
      0 ≤ selfImprovementHelperError params eps delta := by
    exact selfImprovementHelperError_nonneg params eps delta heps hdelta
  constructor
  simpa [bipartiteSSCError, avgOver, uniformDistribution, constSubMeasFamily,
    qBipartiteSSCDefect, subMeasMass, SubMeas.liftLeft] using
    (max_le hhelperErr_nonneg hhelperGap_absorbed)

/-- Promote a producer of the four add-in-`u`/variance helper-SSC bounds to the
`HelperStrongSelfConsistencyInput` surface consumed by `selfImprovement`.

This theorem does not alter the `selfImprovement` statement. It narrows the
remaining hypothesis from the final `BipartiteSSCRel` conclusion to a producer
which consumes the actual helper output together with the named intermediate
transport bounds. -/
theorem helper_strong_self_consistency_input_of_producer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    (hd_le_q : (params.d : Error) ≤ (params.q : Error))
    (hproducer :
      ∀ {T : Measurement (Polynomial params) ι}
        {Hhat : SubMeas (Polynomial params) ι}
        {Z : MIPStarRE.Quantum.Op ι},
        SelfImprovementHelperConclusion params strategy T Hhat Z eps delta →
          HelperStrongSelfConsistencyProducerInputs
            params strategy T Hhat eps delta) :
    HelperStrongSelfConsistencyInput params strategy eps delta := by
  intro T Hhat Z hhelper
  exact helper_strong_self_consistency_of_helper_conclusion
    params strategy eps delta heps hdelta hd_le_q hhelper (hproducer hhelper)

/-! ## Final-fields projective-residual boundedness transport (issue #931)

The boundedness paragraph of `thm:self-improvement` first compares the
projective residual against the point-agreement average and then replaces the
projective family `H` by the helper family `Hhat` through the data-processing
SDD bound. The lemma below isolates the second step: it transports the scalar
helper boundedness gap across
`selfConsistencyImpliesDataProcessing`.

This is not a raw residual assumption and does not restate `FinalFieldsInput`;
it is the checked `easy-approx-from-approx-delta` part of
`references/ldt-paper/self_improvement.tex` lines 747--755, mirrored in
`blueprint/src/chapter/ch07_self_improvement.tex` lines 609--618. -/

private lemma helper_agreement_average_ev_eq_avg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι) :
    ev strategy.state (helperAgreementAverageOperator params strategy H) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ a : Fq params,
          ev strategy.state
            (opTensor ((strategy.pointMeasurement u).outcome a)
              ((evaluateAt params u H).outcome a))) := by
  rw [helperAgreementAverageOperator, ev_averageOperatorOverDistribution]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  simp [helperAgreementOperatorAtPoint, ev_sum]

/-- Reindexing identity for the pointwise helper-agreement operator.

The fiberwise definition `H_{[h(u)=a]} := ∑_{h : h(u)=a} H_h` collapses the
`a`-summed expression `∑_a A^u_a ⊗ H_{[h(u)=a]}` to the polynomial-indexed sum
`∑_h A^u_{h(u)} ⊗ H_h`, by expanding the tensor product fiberwise and applying
`Finset.sum_fiberwise` along `h ↦ h u`.

This is the first equality of the boundedness display in the proof of
`\ref{item:self-improvement-boundedness}`:
`references/ldt-paper/self_improvement.tex` line 612, mirrored at
`blueprint/src/chapter/ch07_self_improvement.tex` lines 274--282
("Reindexing the sum by~$h$"). It is a purely algebraic identity — no estimate,
no measurement structure used beyond the postprocess fiber decomposition built
into `evaluateAt`. -/
theorem helperAgreementOperatorAtPoint_eq_sum_polynomial
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι)
    (u : Point params) :
    helperAgreementOperatorAtPoint params strategy H u =
      ∑ h : Polynomial params,
        opTensor ((strategy.pointMeasurement u).outcome (h u))
          (H.outcome h) := by
  classical
  -- First reduce `helperAgreementOperatorAtPoint`'s `evaluateAt` to the explicit
  -- fiber sum on each summand; everything else then follows from
  -- `Finset.sum_fiberwise` along `h ↦ h u` and bilinearity of `opTensor`.
  have hexpand :
      helperAgreementOperatorAtPoint params strategy H u =
        ∑ a : Fq params,
          opTensor ((strategy.pointMeasurement u).outcome a)
            (∑ h ∈ Finset.univ.filter
                (fun h : Polynomial params => h u = a), H.outcome h) := by
    change (∑ a : Fq params,
        opTensor ((strategy.pointMeasurement u).outcome a)
          ((evaluateAt params u H).outcome a)) = _
    refine Finset.sum_congr rfl ?_
    intro a _
    have hev :
        (evaluateAt params u H).outcome a =
          ∑ h ∈ Finset.univ.filter
              (fun h : Polynomial params => h u = a), H.outcome h := by
      ext i j
      simp only [evaluateAt, postprocess]
      convert rfl
    rw [hev]
  rw [hexpand]
  calc
    ∑ a : Fq params,
        opTensor ((strategy.pointMeasurement u).outcome a)
          (∑ h ∈ Finset.univ.filter
              (fun h : Polynomial params => h u = a), H.outcome h)
        = ∑ a : Fq params, ∑ h ∈ Finset.univ.filter
              (fun h : Polynomial params => h u = a),
            opTensor ((strategy.pointMeasurement u).outcome a) (H.outcome h) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [opTensor_sum_right_finset]
      _ = ∑ a : Fq params, ∑ h ∈ Finset.univ.filter
              (fun h : Polynomial params => h u = a),
            opTensor ((strategy.pointMeasurement u).outcome (h u)) (H.outcome h) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              refine Finset.sum_congr rfl ?_
              intro h hh
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
              rw [show h u = a from hh]
      _ = ∑ h : Polynomial params,
            opTensor ((strategy.pointMeasurement u).outcome (h u)) (H.outcome h) := by
              simpa using
                Finset.sum_fiberwise (Finset.univ : Finset (Polynomial params))
                  (fun h : Polynomial params => h u)
                  (fun h =>
                    opTensor ((strategy.pointMeasurement u).outcome (h u))
                      (H.outcome h))

/-- Reindexed expansion of the averaged helper-agreement operator.

Combining the pointwise reindexing identity
`helperAgreementOperatorAtPoint_eq_sum_polynomial` with
`helper_agreement_average_ev_eq_avg`, the scalar
`⟨ψ| E_u Σ_a A^u_a ⊗ H_{[h(u)=a]} |ψ⟩` equals the polynomial-indexed expectation
`E_u Σ_h ⟨ψ| A^u_{h(u)} ⊗ H_h |ψ⟩` from the second line of the boundedness
display in the proof of `\ref{item:self-improvement-boundedness}`
(`references/ldt-paper/self_improvement.tex` line 612;
`blueprint/src/chapter/ch07_self_improvement.tex` lines 274--282). -/
theorem helper_agreement_average_ev_eq_polynomial_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (H : SubMeas (Polynomial params) ι) :
    ev strategy.state (helperAgreementAverageOperator params strategy H) =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((strategy.pointMeasurement u).outcome (h u))
              (H.outcome h))) := by
  rw [helper_agreement_average_ev_eq_avg]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  have hpt :
      helperAgreementOperatorAtPoint params strategy H u =
        ∑ h : Polynomial params,
          opTensor ((strategy.pointMeasurement u).outcome (h u)) (H.outcome h) :=
    helperAgreementOperatorAtPoint_eq_sum_polynomial params strategy H u
  have hpt_ev :
      ev strategy.state (helperAgreementOperatorAtPoint params strategy H u) =
        ∑ h : Polynomial params,
          ev strategy.state
            (opTensor ((strategy.pointMeasurement u).outcome (h u))
              (H.outcome h)) := by
    rw [hpt, ev_sum]
  -- The LHS goal is the unfolded `helperAgreementOperatorAtPoint`-summand at `u`.
  simp only [helperAgreementOperatorAtPoint, ev_sum] at hpt_ev
  exact hpt_ev

/-- Transport the helper boundedness gap through the data-processing
approximation between `Hhat` and `H`.

The input `hdata` is exactly the data-processing SDD bound already produced
inside `selfImprovement`. The conclusion says that replacing the helper
polynomial family in the point-agreement average by the projective family costs
at most `sqrt ε`, matching Proposition `easy-approx-from-approx-delta` in the
boundedness paragraph of the paper. -/
theorem helper_boundedness_gap_transport_through_data_processing
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (Hhat : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (ε : Error)
    (hdata :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftLeft)
        ((polynomialEvaluationFamily params H.toSubMeas).liftLeft)
        ε) :
    helperBoundednessGap params strategy H.toSubMeas Z ≤
      helperBoundednessGap params strategy Hhat Z + Real.sqrt ε := by
  have hdata_right :
      SDDRel strategy.state (uniformDistribution (Point params))
        ((polynomialEvaluationFamily params Hhat).liftRight)
        ((polynomialEvaluationFamily params H.toSubMeas).liftRight)
        ε := by
    simpa [IdxSubMeas.liftLeft, IdxSubMeas.liftRight]
      using
        sddRel_liftRight_of_liftLeft_permInv
          strategy.permInvState (uniformDistribution (Point params))
          (polynomialEvaluationFamily params Hhat)
          (polynomialEvaluationFamily params H.toSubMeas) ε hdata
  have happrox :=
    Preliminaries.easyApproxFromApproxDelta
      strategy.state strategy.isNormalized
      (uniformDistribution (Point params))
      (uniformDistribution_weight_sum_le_one (Point params))
      ((polynomialEvaluationFamily params Hhat).liftRight)
      ((polynomialEvaluationFamily params H.toSubMeas).liftRight)
      (IdxSubMeas.liftLeft (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement))
      ε hdata_right
  have hscalar :
      |ev strategy.state (helperAgreementAverageOperator params strategy Hhat) -
        ev strategy.state (helperAgreementAverageOperator params strategy H.toSubMeas)| ≤
        Real.sqrt ε := by
    rw [helper_agreement_average_ev_eq_avg params strategy Hhat,
      helper_agreement_average_ev_eq_avg params strategy H.toSubMeas]
    simpa [polynomialEvaluationFamily, evaluateAt, IdxSubMeas.liftRight,
      IdxSubMeas.liftLeft, IdxProjMeas.toIdxSubMeas,
      rightTensor_mul_leftTensor_eq_opTensor] using happrox
  unfold helperBoundednessGap helperBoundednessOperator
  rw [ev_sub, ev_sub]
  have hle := le_abs_self
    (ev strategy.state (helperAgreementAverageOperator params strategy Hhat) -
      ev strategy.state (helperAgreementAverageOperator params strategy H.toSubMeas))
  linarith

/-- Final-fields producer for the `BoundedByOperator` conclusion.

If the SDP dual witness dominates the identity, then the left-placed mass of any
submeasurement is dominated by `Z ⊗ I`: the total bound `A.total ≤ 1 ≤ Z` lifts
by monotonicity to `leftTensor A.total ≤ leftTensor Z`, and evaluation against
the state preserves this order. Consequently `bndError ψ A.liftLeft (Z ⊗ I) = 0`,
so the boundedness statement holds at any nonnegative tolerance. This is a
standalone producer; it does not alter the current `FinalFieldsInput` interface. -/
theorem final_fields_bounded
    {α : Type*} [Fintype α]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas α ι)
    {Z : MIPStarRE.Quantum.Op ι}
    (hOne : (1 : MIPStarRE.Quantum.Op ι) ≤ Z)
    {ε : Error}
    (hε : 0 ≤ ε) :
    BoundedByOperator ψ A.liftLeft (leftTensor (ι₂ := ι) Z) ε := by
  refine
    { witnessOpPSD := ?_
      upperBound := ?_ }
  · have : leftTensor (ι₂ := ι) Z = opTensor Z (1 : MIPStarRE.Quantum.Op ι) := rfl
    rw [this]
    have hPSD : 0 ≤ Z := le_trans (op_one_nonneg (d := ι)) hOne
    exact opTensor_nonneg hPSD op_one_nonneg
  · have hAle : A.total ≤ Z :=
      le_trans A.total_le_one hOne
    have hLTle :
        leftTensor (ι₂ := ι) A.total ≤ leftTensor (ι₂ := ι) Z := by
      have hopMono :
          opTensor A.total (1 : MIPStarRE.Quantum.Op ι) ≤
            opTensor Z (1 : MIPStarRE.Quantum.Op ι) :=
        opTensor_mono_left hAle op_one_nonneg
      simpa [leftTensor, opTensor] using hopMono
    have hsubmass :
        subMeasMass ψ A.liftLeft = ev ψ (leftTensor (ι₂ := ι) A.total) := rfl
    have hev_le :
        ev ψ (leftTensor (ι₂ := ι) A.total) ≤ ev ψ (leftTensor (ι₂ := ι) Z) :=
      ev_mono ψ _ _ hLTle
    have hbnd_zero :
        bndError ψ A.liftLeft (leftTensor (ι₂ := ι) Z) = 0 := by
      unfold bndError
      rw [hsubmass]
      have :
          ev ψ (leftTensor (ι₂ := ι) A.total) -
              ev ψ (leftTensor (ι₂ := ι) Z) ≤ 0 := by
        linarith
      exact max_eq_left this
    rw [hbnd_zero]
    exact hε

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

/-! ## Final-fields completeness producer (issue #931)

The reduced `FinalFieldsInput` lumps five distinct paper-side obligations into a
single residual. The lemmas below isolate the **completeness** field, exposing
the precise analytic ingredient that is still missing — the helper-stage
completeness lower bound on `Hhat.liftLeft` — and discharging the rest of the
transport algebra (orthonormalization SDD step) with a checked proof.

Concretely, `completeness_transport_through_orthonormalization` is a generic
transport theorem that lifts `completenessTransferSelfConsistentA` (already
proved in `Preliminaries.SelfConsistency.Extensions`) to the
`Unit`-indexed constant-family setting used by `selfImprovement`.
`final_fields_completeness_of_helper_completeness` specializes that to the
self-improvement parameters and yields the precise `(1 - nu) - δ - 2 √ε`
target on `H.toSubMeas.liftLeft`.

This does **not** add a raw residual: the residual hypothesis has been narrowed
from the entire `FinalFieldsInput` lump to the single named paper obligation
`hhelperCompleteness`, which corresponds to `self_improvement.tex` lines
351--414 (helper completeness, especially the Cauchy--Schwarz step at lines
366--414) followed by the projective transfer at lines 713--717. The remaining
four `FinalFieldsInput` fields (point-consistency, self-closeness,
projective-residual, boundedness) are not addressed here.

Paper anchors:
* `references/ldt-paper/self_improvement.tex` lines 351--414 — helper-stage
  completeness `⟨ψ|Hhat ⊗ I|ψ⟩ ≥ 1 - ν - O(...)`, with the Cauchy--Schwarz
  argument fed by the input consistency hypothesis on `G` and `nu` at lines
  366--414. The blueprint mirror is
  `blueprint/src/chapter/ch07_self_improvement.tex` lines 101--142.
* `references/ldt-paper/self_improvement.tex` lines 713--717 — projective
  transport of completeness from `Hhat` to `H` using strong self-consistency
  and the orthonormalization SDD bound.
-/

private lemma idx_sub_meas_mass_uniform_unit_const_sub_meas_family_lift_left
    {α : Type*} [Fintype α]
    (ψ : QuantumState (ι × ι)) (A : SubMeas α ι) :
    idxSubMeasMass ψ (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily A)) =
      subMeasMass ψ A.liftLeft := by
  simp [idxSubMeasMass, avgOver, uniformDistribution, constSubMeasFamily,
    IdxSubMeas.liftLeft, SubMeas.liftLeft]

/-- Completeness transport through helper-stage strong self-consistency and the
orthonormalization SDD step, for the `Unit`-indexed constant-family setting
used by the self-improvement pipeline.

This is the orthonormalization transport ingredient of the final-fields
completeness producer for `thm:self-improvement` (issue #931). Given:

* `hcomplete` — completeness of the *helper-stage* submeasurement `A` at level
  `m`, expressed as `subMeasMass ψ A.liftLeft ≥ m`. This is the still-missing
  paper obligation; with the current API the only way to obtain it is from the
  Cauchy--Schwarz argument in `references/ldt-paper/self_improvement.tex`
  lines 351--414, especially lines 366--414, which uses the incoming
  consistency hypothesis on `G` and `nu`.
* `hssc` — bipartite strong self-consistency of `A` (the helper SSC supplied
  by `HelperStrongSelfConsistencyInput`).
* `hsdd` — the orthonormalization SDD bound between the left lifts of `A` and
  `B` (the SDD bound supplied by the orthonormalization step inside
  `selfImprovement`).

The conclusion is the projective-stage completeness of `B.liftLeft` with the
natural sum-of-errors `m - δ - 2 √ε` from the paper transport.

The proof reduces to `completenessTransferSelfConsistentA` after rewriting
`idxSubMeasMass` of a `Unit`-indexed constant family as `subMeasMass`. -/
theorem completeness_transport_through_orthonormalization
    {α : Type*} [Fintype α]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (A B : SubMeas α ι)
    (m δ ε : Error)
    (hcomplete : CompletenessAtLeast strategy.state A.liftLeft m)
    (hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily A) δ)
    (hsdd :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily A))
        (IdxSubMeas.liftLeft (constSubMeasFamily B)) ε) :
    CompletenessAtLeast strategy.state B.liftLeft (m - δ - 2 * Real.sqrt ε) := by
  -- Mass equalities for `Unit`-indexed constant families.
  have hA_eq :
      idxSubMeasMass strategy.state (uniformDistribution Unit)
          (IdxSubMeas.liftLeft (constSubMeasFamily A)) =
        subMeasMass strategy.state A.liftLeft :=
    idx_sub_meas_mass_uniform_unit_const_sub_meas_family_lift_left strategy.state A
  have hB_eq :
      idxSubMeasMass strategy.state (uniformDistribution Unit)
          (IdxSubMeas.liftLeft (constSubMeasFamily B)) =
        subMeasMass strategy.state B.liftLeft :=
    idx_sub_meas_mass_uniform_unit_const_sub_meas_family_lift_left strategy.state B
  -- Apply the bipartite-SSC + SDD completeness transfer at `Question = Unit`.
  have htransfer :=
    Preliminaries.completenessTransferSelfConsistentA
      strategy.state strategy.permInvState strategy.isNormalized
      (uniformDistribution Unit)
      (uniformDistribution_weight_sum_le_one Unit)
      (constSubMeasFamily A) (constSubMeasFamily B) δ ε hssc hsdd
  rw [hA_eq, hB_eq] at htransfer
  rcases hcomplete with ⟨hAmass⟩
  refine ⟨?_⟩
  -- `hAmass : m ≤ subMeasMass ψ A.liftLeft`
  -- `htransfer : subMeasMass ψ A.liftLeft - δ - 2 √ε ≤ subMeasMass ψ B.liftLeft`
  linarith

/-- Final-fields completeness producer (issue #931).

Given the still-missing helper-stage completeness lower bound on `Hhat.liftLeft`
together with the helper-stage strong self-consistency of `Hhat` and the
orthonormalization SDD bound between `Hhat.liftLeft` and `H.toSubMeas.liftLeft`
(the latter two are already produced inside `selfImprovement`), this checked
theorem derives the `completeness` field of `SelfImprovementFinalFields`.

The output bound is the **natural** paper sum

```
(1 - nu) - selfImprovementHelperError - selfImprovementHelperError
         - 2 * sqrt (selfImprovementOrthogonalizationError)
```

rather than `(1 - nu) - selfImprovementError`. Comparing the two thresholds is
a separate numerical step on the explicit error definitions
(`selfImprovementHelperError`, `selfImprovementOrthogonalizationError`,
`selfImprovementError`) that does not require any new analytic input.

This narrows the missing input for the `completeness` field of
`FinalFieldsInput` from the entire five-field residual to the single named
paper obligation `hhelperCompleteness` matching
`references/ldt-paper/self_improvement.tex` lines 351--414, which is the only
remaining analytic step (especially the Cauchy--Schwarz argument at lines
366--414 that feeds on `G`/`nu` and the strategy's input consistency). The
blueprint mirror is `blueprint/src/chapter/ch07_self_improvement.tex` lines
101--142.

The hypothesis uses the weaker `(1 - nu) - selfImprovementHelperError`
bookkeeping expected by the final-fields chain. A future helper-completeness
producer may prove the paper's tighter `1 - ν - 3√δ` bound and then weaken it
to this threshold.

It does **not** assume the projective completeness it produces, and it does
**not** restate `FinalFieldsInput`. -/
theorem final_fields_completeness_of_helper_completeness
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta nu : Error)
    (Hhat : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (hhelperCompleteness :
      CompletenessAtLeast strategy.state Hhat.liftLeft
        ((1 - nu) - selfImprovementHelperError params eps delta))
    (hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta)) :
    CompletenessAtLeast strategy.state H.toSubMeas.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta
        - selfImprovementHelperError params eps delta
        - 2 * Real.sqrt (selfImprovementOrthogonalizationError params eps delta)) := by
  -- The orthonormalization SDD bound is stated on `constSubMeasFamily` of the
  -- left lifts; rewrite it into the `IdxSubMeas.liftLeft` form expected by the
  -- generic transport theorem.
  have hsdd :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily Hhat))
        (IdxSubMeas.liftLeft (constSubMeasFamily H.toSubMeas))
        (selfImprovementOrthogonalizationError params eps delta) := by
    simpa [IdxSubMeas.liftLeft, constSubMeasFamily] using horth
  -- Apply the generic transport theorem.
  have hresult :=
    completeness_transport_through_orthonormalization params strategy Hhat H.toSubMeas
      ((1 - nu) - selfImprovementHelperError params eps delta)
      (selfImprovementHelperError params eps delta)
      (selfImprovementOrthogonalizationError params eps delta)
      hhelperCompleteness hssc hsdd
  -- Rearrange `(1 - nu - δ) - δ - 2 √ε` into the displayed form.
  refine ⟨?_⟩
  rcases hresult with ⟨hresult⟩
  linarith


/-! ## Final-fields self-closeness producer (issue #931)

Same playbook as `final_fields_completeness_of_helper_completeness`, but for
the `selfCloseness` field. Unlike completeness, this field is closed
**without any new analytic obligation**: the helper-stage strong
self-consistency `hssc` and the orthonormalization SDD bound `horth` already
supplied to `selfImprovement` together suffice, by combining the bipartite-SSC
left↔right transport (`twoNotionsOfSelfConsistency`), the perm-inv
left↔right SDD reflection
(`MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv`), and the
three-step SDD triangle inequality
(`Preliminaries.stateDependentDistanceRel_triangle_three`).

Concretely the chain is `H.liftLeft → Hhat.liftLeft → Hhat.liftRight →
H.liftRight`, with edges of error `ε`, `2δ`, `ε` and the triangle constant `3`,
giving the final `3 * (ε + 2δ + ε)` bound. The remaining gap to the literal
`selfImprovementError` threshold used inside `SelfImprovementFinalFields` is a
separate numerical comparison on the explicit error definitions.

This is **not** a raw residual: the producer derives the entire
`selfCloseness` field from data already present in the `selfImprovement`
proof. It does not assume the projective self-closeness it produces and does
not restate `FinalFieldsInput`.

Paper anchors:
* `references/ldt-paper/self_improvement.tex` lines 727--741 — projective
  self-closeness `Hhat ⊗ I ≈ I ⊗ Hhat → H ⊗ I ≈ I ⊗ H` via the
  triangle. The corresponding blueprint paragraph is
  `blueprint/src/chapter/ch07_self_improvement.tex` `\emph{Proof of
  \ref{item:self-improvement-self-closeness}}`.
-/

/-- Generic self-closeness transport through helper-stage strong
self-consistency and the orthonormalization SDD step, for the `Unit`-indexed
constant-family setting used by the self-improvement pipeline.

Given:
* `hssc` — bipartite strong self-consistency of the helper submeasurement `A`
  (helper SSC).
* `horth` — orthonormalization SDD bound between the left lifts of `A` and
  the projective replacement `B`.

Conclusion: SDD between the left and right placements of `B`, with the natural
three-step paper sum `3 * (ε + 2δ + ε)`.

Proof: `twoNotionsOfSelfConsistency` gives `A.liftLeft ≃_{2δ} A.liftRight`;
`sddRel_liftRight_of_liftLeft_permInv` reflects `horth` to a right-lift bound;
the triangle `B.liftLeft ↔ A.liftLeft ↔ A.liftRight ↔ B.liftRight` then
applies `stateDependentDistanceRel_triangle_three`. -/
theorem self_closeness_transport_through_orthonormalization
    {α : Type*} [Fintype α]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (A B : SubMeas α ι)
    (δ ε : Error)
    (hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily A) δ)
    (horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily A))
        (IdxSubMeas.liftLeft (constSubMeasFamily B)) ε) :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily B.liftLeft)
      (constSubMeasFamily B.liftRight)
      (3 * (ε + 2 * δ + ε)) := by
  -- Step 1 — helper bipartite SSC + perm inv ⇒ A.liftLeft ≃_{2δ} A.liftRight.
  have hA_lr :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily A))
        (IdxSubMeas.liftRight (constSubMeasFamily A)) (2 * δ) :=
    Preliminaries.twoNotionsOfSelfConsistency strategy.state
      (uniformDistribution Unit) (constSubMeasFamily A) δ
      ⟨strategy.permInvState, hssc⟩
  -- Step 2 — orthonormalization SDD reflected to right lifts.
  have horth_right :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftRight (constSubMeasFamily A))
        (IdxSubMeas.liftRight (constSubMeasFamily B)) ε :=
    MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv
      strategy.permInvState (uniformDistribution Unit)
      (constSubMeasFamily A) (constSubMeasFamily B) ε horth
  -- Step 3 — symmetrize the orthonormalization SDD on the left lifts.
  have horth_left_swap :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily B))
        (IdxSubMeas.liftLeft (constSubMeasFamily A)) ε :=
    Preliminaries.sddRel_symm strategy.state (uniformDistribution Unit)
      (IdxSubMeas.liftLeft (constSubMeasFamily A))
      (IdxSubMeas.liftLeft (constSubMeasFamily B)) ε horth
  -- Step 4 — three-step triangle B.liftLeft → A.liftLeft → A.liftRight → B.liftRight.
  have htri :=
    Preliminaries.stateDependentDistanceRel_triangle_three (Question := Unit)
      (Outcome := α) strategy.state (uniformDistribution Unit)
      (IdxSubMeas.liftLeft (constSubMeasFamily B))
      (IdxSubMeas.liftLeft (constSubMeasFamily A))
      (IdxSubMeas.liftRight (constSubMeasFamily A))
      (IdxSubMeas.liftRight (constSubMeasFamily B))
      ε (2 * δ) ε horth_left_swap hA_lr horth_right
  -- Reshape the IdxSubMeas.liftLeft/liftRight wrappers back to constSubMeasFamily form.
  simpa [IdxSubMeas.liftLeft, IdxSubMeas.liftRight, constSubMeasFamily] using htri

/-- Final-fields self-closeness producer (issue #931).

Specializes `self_closeness_transport_through_orthonormalization` to the
self-improvement parameters. Given the helper-stage bipartite SSC of `Hhat`
and the orthonormalization SDD bound between `Hhat.liftLeft` and
`H.toSubMeas.liftLeft` (both already produced inside `selfImprovement`), this
checked theorem derives the `selfCloseness` field of
`SelfImprovementFinalFields` with the natural paper sum-of-errors
`3 * (selfImprovementOrthogonalizationError +
      2 * selfImprovementHelperError +
      selfImprovementOrthogonalizationError)`.

Crucially, this producer adds **no** new analytic hypothesis: both `hssc` and
`horth` are already supplied to `selfImprovement`, so the `selfCloseness`
field of `SelfImprovementFinalFields` is now fully derivable up to a numerical
threshold comparison. -/
theorem final_fields_self_closeness
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    (Hhat : SubMeas (Polynomial params) ι)
    (H : ProjSubMeas (Polynomial params) ι)
    (hssc :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
    (horth :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat.liftLeft)
        (constSubMeasFamily H.toSubMeas.liftLeft)
        (selfImprovementOrthogonalizationError params eps delta)) :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (leftPlacedSubMeas (ιB := ι) H.toSubMeas))
      (constSubMeasFamily
        (rightPlacedSubMeas (ιA := ι) H.toSubMeas))
      (3 * (selfImprovementOrthogonalizationError params eps delta
        + 2 * selfImprovementHelperError params eps delta
        + selfImprovementOrthogonalizationError params eps delta)) := by
  -- Reshape `horth` into the `IdxSubMeas.liftLeft` form expected by the
  -- generic transport theorem.
  have horthIdx :
      SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft (constSubMeasFamily Hhat))
        (IdxSubMeas.liftLeft (constSubMeasFamily H.toSubMeas))
        (selfImprovementOrthogonalizationError params eps delta) := by
    simpa [IdxSubMeas.liftLeft, constSubMeasFamily] using horth
  -- Apply the generic transport theorem.
  have hresult :=
    self_closeness_transport_through_orthonormalization params strategy
      Hhat H.toSubMeas
      (selfImprovementHelperError params eps delta)
      (selfImprovementOrthogonalizationError params eps delta)
      hssc horthIdx
  -- Reshape `B.liftLeft / B.liftRight` into the `leftPlacedSubMeas /
  -- rightPlacedSubMeas` form used by the `selfCloseness` field.
  simpa [SubMeas.liftLeft, SubMeas.liftRight,
    leftPlacedSubMeas, rightPlacedSubMeas, constSubMeasFamily] using hresult

end MIPStarRE.LDT.SelfImprovement
