import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.GlobalVariance.Theorems.Results
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.CommonHelpers

/-!
# Helper completeness and SDP bridge

Input-consistency lower bounds, SDP dual feasibility, helper-mass
identities, and the reduced `sdp` and `addInU` wrappers.

## Contents

- **input_consistency_match_mass_lower_bound** — the incoming `ConsRel`
  gives `1 - nu ≤ avgOver matchMass` (paper lines 407–414).
- **input_match_mass_eq_sdp_overlap** — reindex the averaged overlap as
  `Σ_g ⟨ψ, A_g ⊗ G_g⟩` (paper lines 410–411).
- **sdp_overlap_le_dual_mass** — dual feasibility upper-bounds the SDP
  overlap by `⟨ψ, Z ⊗ I ψ⟩` (paper lines 408–410).
- **input_consistency_dual_mass_lower_bound** — the combined lower bound
  `1 - nu ≤ ev ψ (leftTensor Z)` (paper lines 406–412).
- **sdp_complementary_slackness_sum_eq_dual_mass** — converts the
  complementary-slackness sum `Σ_h T_h(E_u A^u_{h(u)})` to the dual mass
  `⟨ψ, Z ⊗ I ψ⟩`.
- **helper_linearized_completeness_eq_dual_mass_of_complementary_slackness** —
  the final average-over-`u` algebraic SDP rewrite after the Cauchy--Schwarz
  moves.
- **helper_completeness_of_dual_mass_lower_bound** — combines the
  `Hhat`-versus-`Z` comparison with the dual-mass lower bound.
- **helper_completeness_of_input_consistency** — uses SDP dual feasibility and
  input consistency to produce the helper-stage completeness bound from the
  `Hhat`-versus-`Z` comparison.
- **helper_mass_eq_avg_pointwise_sandwich_sum** — exact Ĥ reindexing for
  the helper-stage left-tensor mass (paper lines 354–356).
- **helper_pointwise_sandwich_sum_eq_bracketed** / **helper_mass_eq_avg_pointwise_bracketed_sum** —
  fiberwise bracketing identity (paper lines 356–358).
- **sdp** — reduced wrapper instantiating the paper's SDP primal/dual
  witnesses.
- **addInU** — reduced wrapper for `AddInUStatement` from the
  global-variance transport chain.

## References

- `references/ldt-paper/self_improvement.tex` lines 354–468
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/


namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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

/-- Reindex a polynomial sum by the value of the polynomial at a fixed point.

This is the finite fiber decomposition used in the input-mass SDP bridge. The
lemma keeps the `Finset.sum_fiberwise` invocation separate from the tensor
algebra in `input_match_mass_eq_sdp_overlap`. -/
private lemma input_sdp_overlap_fiberwise_sum_eq
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (u : Point params) :
    (∑ g : Polynomial params,
        ev strategy.state
          (opTensor (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
            (G.outcome g))) =
      ∑ a : Fq params,
        ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
          ev strategy.state
            (opTensor (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
              (G.outcome g)) := by
  classical
  simpa using (Finset.sum_fiberwise Finset.univ
    (fun g : Polynomial params => g u)
    (fun g =>
      ev strategy.state
        (opTensor (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
          (G.outcome g)))).symm

/-- The bracketed fiber expression is exactly the bipartite matching mass of
the point measurement against the polynomial measurement evaluated at `u`. -/
private lemma input_sdp_bracketed_sum_eq_match_mass
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : SubMeas (Polynomial params) ι)
    (u : Point params) :
    (∑ a : Fq params,
        ev strategy.state
          (opTensor ((strategy.pointMeasurement u).outcome a)
            (∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
              G.outcome g))) =
      qBipartiteMatchMass strategy.state
        ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) u)
        ((polynomialEvaluationFamily params G) u) := by
  classical
  unfold qBipartiteMatchMass polynomialEvaluationFamily evaluateAt postprocess
  refine Finset.sum_congr rfl ?_
  intro a _
  simp only [IdxProjMeas.toIdxSubMeas]
  congr 2
  refine Finset.sum_congr ?_ ?_
  · ext g
    simp
  · intro g _
    rfl

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
              rw [input_sdp_overlap_fiberwise_sum_eq]
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
              exact input_sdp_bracketed_sum_eq_match_mass params strategy G u
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

/-- Complementary slackness converts the averaged-point sum to the dual mass.

This is the exact algebraic replacement used at the end of
`references/ldt-paper/self_improvement.tex`, lines 397--403: after the
Cauchy--Schwarz moves have produced
`Σ_h ⟨ψ, T_h · (E_u A^u_{h(u)}) ⊗ I ψ⟩`, complementary slackness replaces
`T_h · (E_u A^u_{h(u)})` by `T_h · Z`, and the primal completeness
`Σ_h T_h = I` reduces the sum to `⟨ψ, Z ⊗ I ψ⟩`. -/
theorem sdp_complementary_slackness_sum_eq_dual_mass
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hT_total : T.total = 1)
    (hcomp :
      ∀ h : Polynomial params,
        sdpComplementarySlacknessEquation params strategy T Z h) :
    (∑ h : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            (T.outcome h * averagedPointOperator params strategy h))) =
      ev strategy.state (leftTensor (ι₂ := ι) Z) := by
  calc
    (∑ h : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            (T.outcome h * averagedPointOperator params strategy h)))
        =
      ∑ h : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι) (T.outcome h * Z)) := by
        refine Finset.sum_congr rfl ?_
        intro h _
        rw [← hcomp h]
    _ =
      ev strategy.state
        (leftTensor (ι₂ := ι)
          (∑ h : Polynomial params, T.outcome h * Z)) := by
        rw [← ev_finset_sum]
        congr 1
        rw [leftTensor_finset_sum]
    _ =
      ev strategy.state
        (leftTensor (ι₂ := ι) (T.total * Z)) := by
        rw [← Finset.sum_mul, T.sum_eq_total]
    _ = ev strategy.state (leftTensor (ι₂ := ι) Z) := by
        rw [hT_total, Matrix.one_mul]

/-- The final algebraic rewrite in the helper-completeness Cauchy--Schwarz
argument, isolated from the two analytic estimates.

After the two Cauchy--Schwarz moves in
`references/ldt-paper/self_improvement.tex`, lines 360--399, the remaining
linear expression is

`E_u Σ_h ⟨ψ, (T_h A^u_{h(u)}) ⊗ I ψ⟩`.

This theorem reindexes the average to
`Σ_h ⟨ψ, (T_h E_u A^u_{h(u)}) ⊗ I ψ⟩`, applies the complementary-slackness
identity `T_h E_u A^u_{h(u)} = T_h Z`, and finally invokes
`sdp_complementary_slackness_sum_eq_dual_mass` to use `Σ_h T_h = I`.
The statement deliberately keeps complementary slackness as an explicit
hypothesis; it is not a consequence of the current reduced
`SdpOptimalPair` interface. -/
theorem helper_linearized_completeness_eq_dual_mass_of_complementary_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hTtotal : T.total = 1)
    (hslack :
      ∀ h : Polynomial params,
        T.outcome h * averagedPointOperator params strategy h =
          T.outcome h * Z) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (T.outcome h *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h u))) =
      ev strategy.state (leftTensor (ι₂ := ι) Z) := by
  classical
  let 𝒟 := uniformDistribution (Point params)
  have hmul_avg :
      ∀ h : Polynomial params,
        averageOperatorOverDistribution 𝒟
            (fun u => T.outcome h *
              pointConditionedOutcomeOperatorAtPolynomial params strategy h u) =
          T.outcome h * averagedPointOperator params strategy h := by
    intro h
    calc
      averageOperatorOverDistribution 𝒟
          (fun u => T.outcome h *
            pointConditionedOutcomeOperatorAtPolynomial params strategy h u)
          =
        ∑ u ∈ 𝒟.support,
          𝒟.weight u •
            (T.outcome h *
              pointConditionedOutcomeOperatorAtPolynomial params strategy h u) := by
          rfl
      _ =
        ∑ u ∈ 𝒟.support,
          T.outcome h *
            (𝒟.weight u •
              pointConditionedOutcomeOperatorAtPolynomial params strategy h u) := by
          refine Finset.sum_congr rfl ?_
          intro u _
          rw [mul_smul_comm]
      _ =
        T.outcome h *
          (∑ u ∈ 𝒟.support,
            𝒟.weight u •
              pointConditionedOutcomeOperatorAtPolynomial params strategy h u) := by
          rw [Matrix.mul_sum]
      _ =
        T.outcome h * averagedPointOperator params strategy h := by
          rfl
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ h : Polynomial params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (T.outcome h *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h u)))
        =
      ∑ h : Polynomial params,
        avgOver (uniformDistribution (Point params)) (fun u =>
          ev strategy.state
            (leftTensor (ι₂ := ι)
              (T.outcome h *
                pointConditionedOutcomeOperatorAtPolynomial params strategy h u))) := by
        rw [avgOver_sum]
    _ =
      ∑ h : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            (T.outcome h * averagedPointOperator params strategy h)) := by
        refine Finset.sum_congr rfl ?_
        intro h _
        calc
          avgOver (uniformDistribution (Point params)) (fun u =>
              ev strategy.state
                (leftTensor (ι₂ := ι)
                  (T.outcome h *
                    pointConditionedOutcomeOperatorAtPolynomial params strategy h u)))
              =
            ev strategy.state
              (leftTensor (ι₂ := ι)
                (averageOperatorOverDistribution 𝒟
                  (fun u =>
                    T.outcome h *
                      pointConditionedOutcomeOperatorAtPolynomial params strategy h u))) := by
              exact (ev_opTensor_averageOperatorOverDistribution_left strategy.state
                𝒟
                (fun u =>
                  T.outcome h *
                    pointConditionedOutcomeOperatorAtPolynomial params strategy h u)
                (1 : MIPStarRE.Quantum.Op ι)).symm
          _ =
            ev strategy.state
              (leftTensor (ι₂ := ι)
                (T.outcome h * averagedPointOperator params strategy h)) := by
              rw [hmul_avg]
    _ = ev strategy.state (leftTensor (ι₂ := ι) Z) := by
        refine sdp_complementary_slackness_sum_eq_dual_mass
          params strategy T Z hTtotal ?_
        intro h
        exact (hslack h).symm

/-- Complementary-slackness conversion specialized to the SDP witness packaged
inside `SelfImprovementHelperConclusion`. -/
theorem helper_sdp_complementary_slackness_sum_eq_dual_mass
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hcomp :
      ∀ h : Polynomial params,
        sdpComplementarySlacknessEquation params strategy T.toSubMeas Z h) :
    (∑ h : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            (T.toSubMeas.outcome h * averagedPointOperator params strategy h))) =
      ev strategy.state (leftTensor (ι₂ := ι) Z) :=
  sdp_complementary_slackness_sum_eq_dual_mass params strategy T.toSubMeas Z
    hhelper.sdpWitness.primalTotalOperator hcomp

/-- Helper-stage completeness from the `Hhat`-versus-`Z` comparison and the
dual-mass lower bound.

The paper proves
`subMeasMass ψ Hhat.liftLeft ≥ ⟨ψ, Z ⊗ I, ψ⟩ - 3 √δ` by the two
Cauchy--Schwarz moves in the helper-completeness paragraph.  Once the separate
input-consistency argument gives `1 - ν ≤ ⟨ψ, Z ⊗ I, ψ⟩`, this theorem performs
the scalar assembly and absorbs the loss `3 √δ` into the helper threshold
`ζ̂ = selfImprovementHelperError params eps delta`. -/
theorem helper_completeness_of_dual_mass_lower_bound
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta nu : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hHhat_vs_Z :
      ev strategy.state (leftTensor (ι₂ := ι) Z) - 3 * Real.sqrt delta ≤
        subMeasMass strategy.state Hhat.liftLeft)
    (hdualMass :
      1 - nu ≤ ev strategy.state (leftTensor (ι₂ := ι) Z)) :
    CompletenessAtLeast strategy.state Hhat.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta) := by
  refine ⟨?_⟩
  have herr :=
    helper_completeness_error_le_selfImprovementHelperError params eps delta heps hdelta
  linarith

/-- Helper-stage completeness from input consistency and the
`Hhat`-versus-`Z` comparison.

This is the checked assembly of the final part of the helper-completeness
paragraph in `thm:self-improvement`.  The only analytic input still external is
the paper's Cauchy--Schwarz comparison
`subMeasMass ψ Hhat.liftLeft ≥ ⟨ψ, Z ⊗ I, ψ⟩ - 3 √δ`; the SDP dual-feasibility
fields of `SelfImprovementHelperConclusion` and the input consistency of `G`
produce the dual-mass lower bound internally. -/
theorem helper_completeness_of_input_consistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : Measurement (Polynomial params) ι)
    (eps delta nu : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hHhat_vs_Z :
      ev strategy.state (leftTensor (ι₂ := ι) Z) - 3 * Real.sqrt delta ≤
        subMeasMass strategy.state Hhat.liftLeft)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    CompletenessAtLeast strategy.state Hhat.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta) := by
  refine
    helper_completeness_of_dual_mass_lower_bound params strategy eps delta nu
      heps hdelta hHhat_vs_Z ?_
  exact
    input_consistency_dual_mass_lower_bound params strategy G Z nu
      hhelper.positiveSemidefiniteWitness hhelper.dualDominatesAveragedPoint hcons

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

/-- Operator-level fiberwise reindexing identity for the per-point sandwich
operator. Inside each fiber `{h : h u = a}` the inner `A^u_{h(u)}` is constant
(equal to `A^u_a`), and `Matrix.sum_mul`/`Matrix.mul_sum` pull this constant
factor through the sum over `T_h`. Mirrors the operator-level computation in
`sandwichedPolynomialSubMeasAt.total_le_one`. -/
private lemma sandwichedPolynomialOutcomeOperatorAt_sum_eq_bracketed
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) (u : Point params) :
    (∑ h : Polynomial params,
        sandwichedPolynomialOutcomeOperatorAt params strategy T u h) =
      ∑ a : Fq params,
        (strategy.pointMeasurement u).outcome a *
          (∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
            T.outcome h) *
          (strategy.pointMeasurement u).outcome a := by
  classical
  rw [show (∑ h : Polynomial params,
              sandwichedPolynomialOutcomeOperatorAt params strategy T u h) =
            ∑ a : Fq params,
              ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
                sandwichedPolynomialOutcomeOperatorAt params strategy T u h from by
          simpa using (Finset.sum_fiberwise Finset.univ
            (fun h : Polynomial params => h u)
            (sandwichedPolynomialOutcomeOperatorAt params strategy T u)).symm]
  refine Finset.sum_congr rfl ?_
  intro a _
  have hreplace :
      ∀ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
        sandwichedPolynomialOutcomeOperatorAt params strategy T u h =
          (strategy.pointMeasurement u).outcome a *
            T.outcome h *
            (strategy.pointMeasurement u).outcome a := by
    intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
    simp [sandwichedPolynomialOutcomeOperatorAt,
      pointConditionedOutcomeOperatorAtPolynomial, hh]
  rw [Finset.sum_congr rfl hreplace, ← Matrix.sum_mul, ← Matrix.mul_sum]

/-- Per-point bracketing identity for the helper-stage left-tensor mass.

Fiberwise reindexing by `h ↦ h(u)` and pulling `A^u_a · _ · A^u_a` through the
sum, `leftTensor`, and `ev` give the paper identity at a fixed point `u`:

  `Σ_h ⟨ψ| H^u_h ⊗ I |ψ⟩
    = Σ_a ⟨ψ| (A^u_a · T_{[h(u) = a]} · A^u_a) ⊗ I |ψ⟩`,

where `H^u_h = A^u_{h(u)} · T_h · A^u_{h(u)}` is
`sandwichedPolynomialOutcomeOperatorAt`, and the bracketed
`T_{[h(u) = a]} = Σ_{h : h u = a} T_h` is the inner fiber sum.

This is the identity `eq:bracketize-the-expression` of
`references/ldt-paper/self_improvement.tex`, lines 356--358 (mirrored at
`blueprint/src/chapter/ch07_self_improvement.tex`, lines 110--113), at a fixed
point `u` (before averaging). The conclusion is exact (not approximate) and
depends on no input-consistency, SDP, or self-consistency hypotheses; it is
purely an algebraic regrouping of `Σ_h H^u_h` by the value of `h` at `u`.

Composed with `helper_mass_eq_avg_pointwise_sandwich_sum` (PR #1119) this yields
the bracketed form `helper_mass_eq_avg_pointwise_bracketed_sum` of the
helper-stage `Hhat ⊗ I` mass, which is the starting point for the remaining
Cauchy--Schwarz reduction at `self_improvement.tex:360--403` toward
`eq:gonna-use-this-later-H-versus-Z`. -/
theorem helper_pointwise_sandwich_sum_eq_bracketed
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) (u : Point params) :
    (∑ h : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            (sandwichedPolynomialOutcomeOperatorAt params strategy T u h))) =
      ∑ a : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            ((strategy.pointMeasurement u).outcome a *
              (∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
                T.outcome h) *
              (strategy.pointMeasurement u).outcome a)) := by
  classical
  calc
    (∑ h : Polynomial params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            (sandwichedPolynomialOutcomeOperatorAt params strategy T u h)))
        =
      ev strategy.state
        (leftTensor (ι₂ := ι)
          (∑ h : Polynomial params,
            sandwichedPolynomialOutcomeOperatorAt params strategy T u h)) := by
        rw [← ev_finset_sum, leftTensor_finset_sum]
    _ =
      ev strategy.state
        (leftTensor (ι₂ := ι)
          (∑ a : Fq params,
            (strategy.pointMeasurement u).outcome a *
              (∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
                T.outcome h) *
              (strategy.pointMeasurement u).outcome a)) := by
        rw [sandwichedPolynomialOutcomeOperatorAt_sum_eq_bracketed]
    _ =
      ∑ a : Fq params,
        ev strategy.state
          (leftTensor (ι₂ := ι)
            ((strategy.pointMeasurement u).outcome a *
              (∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
                T.outcome h) *
              (strategy.pointMeasurement u).outcome a)) := by
        rw [← leftTensor_finset_sum, ev_finset_sum]

/-- Bracketed form of the helper-stage `Hhat ⊗ I` mass identity.

Combines `helper_mass_eq_avg_pointwise_sandwich_sum` (PR #1119) with the
per-point bracketing identity `helper_pointwise_sandwich_sum_eq_bracketed`:

  `⟨ψ| Hhat ⊗ I |ψ⟩
    = E_u Σ_a ⟨ψ| (A^u_a · T_{[h(u) = a]} · A^u_a) ⊗ I |ψ⟩`,

where `T_{[h(u) = a]} = Σ_{h : h u = a} T_h`. This is the second equality in the
displayed completeness chain at
`references/ldt-paper/self_improvement.tex`, lines 354--358 (mirrored at
`blueprint/src/chapter/ch07_self_improvement.tex`, lines 103--113), composed
with the bracketing reindexing `eq:bracketize-the-expression`. The conclusion
is exact (not approximate) and depends on no input-consistency, SDP, or
self-consistency hypotheses. -/
theorem helper_mass_eq_avg_pointwise_bracketed_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    subMeasMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T).liftLeft =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ a : Fq params,
          ev strategy.state
            (leftTensor (ι₂ := ι)
              ((strategy.pointMeasurement u).outcome a *
                (∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
                  T.outcome h) *
                (strategy.pointMeasurement u).outcome a))) := by
  rw [helper_mass_eq_avg_pointwise_sandwich_sum]
  refine avgOver_congr (uniformDistribution (Point params)) _ _ ?_
  intro u
  exact helper_pointwise_sandwich_sum_eq_bracketed params strategy T u

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
      dualDominatesIdentity := by
        simpa [Z] using one_le_sdpStrictDualWitness (ι := ι)
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


end MIPStarRE.LDT.SelfImprovement
