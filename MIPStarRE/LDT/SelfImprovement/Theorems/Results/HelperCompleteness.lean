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
- **helper_hhat_vs_z_of_cauchy_schwarz_and_complementary_slackness** — assembles
  the two scalar Cauchy--Schwarz estimates and complementary slackness into the
  recorded `Hhat`-versus-`Z` comparison.
- **helper_completeness_of_dual_mass_lower_bound** — combines the
  `Hhat`-versus-`Z` comparison with the dual-mass lower bound.
- **helper_completeness_of_input_consistency** — uses SDP dual feasibility and
  input consistency to produce the helper-stage completeness bound from the
  `Hhat`-versus-`Z` comparison.
- **helper_mass_eq_avg_pointwise_sandwich_sum** — exact Ĥ reindexing for
  the helper-stage left-tensor mass (paper lines 354–356).
- **helperFiberOperator**, **helperFiberOperator_nonneg**,
  **helperFiberOperator_le_one** — the fiber operator `T_[h(u)=a]` and its
  positivity / identity bounds.
- **helper_first_move_second_factor_le_one** — the identity bound for the
  second Cauchy--Schwarz factor in the first helper-completeness move.
- **helper_first_move_abs_sub_bracketed_le_two_sqrt_delta** — the first
  Cauchy--Schwarz move in the helper-completeness proof.
- **helper_second_move_first_factor_le_one** — the identity bound for the
  first Cauchy--Schwarz factor in the second helper-completeness move.
- **helper_second_move_second_factor_le_delta** — the self-consistency bound
  for the second Cauchy--Schwarz factor in the second helper-completeness move.
- **helper_linearized_completeness_quantity_eq_fiber_sum** — the fiberwise form
  of the linearized helper-completeness quantity.
- **helper_second_move_abs_sub_first_moved_le_sqrt_delta** — the second
  Cauchy--Schwarz move in the helper-completeness proof.
- **helperBracketedCompletenessQuantity**,
  **helper_pointwise_sandwich_sum_eq_bracketed**,
  **helper_mass_eq_avg_pointwise_bracketed_sum** — the fiberwise bracketed
  expression and its equality with the helper-stage Ĥ mass (paper lines
  356–358).
- **helper_hhat_vs_z_of_bracketed_cauchy_schwarz_and_complementary_slackness** —
  the paper-shaped assembly from the bracketed expression, the two
  Cauchy--Schwarz estimates, and complementary slackness.
- **helper_hhat_vs_z_of_self_consistency_and_complementary_slackness** — the
  `Hhat`-versus-`Z` comparison with both Cauchy--Schwarz estimates produced from
  point self-consistency.
- **helper_hhat_vs_z_of_self_consistency_and_helper_slackness** — the same
  comparison using the strengthened helper conclusion that carries SDP
  complementary slackness.
- **helper_sdp_optimal_pair_with_slackness** — reconstructs the slackness-carrying
  SDP pair from the strengthened helper conclusion.
- **helper_completeness_of_self_consistency_helper_slackness_input_consistency** —
  helper completeness with no separate `hslack` argument.
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
  simpa using polynomial_sum_fiberwise params u
    (fun g =>
      ev strategy.state
        (opTensor (pointConditionedOutcomeOperatorAtPolynomial params strategy g u)
          (G.outcome g)))

/-- The pointwise polynomial-evaluation family has the expected fiber outcome. -/
private lemma polynomialEvaluationFamily_outcome_eq_fiber_sum
    (params : Parameters)
    [FieldModel params.q]
    (G : SubMeas (Polynomial params) ι)
    (u : Point params)
    (a : Fq params) :
    ((polynomialEvaluationFamily params G) u).outcome a =
      ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a), G.outcome g := by
  rw [polynomialEvaluationFamily, evaluateAt, SubMeas.postprocess_outcome]

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
  unfold qBipartiteMatchMass
  refine Finset.sum_congr rfl ?_
  intro a _
  simp only [IdxProjMeas.toIdxSubMeas]
  rw [polynomialEvaluationFamily_outcome_eq_fiber_sum]

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

/-- The fiber operator `T_[h(u)=a]` in the helper-completeness proof.

It is the sum of all SDP-measurement outcomes indexed by polynomials whose
value at the point `u` is `a`. -/
noncomputable def helperFiberOperator
    (params : Parameters)
    [FieldModel params.q]
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) (a : Fq params) : MIPStarRE.Quantum.Op ι :=
  ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a), T.outcome h

/-- The helper fiber operator is positive. -/
theorem helperFiberOperator_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) (a : Fq params) :
    0 ≤ helperFiberOperator params T u a :=
  Finset.sum_nonneg fun h _ => T.outcome_pos h

/-- The helper fiber operator is bounded by the identity. -/
theorem helperFiberOperator_le_one
    (params : Parameters)
    [FieldModel params.q]
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) (a : Fq params) :
    helperFiberOperator params T u a ≤ 1 := by
  calc
    helperFiberOperator params T u a
        ≤ ∑ h : Polynomial params, T.outcome h :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) (fun h _ _ => T.outcome_pos h)
    _ = T.total := T.sum_eq_total
    _ ≤ 1 := T.total_le_one

/-- The fiber operators over all values at a fixed point sum to the total SDP
submeasurement operator. -/
theorem helperFiberOperator_sum_eq_total
    (params : Parameters)
    [FieldModel params.q]
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) :
    (∑ a : Fq params, helperFiberOperator params T u a) = T.total := by
  calc
    (∑ a : Fq params, helperFiberOperator params T u a)
        = ∑ h : Polynomial params, T.outcome h := by
          simpa [helperFiberOperator] using (polynomial_sum_fiberwise params u T.outcome).symm
    _ = T.total := T.sum_eq_total

/-- Pointwise operator form of the identity bound for the first
Cauchy--Schwarz factor in the second helper-completeness move.

At a fixed point `u`, the fiber operators form a submeasurement after grouping
by the value `h(u)`.  Thus `Σ_a T_[h(u)=a]^2 ≤ Σ_a T_[h(u)=a] = T.total ≤ I`. -/
theorem helper_second_move_first_factor_operator_le_one
    (params : Parameters)
    [FieldModel params.q]
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) :
    (∑ a : Fq params,
      let Tfiber := helperFiberOperator params T u a
      leftTensor (ι₂ := ι) (Tfiber * Tfiber)) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  calc
    (∑ a : Fq params,
      let Tfiber := helperFiberOperator params T u a
      leftTensor (ι₂ := ι) (Tfiber * Tfiber))
        ≤ ∑ a : Fq params, leftTensor (ι₂ := ι)
          (helperFiberOperator params T u a) := by
          refine Finset.sum_le_sum ?_
          intro a _
          have hT_nonneg : 0 ≤ helperFiberOperator params T u a :=
            helperFiberOperator_nonneg params T u a
          have hT_le_one : helperFiberOperator params T u a ≤ 1 :=
            helperFiberOperator_le_one params T u a
          have hT_sq_le : helperFiberOperator params T u a *
              helperFiberOperator params T u a ≤ helperFiberOperator params T u a :=
            MIPStarRE.Quantum.sq_le_self hT_nonneg hT_le_one
          simpa [leftTensor, opTensor] using
            (opTensor_mono_left (ι₂ := ι)
              (B := (1 : MIPStarRE.Quantum.Op ι)) hT_sq_le
              (zero_le_one : (0 : MIPStarRE.Quantum.Op ι) ≤ 1))
    _ = leftTensor (ι₂ := ι) (∑ a : Fq params, helperFiberOperator params T u a) := by
        rw [leftTensor_finset_sum]
    _ = leftTensor (ι₂ := ι) T.total := by
        rw [helperFiberOperator_sum_eq_total]
    _ ≤ 1 := leftTensor_le_one (ι₂ := ι) T.total_le_one

/-- The first Cauchy--Schwarz factor in the second helper-completeness move is
bounded by one.

This is the Lean form of the paper's assertion, following
`eq:mysterious-case-of-the-disappearing-a`, that
`E_u Σ_a ⟨ψ, T_[h(u)=a]^2 ⊗ I ψ⟩ ≤ 1`. -/
theorem helper_second_move_first_factor_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      ∑ a : Fq params,
        let Tfiber := helperFiberOperator params T u a
        ev strategy.state (leftTensor (ι₂ := ι) (Tfiber * Tfiber))) ≤
      1 := by
  refine Distribution.IsProbability.avgOver_le_of_forall_le_on_support
    (𝒟 := uniformDistribution (Point params))
    (uniformDistribution_isProbability (Point params)) _ 1 ?_
  intro u _
  have hop := helper_second_move_first_factor_operator_le_one params T u
  have hev := ev_mono strategy.state _ _ hop
  rw [ev_sum] at hev
  simpa [ev_one_of_isNormalized strategy.state strategy.isNormalized] using hev

/-- Pointwise comparison between the projective residual in the second
Cauchy--Schwarz move and the bipartite strong self-consistency defect.

Projectivity gives `(A^u_a)^2 = A^u_a` and `(I - A^u_a)^2 = I - A^u_a`.
After summing over `a`, the residual is the one-register total mass minus the
diagonal cross-register overlap, and hence is bounded by the `max 0` defining
`qBipartiteSSCDefect`. -/
theorem helper_second_move_second_factor_pointwise_le_qBipartiteSSCDefect
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (u : Point params) :
    (∑ a : Fq params,
      let Au := (strategy.pointMeasurement u).outcome a
      ev strategy.state (opTensor (Au * Au) ((1 - Au) * (1 - Au)))) ≤
      qBipartiteSSCDefect strategy.state ((strategy.pointMeasurement u).toSubMeas) := by
  classical
  have hresidual_eq :
      (∑ a : Fq params,
        let Au := (strategy.pointMeasurement u).outcome a
        ev strategy.state (opTensor (Au * Au) ((1 - Au) * (1 - Au)))) =
        ev strategy.state
          (leftTensor (ι₂ := ι) ((strategy.pointMeasurement u).toSubMeas.total)) -
          ∑ a : Fq params,
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                ((strategy.pointMeasurement u).outcome a)) := by
    calc
      (∑ a : Fq params,
        let Au := (strategy.pointMeasurement u).outcome a
        ev strategy.state (opTensor (Au * Au) ((1 - Au) * (1 - Au))))
          =
        ∑ a : Fq params,
          ev strategy.state
            (opTensor ((strategy.pointMeasurement u).outcome a)
              (1 - (strategy.pointMeasurement u).outcome a)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            set Au := (strategy.pointMeasurement u).outcome a
            have hproj : Au * Au = Au := by
              simpa [Au] using (strategy.pointMeasurement u).proj a
            have hsq : (1 - Au) * (1 - Au) = 1 - Au := by
              calc
                (1 - Au) * (1 - Au) = 1 - Au - Au + Au * Au := by noncomm_ring
                _ = 1 - Au := by rw [hproj]; noncomm_ring
            simp [Au, hproj, hsq]
      _ =
        ∑ a : Fq params,
          (ev strategy.state (leftTensor (ι₂ := ι) ((strategy.pointMeasurement u).outcome a)) -
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                ((strategy.pointMeasurement u).outcome a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [← ev_sub]
            congr 1
            simpa [leftTensor, opTensor] using
              (MIPStarRE.Quantum.kronecker_sub_right
                (A := (strategy.pointMeasurement u).outcome a)
                (B₁ := (1 : MIPStarRE.Quantum.Op ι))
                (B₂ := (strategy.pointMeasurement u).outcome a)).symm
      _ =
        (∑ a : Fq params,
          ev strategy.state (leftTensor (ι₂ := ι) ((strategy.pointMeasurement u).outcome a))) -
          ∑ a : Fq params,
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                ((strategy.pointMeasurement u).outcome a)) := by
            rw [Finset.sum_sub_distrib]
      _ =
        ev strategy.state
          (leftTensor (ι₂ := ι) ((strategy.pointMeasurement u).toSubMeas.total)) -
          ∑ a : Fq params,
            ev strategy.state
              (opTensor ((strategy.pointMeasurement u).outcome a)
                ((strategy.pointMeasurement u).outcome a)) := by
            rw [← ev_sum strategy.state
              (fun a : Fq params =>
                leftTensor (ι₂ := ι) ((strategy.pointMeasurement u).outcome a))]
            rw [leftTensor_finset_sum, (strategy.pointMeasurement u).toSubMeas.sum_eq_total]
  rw [hresidual_eq]
  unfold qBipartiteSSCDefect
  exact le_max_right 0 _

/-- The second Cauchy--Schwarz factor in the second helper-completeness move is
bounded by the bipartite strong self-consistency error.

This is the Lean form of the paper's assertion that
`E_u Σ_a ⟨ψ, A^u_a ⊗ (I-A^u_a) ψ⟩ ≤ delta`. -/
theorem helper_second_move_second_factor_le_delta
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (delta : Error)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      ∑ a : Fq params,
        let Au := (strategy.pointMeasurement u).outcome a
        ev strategy.state (opTensor (Au * Au) ((1 - Au) * (1 - Au)))) ≤
      delta := by
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
      ∑ a : Fq params,
        let Au := (strategy.pointMeasurement u).outcome a
        ev strategy.state (opTensor (Au * Au) ((1 - Au) * (1 - Au))))
        ≤
      avgOver (uniformDistribution (Point params)) (fun u =>
        qBipartiteSSCDefect strategy.state ((strategy.pointMeasurement u).toSubMeas)) := by
        refine avgOver_mono _ _ _ ?_
        intro u
        exact helper_second_move_second_factor_pointwise_le_qBipartiteSSCDefect
          params strategy u
    _ ≤ delta := hssc.overlapBound

/-- Pointwise operator form of the identity bound for the second
Cauchy--Schwarz factor in the first helper-completeness move.

For a fixed point `u`, each fiber operator satisfies
`0 ≤ T_[h(u)=a] ≤ I`, hence `T_[h(u)=a]^2 ≤ I`.  Sandwiching by the
projection `A^u_a` gives
`A^u_a T_[h(u)=a]^2 A^u_a ≤ A^u_a`, and the projective measurement
`A^u` sums to the identity. -/
theorem helper_first_move_second_factor_operator_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) :
    (∑ a : Fq params,
      let Au := (strategy.pointMeasurement u).outcome a
      let Tfiber := helperFiberOperator params T u a
      leftTensor (ι₂ := ι) (Au * (Tfiber * Tfiber) * Au)) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  have hsum :
      (∑ a : Fq params,
        let Au := (strategy.pointMeasurement u).outcome a
        let Tfiber := helperFiberOperator params T u a
        leftTensor (ι₂ := ι) (Au * (Tfiber * Tfiber) * Au)) ≤
        ∑ a : Fq params, leftTensor (ι₂ := ι)
          ((strategy.pointMeasurement u).outcome a) := by
    refine Finset.sum_le_sum ?_
    intro a _
    set Au := (strategy.pointMeasurement u).outcome a
    set Tfiber := helperFiberOperator params T u a
    have hT_nonneg : 0 ≤ Tfiber := by
      simpa [Tfiber] using helperFiberOperator_nonneg params T u a
    have hT_le_one : Tfiber ≤ 1 := by
      simpa [Tfiber] using helperFiberOperator_le_one params T u a
    have hT_sq_le_one : Tfiber * Tfiber ≤ 1 := by
      exact le_trans (MIPStarRE.Quantum.sq_le_self hT_nonneg hT_le_one) hT_le_one
    have hAu_herm : Auᴴ = Au := by
      simpa [Au] using
        SubMeas.outcome_hermitian (strategy.pointMeasurement u).toSubMeas a
    have hAu_proj : Au * Au = Au := by
      simpa [Au] using (strategy.pointMeasurement u).proj a
    have hterm : Au * (Tfiber * Tfiber) * Au ≤ Au := by
      calc
        Au * (Tfiber * Tfiber) * Au
            ≤ Au * 1 * Au :=
              MIPStarRE.Quantum.sandwich_mono hAu_herm hT_sq_le_one
        _ = Au := by simp [hAu_proj]
    simpa [leftTensor, opTensor] using
      (opTensor_mono_left (ι₂ := ι)
        (B := (1 : MIPStarRE.Quantum.Op ι)) hterm
        (zero_le_one : (0 : MIPStarRE.Quantum.Op ι) ≤ 1))
  calc
    (∑ a : Fq params,
      let Au := (strategy.pointMeasurement u).outcome a
      let Tfiber := helperFiberOperator params T u a
      leftTensor (ι₂ := ι) (Au * (Tfiber * Tfiber) * Au))
        ≤ ∑ a : Fq params, leftTensor (ι₂ := ι)
          ((strategy.pointMeasurement u).outcome a) := hsum
    _ = leftTensor (ι₂ := ι) ((strategy.pointMeasurement u).toSubMeas.total) := by
        rw [leftTensor_finset_sum, (strategy.pointMeasurement u).toSubMeas.sum_eq_total]
    _ = 1 := by
        rw [(strategy.pointMeasurement u).total_eq_one, leftTensor_one]

/-- The second Cauchy--Schwarz factor in the first helper-completeness move is
bounded by the identity contribution.

This is the Lean form of the paper's assertion, following
`eq:yet-another-move-a`, that
`E_u Σ_a ⟨ψ, (A^u_a T_[h(u)=a]^2 A^u_a) ⊗ I ψ⟩ ≤ 1`. -/
theorem helper_first_move_second_factor_le_one
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      ∑ a : Fq params,
        let Au := (strategy.pointMeasurement u).outcome a
        let Tfiber := helperFiberOperator params T u a
        ev strategy.state (leftTensor (ι₂ := ι) (Au * (Tfiber * Tfiber) * Au))) ≤
      1 := by
  refine Distribution.IsProbability.avgOver_le_of_forall_le_on_support
    (𝒟 := uniformDistribution (Point params))
    (uniformDistribution_isProbability (Point params)) _ 1 ?_
  intro u _
  have hop := helper_first_move_second_factor_operator_le_one params strategy T u
  have hev := ev_mono strategy.state _ _ hop
  rw [ev_sum] at hev
  simpa [ev_one_of_isNormalized strategy.state strategy.isNormalized] using hev

/-- The scalar expression after the first Cauchy--Schwarz move in helper
completeness.

This is
`E_u Σ_a ⟨ψ, (T_[h(u)=a] A^u_a) ⊗ A^u_a ψ⟩`, the right-hand side of
`eq:yet-another-move-a` in the paper.  The fiber
`T_[h(u)=a]` is represented by the finite sum over polynomials whose value at
`u` is `a`. -/
noncomputable def helperFirstMovedCompletenessQuantity
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ a : Fq params,
      let Au := (strategy.pointMeasurement u).outcome a
      let Tfiber := helperFiberOperator params T u a
      ev strategy.state (opTensor (Tfiber * Au) Au))

/-- The scalar expression after removing the remaining point-measurement
operator in helper completeness.

This is
`E_u Σ_h ⟨ψ, (T_h A^u_{h(u)}) ⊗ I ψ⟩`.  Complementary slackness identifies this
quantity with the dual mass `⟨ψ, Z ⊗ I ψ⟩`. -/
noncomputable def helperLinearizedCompletenessQuantity
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ h : Polynomial params,
      ev strategy.state
        (leftTensor (ι₂ := ι)
          (T.outcome h *
            pointConditionedOutcomeOperatorAtPolynomial params strategy h u)))

/-- Fiberwise form of the linearized helper-completeness quantity.

The expression
`E_u Σ_h ⟨ψ, (T_h A^u_{h(u)}) ⊗ I ψ⟩` may equivalently be grouped by the value
`a = h(u)`, giving
`E_u Σ_a ⟨ψ, (T_[h(u)=a] A^u_a) ⊗ I ψ⟩`.  This is the algebraic rewrite used
after `eq:mysterious-case-of-the-disappearing-a` in the paper. -/
theorem helper_linearized_completeness_quantity_eq_fiber_sum
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    helperLinearizedCompletenessQuantity params strategy T =
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ a : Fq params,
          let Au := (strategy.pointMeasurement u).outcome a
          let Tfiber := helperFiberOperator params T u a
          ev strategy.state (leftTensor (ι₂ := ι) (Tfiber * Au))) := by
  unfold helperLinearizedCompletenessQuantity
  refine avgOver_congr _ _ _ ?_
  intro u
  rw [show (∑ h : Polynomial params,
      ev strategy.state (leftTensor (ι₂ := ι)
        (T.outcome h * pointConditionedOutcomeOperatorAtPolynomial params strategy h u))) =
      ∑ a : Fq params, ∑ h ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
        ev strategy.state (leftTensor (ι₂ := ι)
          (T.outcome h * pointConditionedOutcomeOperatorAtPolynomial params strategy h u)) from by
      exact polynomial_sum_fiberwise params u
        (fun h => ev strategy.state (leftTensor (ι₂ := ι)
          (T.outcome h * pointConditionedOutcomeOperatorAtPolynomial params strategy h u)))]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [← ev_finset_sum]
  congr 1
  rw [leftTensor_finset_sum]
  congr 1
  calc
    (∑ x ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
      T.outcome x * pointConditionedOutcomeOperatorAtPolynomial params strategy x u)
        = ∑ x ∈ Finset.univ.filter (fun h : Polynomial params => h u = a),
            T.outcome x * (strategy.pointMeasurement u).outcome a := by
          refine Finset.sum_congr rfl ?_
          intro h hh
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hh
          simp [pointConditionedOutcomeOperatorAtPolynomial, hh]
    _ = (∑ x ∈ Finset.univ.filter (fun h : Polynomial params => h u = a), T.outcome x) *
          (strategy.pointMeasurement u).outcome a := by
          rw [Finset.sum_mul]

/-- Pointwise Cauchy--Schwarz estimate for the second helper-completeness move.

For fixed `u` and `a`, this bounds the residual term
`⟨ψ, (T_[h(u)=a] A^u_a) ⊗ (I - A^u_a) ψ⟩` by the product of the two square-root
factors appearing after `eq:mysterious-case-of-the-disappearing-a`. -/
theorem helper_second_move_pointwise_abs_le_sqrt
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (u : Point params) (a : Fq params) :
    |ev strategy.state (opTensor
      (helperFiberOperator params T u a * (strategy.pointMeasurement u).outcome a)
      (1 - (strategy.pointMeasurement u).outcome a))| ≤
      Real.sqrt (ev strategy.state (leftTensor (ι₂ := ι)
        (helperFiberOperator params T u a * helperFiberOperator params T u a))) *
      Real.sqrt (ev strategy.state (opTensor
        ((strategy.pointMeasurement u).outcome a * (strategy.pointMeasurement u).outcome a)
        ((1 - (strategy.pointMeasurement u).outcome a) *
          (1 - (strategy.pointMeasurement u).outcome a)))) := by
  set Tf := helperFiberOperator params T u a
  set Au := (strategy.pointMeasurement u).outcome a
  have hTf_herm : Tfᴴ = Tf := by
    simpa [Tf] using (Matrix.nonneg_iff_posSemidef.mp
      (helperFiberOperator_nonneg params T u a)).isHermitian.eq
  have hAu_herm : Auᴴ = Au := by
    simpa [Au] using SubMeas.outcome_hermitian (strategy.pointMeasurement u).toSubMeas a
  have hOneSub_herm : (1 - Au)ᴴ = 1 - Au := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hAu_herm]
  have hcs := ev_abs_mul_le_sqrt strategy.state
    (leftTensor (ι₂ := ι) Tf)
    (opTensor Au (1 - Au))
  change |ev strategy.state (opTensor Tf (1 : MIPStarRE.Quantum.Op ι) *
      opTensor Au (1 - Au))| ≤
    Real.sqrt (ev strategy.state
      (opTensor Tf (1 : MIPStarRE.Quantum.Op ι) *
        (opTensor Tf (1 : MIPStarRE.Quantum.Op ι))ᴴ)) *
    Real.sqrt (ev strategy.state
      ((opTensor Au (1 - Au))ᴴ * opTensor Au (1 - Au))) at hcs
  rw [opTensor_mul] at hcs
  rw [conjTranspose_opTensor, hTf_herm, Matrix.conjTranspose_one, opTensor_mul] at hcs
  rw [conjTranspose_opTensor, hAu_herm, hOneSub_herm, opTensor_mul] at hcs
  simpa [Tf, Au, leftTensor] using hcs

/-- The second Cauchy--Schwarz move in the helper-completeness proof.

Assuming bipartite strong self-consistency of the point measurement with error
`delta`, the first-moved helper-completeness expression
`E_u Σ_a ⟨ψ, (T_[h(u)=a] A^u_a) ⊗ A^u_a ψ⟩` differs from the linearized
expression `E_u Σ_a ⟨ψ, (T_[h(u)=a] A^u_a) ⊗ I ψ⟩` by at most `sqrt delta`.
The first factor is bounded by the grouped submeasurement estimate, and the
second is exactly the projective residual controlled by self-consistency. -/
theorem helper_second_move_abs_sub_first_moved_le_sqrt_delta
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (delta : Error)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |helperLinearizedCompletenessQuantity params strategy T -
      helperFirstMovedCompletenessQuantity params strategy T| ≤
      Real.sqrt delta := by
  classical
  let t : Point params → Fq params → Error := fun u a =>
    let Au := (strategy.pointMeasurement u).outcome a
    let Tfiber := helperFiberOperator params T u a
    ev strategy.state (opTensor (Tfiber * Au) (1 - Au))
  let x : Point params → Fq params → Error := fun u a =>
    let Tfiber := helperFiberOperator params T u a
    ev strategy.state (leftTensor (ι₂ := ι) (Tfiber * Tfiber))
  let y : Point params → Fq params → Error := fun u a =>
    let Au := (strategy.pointMeasurement u).outcome a
    ev strategy.state (opTensor (Au * Au) ((1 - Au) * (1 - Au)))
  have ht : ∀ u a, |t u a| ≤ Real.sqrt (x u a) * Real.sqrt (y u a) := by
    intro u a
    exact helper_second_move_pointwise_abs_le_sqrt params strategy T u a
  have hx : ∀ u a, 0 ≤ x u a := by
    intro u a
    set Tf := helperFiberOperator params T u a
    have hTf_herm : Tfᴴ = Tf := by
      simpa [Tf] using (Matrix.nonneg_iff_posSemidef.mp
        (helperFiberOperator_nonneg params T u a)).isHermitian.eq
    have hnonneg := ev_adjoint_self_nonneg strategy.state (leftTensor (ι₂ := ι) Tf)
    simpa [x, Tf, leftTensor_conjTranspose, hTf_herm, leftTensor_mul_leftTensor] using hnonneg
  have hy : ∀ u a, 0 ≤ y u a := by
    intro u a
    set Au := (strategy.pointMeasurement u).outcome a
    have hAu_herm : Auᴴ = Au := by
      simpa [Au] using SubMeas.outcome_hermitian (strategy.pointMeasurement u).toSubMeas a
    have hOneSub_herm : (1 - Au)ᴴ = 1 - Au := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hAu_herm]
    have hnonneg := ev_adjoint_self_nonneg strategy.state (opTensor Au (1 - Au))
    simpa [y, Au, conjTranspose_opTensor, hAu_herm, hOneSub_herm, opTensor_mul] using hnonneg
  have hweighted := MIPStarRE.LDT.Preliminaries.weightedFinsetCauchySchwarz
    (Question := Point params) (Outcome := Fq params)
    (uniformDistribution (Point params)) t x y ht hx hy
  have hgap :
      avgOver (uniformDistribution (Point params)) (fun u => ∑ a : Fq params, t u a) =
        helperLinearizedCompletenessQuantity params strategy T -
          helperFirstMovedCompletenessQuantity params strategy T := by
    rw [helper_linearized_completeness_quantity_eq_fiber_sum]
    unfold helperFirstMovedCompletenessQuantity
    rw [← avgOver_sub]
    refine avgOver_congr _ _ _ ?_
    intro u
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro a _
    dsimp [t]
    set Au := (strategy.pointMeasurement u).outcome a
    set Tfiber := helperFiberOperator params T u a
    rw [← ev_sub]
    congr 1
    simpa [leftTensor, opTensor, Tfiber, Au] using
      (MIPStarRE.Quantum.kronecker_sub_right
        (A := Tfiber * Au) (B₁ := (1 : MIPStarRE.Quantum.Op ι)) (B₂ := Au)).symm
  have hx_avg_le_one :
      avgOver (uniformDistribution (Point params))
          (fun u => ∑ a : Fq params, x u a) ≤
        1 := by
    simpa [x] using helper_second_move_first_factor_le_one params strategy T
  have hy_avg_le_delta :
      avgOver (uniformDistribution (Point params))
          (fun u => ∑ a : Fq params, y u a) ≤
        delta := by
    simpa [y] using helper_second_move_second_factor_le_delta params strategy delta hssc
  have hsqrt_x_le_one :
      Real.sqrt (avgOver (uniformDistribution (Point params))
          (fun u => ∑ a : Fq params, x u a)) ≤
        1 := by
    simpa using Real.sqrt_le_sqrt hx_avg_le_one
  have hsqrt_y_le_delta :
      Real.sqrt (avgOver (uniformDistribution (Point params))
          (fun u => ∑ a : Fq params, y u a)) ≤
        Real.sqrt delta :=
    Real.sqrt_le_sqrt hy_avg_le_delta
  calc
    |helperLinearizedCompletenessQuantity params strategy T -
      helperFirstMovedCompletenessQuantity params strategy T|
        = |avgOver (uniformDistribution (Point params))
            (fun u => ∑ a : Fq params, t u a)| := by
          rw [hgap]
    _ ≤ Real.sqrt (avgOver (uniformDistribution (Point params))
          (fun u => ∑ a : Fq params, x u a)) *
        Real.sqrt (avgOver (uniformDistribution (Point params))
          (fun u => ∑ a : Fq params, y u a)) :=
          hweighted
    _ ≤ 1 * Real.sqrt delta := by
        exact mul_le_mul hsqrt_x_le_one hsqrt_y_le_delta
          (Real.sqrt_nonneg _) (by norm_num : (0 : Error) ≤ 1)
    _ = Real.sqrt delta := by ring

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

/-- The named linearized helper-completeness quantity is the SDP dual mass under
complementary slackness. -/
theorem helper_linearized_completeness_quantity_eq_dual_mass_of_complementary_slackness
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
    helperLinearizedCompletenessQuantity params strategy T =
      ev strategy.state (leftTensor (ι₂ := ι) Z) := by
  simpa [helperLinearizedCompletenessQuantity] using
    helper_linearized_completeness_eq_dual_mass_of_complementary_slackness
      params strategy T Z hTtotal hslack

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

/-- The bracketed scalar expression before the first Cauchy--Schwarz move in
helper completeness.

This is the right-hand side of `eq:bracketize-the-expression`:

`E_u Σ_a ⟨ψ, (A^u_a · T_[h(u)=a] · A^u_a) ⊗ I ψ⟩`.

The finite sum
`Σ_{h : h(u)=a} T_h` represents the paper's fiber operator
`T_[h(u)=a]`. -/
noncomputable def helperBracketedCompletenessQuantity
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) : Error :=
  avgOver (uniformDistribution (Point params)) (fun u =>
    ∑ a : Fq params,
      let Au := (strategy.pointMeasurement u).outcome a
      let Tfiber := helperFiberOperator params T u a
      ev strategy.state (leftTensor (ι₂ := ι) (Au * Tfiber * Au)))

/-- The first Cauchy--Schwarz move in the helper-completeness proof.

Assuming bipartite strong self-consistency of the point measurement with error
`delta`, the bracketed expression
`E_u Σ_a ⟨ψ, (A^u_a T_[h(u)=a] A^u_a) ⊗ I ψ⟩`
differs from
`E_u Σ_a ⟨ψ, (T_[h(u)=a] A^u_a) ⊗ A^u_a ψ⟩`
by at most `2 sqrt delta`.  The proof is the paper's
`eq:yet-another-move-a`: `twoNotionsOfSelfConsistency` supplies the first
square-root factor, while `helper_first_move_second_factor_le_one` supplies
the second. -/
theorem helper_first_move_abs_sub_bracketed_le_two_sqrt_delta
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (delta : Error)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |helperFirstMovedCompletenessQuantity params strategy T -
      helperBracketedCompletenessQuantity params strategy T| ≤
      2 * Real.sqrt delta := by
  classical
  let Aop : Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun u a => leftTensor (ι₂ := ι) ((strategy.pointMeasurement u).outcome a)
  let Bop : Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun u a => rightTensor (ι₁ := ι) ((strategy.pointMeasurement u).outcome a)
  let Cop : Point params → Fq params → Unit → MIPStarRE.Quantum.Op (ι × ι) :=
    fun u a _ =>
      let Au := (strategy.pointMeasurement u).outcome a
      let Tfiber := helperFiberOperator params T u a
      leftTensor (ι₂ := ι) (Tfiber * Au)
  have hOutcome_herm : ∀ (u : Point params) (a : Fq params),
      ((strategy.pointMeasurement u).outcome a)ᴴ =
        (strategy.pointMeasurement u).outcome a := fun u a =>
    SubMeas.outcome_hermitian (strategy.pointMeasurement u).toSubMeas a
  have hTfiber_herm : ∀ (u : Point params) (a : Fq params),
      (helperFiberOperator params T u a)ᴴ = helperFiberOperator params T u a := fun u a =>
    (Matrix.nonneg_iff_posSemidef.mp
      (helperFiberOperator_nonneg params T u a)).isHermitian.eq
  have hAop_herm : ∀ u a, (Aop u a)ᴴ = Aop u a := by
    intro u a
    simp [Aop, leftTensor_conjTranspose, hOutcome_herm u a]
  have hBop_herm : ∀ u a, (Bop u a)ᴴ = Bop u a := by
    intro u a
    simp [Bop, rightTensor_conjTranspose, hOutcome_herm u a]
  have hfun_A : ∀ u : Point params, (fun a : Fq params => (Aop u a)ᴴ) = Aop u := by
    intro u
    funext a
    exact hAop_herm u a
  have hfun_B : ∀ u : Point params, (fun a : Fq params => (Bop u a)ᴴ) = Bop u := by
    intro u
    funext a
    exact hBop_herm u a
  have hSDD := Preliminaries.twoNotionsOfSelfConsistency strategy.state
    (uniformDistribution (Point params))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta
    ⟨strategy.permInvState, hssc⟩
  have hAB :
      avgOver (uniformDistribution (Point params)) (fun u =>
        qSDDCore strategy.state
          (fun a : Fq params => (Aop u a)ᴴ)
          (fun a : Fq params => (Bop u a)ᴴ)) ≤
        2 * delta := by
    rcases hSDD with ⟨hsdd⟩
    refine le_trans ?_ hsdd
    refine le_of_eq ?_
    refine avgOver_congr _ _ _ ?_
    intro u
    rw [hfun_A u, hfun_B u]
    rfl
  have hC : ∀ u : Point params,
      (∑ a : Fq params, (∑ b : Unit, Cop u a b)ᴴ * (∑ b : Unit, Cop u a b)) ≤
        (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    intro u
    have hop := helper_first_move_second_factor_operator_le_one params strategy T u
    simpa [Cop, leftTensor_conjTranspose, leftTensor_mul_leftTensor, Matrix.conjTranspose_mul,
      hOutcome_herm, hTfiber_herm, mul_assoc] using hop
  have hcs := Preliminaries.closenessOfInnerProduct_right
    strategy.state strategy.isNormalized
    (uniformDistribution (Point params))
    (uniformDistribution_weight_sum_le_one (Point params))
    Aop Bop Cop (2 * delta) hAB hC
  have hbracket :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ a : Fq params, ∑ b : Unit, ev strategy.state (Aop u a * Cop u a b)) =
        helperBracketedCompletenessQuantity params strategy T := by
    unfold helperBracketedCompletenessQuantity
    refine avgOver_congr _ _ _ ?_
    intro u
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [Aop, Cop, leftTensor_mul_leftTensor, mul_assoc]
  have hfirst :
      avgOver (uniformDistribution (Point params)) (fun u =>
        ∑ a : Fq params, ∑ b : Unit, ev strategy.state (Bop u a * Cop u a b)) =
        helperFirstMovedCompletenessQuantity params strategy T := by
    unfold helperFirstMovedCompletenessQuantity
    refine avgOver_congr _ _ _ ?_
    intro u
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [Bop, Cop, rightTensor_mul_leftTensor_eq_opTensor]
  have hsqrt2_le_2 : Real.sqrt 2 ≤ (2 : Error) := by
    nlinarith [Real.mul_self_sqrt (by norm_num : (0 : Error) ≤ 2),
      Real.sqrt_nonneg (2 : Error)]
  have hsqrt2delta_le :
      Real.sqrt (2 * delta) ≤ 2 * Real.sqrt delta := by
    rw [Real.sqrt_mul (by norm_num : (0 : Error) ≤ 2)]
    exact mul_le_mul_of_nonneg_right hsqrt2_le_2 (Real.sqrt_nonneg _)
  calc
    |helperFirstMovedCompletenessQuantity params strategy T -
      helperBracketedCompletenessQuantity params strategy T|
        = |avgOver (uniformDistribution (Point params)) (fun u =>
            ∑ a : Fq params, ∑ b : Unit, ev strategy.state (Aop u a * Cop u a b)) -
            avgOver (uniformDistribution (Point params)) (fun u =>
              ∑ a : Fq params, ∑ b : Unit, ev strategy.state (Bop u a * Cop u a b))| := by
          rw [hbracket, hfirst]
          exact abs_sub_comm _ _
    _ ≤ Real.sqrt (2 * delta) := hcs
    _ ≤ 2 * Real.sqrt delta := hsqrt2delta_le

/-- The recorded `Hhat`-versus-`Z` comparison follows from the two
Cauchy--Schwarz scalar bounds and complementary slackness.

The first hypothesis is the bound for moving the leftmost copy of `A^u_a` across
the bipartition; the second is the bound for removing the remaining copy of
`A^u_a` on the right register.  Together with complementary slackness, these
are precisely the estimates leading to
`eq:gonna-use-this-later-H-versus-Z` in the paper. -/
theorem helper_hhat_vs_z_of_cauchy_schwarz_and_complementary_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hmove_left :
      |helperFirstMovedCompletenessQuantity params strategy T.toSubMeas -
        subMeasMass strategy.state Hhat.liftLeft| ≤
        2 * Real.sqrt delta)
    (hremove_right :
      |helperLinearizedCompletenessQuantity params strategy T.toSubMeas -
        helperFirstMovedCompletenessQuantity params strategy T.toSubMeas| ≤
        Real.sqrt delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z) :
    ev strategy.state (leftTensor (ι₂ := ι) Z) - 3 * Real.sqrt delta ≤
      subMeasMass strategy.state Hhat.liftLeft := by
  have hmove_left_upper :
      helperFirstMovedCompletenessQuantity params strategy T.toSubMeas -
        subMeasMass strategy.state Hhat.liftLeft ≤
        2 * Real.sqrt delta :=
    (abs_le.mp hmove_left).2
  have hremove_right_upper :
      helperLinearizedCompletenessQuantity params strategy T.toSubMeas -
        helperFirstMovedCompletenessQuantity params strategy T.toSubMeas ≤
        Real.sqrt delta :=
    (abs_le.mp hremove_right).2
  have hlinearized :
      helperLinearizedCompletenessQuantity params strategy T.toSubMeas =
        ev strategy.state (leftTensor (ι₂ := ι) Z) :=
    helper_linearized_completeness_quantity_eq_dual_mass_of_complementary_slackness
      params strategy T.toSubMeas Z hhelper.sdpWitness.primalTotalOperator hslack
  linarith

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
      hhelper.sdpWitness.dualPositive hhelper.sdpWitness.dualFeasible hcons

/-- Helper-stage completeness from the two Cauchy--Schwarz scalar bounds,
complementary slackness, and input consistency.

This theorem is the completeness paragraph with the `Hhat`-versus-`Z`
comparison assembled internally from its two analytic estimates and the exact
SDP rewrite.  The remaining external hypotheses are therefore the two
Cauchy--Schwarz estimates themselves and the complementary-slackness equation. -/
theorem helper_completeness_of_cauchy_schwarz_input_consistency
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
    (hmove_left :
      |helperFirstMovedCompletenessQuantity params strategy T.toSubMeas -
        subMeasMass strategy.state Hhat.liftLeft| ≤
        2 * Real.sqrt delta)
    (hremove_right :
      |helperLinearizedCompletenessQuantity params strategy T.toSubMeas -
        helperFirstMovedCompletenessQuantity params strategy T.toSubMeas| ≤
        Real.sqrt delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    CompletenessAtLeast strategy.state Hhat.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta) := by
  refine
    helper_completeness_of_input_consistency params strategy G eps delta nu
      heps hdelta hhelper ?_ hcons
  exact
    helper_hhat_vs_z_of_cauchy_schwarz_and_complementary_slackness
      params strategy eps delta hhelper hmove_left hremove_right hslack

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
          exact polynomial_sum_fiberwise params u
            (sandwichedPolynomialOutcomeOperatorAt params strategy T u)]
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

/-- The named bracketed helper-completeness quantity is exactly the
helper-stage `Hhat ⊗ I` mass for the averaged sandwiched family.

This is the Lean form of the equality labelled
`eq:bracketize-the-expression`, after composing the fiberwise reindexing with
the preceding expansion of `Hhat` as the average of the pointwise sandwiched
submeasurements. -/
theorem helperBracketedCompletenessQuantity_eq_mass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι) :
    helperBracketedCompletenessQuantity params strategy T =
      subMeasMass strategy.state
        (averagedSandwichedPolynomialSubMeas params strategy T).liftLeft := by
  rw [helper_mass_eq_avg_pointwise_bracketed_sum]
  rfl

/-- The paper-shaped `Hhat`-versus-`Z` comparison assembled from the bracketed
expression, the two Cauchy--Schwarz estimates, and complementary slackness.

The first Cauchy--Schwarz hypothesis moves from the bracketed expression
`E_u Σ_a ⟨ψ, (A^u_a T_[h(u)=a] A^u_a) ⊗ I ψ⟩` to
`helperFirstMovedCompletenessQuantity`.  The second removes the remaining
right-register copy of `A^u_a`, giving `helperLinearizedCompletenessQuantity`.
The latter is then identified with the dual mass by the SDP
complementary-slackness equation. -/
theorem helper_hhat_vs_z_of_bracketed_cauchy_schwarz_and_complementary_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hmove_left :
      |helperFirstMovedCompletenessQuantity params strategy T.toSubMeas -
        helperBracketedCompletenessQuantity params strategy T.toSubMeas| ≤
        2 * Real.sqrt delta)
    (hremove_right :
      |helperLinearizedCompletenessQuantity params strategy T.toSubMeas -
        helperFirstMovedCompletenessQuantity params strategy T.toSubMeas| ≤
        Real.sqrt delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z) :
    ev strategy.state (leftTensor (ι₂ := ι) Z) - 3 * Real.sqrt delta ≤
      subMeasMass strategy.state Hhat.liftLeft := by
  have hbracket_mass :
      helperBracketedCompletenessQuantity params strategy T.toSubMeas =
        subMeasMass strategy.state Hhat.liftLeft := by
    rw [hhelper.averagedConstruction]
    exact helperBracketedCompletenessQuantity_eq_mass params strategy T.toSubMeas
  refine
    helper_hhat_vs_z_of_cauchy_schwarz_and_complementary_slackness
      params strategy eps delta hhelper ?_ hremove_right hslack
  simpa [hbracket_mass] using hmove_left

/-- The `Hhat`-versus-`Z` comparison from point self-consistency and
complementary slackness.

This is the helper-completeness comparison at
`eq:gonna-use-this-later-H-versus-Z` with the two Cauchy--Schwarz estimates
supplied internally by `helper_first_move_abs_sub_bracketed_le_two_sqrt_delta`
and `helper_second_move_abs_sub_first_moved_le_sqrt_delta`. -/
theorem helper_hhat_vs_z_of_self_consistency_and_complementary_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper : SelfImprovementHelperConclusion params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z) :
    ev strategy.state (leftTensor (ι₂ := ι) Z) - 3 * Real.sqrt delta ≤
      subMeasMass strategy.state Hhat.liftLeft :=
  helper_hhat_vs_z_of_bracketed_cauchy_schwarz_and_complementary_slackness
    params strategy eps delta hhelper
    (helper_first_move_abs_sub_bracketed_le_two_sqrt_delta
      params strategy T.toSubMeas delta hssc)
    (helper_second_move_abs_sub_first_moved_le_sqrt_delta
      params strategy T.toSubMeas delta hssc)
    hslack

/-- Helper-stage completeness from the paper-shaped Cauchy--Schwarz estimates,
complementary slackness, and input consistency.

Compared with `helper_completeness_of_cauchy_schwarz_input_consistency`, this
version names the expression before the first Cauchy--Schwarz move exactly as
it appears in `eq:bracketize-the-expression`; the equality with the
`Hhat`-mass is supplied internally by
`helperBracketedCompletenessQuantity_eq_mass`. -/
theorem helper_completeness_of_bracketed_cauchy_schwarz_input_consistency
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
    (hmove_left :
      |helperFirstMovedCompletenessQuantity params strategy T.toSubMeas -
        helperBracketedCompletenessQuantity params strategy T.toSubMeas| ≤
        2 * Real.sqrt delta)
    (hremove_right :
      |helperLinearizedCompletenessQuantity params strategy T.toSubMeas -
        helperFirstMovedCompletenessQuantity params strategy T.toSubMeas| ≤
        Real.sqrt delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    CompletenessAtLeast strategy.state Hhat.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta) := by
  refine
    helper_completeness_of_input_consistency params strategy G eps delta nu
      heps hdelta hhelper ?_ hcons
  exact
    helper_hhat_vs_z_of_bracketed_cauchy_schwarz_and_complementary_slackness
      params strategy eps delta hhelper hmove_left hremove_right hslack

/-- Helper-stage completeness from point self-consistency, complementary
slackness, and input consistency.

This wrapper removes the two external Cauchy--Schwarz hypotheses from
`helper_completeness_of_bracketed_cauchy_schwarz_input_consistency`; both are
proved from the single point-measurement self-consistency hypothesis. -/
theorem helper_completeness_of_self_consistency_complementary_slackness_input_consistency
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
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hslack :
      ∀ h : Polynomial params,
        T.toSubMeas.outcome h * averagedPointOperator params strategy h =
          T.toSubMeas.outcome h * Z)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    CompletenessAtLeast strategy.state Hhat.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta) := by
  refine
    helper_completeness_of_bracketed_cauchy_schwarz_input_consistency
      params strategy G eps delta nu heps hdelta hhelper ?_ ?_ hslack hcons
  · exact helper_first_move_abs_sub_bracketed_le_two_sqrt_delta
      params strategy T.toSubMeas delta hssc
  · exact helper_second_move_abs_sub_first_moved_le_sqrt_delta
      params strategy T.toSubMeas delta hssc

/-- Extract the orientation of complementary slackness used by the helper
completeness proof from the strengthened helper conclusion. -/
theorem helper_slackness_eq_of_helper_with_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper :
      SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta)
    (h : Polynomial params) :
    T.toSubMeas.outcome h * averagedPointOperator params strategy h =
      T.toSubMeas.outcome h * Z :=
  (hhelper.complementarySlackness h).symm

/-- Reconstruct the slackness-carrying SDP pair from the strengthened helper
conclusion. -/
theorem helper_sdp_optimal_pair_with_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper :
      SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta) :
    SdpOptimalPairWithSlackness params strategy T.toSubMeas Z :=
  { toSdpOptimalPair := hhelper.toHelperConclusion.sdpWitness
    complementarySlackness := hhelper.complementarySlackness }

/-- The `Hhat`-versus-`Z` comparison from point self-consistency and a helper
conclusion carrying SDP complementary slackness.

This is the version of `eq:gonna-use-this-later-H-versus-Z` whose inputs are a
single strengthened helper conclusion and point-measurement self-consistency,
rather than a separate family of slackness equations. -/
theorem helper_hhat_vs_z_of_self_consistency_and_helper_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta : Error)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper :
      SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    ev strategy.state (leftTensor (ι₂ := ι) Z) - 3 * Real.sqrt delta ≤
      subMeasMass strategy.state Hhat.liftLeft :=
  helper_hhat_vs_z_of_self_consistency_and_complementary_slackness
    params strategy eps delta hhelper.toHelperConclusion hssc
    (helper_slackness_eq_of_helper_with_slackness params strategy eps delta hhelper)

/-- Helper-stage completeness from point self-consistency, a helper conclusion
carrying SDP complementary slackness, and input consistency.

This wrapper removes the standalone `hslack` hypothesis from
`helper_completeness_of_self_consistency_complementary_slackness_input_consistency`;
the slackness equations are read from
`SelfImprovementHelperConclusionWithSlackness`. -/
theorem helper_completeness_of_self_consistency_helper_slackness_input_consistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι)
    (G : Measurement (Polynomial params) ι)
    (eps delta nu : Error)
    (heps : 0 ≤ eps) (hdelta : 0 ≤ delta)
    {T : Measurement (Polynomial params) ι}
    {Hhat : SubMeas (Polynomial params) ι}
    {Z : MIPStarRE.Quantum.Op ι}
    (hhelper :
      SelfImprovementHelperConclusionWithSlackness params strategy T Hhat Z eps delta)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta)
    (hcons : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas) nu) :
    CompletenessAtLeast strategy.state Hhat.liftLeft
      ((1 - nu) - selfImprovementHelperError params eps delta) :=
  helper_completeness_of_self_consistency_complementary_slackness_input_consistency
    params strategy G eps delta nu heps hdelta hhelper.toHelperConclusion hssc
    (helper_slackness_eq_of_helper_with_slackness params strategy eps delta hhelper)
    hcons

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
