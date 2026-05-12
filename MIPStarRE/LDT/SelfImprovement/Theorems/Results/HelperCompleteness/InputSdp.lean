import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.GlobalVariance.Defs.Families
import MIPStarRE.LDT.Preliminaries.SelfConsistency.DataProcessing
import MIPStarRE.LDT.SelfImprovement.Theorems.Thresholds
import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.CommonHelpers

/-!
# Helper completeness: input consistency and the SDP bridge

This file contains the part of the helper-completeness argument which relates
input consistency, SDP dual feasibility, and complementary slackness.  These
lemmas correspond to the lower-bound calculation at the end of the completeness
proof in `references/ldt-paper/self_improvement.tex`, lines 406--414.

## References

- `references/ldt-paper/self_improvement.tex` lines 406--414
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
end MIPStarRE.LDT.SelfImprovement
