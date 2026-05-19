import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperCompleteness.Linearized
import MIPStarRE.LDT.SelfImprovement.Theorems.Results.SdpMatrixBridge
import MIPStarRE.LDT.GlobalVariance.Theorems.MainTheorems

/-!
# Helper completeness: bracketed mass identities and reduced reductions

This file contains the exact bracketed reindexing of the helper-stage mass, the
paper-shaped completeness assemblies, and the reduced `sdp` and `addInU`
reductions used by the surrounding self-improvement theorem.

## References

- `references/ldt-paper/self_improvement.tex` lines 354--414
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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

Composed with `helper_mass_eq_avg_pointwise_sandwich_sum`, this yields the
bracketed form `helper_mass_eq_avg_pointwise_bracketed_sum` of the helper-stage
`Hhat ⊗ I` mass, which is the starting point for the remaining
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

Combines `helper_mass_eq_avg_pointwise_sandwich_sum` with the per-point
bracketing identity `helper_pointwise_sandwich_sum_eq_bracketed`:

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

This theorem removes the two external Cauchy--Schwarz hypotheses from
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

This theorem removes the standalone `hslack` hypothesis from
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

This reduced theorem now instantiates the paper's explicit Slater witnesses: the
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
      dualFeasible := ?_ }
  intro g
  simpa [Z, sdpDualSlackOperator] using
    sub_nonneg.mpr
      (le_trans (averagedPointOperator_le_one params strategy g)
        (one_le_sdpStrictDualWitness (ι := ι)))

/-- Paper-origin statement for `lem:sdp` with complementary slackness.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 62--88 state
`\label{lem:sdp}` for the primal/dual SDP pair and assert optimal witnesses
`{T_g}`, `Z` with `∑ g, T_g = I` and `T_g Z = T_g A_g`.  Lines 168--190 prove
this by Slater strong duality and complementary slackness after passing through
the canonical SDP form.

The proof is deferred to the formalized strong-duality argument for the Section
9 SDP.  The remaining proof obligation is now isolated as the native canonical
optimal-pair theorem `matrixSdpPointRealization_canonicalOptimalPair`; this
theorem transports that saturated canonical SDP output to the abstract
self-improvement statement. -/
theorem sdp_statement_with_slackness
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    SdpStatementWithSlackness params strategy := by
  exact sdpStatementWithSlackness_of_exists_canonicalOptimalPair params strategy
    (matrixSdpPointRealization_canonicalOptimalPair params strategy)

/-- Displayed measurement and complementary-slackness conclusion of `lem:sdp`.

Paper origin: `references/ldt-paper/self_improvement.tex` lines 82--88 state
that the Section 9 SDP admits a primal family `{T_g}` with `∑ g, T_g = I` and
a dual operator `Z` satisfying `T_g Z = T_g A_g` for every polynomial `g`.
This theorem extracts exactly that complete-measurement and slackness form from
the source-shaped SDP statement `sdp_statement_with_slackness`.

**Unfaithful:** This proof currently relies on
`sdp_statement_with_slackness`, whose complementary-slackness proof is not yet
derived from `references/ldt-paper/self_improvement.tex` (`lem:sdp`).
Documented by issue #1230.  Elimination: prove
`sdp_statement_with_slackness` from the SDP strong-duality and
complementary-slackness argument. -/
theorem sdp_slackness_measurement
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params ι) :
    ∃ T : Measurement (Polynomial params) ι,
      ∃ Z : MIPStarRE.Quantum.Op ι,
        0 ≤ Z ∧
        (∀ g : Polynomial params, 0 ≤ sdpDualSlackOperator params strategy Z g) ∧
        ∀ g : Polynomial params,
          sdpComplementarySlacknessEquation params strategy T.toSubMeas Z g :=
  sdpMeasurementWitness_of_exists_canonicalOptimalPair params strategy
    (matrixSdpPointRealization_canonicalOptimalPair params strategy)

-- The reduced add-in-u lemma invokes the global-variance transport record and
-- checks the full polynomial-indexed variance family.
/-- Reduced version of `lem:add-in-u`.

This currently keeps only the global-variance consequence used downstream. It
now derives that consequence from the post-triangle six-step edge-transport
chain bound via `globalVarianceOfPointsFromTransportChainBound`. The `gamma` and
`hgood` arguments are intentionally retained so this reduced theorem still
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
