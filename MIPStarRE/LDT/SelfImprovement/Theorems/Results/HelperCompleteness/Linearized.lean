import MIPStarRE.LDT.SelfImprovement.Theorems.Results.HelperCompleteness.FiberBounds

/-!
# Helper completeness: the linearized SDP expression

This file rewrites the linearized helper-completeness expression as the dual
mass and assembles the Cauchy--Schwarz estimates with input consistency.  The
statements here are the algebraic bridge from the two analytic moves to the
`Hhat`-versus-`Z` lower bound.

## References

- `references/ldt-paper/self_improvement.tex` lines 395--414
- `blueprint/src/chapter/ch07_self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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
end MIPStarRE.LDT.SelfImprovement
