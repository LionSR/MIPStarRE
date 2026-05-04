import MIPStarRE.LDT.Test.MainTheorem.OrthonormalizationData

/-!
# Diagonal completion inputs

Statement-preserving slice of `MIPStarRE.LDT.Test.MainTheorem`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- Additional diagonal consistency input for the two unsymmetrized role POVMs.

The diagonal consistency handoff supplies only the cross relation `G^A ⊗ I ≃ I ⊗ G^B`. The
completion theorem used at lines 143--147 needs the diagonal hypotheses for each
completed side. This structure records the stronger, self-referential `ConsRel`
form of that missing bridge, keeping the obligation tied to the concrete role
package rather than to the public `mainFormal` statement. -/
structure MainFormalPostRolePackageDiagonalConsistencyInput
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars) where
  /-- Alice-role diagonal version of paper line 130. -/
  leftDiagonalConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1
  /-- Bob-role diagonal version of paper line 130. -/
  rightDiagonalConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1

/-- The `BipartiteSSCRel` form of the additional diagonal obligation consumed
by `completingToMeasurement`. -/
structure MainFormalPostRolePackageDiagonalSSCInput
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars) where
  /-- Strong self-consistency for the Alice-role unsymmetrized POVM. -/
  leftSelfConsistency :
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1
  /-- Strong self-consistency for the Bob-role unsymmetrized POVM. -/
  rightSelfConsistency :
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1

namespace MainFormalPostRolePackageDiagonalSSCInput

/-- Convert the diagonal self-`ConsRel` completion input into the
`BipartiteSSCRel` form required by the completion theorem.

This is a checked bookkeeping step only: the real mathematical gap remains
proving the two diagonal consistency fields from the paper's cross `G^A/G^B`
relation or from a stronger role-residual package. -/
theorem ofDiagonalConsistency
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (input : MainFormalPostRolePackageDiagonalConsistencyInput
      params strategy eps k scalars rolePackage) :
    MainFormalPostRolePackageDiagonalSSCInput
      params strategy eps k scalars rolePackage where
  leftSelfConsistency := by
    let GLeft : IdxMeas Unit (Polynomial params) ι :=
      fun _ => unsymmetrizedLeftPOVM rolePackage.roleMeasurement
    have hleft :=
      Preliminaries.bipartiteSSCRel_of_consRel_self_measurement
        strategy.state (uniformDistribution Unit) GLeft scalars.zeta1
        (by
          simpa [GLeft, IdxMeas.toIdxSubMeas, constSubMeasFamily] using
            input.leftDiagonalConsistency)
    simpa [GLeft, IdxMeas.toIdxSubMeas, constSubMeasFamily] using hleft
  rightSelfConsistency := by
    let GRight : IdxMeas Unit (Polynomial params) ι :=
      fun _ => unsymmetrizedRightPOVM rolePackage.roleMeasurement
    have hright :=
      Preliminaries.bipartiteSSCRel_of_consRel_self_measurement
        strategy.state (uniformDistribution Unit) GRight scalars.zeta1
        (by
          simpa [GRight, IdxMeas.toIdxSubMeas, constSubMeasFamily] using
            input.rightDiagonalConsistency)
    simpa [GRight, IdxMeas.toIdxSubMeas, constSubMeasFamily] using hright

end MainFormalPostRolePackageDiagonalSSCInput

/-- Explicit completion witnesses for a fixed line-130 orthonormalization residual.

This is the data-valued version of the remaining Step 6 completion producer: it
records the distinguished completion outcomes, the two completed-closeness
statements, and the construction-level orthonormalization match-mass preservation
facts for the chosen line-130 projective submeasurements.  The self-consistency
hypotheses used by `completingToMeasurement` are not stored here after the
completed-closeness fields have been produced; see
`nonempty_ofCompletingToMeasurementInputs` below for the proposition-valued
constructor that derives these fields from `BipartiteSSCRel`. -/
structure MainFormalPostRolePackageDiagonalCompletionInput
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars)
    (orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
      params strategy eps k scalars rolePackage) where
  /-- Alice-side distinguished outcome receiving the completion residual. -/
  a_A : Polynomial params
  /-- Bob-side distinguished outcome receiving the completion residual. -/
  a_B : Polynomial params
  /-- Alice-side completed-closeness proof for the line-130 projective submeasurement. -/
  leftCompletedCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily
        (Preliminaries.completeAtOutcomeProj orthResidual.P_A a_A).toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1)
  /-- Bob-side completed-closeness proof in the left-register form returned by
  `completingToMeasurement`. -/
  rightCompletedCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily
        (Preliminaries.completeAtOutcomeProj orthResidual.P_B a_B).toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1)
  /-- Alice-side match-mass preservation for the line-130 orthonormalized
  submeasurement against Bob's unsymmetrized POVM. -/
  leftMatchMassPreservation :
    MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
      (unsymmetrizedLeftPOVM rolePackage.roleMeasurement) orthResidual.P_A
      (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
  /-- Bob-side match-mass preservation, in the role-reversed orientation used by
  the mirror line-169 link. -/
  rightMatchMassPreservation :
    MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
      (unsymmetrizedRightPOVM rolePackage.roleMeasurement) orthResidual.P_B
      (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)

namespace MainFormalPostRolePackageDiagonalCompletionInput

/-- Convert explicit line-130 completion witnesses into the residual shape
consumed by the live Step 6 assembly.

This is the checked data-valued constructor for the old generic
`completionProducer`: callers may supply a function returning this input for each
line-130 orthonormalization residual and then use `toCompletionResidual` as the
producer. -/
noncomputable def toCompletionResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    {orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
      params strategy eps k scalars rolePackage}
    (input : MainFormalPostRolePackageDiagonalCompletionInput
      params strategy eps k scalars rolePackage orthResidual) :
    MainFormalPostRolePackageDiagonalCompletionResidual
      params strategy eps k scalars rolePackage where
  orthResidual := orthResidual
  a_A := input.a_A
  a_B := input.a_B
  leftCompletedCloseness := input.leftCompletedCloseness
  rightCompletedCloseness := input.rightCompletedCloseness
  leftMatchMass := input.leftMatchMassPreservation.matchMassPreservation
  rightMatchMass := input.rightMatchMassPreservation.matchMassPreservation

/-- The completed measurements obtained from a completion input satisfy the
construction-level match-mass monotonicity invariant used for the exact paper
line-169 `ζ₁` links.

This exposes the role of
`ProjectivizationMatchMassMonotonicity.of_submeasurement_match_mass_and_completion`
for callers that reason directly with completed projective measurements, while
`toCompletionResidual` keeps the older residual's P-level match-mass fields.

**Status:** currently unused (no callers).  Kept as a named interface for
downstream consumers that need the `ProjectivizationMatchMassMonotonicity`
witness directly rather than going through `toCompletionResidual`. -/
theorem toProjectivizationMatchMassMonotonicity
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    {orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
      params strategy eps k scalars rolePackage}
    (input : MainFormalPostRolePackageDiagonalCompletionInput
      params strategy eps k scalars rolePackage orthResidual) :
    MakingMeasurementsProjective.ProjectivizationMatchMassMonotonicity strategy.state
      (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
      (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
      (Preliminaries.completeAtOutcomeProj orthResidual.P_A input.a_A)
      (Preliminaries.completeAtOutcomeProj orthResidual.P_B input.a_B) := by
  open MakingMeasurementsProjective.ProjectivizationMatchMassMonotonicity in
    exact of_submeasurement_match_mass_and_completion
      orthResidual.P_A orthResidual.P_B input.a_A input.a_B
      (Preliminaries.completeAtOutcomeProj orthResidual.P_A input.a_A)
      (Preliminaries.completeAtOutcomeProj orthResidual.P_B input.a_B)
      rfl rfl input.leftMatchMassPreservation input.rightMatchMassPreservation

/-- Completing after lifting to the left tensor agrees with lifting the
completion of the original submeasurement.

This identifies the `qSDD` term coming from
`Preliminaries.completion_self_distance` for `B.liftLeft` with the left-lifted
completion of `B` used by `completeAtOutcomeProj`. -/
private lemma qSDD_liftLeft_completeAtOutcome_eq
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (A B : SubMeas Outcome ι) (a0 : Outcome) :
    qSDD ψ A.liftLeft (Preliminaries.completeAtOutcome B.liftLeft a0).toSubMeas =
      qSDD ψ A.liftLeft (Preliminaries.completeAtOutcome B a0).toSubMeas.liftLeft := by
  have hcomplete_outcome :
      ∀ a : Outcome,
        (Preliminaries.completeAtOutcome B.liftLeft a0).toSubMeas.outcome a =
          ((Preliminaries.completeAtOutcome B a0).toSubMeas.liftLeft).outcome a := by
    intro a
    by_cases h : a = a0
    · subst h
      ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
        simp [Preliminaries.completeAtOutcome, SubMeas.liftLeft, leftTensor, sub_eq_add_neg,
          h₁, h₂, add_comm, add_assoc]
    · ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
        simp [Preliminaries.completeAtOutcome, SubMeas.liftLeft, leftTensor, h, h₁, h₂]
  unfold qSDD qSDDCore
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [hcomplete_outcome a]

/-- The diagonal match mass against a genuine measurement is bounded by the left
total of the other submeasurement.

The hypothesis `B : Measurement` is essential: the proof uses
`Measurement.outcome_le_one` to dominate each tensor summand by the left tensor
of the corresponding outcome of `A`. -/
private lemma qBipartiteMatchMass_le_left_total_of_measurement
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (A : SubMeas Outcome ι) (B : Measurement Outcome ι) :
    qBipartiteMatchMass ψ A B.toSubMeas ≤
      ev ψ (leftTensor (ι₂ := ι) A.total) := by
  unfold qBipartiteMatchMass
  calc
    ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))
      ≤ ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact ev_mono ψ _ _ <|
            opTensor_le_leftTensor (ι₂ := ι)
              (A.outcome_pos a) (Measurement.outcome_le_one B a)
    _ = ev ψ (leftTensor (ι₂ := ι) A.total) := by
          rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ι) (A.outcome a))]
          rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ A.outcome]
          rw [A.sum_eq_total]

/-- A bound on the missing left total controls the completion defect of a
projective submeasurement.

The proof rewrites the completion distance as `ev ψ ((1 - P.total)^2)` via
`Preliminaries.completion_self_distance`, then uses `R^2 ≤ R` for
`R = 1 - P.liftLeft.total`. -/
private lemma qSDD_completeAtOutcomeProj_le_of_total_gap
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (P : ProjSubMeas Outcome ι) (a0 : Outcome) {ζ : Error}
    (hgap : 1 - ev ψ (leftTensor (ι₂ := ι) P.toSubMeas.total) ≤ ζ) :
    qSDD ψ P.toSubMeas.liftLeft
      (Preliminaries.completeAtOutcomeProj P a0).toSubMeas.liftLeft ≤ ζ := by
  let R : MIPStarRE.Quantum.Op (ι × ι) :=
    (1 : MIPStarRE.Quantum.Op (ι × ι)) - P.toSubMeas.liftLeft.total
  have hraw :
      qSDD ψ P.toSubMeas.liftLeft
          (Preliminaries.completeAtOutcome P.toSubMeas.liftLeft a0).toSubMeas ≤
        ζ := by
    have hcomp :
        qSDD ψ P.toSubMeas.liftLeft
            (Preliminaries.completeAtOutcome P.toSubMeas.liftLeft a0).toSubMeas =
          ev ψ (R * R) := by
      simpa [R] using
        (Preliminaries.completion_self_distance ψ P.toSubMeas.liftLeft a0)
    have hR_nonneg : 0 ≤ R := by
      dsimp [R]
      exact sub_nonneg.mpr P.toSubMeas.liftLeft.total_le_one
    have hR_le_one : R ≤ 1 := by
      dsimp [R]
      exact sub_le_self (1 : MIPStarRE.Quantum.Op (ι × ι))
        P.toSubMeas.liftLeft.total_nonneg
    have hR_sq_le : R * R ≤ R :=
      MIPStarRE.Quantum.sq_le_self hR_nonneg hR_le_one
    have hR_sq_ev : ev ψ (R * R) ≤ ev ψ R :=
      ev_mono ψ _ _ hR_sq_le
    have hR_ev : ev ψ R ≤ ζ := by
      have hR_eq :
          ev ψ R =
            1 - ev ψ (leftTensor (ι₂ := ι) P.toSubMeas.total) := by
        dsimp [R]
        rw [ev_sub]
        simp [SubMeas.liftLeft, ev_one_of_isNormalized ψ hψ]
      linarith
    rw [hcomp]
    exact le_trans hR_sq_ev hR_ev
  have hq_eq := qSDD_liftLeft_completeAtOutcome_eq ψ P.toSubMeas P.toSubMeas a0
  rw [hq_eq] at hraw
  simpa [Preliminaries.completeAtOutcomeProj_toSubMeas] using hraw

/-- Combine cross consistency, orthonormalization closeness, and match-mass
preservation into the completed-closeness estimate for one side.

This is the side-agnostic Step 6 argument used below for both roles: the cross
`ConsRel` bounds `1 - qBipartiteMatchMass`, the match-mass hypothesis turns that
into a bound on the missing total of `P`, and `questionSDD_triangle` then joins
the orthonormalization and completion errors. -/
private lemma completedCloseness_of_consistency_and_matchMassPreservation
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized) (ζ : Error)
    (G H : Measurement Outcome ι) (P : ProjSubMeas Outcome ι) (a0 : Outcome)
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G.toSubMeas) (constSubMeasFamily H.toSubMeas) ζ)
    (hmatch :
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation ψ G P H)
    (horth :
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily G.toSubMeas.liftLeft)
        (constSubMeasFamily P.toSubMeas.liftLeft)
        (MakingMeasurementsProjective.orthonormalizationError ζ)) :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G.toSubMeas.liftLeft)
      (constSubMeasFamily
        (Preliminaries.completeAtOutcomeProj P a0).toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ) := by
  let Q := Preliminaries.completeAtOutcomeProj P a0
  have hpre_q : qBipartiteConsDefect ψ G.toSubMeas H.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily] using
      hpre.offDiagonalBound
  have hmatch_GH : 1 - qBipartiteMatchMass ψ G.toSubMeas H.toSubMeas ≤ ζ := by
    rw [qBipartiteConsDefect_of_measurements ψ G H] at hpre_q
    have hone : ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) = 1 :=
      ev_one_of_isNormalized ψ hψ
    linarith
  have hmatch_PH : 1 - qBipartiteMatchMass ψ P.toSubMeas H.toSubMeas ≤ ζ := by
    linarith [hmatch_GH, hmatch.matchMassPreservation]
  have hmass_P :
      1 - ev ψ (leftTensor (ι₂ := ι) P.toSubMeas.total) ≤ ζ := by
    have hmatch_le :=
      qBipartiteMatchMass_le_left_total_of_measurement ψ P.toSubMeas H
    linarith
  have hPP_q : qSDD ψ P.toSubMeas.liftLeft Q.toSubMeas.liftLeft ≤ ζ := by
    simpa [Q] using qSDD_completeAtOutcomeProj_le_of_total_gap ψ hψ P a0 hmass_P
  have hGP_q :
      qSDD ψ G.toSubMeas.liftLeft P.toSubMeas.liftLeft ≤
        MakingMeasurementsProjective.orthonormalizationError ζ := by
    simpa [Preliminaries.constFamily_sdd_unit] using horth.squaredDistanceBound
  constructor
  rw [Preliminaries.constFamily_sdd_unit]
  calc
    qSDD ψ G.toSubMeas.liftLeft Q.toSubMeas.liftLeft
      ≤ 2 * (qSDD ψ G.toSubMeas.liftLeft P.toSubMeas.liftLeft +
          qSDD ψ P.toSubMeas.liftLeft Q.toSubMeas.liftLeft) := by
            exact Preliminaries.questionSDD_triangle ψ
              G.toSubMeas.liftLeft P.toSubMeas.liftLeft Q.toSubMeas.liftLeft
    _ ≤ 2 * (MakingMeasurementsProjective.orthonormalizationError ζ + ζ) := by
          gcongr
    _ = 2 * MakingMeasurementsProjective.orthonormalizationError ζ + 2 * ζ := by ring
    _ ≤ MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ := by
          have hsqrt_nonneg :
              0 ≤ 4 * Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
            positivity
          unfold MakingMeasurementsProjective.orthonormalizeAndCompleteError
          linarith

/-- Produce the line-130 completion witnesses directly from the cross
consistency statement and the orthonormalization match-mass data.

This argument does not invoke `Preliminaries.completingToMeasurement`.
Instead, the role package already reconstructs line 130 as a cross `ConsRel`
`G^A \simeq_{\zeta_1} G^B`, the orthonormalization residual already carries the
projective submeasurements `P^A,P^B`, and the remaining completion bound is
derived directly from the construction-level match-mass preservation facts for
those `P`-families. -/
theorem nonempty_ofDiagonalConsistencyAndMatchMassPreservation
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
      params strategy eps k scalars rolePackage)
    (a_A a_B : Polynomial params)
    (hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1)
    (leftMatchMassPreservation :
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement) orthResidual.P_A
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement))
    (rightMatchMassPreservation :
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
      (unsymmetrizedRightPOVM rolePackage.roleMeasurement) orthResidual.P_B
      (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)) :
    Nonempty (MainFormalPostRolePackageDiagonalCompletionInput
      params strategy eps k scalars rolePackage orthResidual) := by
  let G_A := unsymmetrizedLeftPOVM rolePackage.roleMeasurement
  let G_B := unsymmetrizedRightPOVM rolePackage.roleMeasurement
  have hleftCompletedCloseness :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily G_A.toSubMeas.liftLeft)
        (constSubMeasFamily
          (Preliminaries.completeAtOutcomeProj orthResidual.P_A a_A).toSubMeas.liftLeft)
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1) := by
    simpa [G_A, G_B] using
      completedCloseness_of_consistency_and_matchMassPreservation
        strategy.state strategy.isNormalized scalars.zeta1
        G_A G_B orthResidual.P_A a_A hpre leftMatchMassPreservation
        orthResidual.leftCloseness
  have hpre_symm : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_B.toSubMeas)
      (constSubMeasFamily G_A.toSubMeas)
      scalars.zeta1 :=
    consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas)
      scalars.zeta1 hpre
  have hrightCompletedCloseness :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily G_B.toSubMeas.liftLeft)
        (constSubMeasFamily
          (Preliminaries.completeAtOutcomeProj orthResidual.P_B a_B).toSubMeas.liftLeft)
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1) := by
    simpa [G_A, G_B] using
      completedCloseness_of_consistency_and_matchMassPreservation
        strategy.state strategy.isNormalized scalars.zeta1
        G_B G_A orthResidual.P_B a_B hpre_symm rightMatchMassPreservation
        orthResidual.rightCloseness
  exact ⟨{
    a_A := a_A
    a_B := a_B
    leftCompletedCloseness := hleftCompletedCloseness
    rightCompletedCloseness := hrightCompletedCloseness
    leftMatchMassPreservation := leftMatchMassPreservation
    rightMatchMassPreservation := rightMatchMassPreservation }⟩

/-- Produce explicit completion witnesses from the analytic completion theorem.

The only analytic hypotheses are exactly the two strong self-consistency facts
for the unsymmetrized role POVMs.  The line-130 orthonormalization residual
provides the `A ≈ P` closeness input to `completingToMeasurement`; the returned
completed-closeness statements are repackaged for the canonical projective
completions `completeAtOutcomeProj`. -/
theorem nonempty_ofCompletingToMeasurementInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
      params strategy eps k scalars rolePackage)
    (a_A a_B : Polynomial params)
    (leftSelfConsistency :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
        scalars.zeta1)
    (rightSelfConsistency :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
        scalars.zeta1)
    (leftMatchMassPreservation :
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement) orthResidual.P_A
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement))
    (rightMatchMassPreservation :
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement) orthResidual.P_B
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)) :
    Nonempty (MainFormalPostRolePackageDiagonalCompletionInput
      params strategy eps k scalars rolePackage orthResidual) := by
  classical
  obtain ⟨C_A, hC_A, hC_Astmt⟩ :=
    Preliminaries.completingToMeasurement
      (Outcome := Polynomial params) (ι := ι) strategy.state strategy.permInvState
      strategy.isNormalized (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
      orthResidual.P_A.toSubMeas a_A
      (MakingMeasurementsProjective.orthonormalizationError scalars.zeta1)
      scalars.zeta1 leftSelfConsistency orthResidual.leftCloseness
  obtain ⟨C_B, hC_B, hC_Bstmt⟩ :=
    Preliminaries.completingToMeasurement
      (Outcome := Polynomial params) (ι := ι) strategy.state strategy.permInvState
      strategy.isNormalized (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
      orthResidual.P_B.toSubMeas a_B
      (MakingMeasurementsProjective.orthonormalizationError scalars.zeta1)
      scalars.zeta1 rightSelfConsistency orthResidual.rightCloseness
  have leftCompletedCloseness :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
        (constSubMeasFamily
          (Preliminaries.completeAtOutcomeProj orthResidual.P_A a_A).toSubMeas.liftLeft)
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1) := by
    simpa [MakingMeasurementsProjective.orthonormalizeAndCompleteError, hC_A] using
      hC_Astmt.closenessAfterCompletion
  have rightCompletedCloseness :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
        (constSubMeasFamily
          (Preliminaries.completeAtOutcomeProj orthResidual.P_B a_B).toSubMeas.liftLeft)
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1) := by
    simpa [MakingMeasurementsProjective.orthonormalizeAndCompleteError, hC_B] using
      hC_Bstmt.closenessAfterCompletion
  exact ⟨{
    a_A := a_A
    a_B := a_B
    leftCompletedCloseness := leftCompletedCloseness
    rightCompletedCloseness := rightCompletedCloseness
    leftMatchMassPreservation := leftMatchMassPreservation
    rightMatchMassPreservation := rightMatchMassPreservation }⟩

/-- Produce completion witnesses from the additional diagonal SSC package.

This is the same construction as `nonempty_ofCompletingToMeasurementInputs`, but
the two self-consistency inputs are bundled under
`MainFormalPostRolePackageDiagonalSSCInput`, the extra diagonal data needed
after the paper's line-130 cross relation has been reconstructed. -/
theorem nonempty_ofDiagonalSSCInput
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
      params strategy eps k scalars rolePackage)
    (a_A a_B : Polynomial params)
    (diagonalSSC :
      MainFormalPostRolePackageDiagonalSSCInput
        params strategy eps k scalars rolePackage)
    (leftMatchMassPreservation :
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement) orthResidual.P_A
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement))
    (rightMatchMassPreservation :
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement) orthResidual.P_B
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)) :
    Nonempty (MainFormalPostRolePackageDiagonalCompletionInput
      params strategy eps k scalars rolePackage orthResidual) :=
  nonempty_ofCompletingToMeasurementInputs orthResidual a_A a_B
    diagonalSSC.leftSelfConsistency diagonalSSC.rightSelfConsistency
    leftMatchMassPreservation rightMatchMassPreservation

/-- Produce completion witnesses from the diagonal self-`ConsRel` version of the
extra completion obligation.

This theorem makes the exact remaining paper lemma usable in the native
`≃`/`ConsRel` form: once callers prove diagonal consistency for `G^A` and
`G^B`, in addition to the paper's line-130 cross relation, the conversion to
`BipartiteSSCRel` and the completion theorem are both checked. -/
theorem nonempty_ofDiagonalConsistencyInput
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (orthResidual : MainFormalPostRolePackageDiagonalOrthonormalizationResidual
      params strategy eps k scalars rolePackage)
    (a_A a_B : Polynomial params)
    (diagonalConsistency :
      MainFormalPostRolePackageDiagonalConsistencyInput
        params strategy eps k scalars rolePackage)
    (leftMatchMassPreservation :
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement) orthResidual.P_A
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement))
    (rightMatchMassPreservation :
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement) orthResidual.P_B
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)) :
    Nonempty (MainFormalPostRolePackageDiagonalCompletionInput
      params strategy eps k scalars rolePackage orthResidual) :=
  nonempty_ofDiagonalSSCInput orthResidual a_A a_B
    (MainFormalPostRolePackageDiagonalSSCInput.ofDiagonalConsistency
      diagonalConsistency)
    leftMatchMassPreservation rightMatchMassPreservation

end MainFormalPostRolePackageDiagonalCompletionInput

namespace MainFormalPostRolePackageDiagonalCompletionResidual

/-- Forget only the provenance wrapper after constructing the fixed Step 6
witness package from line-130 orthonormalization plus completion closeness. -/
noncomputable def toProjectiveCompletionResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (residual : MainFormalPostRolePackageDiagonalCompletionResidual
      params strategy eps k scalars rolePackage) :
    MainFormalPostRolePackageProjectiveCompletionResidual
      params strategy eps k scalars rolePackage :=
  MainFormalPostRolePackageProjectiveCompletionResidual.ofDiagonalOrthonormalizationAndCompletion
    residual.orthResidual residual.a_A residual.a_B
    residual.leftCompletedCloseness residual.rightCompletedCloseness
    residual.leftMatchMass residual.rightMatchMass

end MainFormalPostRolePackageDiagonalCompletionResidual

end Test

end MIPStarRE.LDT
