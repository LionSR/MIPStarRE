import MIPStarRE.LDT.Test.MainTheorem.OrthonormalizationData

/-!
# Diagonal completion construction

Diagonal completion data for the `mainFormal` assembly.  Once
the two unsymmetrized role POVMs `Gᴬ` and `Gᴮ` are obtained together with
their cross-consistency relation `Gᴬ ⊗ I ≃ I ⊗ Gᴮ` at error `ζ₁`, the
remaining construction of completed projective measurements is an internal
proof obligation.  The source-facing construction theorem below is therefore
left unfinished rather than represented by additional diagonal-consistency or
match-mass hypotheses in the public `mainFormal` statement.

The checked auxiliary lemmas in this file keep useful analytic content: they
show how completion follows once the relevant match-mass preservation and
self-consistency estimates have been proved.  They are not source-level
assumptions for the paper theorem.

## References

* Paper: `references/ldt-paper/inductive_step.tex`,
  completing to projective measurements (lines 143–147).
* Blueprint: `blueprint/src/chapter/ch04_projective.tex`,
  `\label{rem:lean-line169-projectivization-match-mass}`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

namespace MainFormalDiagonalCompletionWitness

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
Instead, the role-measurement record already reconstructs line 130 as a cross `ConsRel`
`G^A \simeq_{\zeta_1} G^B`, the orthonormalization witness already carries the
projective submeasurements `P^A,P^B`, and the remaining completion bound is
derived directly from the construction-level match-mass preservation facts for
those `P`-families. -/
private theorem nonempty_ofDiagonalConsistencyAndMatchMassPreservation
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {roleWitness : MainFormalRoleMeasurementWitness params strategy eps k scalars}
    (orthWitness : MainFormalDiagonalOrthonormalizationWitness
      params strategy eps k scalars roleWitness)
    (a_A a_B : Polynomial params)
    (hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM roleWitness.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM roleWitness.roleMeasurement).toSubMeas)
      scalars.zeta1)
    (leftMatchMassPreservation :
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
        (unsymmetrizedLeftPOVM roleWitness.roleMeasurement) orthWitness.P_A
        (unsymmetrizedRightPOVM roleWitness.roleMeasurement))
    (rightMatchMassPreservation :
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
      (unsymmetrizedRightPOVM roleWitness.roleMeasurement) orthWitness.P_B
      (unsymmetrizedLeftPOVM roleWitness.roleMeasurement)) :
    Nonempty (MainFormalDiagonalCompletionWitness
      params strategy eps k scalars roleWitness) := by
  let G_A := unsymmetrizedLeftPOVM roleWitness.roleMeasurement
  let G_B := unsymmetrizedRightPOVM roleWitness.roleMeasurement
  have hleftCompletedCloseness :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily G_A.toSubMeas.liftLeft)
        (constSubMeasFamily
          (Preliminaries.completeAtOutcomeProj orthWitness.P_A a_A).toSubMeas.liftLeft)
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1) := by
    simpa [G_A, G_B] using
      completedCloseness_of_consistency_and_matchMassPreservation
        strategy.state strategy.isNormalized scalars.zeta1
        G_A G_B orthWitness.P_A a_A hpre leftMatchMassPreservation
        orthWitness.leftCloseness
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
          (Preliminaries.completeAtOutcomeProj orthWitness.P_B a_B).toSubMeas.liftLeft)
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1) := by
    simpa [G_A, G_B] using
      completedCloseness_of_consistency_and_matchMassPreservation
        strategy.state strategy.isNormalized scalars.zeta1
        G_B G_A orthWitness.P_B a_B hpre_symm rightMatchMassPreservation
        orthWitness.rightCloseness
  exact ⟨{
    orthWitness := orthWitness
    a_A := a_A
    a_B := a_B
    leftCompletedCloseness := hleftCompletedCloseness
    rightCompletedCloseness := hrightCompletedCloseness }⟩

/-- Alice-side match-mass preservation still needed from the concrete
orthonormalization construction.

Paper origin: `references/ldt-paper/inductive_step.tex:135-169`, where the
paper replaces the pre-projective measurement \(G^{\mathrm A}\) by the
orthonormalized projective submeasurement \(P^{\mathrm A}\) and later applies
the line-169 transport.  The analytic source of the submeasurement is
`references/ldt-paper/orthonormalization.tex:282`.

This is a construction theorem for issue #1566.  It is deliberately not a
hypothesis of `mainFormal`: callers provide only the line-130 consistency
relation and the orthonormalization witness.  The substantive proof now lives
at the QXP repair construction point, tracked by #1610. -/
theorem leftMatchMassPreservation_ofDiagonalConsistency
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {roleWitness : MainFormalRoleMeasurementWitness params strategy eps k scalars}
    (orthWitness : MainFormalDiagonalOrthonormalizationWitness
      params strategy eps k scalars roleWitness)
    (_hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM roleWitness.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM roleWitness.roleMeasurement).toSubMeas)
      scalars.zeta1) :
    MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
      (unsymmetrizedLeftPOVM roleWitness.roleMeasurement) orthWitness.P_A
      (unsymmetrizedRightPOVM roleWitness.roleMeasurement) := by
  exact orthWitness.leftMatchMass

/-- Bob-side mirror of
`leftMatchMassPreservation_ofDiagonalConsistency`.

Paper origin: `references/ldt-paper/inductive_step.tex:135-169`, with the two
roles interchanged.  This is the corresponding construction theorem for issue
#1566 and is not a hypothesis in the statement of `mainFormal`.  The substantive
proof now lives at the QXP repair construction point, tracked by #1610. -/
theorem rightMatchMassPreservation_ofDiagonalConsistency
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {roleWitness : MainFormalRoleMeasurementWitness params strategy eps k scalars}
    (orthWitness : MainFormalDiagonalOrthonormalizationWitness
      params strategy eps k scalars roleWitness)
    (_hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM roleWitness.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM roleWitness.roleMeasurement).toSubMeas)
      scalars.zeta1) :
    MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
      (unsymmetrizedRightPOVM roleWitness.roleMeasurement) orthWitness.P_B
      (unsymmetrizedLeftPOVM roleWitness.roleMeasurement) := by
  exact orthWitness.rightMatchMass

/-- Direct completion construction from the paper line-130 cross consistency.

Paper origin: `references/ldt-paper/inductive_step.tex:130-149`, where the
role-block cross consistency is followed by orthonormalization and completion.

This is the source-shaped internal construction target for the `mainFormal`
proof.  It does not ask callers for a diagonal-consistency record, a
strong-self-consistency record, or match-mass preservation as an extra input.
Those facts must be proved from the role-block construction and the
orthonormalization argument.  The checked lemmas above prove the completion
argument from the two named match-mass preservation obligations, so this
declaration no longer hides the remaining construction as an additional
assumption.

**Unfaithful:** This construction currently depends, through the supplied
orthonormalization witness, on `leftLiftedProjectivizationRepairWithMatchMass`,
whose outcome-expectation preservation theorem is not yet derived from
`references/ldt-paper/inductive_step.tex:130-173`.  This is documented in
issue #1610.  Elimination: prove the QXP outcome-expectation preservation
theorem from the paper hypotheses and use it to discharge the match-mass
preservation obligations.
-/
theorem nonempty_ofDiagonalConsistency
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {roleWitness : MainFormalRoleMeasurementWitness params strategy eps k scalars}
    (orthWitness : MainFormalDiagonalOrthonormalizationWitness
      params strategy eps k scalars roleWitness)
    (hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM roleWitness.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM roleWitness.roleMeasurement).toSubMeas)
      scalars.zeta1) :
    Nonempty (MainFormalDiagonalCompletionWitness
      params strategy eps k scalars roleWitness) := by
  let a0 : Polynomial params :=
    { poly := 0
      lowIndividualDegree := by
        intro i
        simp }
  exact nonempty_ofDiagonalConsistencyAndMatchMassPreservation
    orthWitness a0 a0 hpre
    (leftMatchMassPreservation_ofDiagonalConsistency orthWitness hpre)
    (rightMatchMassPreservation_ofDiagonalConsistency orthWitness hpre)

end MainFormalDiagonalCompletionWitness

end Test

end MIPStarRE.LDT
