import MIPStarRE.LDT.Test.MainTheorem.SourceRoleRegister.Core

/-!
# Source-Boundary Role-Register Handoff: Completion Lemmas

This module contains the completion and line-169 transport lemmas for the
two-space source role-register route.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.LDT.MakingMeasurementsProjective

namespace ProjStrat

/-- Completing after left tensor placement agrees with left tensor placement
after completing the local submeasurement.

This is the bookkeeping needed to apply the standard completion-distance
identity on the product Hilbert space while returning the local completed
projective measurement appearing in the paper. -/
private lemma qSDD_leftPlaced_completeAtOutcome_eq
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (A B : SubMeas Outcome ιA) (a0 : Outcome) :
    qSDD ψ (leftPlacedSubMeas (ιB := ιB) A)
        (Preliminaries.completeAtOutcome (leftPlacedSubMeas (ιB := ιB) B) a0).toSubMeas =
      qSDD ψ (leftPlacedSubMeas (ιB := ιB) A)
        (leftPlacedSubMeas (ιB := ιB)
          (Preliminaries.completeAtOutcome B a0).toSubMeas) := by
  have hcomplete_outcome :
      ∀ a : Outcome,
        (Preliminaries.completeAtOutcome
            (leftPlacedSubMeas (ιB := ιB) B) a0).toSubMeas.outcome a =
          (leftPlacedSubMeas (ιB := ιB)
            (Preliminaries.completeAtOutcome B a0).toSubMeas).outcome a := by
    intro a
    by_cases h : a = a0
    · subst h
      ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
        simp [Preliminaries.completeAtOutcome, leftPlacedSubMeas, leftTensor,
          sub_eq_add_neg, h₁, h₂, add_comm, add_assoc]
    · ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
        simp [Preliminaries.completeAtOutcome, leftPlacedSubMeas, leftTensor, h, h₁, h₂]
  unfold qSDD qSDDCore
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [hcomplete_outcome a]

/-- Completing after right tensor placement agrees with right tensor placement
after completing the local submeasurement. -/
private lemma qSDD_rightPlaced_completeAtOutcome_eq
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (A B : SubMeas Outcome ιB) (a0 : Outcome) :
    qSDD ψ (rightPlacedSubMeas (ιA := ιA) A)
        (Preliminaries.completeAtOutcome (rightPlacedSubMeas (ιA := ιA) B) a0).toSubMeas =
      qSDD ψ (rightPlacedSubMeas (ιA := ιA) A)
        (rightPlacedSubMeas (ιA := ιA)
          (Preliminaries.completeAtOutcome B a0).toSubMeas) := by
  have hcomplete_outcome :
      ∀ a : Outcome,
        (Preliminaries.completeAtOutcome
            (rightPlacedSubMeas (ιA := ιA) B) a0).toSubMeas.outcome a =
          (rightPlacedSubMeas (ιA := ιA)
            (Preliminaries.completeAtOutcome B a0).toSubMeas).outcome a := by
    intro a
    by_cases h : a = a0
    · subst h
      ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
        simp [Preliminaries.completeAtOutcome, rightPlacedSubMeas, rightTensor,
          sub_eq_add_neg, h₁, h₂, add_comm, add_assoc]
    · ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
        simp [Preliminaries.completeAtOutcome, rightPlacedSubMeas, rightTensor, h, h₁, h₂]
  unfold qSDD qSDDCore
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [hcomplete_outcome a]

/-- If the missing left total of a projective submeasurement is small on the
state, then the canonical completion is close to the submeasurement after left
tensor placement. -/
private lemma qSDD_completeAtOutcomeProj_leftPlaced_le_of_total_gap
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (P : ProjSubMeas Outcome ιA) (a0 : Outcome) {ζ : Error}
    (hgap : 1 - ev ψ (leftTensor (ι₂ := ιB) P.toSubMeas.total) ≤ ζ) :
    qSDD ψ (leftPlacedSubMeas (ιB := ιB) P.toSubMeas)
      (leftPlacedSubMeas (ιB := ιB)
        (Preliminaries.completeAtOutcomeProj P a0).toSubMeas) ≤ ζ := by
  let R : MIPStarRE.Quantum.Op (ιA × ιB) :=
    (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
      (leftPlacedSubMeas (ιB := ιB) P.toSubMeas).total
  have hraw :
      qSDD ψ (leftPlacedSubMeas (ιB := ιB) P.toSubMeas)
          (Preliminaries.completeAtOutcome
            (leftPlacedSubMeas (ιB := ιB) P.toSubMeas) a0).toSubMeas ≤
        ζ := by
    have hcomp :
        qSDD ψ (leftPlacedSubMeas (ιB := ιB) P.toSubMeas)
            (Preliminaries.completeAtOutcome
              (leftPlacedSubMeas (ιB := ιB) P.toSubMeas) a0).toSubMeas =
          ev ψ (R * R) := by
      simpa [R] using
        (Preliminaries.completion_self_distance ψ
          (leftPlacedSubMeas (ιB := ιB) P.toSubMeas) a0)
    have hR_nonneg : 0 ≤ R := by
      dsimp [R]
      exact sub_nonneg.mpr (leftPlacedSubMeas (ιB := ιB) P.toSubMeas).total_le_one
    have hR_le_one : R ≤ 1 := by
      dsimp [R]
      exact sub_le_self (1 : MIPStarRE.Quantum.Op (ιA × ιB))
        (leftPlacedSubMeas (ιB := ιB) P.toSubMeas).total_nonneg
    have hR_sq_le : R * R ≤ R :=
      MIPStarRE.Quantum.sq_le_self hR_nonneg hR_le_one
    have hR_sq_ev : ev ψ (R * R) ≤ ev ψ R :=
      ev_mono ψ _ _ hR_sq_le
    have hR_ev : ev ψ R ≤ ζ := by
      have hR_eq :
          ev ψ R =
            1 - ev ψ (leftTensor (ι₂ := ιB) P.toSubMeas.total) := by
        dsimp [R]
        rw [ev_sub]
        simp [ev_one_of_isNormalized ψ hψ]
      rw [hR_eq]
      exact hgap
    rw [hcomp]
    exact le_trans hR_sq_ev hR_ev
  have hq_eq :=
    qSDD_leftPlaced_completeAtOutcome_eq ψ P.toSubMeas P.toSubMeas a0
  rw [hq_eq] at hraw
  simpa [Preliminaries.completeAtOutcomeProj_toSubMeas] using hraw

/-- Right tensor-factor counterpart of
`qSDD_completeAtOutcomeProj_leftPlaced_le_of_total_gap`. -/
private lemma qSDD_completeAtOutcomeProj_rightPlaced_le_of_total_gap
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (P : ProjSubMeas Outcome ιB) (a0 : Outcome) {ζ : Error}
    (hgap : 1 - ev ψ (rightTensor (ι₁ := ιA) P.toSubMeas.total) ≤ ζ) :
    qSDD ψ (rightPlacedSubMeas (ιA := ιA) P.toSubMeas)
      (rightPlacedSubMeas (ιA := ιA)
        (Preliminaries.completeAtOutcomeProj P a0).toSubMeas) ≤ ζ := by
  let R : MIPStarRE.Quantum.Op (ιA × ιB) :=
    (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
      (rightPlacedSubMeas (ιA := ιA) P.toSubMeas).total
  have hraw :
      qSDD ψ (rightPlacedSubMeas (ιA := ιA) P.toSubMeas)
          (Preliminaries.completeAtOutcome
            (rightPlacedSubMeas (ιA := ιA) P.toSubMeas) a0).toSubMeas ≤
        ζ := by
    have hcomp :
        qSDD ψ (rightPlacedSubMeas (ιA := ιA) P.toSubMeas)
            (Preliminaries.completeAtOutcome
              (rightPlacedSubMeas (ιA := ιA) P.toSubMeas) a0).toSubMeas =
          ev ψ (R * R) := by
      simpa [R] using
        (Preliminaries.completion_self_distance ψ
          (rightPlacedSubMeas (ιA := ιA) P.toSubMeas) a0)
    have hR_nonneg : 0 ≤ R := by
      dsimp [R]
      exact sub_nonneg.mpr (rightPlacedSubMeas (ιA := ιA) P.toSubMeas).total_le_one
    have hR_le_one : R ≤ 1 := by
      dsimp [R]
      exact sub_le_self (1 : MIPStarRE.Quantum.Op (ιA × ιB))
        (rightPlacedSubMeas (ιA := ιA) P.toSubMeas).total_nonneg
    have hR_sq_le : R * R ≤ R :=
      MIPStarRE.Quantum.sq_le_self hR_nonneg hR_le_one
    have hR_sq_ev : ev ψ (R * R) ≤ ev ψ R :=
      ev_mono ψ _ _ hR_sq_le
    have hR_ev : ev ψ R ≤ ζ := by
      have hR_eq :
          ev ψ R =
            1 - ev ψ (rightTensor (ι₁ := ιA) P.toSubMeas.total) := by
        dsimp [R]
        rw [ev_sub]
        simp [ev_one_of_isNormalized ψ hψ]
      rw [hR_eq]
      exact hgap
    rw [hcomp]
    exact le_trans hR_sq_ev hR_ev
  have hq_eq :=
    qSDD_rightPlaced_completeAtOutcome_eq ψ P.toSubMeas P.toSubMeas a0
  rw [hq_eq] at hraw
  simpa [Preliminaries.completeAtOutcomeProj_toSubMeas] using hraw

/-- A left-factor SDD estimate controls the loss in bipartite matching mass
against a complete measurement on the right factor. -/
private lemma qBipartiteMatchMass_ge_sub_sqrt_of_left_sdd_heterogeneous
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (G : Measurement Outcome ιA) (P : SubMeas Outcome ιA)
    (B : Measurement Outcome ιB) {ε : Error}
    (hclose : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G.toSubMeas))
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P))
      ε) :
    qBipartiteMatchMass ψ P B.toSubMeas ≥
      qBipartiteMatchMass ψ G.toSubMeas B.toSubMeas - Real.sqrt ε := by
  have hgap :=
    MIPStarRE.LDT.Preliminaries.easyApproxFromApproxDelta ψ hψ
      (uniformDistribution Unit) (uniformDistribution_weight_sum_le_one Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G.toSubMeas))
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) B.toSubMeas))
      ε hclose
  have hgap' :
      |qBipartiteMatchMass ψ G.toSubMeas B.toSubMeas -
          qBipartiteMatchMass ψ P B.toSubMeas| ≤
        Real.sqrt ε := by
    simpa [avgOver, uniformDistribution, constSubMeasFamily,
      qBipartiteMatchMass, leftPlacedSubMeas, rightPlacedSubMeas,
      leftTensor_mul_rightTensor_eq_opTensor] using hgap
  have hdiff :
      qBipartiteMatchMass ψ G.toSubMeas B.toSubMeas -
          qBipartiteMatchMass ψ P B.toSubMeas ≤
        Real.sqrt ε :=
    (abs_le.mp hgap').2
  linarith

/-- A right-factor SDD estimate controls the loss in bipartite matching mass
against a complete measurement on the left factor. -/
private lemma qBipartiteMatchMass_ge_sub_sqrt_of_right_sdd_heterogeneous
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ιA) (G : Measurement Outcome ιB)
    (P : SubMeas Outcome ιB) {ε : Error}
    (hclose : SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P))
      ε) :
    qBipartiteMatchMass ψ A.toSubMeas P ≥
      qBipartiteMatchMass ψ A.toSubMeas G.toSubMeas - Real.sqrt ε := by
  have hgap :=
    MIPStarRE.LDT.Preliminaries.easyApproxFromApproxDelta ψ hψ
      (uniformDistribution Unit) (uniformDistribution_weight_sum_le_one Unit)
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P))
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) A.toSubMeas))
      ε hclose
  have hgap' :
      |qBipartiteMatchMass ψ A.toSubMeas G.toSubMeas -
          qBipartiteMatchMass ψ A.toSubMeas P| ≤
        Real.sqrt ε := by
    simpa [avgOver, uniformDistribution, constSubMeasFamily,
      qBipartiteMatchMass, leftPlacedSubMeas, rightPlacedSubMeas,
      rightTensor_mul_leftTensor_eq_opTensor] using hgap
  have hdiff :
      qBipartiteMatchMass ψ A.toSubMeas G.toSubMeas -
          qBipartiteMatchMass ψ A.toSubMeas P ≤
        Real.sqrt ε :=
    (abs_le.mp hgap').2
  linarith

/-- The bipartite matching mass against a complete right measurement is bounded
by the left total of the other submeasurement. -/
private lemma qBipartiteMatchMass_le_left_total_of_measurement_heterogeneous
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas Outcome ιA)
    (B : Measurement Outcome ιB) :
    qBipartiteMatchMass ψ A B.toSubMeas ≤
      ev ψ (leftTensor (ι₂ := ιB) A.total) := by
  unfold qBipartiteMatchMass
  calc
    ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))
      ≤ ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ιB) (A.outcome a)) := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact ev_mono ψ _ _ <|
            opTensor_le_leftTensor (ι₂ := ιB)
              (A.outcome_pos a) (Measurement.outcome_le_one B a)
    _ = ev ψ (leftTensor (ι₂ := ιB) A.total) := by
          rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ιB) (A.outcome a))]
          rw [leftTensor_finset_sum (ι₂ := ιB) Finset.univ A.outcome]
          rw [A.sum_eq_total]

/-- The bipartite matching mass against a complete left measurement is bounded
by the right total of the other submeasurement. -/
private lemma qBipartiteMatchMass_le_right_total_of_measurement_heterogeneous
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (A : Measurement Outcome ιA)
    (B : SubMeas Outcome ιB) :
    qBipartiteMatchMass ψ A.toSubMeas B ≤
      ev ψ (rightTensor (ι₁ := ιA) B.total) := by
  unfold qBipartiteMatchMass
  calc
    ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))
      ≤ ∑ a : Outcome, ev ψ (rightTensor (ι₁ := ιA) (B.outcome a)) := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact ev_mono ψ _ _ <|
            calc
              opTensor (A.outcome a) (B.outcome a)
                  ≤ opTensor (1 : MIPStarRE.Quantum.Op ιA) (B.outcome a) :=
                    opTensor_mono_left (Measurement.outcome_le_one A a) (B.outcome_pos a)
              _ = rightTensor (ι₁ := ιA) (B.outcome a) := by
                    simp [rightTensor, opTensor]
    _ = ev ψ (rightTensor (ι₁ := ιA) B.total) := by
          rw [← ev_sum ψ (fun a : Outcome => rightTensor (ι₁ := ιA) (B.outcome a))]
          rw [rightTensor_finset_sum (ι₁ := ιA) Finset.univ B.outcome]
          rw [B.sum_eq_total]

/-- Completing a projective submeasurement on Alice's side can only increase
its bipartite matching mass against a fixed Bob-side submeasurement. -/
private lemma completeAtOutcomeProj_left_matchMass_ge_heterogeneous
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (P : ProjSubMeas Outcome ιA)
    (B : SubMeas Outcome ιB) (a0 : Outcome) :
    qBipartiteMatchMass ψ (Preliminaries.completeAtOutcomeProj P a0).toSubMeas B ≥
      qBipartiteMatchMass ψ P.toSubMeas B := by
  classical
  unfold qBipartiteMatchMass
  refine Finset.sum_le_sum ?_
  intro a _
  by_cases ha : a = a0
  · subst a
    have hres_nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ιA) - P.toSubMeas.total :=
      sub_nonneg.mpr P.toSubMeas.total_le_one
    have hextra_nonneg :
        0 ≤ ev ψ (opTensor ((1 : MIPStarRE.Quantum.Op ιA) - P.toSubMeas.total)
          (B.outcome a0)) :=
      ev_nonneg_of_psd ψ _ <| opTensor_nonneg hres_nonneg (B.outcome_pos a0)
    simp [Preliminaries.completeAtOutcome, opTensor_add_left_local, ev_add]
    linarith
  · simp [Preliminaries.completeAtOutcome, ha]

/-- Completing a projective submeasurement on Bob's side can only increase its
bipartite matching mass against a fixed Alice-side submeasurement. -/
private lemma completeAtOutcomeProj_right_matchMass_ge_heterogeneous
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (A : SubMeas Outcome ιA)
    (P : ProjSubMeas Outcome ιB) (a0 : Outcome) :
    qBipartiteMatchMass ψ A (Preliminaries.completeAtOutcomeProj P a0).toSubMeas ≥
      qBipartiteMatchMass ψ A P.toSubMeas := by
  classical
  unfold qBipartiteMatchMass
  refine Finset.sum_le_sum ?_
  intro a _
  by_cases ha : a = a0
  · subst a
    have hres_nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ιB) - P.toSubMeas.total :=
      sub_nonneg.mpr P.toSubMeas.total_le_one
    have hextra_nonneg :
        0 ≤ ev ψ (opTensor (A.outcome a0)
          ((1 : MIPStarRE.Quantum.Op ιB) - P.toSubMeas.total)) :=
      ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos a0) hres_nonneg
    simp [Preliminaries.completeAtOutcome, opTensor_add_right_local, ev_add]
    linarith
  · simp [Preliminaries.completeAtOutcome, ha]

/-- Combine cross consistency and Alice-side orthonormalization closeness into
the completion estimate for the left tensor factor. -/
private lemma completedCloseness_left_of_consistency_and_sdd
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized) (ζ : Error)
    (G_A : Measurement Outcome ιA) (G_B : Measurement Outcome ιB)
    (P_A : ProjSubMeas Outcome ιA) (a0 : Outcome)
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ)
    (horth :
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizationError ζ)) :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
      (constSubMeasFamily
        (leftPlacedSubMeas (ιB := ιB)
          (Preliminaries.completeAtOutcomeProj P_A a0).toSubMeas))
      (MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ) := by
  let Q_A := Preliminaries.completeAtOutcomeProj P_A a0
  have hpre_q : qBipartiteConsDefect ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily] using
      hpre.offDiagonalBound
  have hζ0 : 0 ≤ ζ :=
    le_trans (qBipartiteConsDefect_nonneg ψ G_A.toSubMeas G_B.toSubMeas) hpre_q
  have hmatch_G :
      1 - qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    rw [qBipartiteConsDefect_of_measurements ψ G_A G_B] at hpre_q
    have hone : ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) = 1 :=
      ev_one_of_isNormalized ψ hψ
    linarith
  have hmatch_P :
      qBipartiteMatchMass ψ P_A.toSubMeas G_B.toSubMeas ≥
        qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas -
          Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) :=
    qBipartiteMatchMass_ge_sub_sqrt_of_left_sdd_heterogeneous
      ψ hψ G_A P_A.toSubMeas G_B horth
  have hmass_P :
      1 - ev ψ (leftTensor (ι₂ := ιB) P_A.toSubMeas.total) ≤
        ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    have hmatch_le :=
      qBipartiteMatchMass_le_left_total_of_measurement_heterogeneous
        ψ P_A.toSubMeas G_B
    linarith
  have hPP_q : qSDD ψ (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas)
      (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas) ≤
      ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    simpa [Q_A] using
      qSDD_completeAtOutcomeProj_leftPlaced_le_of_total_gap ψ hψ P_A a0 hmass_P
  have hGP_q :
      qSDD ψ (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas)
          (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas) ≤
        MakingMeasurementsProjective.orthonormalizationError ζ := by
    simpa [Preliminaries.constFamily_sdd_unit] using horth.squaredDistanceBound
  constructor
  rw [Preliminaries.constFamily_sdd_unit]
  calc
    qSDD ψ (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas)
        (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas)
      ≤ 2 * (qSDD ψ (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas)
            (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas) +
          qSDD ψ (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas)
            (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas)) := by
            exact Preliminaries.questionSDD_triangle ψ
              (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas)
              (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas)
              (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas)
    _ ≤ 2 * (MakingMeasurementsProjective.orthonormalizationError ζ +
          (ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ))) := by
          gcongr
    _ = 2 * MakingMeasurementsProjective.orthonormalizationError ζ +
          2 * ζ + 2 * Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
          ring
    _ ≤ MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ := by
          have hsqrt_nonneg :
              0 ≤ Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) :=
            Real.sqrt_nonneg _
          unfold MakingMeasurementsProjective.orthonormalizeAndCompleteError
          linarith [hζ0, hsqrt_nonneg]

/-- Bob/right-factor counterpart of
`completedCloseness_left_of_consistency_and_sdd`. -/
private lemma completedCloseness_right_of_consistency_and_sdd
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized) (ζ : Error)
    (G_A : Measurement Outcome ιA) (G_B : Measurement Outcome ιB)
    (P_B : ProjSubMeas Outcome ιB) (a0 : Outcome)
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ)
    (horth :
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizationError ζ)) :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
      (constSubMeasFamily
        (rightPlacedSubMeas (ιA := ιA)
          (Preliminaries.completeAtOutcomeProj P_B a0).toSubMeas))
      (MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ) := by
  let Q_B := Preliminaries.completeAtOutcomeProj P_B a0
  have hpre_q : qBipartiteConsDefect ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily] using
      hpre.offDiagonalBound
  have hζ0 : 0 ≤ ζ :=
    le_trans (qBipartiteConsDefect_nonneg ψ G_A.toSubMeas G_B.toSubMeas) hpre_q
  have hmatch_G :
      1 - qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    rw [qBipartiteConsDefect_of_measurements ψ G_A G_B] at hpre_q
    have hone : ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) = 1 :=
      ev_one_of_isNormalized ψ hψ
    linarith
  have hmatch_P :
      qBipartiteMatchMass ψ G_A.toSubMeas P_B.toSubMeas ≥
        qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas -
          Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) :=
    qBipartiteMatchMass_ge_sub_sqrt_of_right_sdd_heterogeneous
      ψ hψ G_A G_B P_B.toSubMeas horth
  have hmass_P :
      1 - ev ψ (rightTensor (ι₁ := ιA) P_B.toSubMeas.total) ≤
        ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    have hmatch_le :=
      qBipartiteMatchMass_le_right_total_of_measurement_heterogeneous
        ψ G_A P_B.toSubMeas
    linarith
  have hPP_q : qSDD ψ (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas)
      (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas) ≤
      ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    simpa [Q_B] using
      qSDD_completeAtOutcomeProj_rightPlaced_le_of_total_gap ψ hψ P_B a0 hmass_P
  have hGP_q :
      qSDD ψ (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas)
          (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas) ≤
        MakingMeasurementsProjective.orthonormalizationError ζ := by
    simpa [Preliminaries.constFamily_sdd_unit] using horth.squaredDistanceBound
  constructor
  rw [Preliminaries.constFamily_sdd_unit]
  calc
    qSDD ψ (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas)
        (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas)
      ≤ 2 * (qSDD ψ (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas)
            (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas) +
          qSDD ψ (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas)
            (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas)) := by
            exact Preliminaries.questionSDD_triangle ψ
              (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas)
              (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas)
              (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas)
    _ ≤ 2 * (MakingMeasurementsProjective.orthonormalizationError ζ +
          (ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ))) := by
          gcongr
    _ = 2 * MakingMeasurementsProjective.orthonormalizationError ζ +
          2 * ζ + 2 * Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
          ring
    _ ≤ MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ := by
          have hsqrt_nonneg :
              0 ≤ Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) :=
            Real.sqrt_nonneg _
          unfold MakingMeasurementsProjective.orthonormalizeAndCompleteError
          linarith [hζ0, hsqrt_nonneg]

/-- Alice-side repaired line-169 consistency after completing the projective
submeasurement.

This proves the heterogeneous analogue of the paper's
`Q^A_g \otimes I \simeq I \otimes G^B_g` step, with the checked repaired loss
`ζ + sqrt (orthonormalizationError ζ)`. -/
private lemma completedLeftConsistency_of_consistency_and_sdd
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized) (ζ : Error)
    (G_A : Measurement Outcome ιA) (G_B : Measurement Outcome ιB)
    (P_A : ProjSubMeas Outcome ιA) (a0 : Outcome)
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ)
    (horth :
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizationError ζ)) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (Preliminaries.completeAtOutcomeProj P_A a0).toSubMeas)
      (constSubMeasFamily G_B.toSubMeas)
      (ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ)) := by
  let Q_A := Preliminaries.completeAtOutcomeProj P_A a0
  have hpre_q : qBipartiteConsDefect ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
      using hpre.offDiagonalBound
  have hζ0 : 0 ≤ ζ :=
    le_trans (qBipartiteConsDefect_nonneg ψ G_A.toSubMeas G_B.toSubMeas) hpre_q
  have hone : ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) = 1 :=
    ev_one_of_isNormalized ψ hψ
  have hmatch_G :
      1 - qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    rw [qBipartiteConsDefect_of_measurements ψ G_A G_B] at hpre_q
    linarith
  have hmatch_P :
      qBipartiteMatchMass ψ P_A.toSubMeas G_B.toSubMeas ≥
        qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas -
          Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) :=
    qBipartiteMatchMass_ge_sub_sqrt_of_left_sdd_heterogeneous
      ψ hψ G_A P_A.toSubMeas G_B horth
  have hmatch_Q :
      qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas ≥
        qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas -
          Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    calc
      qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas
          ≥ qBipartiteMatchMass ψ P_A.toSubMeas G_B.toSubMeas :=
            completeAtOutcomeProj_left_matchMass_ge_heterogeneous
              ψ P_A G_B.toSubMeas a0
      _ ≥ qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas -
          Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := hmatch_P
  have hmatch_Q' :
      1 - qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas ≤
        ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    linarith
  have hdefect_Q :
      qBipartiteConsDefect ψ Q_A.toSubMeas G_B.toSubMeas ≤
        ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    have hmax :
        max 0 (ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
            qBipartiteMatchMass ψ Q_A.toSubMeas G_B.toSubMeas) ≤
          ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
      exact max_le_iff.mpr
        ⟨add_nonneg hζ0 (Real.sqrt_nonneg _), by simpa [hone] using hmatch_Q'⟩
    simpa [qBipartiteConsDefect, qBipartiteMatchMass, Q_A.total_eq_one,
      G_B.total_eq_one, opTensor] using hmax
  constructor
  simpa [Q_A, bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
    using hdefect_Q

/-- Bob-side repaired line-169 consistency after completing the projective
submeasurement.

This is the heterogeneous analogue of the role-reversed line-169 relation
`G^A_g \otimes I \simeq I \otimes Q^B_g`. -/
private lemma completedRightConsistency_of_consistency_and_sdd
    {Outcome : Type*} {ιA ιB : Type*}
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized) (ζ : Error)
    (G_A : Measurement Outcome ιA) (G_B : Measurement Outcome ιB)
    (P_B : ProjSubMeas Outcome ιB) (a0 : Outcome)
    (hpre : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ)
    (horth :
      SDDRel ψ (uniformDistribution Unit)
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizationError ζ)) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily (Preliminaries.completeAtOutcomeProj P_B a0).toSubMeas)
      (ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ)) := by
  let Q_B := Preliminaries.completeAtOutcomeProj P_B a0
  have hpre_q : qBipartiteConsDefect ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
      using hpre.offDiagonalBound
  have hζ0 : 0 ≤ ζ :=
    le_trans (qBipartiteConsDefect_nonneg ψ G_A.toSubMeas G_B.toSubMeas) hpre_q
  have hone : ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) = 1 :=
    ev_one_of_isNormalized ψ hψ
  have hmatch_G :
      1 - qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas ≤ ζ := by
    rw [qBipartiteConsDefect_of_measurements ψ G_A G_B] at hpre_q
    linarith
  have hmatch_P :
      qBipartiteMatchMass ψ G_A.toSubMeas P_B.toSubMeas ≥
        qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas -
          Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) :=
    qBipartiteMatchMass_ge_sub_sqrt_of_right_sdd_heterogeneous
      ψ hψ G_A G_B P_B.toSubMeas horth
  have hmatch_Q :
      qBipartiteMatchMass ψ G_A.toSubMeas Q_B.toSubMeas ≥
        qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas -
          Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    calc
      qBipartiteMatchMass ψ G_A.toSubMeas Q_B.toSubMeas
          ≥ qBipartiteMatchMass ψ G_A.toSubMeas P_B.toSubMeas :=
            completeAtOutcomeProj_right_matchMass_ge_heterogeneous
              ψ G_A.toSubMeas P_B a0
      _ ≥ qBipartiteMatchMass ψ G_A.toSubMeas G_B.toSubMeas -
          Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := hmatch_P
  have hmatch_Q' :
      1 - qBipartiteMatchMass ψ G_A.toSubMeas Q_B.toSubMeas ≤
        ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    linarith
  have hdefect_Q :
      qBipartiteConsDefect ψ G_A.toSubMeas Q_B.toSubMeas ≤
        ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
    have hmax :
        max 0 (ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
            qBipartiteMatchMass ψ G_A.toSubMeas Q_B.toSubMeas) ≤
          ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ) := by
      exact max_le_iff.mpr
        ⟨add_nonneg hζ0 (Real.sqrt_nonneg _), by simpa [hone] using hmatch_Q'⟩
    simpa [qBipartiteConsDefect, qBipartiteMatchMass, G_A.total_eq_one,
      Q_B.total_eq_one, opTensor] using hmax
  constructor
  simpa [Q_B, bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
    using hdefect_Q

/-- Complete two projective submeasurements obtained after the line-130
cross-consistency estimate to projective measurements, with the tensor-factor
state-dependent-distance estimates required by the paper.

Paper origin: `references/ldt-paper/inductive_step.tex:143-149`.
The proof is the standard completion argument: consistency bounds the total
mass missing from the projective submeasurement after the
orthonormalization-distance loss is charged by Cauchy--Schwarz, and the
completion residual then contributes at most this missing mass. -/
theorem completedProjectiveMeasurements_ofTwoSidedSubmeasurements
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (G_A : Measurement (Polynomial params) ιA)
    (G_B : Measurement (Polynomial params) ιB)
    (P_A : ProjSubMeas (Polynomial params) ιA)
    (P_B : ProjSubMeas (Polynomial params) ιB)
    (ζ : Error)
    (hfull : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ)
    (hleft :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizationError ζ))
    (hright :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizationError ζ)) :
    ∃ Q_A : ProjMeas (Polynomial params) ιA,
      ∃ Q_B : ProjMeas (Polynomial params) ιB,
        SDDRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
          (MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ) ∧
        SDDRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
          (MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ) := by
  let a0 : Polynomial params :=
    { poly := 0
      lowIndividualDegree := by
        intro i
        simp }
  let Q_A := Preliminaries.completeAtOutcomeProj P_A a0
  let Q_B := Preliminaries.completeAtOutcomeProj P_B a0
  have hleftComplete :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ) := by
    simpa [Q_A] using
      completedCloseness_left_of_consistency_and_sdd
        strategy.state strategy.isNormalized ζ G_A G_B P_A a0 hfull hleft
  have hrightComplete :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ) := by
    simpa [Q_B] using
      completedCloseness_right_of_consistency_and_sdd
        strategy.state strategy.isNormalized ζ G_A G_B P_B a0 hfull hright
  exact ⟨Q_A, Q_B, hleftComplete, hrightComplete⟩

/-- Complete the two projective submeasurements and derive the two repaired
polynomial line-169 consistency relations.

Paper origin: `references/ldt-paper/inductive_step.tex:167-172`.  The paper
applies `triangle-sub` after the completion estimates.  The formal statement
uses the checked repaired version: the replacement of `G_A` by `Q_A` and of
`G_B` by `Q_B` is charged directly from the pre-completion orthonormalization
distance, giving the error `ζ + sqrt (orthonormalizationError ζ)`. -/
theorem completedProjectiveMeasurementsAndLine169_ofTwoSidedSubmeasurements
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (G_A : Measurement (Polynomial params) ιA)
    (G_B : Measurement (Polynomial params) ιB)
    (P_A : ProjSubMeas (Polynomial params) ιA)
    (P_B : ProjSubMeas (Polynomial params) ιB)
    (ζ : Error)
    (hfull : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ)
    (hleft :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) P_A.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizationError ζ))
    (hright :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) P_B.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizationError ζ)) :
    ∃ Q_A : ProjMeas (Polynomial params) ιA,
      ∃ Q_B : ProjMeas (Polynomial params) ιB,
        SDDRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
          (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
          (MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ) ∧
        SDDRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
          (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
          (MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ) ∧
        ConsRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily Q_A.toSubMeas)
          (constSubMeasFamily G_B.toSubMeas)
          (ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ)) ∧
        ConsRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily G_A.toSubMeas)
          (constSubMeasFamily Q_B.toSubMeas)
          (ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ)) := by
  let a0 : Polynomial params :=
    { poly := 0
      lowIndividualDegree := by
        intro i
        simp }
  let Q_A := Preliminaries.completeAtOutcomeProj P_A a0
  let Q_B := Preliminaries.completeAtOutcomeProj P_B a0
  have hleftComplete :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ) := by
    simpa [Q_A] using
      completedCloseness_left_of_consistency_and_sdd
        strategy.state strategy.isNormalized ζ G_A G_B P_A a0 hfull hleft
  have hrightComplete :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ) := by
    simpa [Q_B] using
      completedCloseness_right_of_consistency_and_sdd
        strategy.state strategy.isNormalized ζ G_A G_B P_B a0 hfull hright
  have hleftLine169 :
      ConsRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Q_A.toSubMeas)
        (constSubMeasFamily G_B.toSubMeas)
        (ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ)) := by
    simpa [Q_A] using
      completedLeftConsistency_of_consistency_and_sdd
        strategy.state strategy.isNormalized ζ G_A G_B P_A a0 hfull hleft
  have hrightLine169 :
      ConsRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily G_A.toSubMeas)
        (constSubMeasFamily Q_B.toSubMeas)
        (ζ + Real.sqrt (MakingMeasurementsProjective.orthonormalizationError ζ)) := by
    simpa [Q_B] using
      completedRightConsistency_of_consistency_and_sdd
        strategy.state strategy.isNormalized ζ G_A G_B P_B a0 hfull hright
  exact ⟨Q_A, Q_B, hleftComplete, hrightComplete, hleftLine169, hrightLine169⟩

/-- The line-156 projective consistency estimate after completing both
polynomial submeasurements.

Paper origin: `references/ldt-paper/inductive_step.tex:150-157`.  The proof
uses the consistency-to-distance implication for `G_A,G_B`, then telescopes
through the two completion-distance estimates for `Q_A` and `Q_B`. -/
theorem completedProjectiveConsistency_ofFullConsistency
    (params : Parameters)
    [FieldModel params.q]
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB)
    (G_A : Measurement (Polynomial params) ιA)
    (G_B : Measurement (Polynomial params) ιB)
    (Q_A : ProjMeas (Polynomial params) ιA)
    (Q_B : ProjMeas (Polynomial params) ιB)
    (ζ : Error)
    (hfull : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ)
    (hleftComplete :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ))
    (hrightComplete :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ)) :
    let ζ₂ : Error := MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
      (6 * ζ + 6 * ζ₂) := by
  let ζ₂ : Error := MakingMeasurementsProjective.orthonormalizeAndCompleteError ζ
  change SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
      (6 * ζ + 6 * ζ₂)
  let G_A_const : IdxMeas Unit (Polynomial params) ιA := fun _ => G_A
  let G_B_const : IdxMeas Unit (Polynomial params) ιB := fun _ => G_B
  have hfullMeas : ConsRel strategy.state (uniformDistribution Unit)
      (IdxMeas.toIdxSubMeas G_A_const)
      (IdxMeas.toIdxSubMeas G_B_const) ζ := by
    change ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily G_A.toSubMeas)
      (constSubMeasFamily G_B.toSubMeas) ζ
    exact hfull
  have hmid :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
        (2 * ζ) := by
    change SDDRel strategy.state (uniformDistribution Unit)
      (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas G_A_const))
      (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas G_B_const))
      (2 * ζ)
    exact
      Preliminaries.simeqToApprox_heterogeneous strategy.state
        (uniformDistribution Unit) G_A_const G_B_const ζ hfullMeas
  have hleftSymm :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
        ζ₂ := by
    exact
      Preliminaries.sddRel_symm strategy.state (uniformDistribution Unit)
        _ _ ζ₂ (by simpa [ζ₂] using hleftComplete)
  have hrightζ :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
        ζ₂ := by
    simpa [ζ₂] using hrightComplete
  have htri :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
        (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
        (3 * (ζ₂ + 2 * ζ + ζ₂)) :=
    Preliminaries.stateDependentDistanceRel_triangle_three strategy.state
      (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) G_A.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) G_B.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
      ζ₂ (2 * ζ) ζ₂ hleftSymm hmid hrightζ
  exact
    Preliminaries.stateDependentDistanceRel_mono strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (leftPlacedSubMeas (ιB := ιB) Q_A.toSubMeas))
      (constSubMeasFamily (rightPlacedSubMeas (ιA := ιA) Q_B.toSubMeas))
      (3 * (ζ₂ + 2 * ζ + ζ₂)) (6 * ζ + 6 * ζ₂) (by
        ring_nf
        exact le_rfl) htri

end ProjStrat

end MIPStarRE.LDT
