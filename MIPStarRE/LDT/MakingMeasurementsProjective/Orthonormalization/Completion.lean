import MIPStarRE.LDT.Tactic.LdtSimp
import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.Basic.MeasurementLift
import MIPStarRE.LDT.Test.StrategyCore
import MIPStarRE.LDT.Preliminaries.CauchySchwarz

/-!
# Option Completion in the Orthonormalization Argument

This file contains the auxiliary algebra used when the orthonormalization
theorem is applied to the completion of a submeasurement by a fresh failure
outcome.  The results compare the completed measurement with the restriction
obtained by discarding this fresh outcome.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-! ### Restricting an option-completed projective submeasurement -/

/-- Discard the fresh `none` outcome from an option-indexed projective
submeasurement. The remaining `some a` outcomes still form a projective
submeasurement. -/
noncomputable def restrictSomeProjSubMeas {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (P : ProjSubMeas (Option Outcome) ι) :
    ProjSubMeas Outcome ι where
  toSubMeas :=
    { outcome := fun a => P.outcome (some a)
      total := ∑ a : Outcome, P.outcome (some a)
      outcome_pos := fun a => P.outcome_pos (some a)
      sum_eq_total := rfl
      total_le_one := by
        calc
          ∑ a : Outcome, P.outcome (some a)
            ≤ P.outcome none + ∑ a : Outcome, P.outcome (some a) :=
                le_add_of_nonneg_left (P.outcome_pos none)
          _ = ∑ oa : Option Outcome, P.outcome oa := by
                simp [Fintype.sum_option]
          _ = P.total := by rw [P.sum_eq_total]
          _ ≤ 1 := P.total_le_one }
  proj := fun a => by simpa using P.proj (some a)

/-- If the projective replacement of the completed measurement puts at least the
original residual mass on the fresh `none` outcome, then the retained `some`
outcomes have total dominated by the original submeasurement total.

This is the precise construction-level order statement needed by the
monotone-total route in the self-improvement argument.  It separates the
formal algebra from the still-missing repair invariant
`(optionCompletion A).outcome none ≤ P.outcome none`. -/
theorem restrictSomeProjSubMeas_total_le_of_optionCompletion_residual_le
    {Outcome : Type*} {ι : Type*} [Fintype Outcome]
    [Fintype ι] [DecidableEq ι] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) (P : ProjSubMeas (Option Outcome) ι)
    (hresidual : (optionCompletion A).outcome none ≤ P.outcome none) :
    (restrictSomeProjSubMeas P).toSubMeas.total ≤ A.total := by
  let S : MIPStarRE.Quantum.Op ι := ∑ a : Outcome, P.outcome (some a)
  have hsum_le_one :
      P.outcome none + S ≤ (1 : MIPStarRE.Quantum.Op ι) := by
    calc
      P.outcome none + S
          = ∑ oa : Option Outcome, P.outcome oa := by
              simp [S, Fintype.sum_option]
      _ = P.total := by rw [P.sum_eq_total]
      _ ≤ 1 := P.total_le_one
  have hresidual' :
      (1 : MIPStarRE.Quantum.Op ι) - A.total ≤ P.outcome none := by
    simpa using hresidual
  have hcompleted :
      (1 : MIPStarRE.Quantum.Op ι) - A.total + S ≤
        (1 : MIPStarRE.Quantum.Op ι) := by
    calc
      (1 : MIPStarRE.Quantum.Op ι) - A.total + S
          ≤ P.outcome none + S := by
              simpa [add_comm] using add_le_add_right hresidual' S
      _ ≤ 1 := hsum_le_one
  have hnonneg : 0 ≤ A.total - S := by
    have hsub : 0 ≤
        (1 : MIPStarRE.Quantum.Op ι) -
          ((1 : MIPStarRE.Quantum.Op ι) - A.total + S) :=
      sub_nonneg.mpr hcompleted
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hsub
  have hS_le : S ≤ A.total := sub_nonneg.mp hnonneg
  simpa [restrictSomeProjSubMeas, S] using hS_le

/-- The right-register expectation form of
`restrictSomeProjSubMeas_total_le_of_optionCompletion_residual_le`.

This is the scalar comparison needed by the monotone-total transport in the
self-improvement theorem.  The proof first obtains the operator inequality on
the local Hilbert space and then applies monotonicity of right tensor placement
and of expectation in the ambient state. -/
theorem restrictSomeProjSubMeas_rightTensor_total_ev_le_of_optionCompletion_residual_le
    {Outcome : Type*} {ι : Type*} [Fintype Outcome]
    [Fintype ι] [DecidableEq ι] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι)) (A : SubMeas Outcome ι)
    (P : ProjSubMeas (Option Outcome) ι)
    (hresidual : (optionCompletion A).outcome none ≤ P.outcome none) :
    ev ψ (rightTensor (ι₁ := ι) (restrictSomeProjSubMeas P).toSubMeas.total) ≤
      ev ψ (rightTensor (ι₁ := ι) A.total) := by
  exact ev_mono ψ _ _ <|
    rightTensor_mono
      (restrictSomeProjSubMeas_total_le_of_optionCompletion_residual_le A P hresidual)

namespace Orthonormalization
namespace Completion

/-- Completing a submeasurement by a fresh failure outcome preserves bipartite
strong self-consistency up to the paper's factor `2`: the original diagonal gap
controls the original outcomes, and the same gap controls the residual `none`
outcome after applying permutation invariance. -/
lemma optionCompletion_bipartiteSSCRel {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ) (hψ : ψ.IsNormalized)
    (A : SubMeas Outcome ι) (ζ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A) ζ →
      BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily (optionCompletion A).toSubMeas)
        (2 * ζ) := by
  intro hssc
  let R : MIPStarRE.Quantum.Op ι := 1 - A.total
  have hζ_nonneg : 0 ≤ ζ :=
    le_trans
      (bipartiteSSCError_nonneg ψ (uniformDistribution Unit)
        (constSubMeasFamily A))
      hssc.overlapBound
  have horig_q : qBipartiteSSCDefect ψ A ≤ ζ := by
    simpa [ldt_simp] using hssc.overlapBound
  have horig_gap :
      ev ψ (leftTensor (ι₂ := ι) A.total) - qBipartiteMatchMass ψ A A ≤ ζ :=
    le_trans (le_max_right 0 _) horig_q
  have htotal_q :
      qBipartiteSSCDefect ψ (postprocess A (fun _ : Outcome => ())) ≤ ζ :=
    le_trans
      (MIPStarRE.LDT.Preliminaries.qBipartiteSSCDefect_postprocess_le
        (ψ := ψ) (M := A) (f := fun _ : Outcome => ()))
      horig_q
  have htotal_gap :
      ev ψ (leftTensor (ι₂ := ι) A.total) - ev ψ (opTensor A.total A.total) ≤ ζ :=
    le_trans (le_max_right 0 _) <| by
      simpa [qBipartiteSSCDefect, postprocess, A.sum_eq_total] using htotal_q
  have hresidual_eq :
      ev ψ (leftTensor (ι₂ := ι) R) - ev ψ (opTensor R R) =
        ev ψ (rightTensor (ι₁ := ι) A.total) - ev ψ (opTensor A.total A.total) := by
    have hop :
        leftTensor (ι₂ := ι) R - opTensor R R =
          rightTensor (ι₁ := ι) A.total - opTensor A.total A.total := by
      calc
        leftTensor (ι₂ := ι) R - opTensor R R
            = opTensor R (1 : MIPStarRE.Quantum.Op ι) - opTensor R R := by
                rfl
        _ = opTensor R ((1 : MIPStarRE.Quantum.Op ι) - R) := by
                simpa [opTensor] using
                  (MIPStarRE.Quantum.kronecker_sub_right (A := R)
                    (B₁ := (1 : MIPStarRE.Quantum.Op ι)) (B₂ := R))
        _ = opTensor R A.total := by
                simp [R]
        _ = opTensor (1 : MIPStarRE.Quantum.Op ι) A.total - opTensor A.total A.total := by
                simpa [R] using
                  (opTensor_sub_left (A := (1 : MIPStarRE.Quantum.Op ι))
                    (B := A.total) (C := A.total)).symm
        _ = rightTensor (ι₁ := ι) A.total - opTensor A.total A.total := by
                rfl
    simpa [ev_sub] using congrArg (ev ψ) hop
  have hresidual_gap :
      ev ψ (leftTensor (ι₂ := ι) R) - ev ψ (opTensor R R) ≤ ζ := by
    rw [hresidual_eq, ← hperm.swap_ev A.total]
    exact htotal_gap
  have hleftR :
      ev ψ (leftTensor (ι₂ := ι) R) = 1 - ev ψ (leftTensor (ι₂ := ι) A.total) := by
    have hleftSub' :
        1 - leftTensor (ι₂ := ι) A.total = leftTensor (ι₂ := ι) R := by
      calc
        1 - leftTensor (ι₂ := ι) A.total
            = leftTensor (ι₂ := ι) (1 : MIPStarRE.Quantum.Op ι) -
                leftTensor (ι₂ := ι) A.total := by
                  rw [leftTensor_one (ι₁ := ι) (ι₂ := ι)]
        _ = leftTensor (ι₂ := ι) R := by
              change opTensor (1 : MIPStarRE.Quantum.Op ι) (1 : MIPStarRE.Quantum.Op ι) -
                  opTensor A.total (1 : MIPStarRE.Quantum.Op ι) =
                opTensor R (1 : MIPStarRE.Quantum.Op ι)
              simpa [R] using
                (opTensor_sub_left (A := (1 : MIPStarRE.Quantum.Op ι))
                  (B := A.total) (C := (1 : MIPStarRE.Quantum.Op ι)))
    rw [← hleftSub', ev_sub]
    simp [ev_one_of_isNormalized ψ hψ]
  have hcompleted_gap :
      1 - (qBipartiteMatchMass ψ A A + ev ψ (opTensor R R)) ≤ 2 * ζ := by
    linarith [horig_gap, hresidual_gap, hleftR]
  have hoverlap_completion :
      ∑ oa : Option Outcome,
          ev ψ
            (opTensor
              ((optionCompletion A).outcome oa)
              ((optionCompletion A).outcome oa)) =
        ev ψ (opTensor R R) + qBipartiteMatchMass ψ A A := by
    rw [Fintype.sum_option]
    simp [qBipartiteMatchMass, R]
  have hcompleted_q :
      qBipartiteSSCDefect ψ (optionCompletion A).toSubMeas ≤ 2 * ζ := by
    unfold qBipartiteSSCDefect
    dsimp
    have hmass_completion :
        ev ψ (leftTensor (ι₂ := ι) (optionCompletion A).toSubMeas.total) = 1 := by
      calc
        ev ψ (leftTensor (ι₂ := ι) (optionCompletion A).toSubMeas.total)
            = ev ψ (leftTensor (ι₂ := ι) (1 : MIPStarRE.Quantum.Op ι)) := by
                rw [(optionCompletion A).total_eq_one]
        _ = ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
                simpa using
                  congrArg (ev ψ) (leftTensor_one (ι₁ := ι) (ι₂ := ι))
        _ = 1 := ev_one_of_isNormalized ψ hψ
    rw [hmass_completion, hoverlap_completion]
    refine max_le_iff.mpr ?_
    constructor
    · nlinarith
    · simpa [add_comm, add_left_comm, add_assoc] using hcompleted_gap
  constructor
  simpa [bipartiteSSCError, avgOver, uniformDistribution, constSubMeasFamily]
    using hcompleted_q

/-- Discarding the extra `none` outcome from the option-completed measurement can
only decrease the `qSDD` sum: one simply drops a nonnegative summand. -/
lemma qSDD_liftLeft_restrictSomeProjSubMeas_le {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas Outcome ι) (P : ProjSubMeas (Option Outcome) ι) :
    qSDD ψ A.liftLeft (restrictSomeProjSubMeas P).toSubMeas.liftLeft ≤
      qSDD ψ (optionCompletion A).toSubMeas.liftLeft P.toSubMeas.liftLeft := by
  have hsome :
      qSDD ψ A.liftLeft (restrictSomeProjSubMeas P).toSubMeas.liftLeft =
        ∑ a : Outcome,
          ev ψ
            ((((optionCompletion A).toSubMeas.liftLeft).outcome (some a) -
                  (P.toSubMeas.liftLeft).outcome (some a))ᴴ *
                (((optionCompletion A).toSubMeas.liftLeft).outcome (some a) -
                  (P.toSubMeas.liftLeft).outcome (some a))) := by
    unfold qSDD qSDDCore
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [optionCompletion, restrictSomeProjSubMeas, SubMeas.liftLeft]
  rw [hsome]
  have hnone_nonneg :
      0 ≤ ev ψ
        ((((optionCompletion A).toSubMeas.liftLeft).outcome none -
              (P.toSubMeas.liftLeft).outcome none)ᴴ *
            (((optionCompletion A).toSubMeas.liftLeft).outcome none -
              (P.toSubMeas.liftLeft).outcome none)) :=
    ev_adjoint_self_nonneg ψ _
  calc
    ∑ a : Outcome,
        ev ψ
          ((((optionCompletion A).toSubMeas.liftLeft).outcome (some a) -
                (P.toSubMeas.liftLeft).outcome (some a))ᴴ *
              (((optionCompletion A).toSubMeas.liftLeft).outcome (some a) -
                (P.toSubMeas.liftLeft).outcome (some a)))
      ≤
        ev ψ
          ((((optionCompletion A).toSubMeas.liftLeft).outcome none -
                (P.toSubMeas.liftLeft).outcome none)ᴴ *
              (((optionCompletion A).toSubMeas.liftLeft).outcome none -
                (P.toSubMeas.liftLeft).outcome none)) +
          ∑ a : Outcome,
            ev ψ
              ((((optionCompletion A).toSubMeas.liftLeft).outcome (some a) -
                    (P.toSubMeas.liftLeft).outcome (some a))ᴴ *
                  (((optionCompletion A).toSubMeas.liftLeft).outcome (some a) -
                    (P.toSubMeas.liftLeft).outcome (some a))) :=
            le_add_of_nonneg_left hnone_nonneg
    _ = qSDD ψ (optionCompletion A).toSubMeas.liftLeft P.toSubMeas.liftLeft := by
          unfold qSDD qSDDCore
          rw [Fintype.sum_option]

end Completion
end Orthonormalization

end MIPStarRE.LDT.MakingMeasurementsProjective
