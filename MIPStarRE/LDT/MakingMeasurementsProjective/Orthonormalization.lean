import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.MakingMeasurementsProjective.Projectivization
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer
import MIPStarRE.LDT.Preliminaries.CauchySchwarz

/-!
# Section 5 — Orthonormalization

The orthonormalization wrapper theorem and bookkeeping lemmas from Section 5.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

/-! ### Orthonormalization (Theorem 5.4 / thm:orthonormalization) -/

set_option linter.unusedFintypeInType false in
/-- `thm:orthonormalization`.

The explicit normalized-state hypothesis matches the paper's scale-sensitive
`100 · ζ^{1/4}` error bound. -/
theorem orthonormalization {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hψ : ψ.IsNormalized)
    (_hperm : PermInvState ψ)
    (A : SubMeas Outcome ι) (ζ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A) ζ →
      MIPStarRE.LDT.MakingMeasurementsProjective.OrthonormalizationBridgePackage ψ A ζ →
      ∃ P : ProjSubMeas Outcome ι,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily A.liftLeft)
          (constSubMeasFamily P.toSubMeas.liftLeft)
          (orthonormalizationError ζ) := by
  intro hssc hbridge
  exact hbridge.fromSSC hψ hssc



/-- Error bookkeeping for the wrapper around `consistencyToAlmostProjective`
and `roundAlmostProjMeas`. -/
private lemma orthonormalizationMainLemma_error_bound (ζ : Error)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    roundingToProjectiveError (consistencyToAlmostProjectiveError ζ) ≤
      orthonormalizationMainLemmaError ζ := by
  /-
  The wrapper theorem below is structurally just the composition of
  `consistencyToAlmostProjective` and `roundAlmostProjMeas`.
  The remaining bookkeeping is the scalar inequality comparing the composed
  rounding bound with the named `orthonormalizationMainLemmaError`.
  -/
  dsimp [roundingToProjectiveError, consistencyToAlmostProjectiveError,
    orthonormalizationMainLemmaError]
  rw [Real.mul_rpow (by positivity) hζ]
  have hζrpow :
      Real.rpow ζ (1 / (2 : Error)) ≤ Real.rpow ζ (1 / (4 : Error)) := by
    refine Real.rpow_le_rpow_of_exponent_ge' hζ hζ1 ?_ ?_
    · positivity
    · norm_num
  have hsqrt_two_le_seven : Real.rpow (2 : Error) (1 / (2 : Error)) ≤ 7 := by
    have hsqrt_two_le_two : Real.rpow (2 : Error) (1 / (2 : Error)) ≤ 2 := by
      simpa using
        (Real.rpow_le_self_of_one_le
          (h₁ := (by norm_num : (1 : Error) ≤ 2))
          (h₂ := (by norm_num : (1 / (2 : Error)) ≤ 1)))
    exact hsqrt_two_le_two.trans (by norm_num)
  have hquarter_nonneg : 0 ≤ Real.rpow ζ (1 / (4 : Error)) := Real.rpow_nonneg hζ _
  calc
    12 * (Real.rpow (2 : Error) (1 / (2 : Error)) * Real.rpow ζ (1 / (2 : Error)))
      ≤ 12 * (Real.rpow (2 : Error) (1 / (2 : Error)) * Real.rpow ζ (1 / (4 : Error))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact mul_le_mul_of_nonneg_left hζrpow (Real.rpow_nonneg (by norm_num) _)
    _ = (12 * Real.rpow (2 : Error) (1 / (2 : Error))) * Real.rpow ζ (1 / (4 : Error)) := by
      ring
    _ ≤ 84 * Real.rpow ζ (1 / (4 : Error)) := by
      refine mul_le_mul_of_nonneg_right ?_ hquarter_nonneg
      have hcoeff : 12 * Real.rpow (2 : Error) (1 / (2 : Error)) ≤ 12 * 7 := by
        exact mul_le_mul_of_nonneg_left hsqrt_two_le_seven (by norm_num)
      simpa using hcoeff.trans_eq (by norm_num : (12 : Error) * 7 = 84)

private def leftLiftedMeasurement {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (A : Measurement Outcome ιA) :
    Measurement Outcome (ιA × ιB) :=
  { toSubMeas := leftPlacedSubMeas (ιB := ιB) A.toSubMeas
    total_eq_one := by
      calc
        (leftPlacedSubMeas (ιB := ιB) A.toSubMeas).total
            = leftTensor (ι₂ := ιB) A.total :=
              rfl
        _ = leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA) := by
              rw [A.total_eq_one]
        _ = 1 := by
              simp [leftTensor] }

/-- `lem:orthonormalization-main-lemma`.

The bridge inputs isolate the still-unformalized spectral truncation and the
later repair from the raw rounded family to a genuine projective
submeasurement on the lifted space. -/
lemma orthonormalizationMainLemma {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ιA × ιB))
    (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) (ζ : Error)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hspectral :
      MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncationBridgePackage
        ψ (leftLiftedMeasurement (ιB := ιB) A)
        (consistencyToAlmostProjectiveError ζ))
    (hrepair :
      MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationRepairPackage
        ψ (leftLiftedMeasurement (ιB := ιB) A)
        (consistencyToAlmostProjectiveError ζ)) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      let A_lifted : Measurement Outcome (ιA × ιB) := leftLiftedMeasurement (ιB := ιB) A
      ∃ P : ProjSubMeas Outcome (ιA × ιB),
        RoundedProjMeasStatement
          ψ A_lifted P
          (orthonormalizationMainLemmaError ζ) := by
  intro hCons
  change ∃ P : ProjSubMeas Outcome (ιA × ιB),
      RoundedProjMeasStatement
        ψ (leftLiftedMeasurement (ιB := ιB) A) P
        (orthonormalizationMainLemmaError ζ)
  have hAlmost :
      MIPStarRE.LDT.MakingMeasurementsProjective.AlmostProjMeasStatement
        ψ (leftLiftedMeasurement (ιB := ιB) A)
        (consistencyToAlmostProjectiveError ζ) := by
    exact MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjective
        (ψ := ψ) (A := A) (B := B) (ζ := ζ) hCons
  have hRound :
      ∃ P : ProjSubMeas Outcome (ιA × ιB),
        MIPStarRE.LDT.MakingMeasurementsProjective.RoundedProjMeasStatement
          ψ (leftLiftedMeasurement (ιB := ιB) A) P
          (roundingToProjectiveError (consistencyToAlmostProjectiveError ζ)) :=
    MIPStarRE.LDT.MakingMeasurementsProjective.roundAlmostProjMeas (ψ := ψ)
      (hψ := hψ) (A := leftLiftedMeasurement (ιB := ιB) A)
      (ζ := consistencyToAlmostProjectiveError ζ) hAlmost hspectral hrepair
  obtain ⟨P, hRounded⟩ := hRound
  refine ⟨P, ?_⟩
  simpa using
    (MIPStarRE.LDT.MakingMeasurementsProjective.roundedProjMeasStatement_mono hRounded
      (orthonormalizationMainLemma_error_bound ζ hζ hζ1))


end MIPStarRE.LDT.MakingMeasurementsProjective
