import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.Basic.SubMeasurement
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

/-! ### Local helpers for the submeasurement wrapper -/

/-- The zero family is a projective submeasurement. This supplies the trivial
large-`ζ` branch of `orthonormalization`, where the target error bound is already
bigger than the universal `qSDD ≤ 1` estimate. -/
private def zeroProjSubMeas {Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] :
    ProjSubMeas Outcome ι where
  toSubMeas :=
    { outcome := fun _ => 0
      total := 0
      outcome_pos := fun _ => le_rfl
      sum_eq_total := by simp
      total_le_one := zero_le_one }
  proj := fun _ => by simp

/-- Discard the fresh `none` outcome from an option-indexed projective
submeasurement. The remaining `some a` outcomes still form a projective
submeasurement. -/
private noncomputable def restrictSomeProjSubMeas {Outcome : Type*} {ι : Type*}
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

/-- Completing a submeasurement by a fresh failure outcome preserves bipartite
strong self-consistency up to the paper's factor `2`: the original diagonal gap
controls the original outcomes, and the same gap controls the residual `none`
outcome after applying permutation invariance. -/
private lemma optionCompletion_bipartiteSSCRel {Outcome : Type*}
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
    simpa [bipartiteSSCError, avgOver, uniformDistribution, constSubMeasFamily]
      using hssc.overlapBound
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
private lemma qSDD_liftLeft_restrictSomeProjSubMeas_le {Outcome : Type*}
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

/-- The zero projective submeasurement is within unit `qSDD` of any lifted
submeasurement on a normalized state. -/
private lemma qSDD_liftLeft_zeroProjSubMeas_le_one {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized)
    (A : SubMeas Outcome ι) :
    qSDD ψ A.liftLeft
      ((zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.liftLeft) ≤ 1 := by
  have hq :
      qSDD ψ A.liftLeft
          ((zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.liftLeft) =
        ∑ a : Outcome, ev ψ ((A.liftLeft.outcome a) * (A.liftLeft.outcome a)) := by
    unfold qSDD qSDDCore
    refine Finset.sum_congr rfl ?_
    intro a _
    let Z : MIPStarRE.Quantum.Op (ι × ι) := A.liftLeft.outcome a
    have hzero :
        ((zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.liftLeft).outcome a = 0 := by
      ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
        simp [zeroProjSubMeas, SubMeas.liftLeft, leftTensor, h₁, h₂]
    calc
      ev ψ ((Z - ((zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.liftLeft).outcome a)ᴴ *
            (Z - ((zeroProjSubMeas (Outcome := Outcome) (ι := ι)).toSubMeas.liftLeft).outcome a))
        = ev ψ (Zᴴ * Z) := by
            rw [hzero]
            simp
      _ = ev ψ (Z * Z) := by
            rw [SubMeas.outcome_hermitian A.liftLeft a]
      _ = ev ψ ((A.liftLeft.outcome a) * (A.liftLeft.outcome a)) := by
            rfl
  rw [hq]
  simpa using MIPStarRE.LDT.Preliminaries.subMeas_diagMass_le_one ψ hψ A.liftLeft

/-- The quarter-root factor `2^{1/4}` is below the paper-friendly rational bound
`25/21`, which is exactly the slack needed to turn `84·(2ζ)^{1/4}` into
`100·ζ^{1/4}`. -/
private lemma quarterRootTwo_le_twentyFiveTwentyOne :
    Real.rpow (2 : Error) (1 / (4 : Error)) ≤ 25 / 21 := by
  let x : Error := Real.rpow (2 : Error) (1 / (4 : Error))
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact Real.rpow_nonneg (by norm_num) _
  have hx4 : x ^ (4 : ℕ) = 2 := by
    change (Real.rpow (2 : Error) (1 / (4 : Error))) ^ (4 : ℕ) = 2
    calc
      (Real.rpow (2 : Error) (1 / (4 : Error))) ^ (4 : ℕ)
          = (Real.rpow (2 : Error) (1 / (4 : Error))) ^ (4 : Error) := by
              symm
              exact Real.rpow_natCast _ 4
      _ = Real.rpow (2 : Error) ((1 / (4 : Error)) * 4) := by
              simpa using
                (Real.rpow_mul (x := (2 : Error)) (by positivity)
                  (1 / (4 : Error)) 4).symm
      _ = Real.rpow (2 : Error) 1 := by norm_num
      _ = 2 := by norm_num [Real.rpow_natCast]
  by_contra hx_gt
  have hx_lt : (25 / 21 : Error) < x := lt_of_not_ge hx_gt
  have hpow_lt : (25 / 21 : Error) ^ (4 : ℕ) < x ^ (4 : ℕ) := by
    exact pow_lt_pow_left₀ hx_lt (by positivity) (by decide)
  have hq : (2 : Error) < (25 / 21 : Error) ^ (4 : ℕ) := by
    norm_num
  have : (25 / 21 : Error) ^ (4 : ℕ) < 2 := by
    simpa [hx4] using hpow_lt
  linarith

/-- Bookkeeping for the submeasurement version of the orthonormalization theorem:
after completing `A` by a fresh outcome, the local measurement lemma returns the
error `84·(2ζ)^{1/4}`, which is bounded by the paper's `100·ζ^{1/4}`. -/
private lemma orthonormalizationMainLemmaError_two_mul_le_orthonormalizationError
    (ζ : Error) (hζ : 0 ≤ ζ) :
    orthonormalizationMainLemmaError (2 * ζ) ≤ orthonormalizationError ζ := by
  dsimp [orthonormalizationMainLemmaError, orthonormalizationError]
  rw [Real.mul_rpow (by positivity) hζ]
  have hconst :
      84 * Real.rpow (2 : Error) (1 / (4 : Error)) ≤ 100 := by
    calc
      84 * Real.rpow (2 : Error) (1 / (4 : Error))
        ≤ 84 * (25 / 21 : Error) := by
            refine mul_le_mul_of_nonneg_left quarterRootTwo_le_twentyFiveTwentyOne ?_
            norm_num
      _ = 100 := by norm_num
  have hquart_nonneg : 0 ≤ Real.rpow ζ (1 / (4 : Error)) := Real.rpow_nonneg hζ _
  calc
    84 *
        (Real.rpow (2 : Error) (1 / (4 : Error)) *
          Real.rpow ζ (1 / (4 : Error))) =
      (84 * Real.rpow (2 : Error) (1 / (4 : Error))) *
        Real.rpow ζ (1 / (4 : Error)) := by ring
    _ ≤ 100 * Real.rpow ζ (1 / (4 : Error)) := by
          exact mul_le_mul_of_nonneg_right hconst hquart_nonneg

/-- In the large-`ζ` branch `ζ > 1/2`, the target bound `100·ζ^{1/4}` already
exceeds `1`, so the trivial zero projective submeasurement suffices. -/
private lemma orthonormalizationError_ge_one_of_half_lt (ζ : Error)
    (hhalf_lt : (1 / 2 : Error) < ζ) :
    1 ≤ orthonormalizationError ζ := by
  dsimp [orthonormalizationError]
  have hhalf_rpow_le :
      Real.rpow (1 / 2 : Error) (1 / (4 : Error)) ≤
        Real.rpow ζ (1 / (4 : Error)) := by
    exact Real.rpow_le_rpow (by positivity) (le_of_lt hhalf_lt) (by positivity)
  have hhalf_le_root :
      (1 / 2 : Error) ≤ Real.rpow (1 / 2 : Error) (1 / (4 : Error)) := by
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge'
        (show 0 ≤ (1 / 2 : Error) by positivity)
        (show (1 / 2 : Error) ≤ 1 by norm_num)
        (show 0 ≤ (1 / (4 : Error)) by positivity)
        (by norm_num : (1 / (4 : Error)) ≤ 1))
  have hroot_lower : (1 / 2 : Error) ≤ Real.rpow ζ (1 / (4 : Error)) :=
    le_trans hhalf_le_root hhalf_rpow_le
  have h50_le : (50 : Error) ≤ 100 * Real.rpow ζ (1 / (4 : Error)) := by
    nlinarith
  exact (by norm_num : (1 : Error) ≤ 50).trans h50_le

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

/-- The scalar weakening `84·ζ^{1/4} ≤ 100·ζ^{1/4}` from the local
orthonormalization bound to the paper's wrapper error. Factored out as a named
lemma because the same bookkeeping reappears in any top-level wrapper that
derives `orthonormalization` from `orthonormalizationMeasurement` via
submeasurement completion. -/
lemma orthonormalizationMainLemmaError_le_orthonormalizationError
    (ζ : Error) (hζ : 0 ≤ ζ) :
    orthonormalizationMainLemmaError ζ ≤ orthonormalizationError ζ := by
  dsimp [orthonormalizationMainLemmaError, orthonormalizationError]
  exact mul_le_mul_of_nonneg_right
    (by norm_num : (84 : Error) ≤ 100) (Real.rpow_nonneg hζ _)

/-- `lem:orthonormalization-main-lemma`.

The still-unformalized spectral truncation and late repair are exposed here as
explicit theorem hypotheses rather than dedicated bridge-package structures. -/
lemma orthonormalizationMainLemma {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ιA × ιB))
    (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ιA) (B : Measurement Outcome ιB) (ζ : Error)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hspectral : SpectralTruncationInput
      ψ (leftLiftedMeasurement (ιB := ιB) A)
      (consistencyToAlmostProjectiveError ζ))
    (hrepair : ProjectivizationRepairInput
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

/-- Pointwise collapse for a complete measurement `A`: the bipartite
self-consistency defect equals the bipartite consistency defect of `A` with
itself. Both reduce to `max 0 (ev ψ 1 − ∑ a, ev ψ (A_a ⊗ A_a))`, since
`A.total = 1` forces `leftTensor A.total = opTensor A.total A.total`. -/
private lemma qBipartiteSSCDefect_eq_qBipartiteConsDefect_of_measurement
    {Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (A : Measurement Outcome ι) :
    qBipartiteSSCDefect ψ A.toSubMeas =
      qBipartiteConsDefect ψ A.toSubMeas A.toSubMeas := by
  simp [qBipartiteSSCDefect, qBipartiteConsDefect, qBipartiteMatchMass,
    A.total_eq_one, leftTensor, opTensor]

/-- For a complete measurement, bipartite SSC is exactly bipartite
consistency of `A` with itself. -/
private lemma bipartiteSSCRel_self_of_measurement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A : Measurement Outcome ι) (ζ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) ζ →
      ConsRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily A.toSubMeas)
        ζ := by
  intro hssc
  rcases hssc with ⟨hssc⟩
  refine ⟨?_⟩
  have heq :
      bipartiteSSCError ψ (uniformDistribution Unit)
          (constSubMeasFamily A.toSubMeas) =
        bipartiteConsError ψ (uniformDistribution Unit)
          (constSubMeasFamily A.toSubMeas) (constSubMeasFamily A.toSubMeas) := by
    unfold bipartiteSSCError bipartiteConsError
    refine congrArg (avgOver _) ?_
    funext _
    exact qBipartiteSSCDefect_eq_qBipartiteConsDefect_of_measurement ψ A
  exact heq ▸ hssc

/-- A rounded-projective witness for `leftLiftedMeasurement A` coming from a
left-lifted local projective submeasurement immediately yields the local lifted
`≈`-statement. -/
private lemma leftLiftedRoundedProjMeasStatement_to_local {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ι × ι)} {A : Measurement Outcome ι}
    {P : ProjSubMeas Outcome ι} {ζ : Error}
    (h : RoundedProjMeasStatement ψ (leftLiftedMeasurement (ιB := ι) A)
      (ProjSubMeas.liftLeft P) ζ) :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas.liftLeft)
      (constSubMeasFamily P.toSubMeas.liftLeft)
      ζ := by
  simpa [leftLiftedMeasurement, leftPlacedSubMeas, SubMeas.liftLeft,
    ProjSubMeas.liftLeft] using h.closeness

/-- Local version of `orthonormalizationMainLemma` under the explicit
left-lifted repair invariant.

This isolates the exact descent needed for issue #450: once the repair step for
`leftLiftedMeasurement A` is known to return a left-lifted local projective
submeasurement, the paper's local conclusion follows formally. -/
lemma orthonormalizationMainLemma_local {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ι) (ζ : Error)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hspectral : SpectralTruncationInput
      ψ (leftLiftedMeasurement (ιB := ι) A)
      (consistencyToAlmostProjectiveError ζ))
    (hrepair : LeftLiftedProjectivizationRepairInput
      ψ A (consistencyToAlmostProjectiveError ζ)) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) ζ →
      ∃ P : ProjSubMeas Outcome ι,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily A.toSubMeas.liftLeft)
          (constSubMeasFamily P.toSubMeas.liftLeft)
          (orthonormalizationMainLemmaError ζ) := by
  intro hssc
  have hCons :
      ConsRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A.toSubMeas)
        (constSubMeasFamily A.toSubMeas)
        ζ :=
    bipartiteSSCRel_self_of_measurement (ψ := ψ) A ζ hssc
  have hAlmost :
      MIPStarRE.LDT.MakingMeasurementsProjective.AlmostProjMeasStatement
        ψ (leftLiftedMeasurement (ιB := ι) A)
        (consistencyToAlmostProjectiveError ζ) := by
    exact MIPStarRE.LDT.MakingMeasurementsProjective.consistencyToAlmostProjective
      (ψ := ψ) (A := A) (B := A) (ζ := ζ) hCons
  have hSpectral :
      SpectralTruncationStatement ψ (leftLiftedMeasurement (ιB := ι) A)
        (consistencyToAlmostProjectiveError ζ) := by
    exact MIPStarRE.LDT.MakingMeasurementsProjective.spectralTruncateAlmostProjective
      (ψ := ψ) (hψ := hψ) (A := leftLiftedMeasurement (ιB := ι) A)
      (ζ := consistencyToAlmostProjectiveError ζ) hAlmost hspectral
  obtain ⟨P, hRounded⟩ := hrepair hSpectral
  refine ⟨P, ?_⟩
  exact leftLiftedRoundedProjMeasStatement_to_local <|
    MIPStarRE.LDT.MakingMeasurementsProjective.roundedProjMeasStatement_mono
      hRounded (orthonormalizationMainLemma_error_bound ζ hζ hζ1)

/-- Measurement-level orthonormalization once the left-lifted repair witness is
available explicitly. -/
lemma orthonormalizationMeasurement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (hψ : ψ.IsNormalized)
    (A : Measurement Outcome ι) (ζ : Error)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hspectral : SpectralTruncationInput
      ψ (leftLiftedMeasurement (ιB := ι) A)
      (consistencyToAlmostProjectiveError ζ))
    (hrepair : LeftLiftedProjectivizationRepairInput
      ψ A (consistencyToAlmostProjectiveError ζ)) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas) ζ →
      ∃ P : ProjSubMeas Outcome ι,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily A.toSubMeas.liftLeft)
          (constSubMeasFamily P.toSubMeas.liftLeft)
          (orthonormalizationError ζ) := by
  intro hssc
  obtain ⟨P, hP⟩ :=
    orthonormalizationMainLemma_local (ψ := ψ) (hψ := hψ) (A := A) (ζ := ζ)
      hζ hζ1 hspectral hrepair hssc
  refine ⟨P, ?_⟩
  rcases hP with ⟨hP⟩
  exact ⟨hP.trans (orthonormalizationMainLemmaError_le_orthonormalizationError ζ hζ)⟩

set_option linter.unusedFintypeInType false in
/-- `thm:orthonormalization`.

The explicit permutation-invariance and normalized-state hypotheses match the
paper. Once the lifted/local mismatch is discharged by
`orthonormalizationMainLemma_local`, the only remaining external inputs are the
spectral truncation and locality-preserving repair witnesses for the
option-completed measurement `optionCompletion A`. -/
theorem orthonormalization {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized)
    (A : SubMeas Outcome ι) (ζ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit)
        (constSubMeasFamily A) ζ →
      OrthonormalizationInput ψ A ζ →
      ∃ P : ProjSubMeas Outcome ι,
        SDDRel ψ (uniformDistribution Unit)
          (constSubMeasFamily A.liftLeft)
          (constSubMeasFamily P.toSubMeas.liftLeft)
          (orthonormalizationError ζ) := by
  intro hssc hbridge
  rcases hbridge with ⟨hspectral, hrepair⟩
  by_cases hζhalf : ζ ≤ 1 / 2
  · have hζ_nonneg : 0 ≤ ζ :=
      le_trans
        (bipartiteSSCError_nonneg ψ (uniformDistribution Unit)
          (constSubMeasFamily A))
        hssc.overlapBound
    have hTwoζ_nonneg : 0 ≤ 2 * ζ := by
      nlinarith
    have hTwoζ_le_one : 2 * ζ ≤ 1 := by
      nlinarith
    let Ahat : Measurement (Option Outcome) ι := optionCompletion A
    have hspectral' :
        SpectralTruncationInput ψ (leftLiftedMeasurement (ιB := ι) Ahat)
          (consistencyToAlmostProjectiveError (2 * ζ)) := by
      simpa [Ahat] using hspectral
    have hrepair' :
        LeftLiftedProjectivizationRepairInput ψ Ahat
          (consistencyToAlmostProjectiveError (2 * ζ)) := by
      simpa [Ahat] using hrepair
    have hAhatssc :
        BipartiteSSCRel ψ (uniformDistribution Unit)
          (constSubMeasFamily Ahat.toSubMeas)
          (2 * ζ) := by
      simpa [Ahat] using
        optionCompletion_bipartiteSSCRel (ψ := ψ) (hperm := hperm)
          (hψ := hψ) (A := A) (ζ := ζ) hssc
    obtain ⟨P, hP⟩ :=
      orthonormalizationMainLemma_local (Outcome := Option Outcome) (ι := ι)
        (ψ := ψ) (hψ := hψ) (A := Ahat) (ζ := 2 * ζ)
        hTwoζ_nonneg hTwoζ_le_one hspectral' hrepair' hAhatssc
    have hPq :
        qSDD ψ Ahat.toSubMeas.liftLeft P.toSubMeas.liftLeft ≤
          orthonormalizationMainLemmaError (2 * ζ) := by
      simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily] using
        hP.squaredDistanceBound
    let Psome : ProjSubMeas Outcome ι := restrictSomeProjSubMeas P
    have hPsomeq :
        qSDD ψ A.liftLeft Psome.toSubMeas.liftLeft ≤
          orthonormalizationMainLemmaError (2 * ζ) := by
      exact le_trans
        (qSDD_liftLeft_restrictSomeProjSubMeas_le (ψ := ψ) (A := A) (P := P))
        hPq
    refine ⟨Psome, ?_⟩
    constructor
    simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily] using
      (le_trans hPsomeq
        (orthonormalizationMainLemmaError_two_mul_le_orthonormalizationError
          ζ hζ_nonneg))
  · let P : ProjSubMeas Outcome ι := zeroProjSubMeas (Outcome := Outcome) (ι := ι)
    have hq :
        qSDD ψ A.liftLeft P.toSubMeas.liftLeft ≤ 1 := by
      simpa [P] using
        qSDD_liftLeft_zeroProjSubMeas_le_one (ψ := ψ) (hψ := hψ) (A := A)
    have hδ :
        1 ≤ orthonormalizationError ζ :=
      orthonormalizationError_ge_one_of_half_lt ζ (lt_of_not_ge hζhalf)
    refine ⟨P, ?_⟩
    constructor
    simpa [sddError, avgOver, uniformDistribution, constSubMeasFamily] using
      hq.trans hδ

end MIPStarRE.LDT.MakingMeasurementsProjective
