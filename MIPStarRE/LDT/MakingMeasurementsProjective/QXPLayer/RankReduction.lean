import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.Core

/-!
# Section 5 — Q/X/XHat/P rank reduction

Almost-projectivity, scalar truncation, and rank-reduction lemmas for the
paper's `Q/X/XHat/P` intermediate layer.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

universe uOutcome uι

/-- **Almost-projective estimate** (`eq:A-looks-projective`).

This is the opening inequality in the proof of
`lem:orthonormalization-main-lemma`, extracted as an explicit Lean lemma
so the later `Q/X/XHat/P` layer can depend on it directly.

`B` is a `ProjMeas` (not `Measurement`) because the proof relies on
`Bₐ² = Bₐ` (projectivity) to collapse `diagB` to `totalMass`.
In the paper's orthonormalization pipeline, `B` is always the
projective reference measurement obtained from Naimark dilation
(Theorem 5.1), so this is the natural type. -/
lemma aLooksProjective {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : ProjMeas Outcome ιB) (ζ : Error) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      ∑ a, ev ψ
        ((leftPlacedSubMeas (ιB := ιB) A.toSubMeas).outcome a -
          (leftPlacedSubMeas (ιB := ιB) A.toSubMeas).outcome a *
            (leftPlacedSubMeas (ιB := ιB) A.toSubMeas).outcome a) ≤ 2 * ζ := by
  intro hCons
  classical
  let ALeft : SubMeas Outcome (ιA × ιB) := leftPlacedSubMeas (ιB := ιB) A.toSubMeas
  let BRight : SubMeas Outcome (ιA × ιB) := rightPlacedSubMeas (ιA := ιA) B.toSubMeas
  let totalMass : Error := ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB))
  let diagA : Error := ∑ a : Outcome, ev ψ (ALeft.outcome a * ALeft.outcome a)
  let diagB : Error := ∑ a : Outcome, ev ψ (BRight.outcome a * BRight.outcome a)
  let overlap : Error := ∑ a : Outcome, ev ψ (ALeft.outcome a * BRight.outcome a)
  have hCons' :
      qConsDefect ψ ALeft BRight ≤ ζ := by
    have hConsPlaced := hCons.offDiagonalBound
    rw [bipartiteConsError_eq_consError_placed] at hConsPlaced
    have hConsConst :
        consError ψ (uniformDistribution Unit)
          (constSubMeasFamily ALeft) (constSubMeasFamily BRight) ≤ ζ := by
      simpa [constSubMeasFamily, ALeft, BRight] using hConsPlaced
    simpa [MIPStarRE.LDT.Preliminaries.constFamily_cons_unit] using hConsConst
  have hgap : totalMass - overlap ≤ ζ := by
    have hmax :
        max 0 (totalMass - overlap) ≤ ζ := by
      simpa [qConsDefect, qMatchMass, totalMass, overlap, ALeft, BRight,
        leftPlacedSubMeas, rightPlacedSubMeas, leftTensor, rightTensor,
        A.total_eq_one, B.total_eq_one] using hCons'
    exact le_trans (le_max_right 0 (totalMass - overlap)) hmax
  have hdiagB :
      diagB = totalMass := by
    calc
      diagB = ∑ a : Outcome, ev ψ (BRight.outcome a) := by
        unfold diagB
        refine Finset.sum_congr rfl ?_
        intro a _
        simp [BRight, rightPlacedSubMeas, rightTensor_mul_rightTensor, B.proj a]
      _ = totalMass := by
        rw [← ev_sum ψ BRight.outcome, BRight.sum_eq_total]
        simp [BRight, rightPlacedSubMeas, rightTensor, totalMass, B.total_eq_one]
  have hdiagA_nonneg : 0 ≤ diagA := by
    unfold diagA
    exact Finset.sum_nonneg fun a _ => by
      simpa [SubMeas.outcome_hermitian] using ev_adjoint_self_nonneg ψ (ALeft.outcome a)
  have hmass_nonneg : 0 ≤ totalMass := by
    simpa [totalMass] using ev_adjoint_self_nonneg ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB))
  have hoverlap_abs :
      |overlap| ≤ Real.sqrt diagA * Real.sqrt totalMass := by
    calc
      |overlap|
        = |∑ a : Outcome, ev ψ (ALeft.outcome a * BRight.outcome a)| := by
            simp [overlap]
      _ ≤ ∑ a : Outcome,
            |ev ψ (ALeft.outcome a * BRight.outcome a)| := by
              exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Outcome,
            Real.sqrt (ev ψ (ALeft.outcome a * ALeft.outcome a)) *
              Real.sqrt (ev ψ (BRight.outcome a * BRight.outcome a)) := by
              refine Finset.sum_le_sum ?_
              intro a _
              simpa [SubMeas.outcome_hermitian] using
                ev_abs_mul_le_sqrt ψ (ALeft.outcome a) (BRight.outcome a)
      _ ≤ Real.sqrt diagA * Real.sqrt diagB := by
            simpa [diagA, diagB] using
              Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
                (f := fun a => ev ψ (ALeft.outcome a * ALeft.outcome a))
                (g := fun a => ev ψ (BRight.outcome a * BRight.outcome a))
                (fun a => by
                  simpa [SubMeas.outcome_hermitian] using
                    ev_adjoint_self_nonneg ψ (ALeft.outcome a))
                (fun a => by
                  simpa [SubMeas.outcome_hermitian] using
                    ev_adjoint_self_nonneg ψ (BRight.outcome a))
      _ = Real.sqrt diagA * Real.sqrt totalMass := by rw [hdiagB]
  have hoverlap_le : overlap ≤ Real.sqrt diagA * Real.sqrt totalMass := by
    exact (abs_le.mp hoverlap_abs).2
  have htwosqrt :
      2 * (Real.sqrt diagA * Real.sqrt totalMass) ≤ diagA + totalMass := by
    nlinarith [sq_nonneg (Real.sqrt diagA - Real.sqrt totalMass),
      Real.sq_sqrt hdiagA_nonneg, Real.sq_sqrt hmass_nonneg]
  have hcore : totalMass - diagA ≤ 2 * (totalMass - overlap) := by
    have haux : 2 * overlap ≤ diagA + totalMass := by
      calc
        2 * overlap ≤ 2 * (Real.sqrt diagA * Real.sqrt totalMass) := by
          gcongr
        _ ≤ diagA + totalMass := htwosqrt
    nlinarith
  calc
    ∑ a, ev ψ (ALeft.outcome a - ALeft.outcome a * ALeft.outcome a)
      = totalMass - diagA := by
          unfold totalMass diagA
          calc
            ∑ a, ev ψ (ALeft.outcome a - ALeft.outcome a * ALeft.outcome a)
              = ∑ a, (ev ψ (ALeft.outcome a) - ev ψ (ALeft.outcome a * ALeft.outcome a)) := by
                  refine Finset.sum_congr rfl ?_
                  intro a _
                  exact ev_sub ψ (ALeft.outcome a) (ALeft.outcome a * ALeft.outcome a)
            _ = (∑ a, ev ψ (ALeft.outcome a)) - ∑ a, ev ψ (ALeft.outcome a * ALeft.outcome a) := by
                  rw [Finset.sum_sub_distrib]
            _ = totalMass - ∑ a, ev ψ (ALeft.outcome a * ALeft.outcome a) := by
                  rw [← ev_sum ψ ALeft.outcome, ALeft.sum_eq_total]
                  simp [ALeft, leftPlacedSubMeas, leftTensor, totalMass, A.total_eq_one]
            _ = totalMass - diagA := by simp [diagA]
    _ ≤ 2 * (totalMass - overlap) := hcore
    _ ≤ 2 * ζ := by gcongr

/-- **Scalar truncation inequality** (`lem:trunc-inequality`).

For `x ∈ [0,1]`, truncating at threshold `1 - δ` changes `x` by at most
`(1 / δ) * (x - x^2)` in squared distance. -/
lemma truncationInequality (δ x : Error) :
    0 < δ →
      δ ≤ 1 / 2 →
      0 ≤ x →
      x ≤ 1 →
      let trunc : Error := if 1 - δ ≤ x then 1 else 0
      (x - trunc) ^ (2 : Nat) ≤ (1 / δ) * (x - x ^ (2 : Nat)) := by
  intro hδ hδhalf hx hx1
  simp only []
  split
  · next h =>
    have h1x : 0 ≤ 1 - x := by linarith
    have hxd : 1 - x ≤ δ := by linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    nlinarith [sq_nonneg (1 - x), sq_nonneg δ]
  · next h =>
    push_neg at h
    simp only [sub_zero]
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    have hlt : 0 ≤ 1 - δ - x := by linarith
    nlinarith [mul_nonneg hx hlt,
      mul_nonneg (mul_nonneg (le_of_lt hδ) hx)
        (by linarith : (0 : ℝ) ≤ 1 - x)]

/-- The spectral truncation error is nonnegative on nonnegative input. -/
lemma spectralTruncationError_nonneg {ζ : Error} (hζ : 0 ≤ ζ) :
    0 ≤ spectralTruncationError ζ := by
  dsimp [spectralTruncationError]
  exact Real.rpow_nonneg hζ _

/-- **Rounding to projectors** (`lem:projective-non-measurement`).

From the estimate `eq:A-looks-projective`, construct a family `R_a` of
projectors close to `A_a` whose total is bounded by `(1 + 2√ζ)I`. -/
lemma projectiveNonMeasurement {Outcome : Type uOutcome}
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (hbridge : ProjectiveNonMeasurementBridgePackage ψ A ζ) :
    (∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) →
      ∃ R : OpFamily Outcome ι,
        RoundingToProjectorsWitness ψ A ζ R := by
  intro hsource
  rcases hbridge.fromSourceAlmostProjective hsource with ⟨R, hR, _⟩
  exact ⟨R, hR⟩

/-- **Degenerate empty-outcome branch** for `lem:projective-low-rank-sum`.

In `references/ldt-paper/orthonormalization.tex`, lines 540--658, the rank-
reduction argument starts from an honest measurement `A = {A_a}` on a nontrivial
ambient space. If `Outcome` were empty, then `∑ a, A_a = 0` while
`A.total_eq_one` forces the same sum to be `1`, so this branch is impossible.
We isolate that contradiction here so `projectiveLowRankSum` can focus on the
spectral construction in the nonempty case. -/
private lemma rankReduction_emptyOutcome
    {Outcome : Type uOutcome} {ι : Type uι}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype Outcome] [DecidableEq Outcome] [IsEmpty Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data := by
  exfalso
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have htotal_zero : A.toSubMeas.total = 0 := by
    simpa using A.toSubMeas.sum_eq_total.symm
  have hzero_one : (0 : MIPStarRE.Quantum.Op ι) = 1 := by
    rw [← htotal_zero, A.total_eq_one]
  have hentry : (0 : ℂ) = 1 := by
    simpa using congrFun (congrFun hzero_one i) i
  norm_num at hentry

/-- **Rank reduction** (`lem:projective-low-rank-sum`).

Construct the paper's rank-reduced family `Q_a`, together with the auxiliary
projective measurement `T_a`, so that `Q_a` remains close to `A_a`, its total
stays bounded by `(1 + 2√ζ)I`, and the auxiliary dimension is at most the
original ambient dimension.

The auxiliary-space-and-`T` data is supplied via
`RankReductionBridgePackage`, parametric on the specific rounded family
`(q, hq)`; this keeps the paper's spectral derivation of `(auxSpace, T_a)`
from the rounded family `R_a` localized to one bridge rather than silently
filled in with a vacuous `default` witness. -/
lemma projectiveLowRankSum {Outcome : Type uOutcome}
    {ι : Type uι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (hζ : 0 ≤ ζ)
    (hbridge : ProjectiveNonMeasurementBridgePackage ψ A ζ)
    (hrankBridge : ∀ (q : OpFamily Outcome ι)
        (hq : RoundingToProjectorsWitness ψ A ζ q),
      RankReductionBridgePackage ψ A ζ q hq)
    (source_almost_projective :
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data := by
  classical
  by_cases hOutcome : Nonempty Outcome
  · obtain ⟨q, hrounded, hsum⟩ := hbridge.fromSourceAlmostProjective source_almost_projective
    let aux : RankReductionAuxOutput Outcome ι := (hrankBridge q hrounded).out
    let data : QLayerData Outcome ι :=
      { auxSpace := aux.auxSpace
        q := q
        t := aux.t }
    refine ⟨data, ?_⟩
    refine ⟨?_, ?_, ?_, source_almost_projective, ?_, ?_, ?_⟩
    · intro a
      exact hrounded.projective a
    · intro a
      have hproj := hrounded.projective a
      simpa [hproj.isHermitian.eq, hproj.idempotent] using
        (Matrix.posSemidef_conjTranspose_mul_self (q.outcome a)).nonneg
    · simpa [Qa, QTotal, data] using hsum
    · exact MIPStarRE.LDT.Preliminaries.sddOpRel_mono ψ (uniformDistribution Unit)
        (constOpFamily (A.toSubMeas : OpFamily Outcome ι)) (constOpFamily q)
        (2 * spectralTruncationError ζ) (roundingToProjectiveError ζ)
        hrounded.closeness
        (by
          have hε_nonneg : 0 ≤ spectralTruncationError ζ := spectralTruncationError_nonneg hζ
          dsimp [roundingToProjectiveError]
          exact mul_le_mul_of_nonneg_right (by norm_num : (2 : Error) ≤ 12) hε_nonneg)
    · calc
        QTotal data = q.total := rfl
        _ ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
            (1 : MIPStarRE.Quantum.Op ι) := hrounded.total_le
    · exact aux.auxDim_le
  · letI : IsEmpty Outcome := not_nonempty_iff.mp hOutcome
    exact rankReduction_emptyOutcome (ψ := ψ) (A := A) (ζ := ζ)


end

end MIPStarRE.LDT.MakingMeasurementsProjective
