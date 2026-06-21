import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities.LayerAlgebra
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities.RectangularSvd

/-!
# Section 5 — P-Q approximation for QXP layers

The final comparison estimates between the projective family `P` produced
from `XHat` and the original projective `Q` layer.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe uOutcome uι

noncomputable section

private lemma pa_nonneg {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    0 ≤ Pa data a := by
  rcases pProjectivity data with ⟨P, hP⟩
  simpa [hP a] using P.outcome_pos a

private lemma pa_hermitian {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    (Pa data a)ᴴ = Pa data a :=
  (Matrix.nonneg_iff_posSemidef.mp (pa_nonneg data a)).isHermitian.eq

private lemma pa_idempotent {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Pa data a * Pa data a = Pa data a := by
  rcases pProjectivity data with ⟨P, hP⟩
  simpa [hP a] using P.proj a

private lemma pa_mass_le_one {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (ψ : QuantumState ι)
    (hψ : ψ.IsNormalized) :
    (∑ a : Outcome, ev ψ (Pa data a)) ≤ 1 := by
  rcases pProjectivity data with ⟨P, hP⟩
  calc
    (∑ a : Outcome, ev ψ (Pa data a))
        = ∑ a : Outcome, ev ψ (P.outcome a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hP a]
    _ = ev ψ (∑ a : Outcome, P.outcome a) := by
          exact (ev_sum ψ P.outcome).symm
    _ = ev ψ P.total := by rw [P.sum_eq_total]
    _ ≤ ev ψ (1 : MIPStarRE.Quantum.Op ι) := ev_mono ψ _ _ P.total_le_one
    _ = 1 := ev_one_of_isNormalized ψ hψ

private lemma xHat_cross_sum_eq_sqrt {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (∑ a : Outcome, (Xa data a)ᴴ * data.xHat * Pa data a) =
      CFC.sqrt (QTotal data.qLayer) := by
  have hterm : ∀ a : Outcome,
      (Xa data a)ᴴ * data.xHat * Pa data a =
        data.xᴴ * Ta data.qLayer a * data.xHat := by
    intro a
    have hTa : (Ta data.qLayer a)ᴴ = Ta data.qLayer a := by
      simpa [Ta] using ProjMeas.outcome_hermitian data.qLayer.t a
    calc
      (Xa data a)ᴴ * data.xHat * Pa data a
          = (data.xᴴ * Ta data.qLayer a) * data.xHat *
              (data.xHatᴴ * Ta data.qLayer a * data.xHat) := by
              simp [Xa, Pa, Matrix.conjTranspose_mul, hTa, Matrix.mul_assoc]
      _ = data.xᴴ * Ta data.qLayer a * (data.xHat * data.xHatᴴ) *
              Ta data.qLayer a * data.xHat := by
              simp [Matrix.mul_assoc]
      _ = data.xᴴ * Ta data.qLayer a * Ta data.qLayer a * data.xHat := by
              simp [data.xHat_coisometry, Matrix.mul_assoc]
      _ = data.xᴴ * Ta data.qLayer a * data.xHat := by
              simp [Ta, data.qLayer.t.proj a, Matrix.mul_assoc]
  calc
    (∑ a : Outcome, (Xa data a)ᴴ * data.xHat * Pa data a)
        = ∑ a : Outcome, data.xᴴ * Ta data.qLayer a * data.xHat := by
            refine Finset.sum_congr rfl ?_
            intro a _
            exact hterm a
    _ = (∑ a : Outcome, data.xᴴ * Ta data.qLayer a) * data.xHat := by
          simpa using
            (Matrix.sum_mul (s := Finset.univ)
              (f := fun a : Outcome => data.xᴴ * Ta data.qLayer a)
              (M := data.xHat)).symm
    _ = data.xᴴ * (∑ a : Outcome, Ta data.qLayer a) * data.xHat := by
          have hsum : (∑ a : Outcome, data.xᴴ * Ta data.qLayer a) =
              data.xᴴ * (∑ a : Outcome, Ta data.qLayer a) := by
            simpa using
              (Matrix.mul_sum (s := Finset.univ)
                (f := fun a : Outcome => Ta data.qLayer a)
                (M := data.xᴴ)).symm
          rw [hsum]
    _ = data.xᴴ * data.xHat := by
          simpa [Ta] using
            congrArg (fun M => data.xᴴ * M * data.xHat) data.qLayer.t.sum_eq
    _ = CFC.sqrt (QTotal data.qLayer) := data.xHat_mixed

/-- The mixed `X`--`Xhat` summation appearing in the proof of
`lem:P-Q-approx`.

After rewriting `Q_a` and `P_a` through the matrices `X`, `Xhat`, and the
projective measurement `T`, the sum of the mixed terms collapses to
`Xᴴ * Xhat`, hence to `sqrt Q` by `lem:X-times-X-hat`. -/
lemma qxpMixedCrossSum_eq_sqrt {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (∑ a : Outcome, (Xa data a)ᴴ * data.xHat * Pa data a) =
      CFC.sqrt (QTotal data.qLayer) :=
  xHat_cross_sum_eq_sqrt data

private lemma q_p_cross_close {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QXPLayerData Outcome ι)
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error))
    (hRank : RankReductionWitness ψ A ζ data.qLayer) :
    |(∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
        ev ψ (CFC.sqrt (QTotal data.qLayer))| ≤
      2 * zetaQuarterRoot ζ := by
  let D : Matrix data.qLayer.auxSpace.carrier ι ℂ := data.x - data.xHat
  let first : Outcome → Error := fun a =>
    ev ψ ((Xa data a)ᴴ * (D * Dᴴ) * Xa data a)
  let second : Outcome → Error := fun a =>
    ev ψ ((Pa data a)ᴴ * Pa data a)
  have hfirst_nonneg : ∀ a : Outcome, 0 ≤ first a := by
    intro a
    dsimp [first, D]
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using
      ev_adjoint_self_nonneg ψ ((data.x - data.xHat)ᴴ * Xa data a)
  have hsecond_nonneg : ∀ a : Outcome, 0 ≤ second a := by
    intro a
    dsimp [second]
    exact ev_adjoint_self_nonneg ψ (Pa data a)
  have hfirst_le : (∑ a : Outcome, first a) ≤
      4 * spectralTruncationError ζ := by
    have hpoint : ∀ a : Outcome,
        first a ≤ ev ψ (Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
          Qa data.qLayer a) := by
      intro a
      have hrect :
          (Xa data a)ᴴ * (D * Dᴴ) * Xa data a ≤
            (Xa data a)ᴴ *
              ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1)) *
              Xa data a := by
        apply sub_nonneg.mp
        have hpsd :
            0 ≤ (Xa data a)ᴴ *
              (((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1)) - D * Dᴴ) *
              Xa data a := by
          exact
            (Matrix.PosSemidef.conjTranspose_mul_mul_same
              (Matrix.nonneg_iff_posSemidef.mp <|
                sub_nonneg.mpr (by simpa [D] using squaredDifference data))
              (Xa data a)).nonneg
        simpa [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc] using hpsd
      calc
        first a ≤ ev ψ ((Xa data a)ᴴ *
              ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1)) *
              Xa data a) := by
            dsimp [first]
            exact ev_mono ψ _ _ hrect
        _ = ev ψ (Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
              Qa data.qLayer a) := by
            rw [xExpressionToQExpression data a]
    calc
      (∑ a : Outcome, first a)
          ≤ ∑ a : Outcome,
              ev ψ (Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
                Qa data.qLayer a) := by
              exact Finset.sum_le_sum fun a _ => hpoint a
      _ = ev ψ (∑ a : Outcome,
              (Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
                Qa data.qLayer a)) := by
            exact (ev_sum ψ (fun a : Outcome =>
              Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
                Qa data.qLayer a)).symm
      _ ≤ ev ψ ((((4 : Error) * spectralTruncationError ζ) : ℂ) •
              (1 : MIPStarRE.Quantum.Op ι)) := by
            exact ev_mono ψ _ _ (qAlmostProjective ψ A ζ data.qLayer hζ hζ_small hRank)
      _ = 4 * spectralTruncationError ζ := by
            simpa [Complex.ofReal_mul, ev_one_of_isNormalized ψ hψ] using
              ev_scale ψ (4 * spectralTruncationError ζ)
                (1 : MIPStarRE.Quantum.Op ι)
  have hsecond_le : (∑ a : Outcome, second a) ≤ 1 := by
    calc
      (∑ a : Outcome, second a)
          = ∑ a : Outcome, ev ψ (Pa data a) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              simp [second, pa_hermitian data a, pa_idempotent data a]
      _ ≤ 1 := pa_mass_le_one data ψ hψ
  have hhat_ev :
      (∑ a : Outcome, ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a)) =
        ev ψ (CFC.sqrt (QTotal data.qLayer)) := by
    calc
      (∑ a : Outcome, ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a))
          = ev ψ (∑ a : Outcome, (Xa data a)ᴴ * data.xHat * Pa data a) := by
              exact (ev_sum ψ (fun a : Outcome =>
                (Xa data a)ᴴ * data.xHat * Pa data a)).symm
      _ = ev ψ (CFC.sqrt (QTotal data.qLayer)) := by
            rw [xHat_cross_sum_eq_sqrt data]
  have hdiff_sum :
      ((∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
        ∑ a : Outcome, ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a)) =
        ∑ a : Outcome, ev ψ (((Xa data a)ᴴ * D) * Pa data a) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro a _
    calc
      ev ψ (Qa data.qLayer a * Pa data a) -
          ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a)
          = ev ψ (Qa data.qLayer a * Pa data a -
              (Xa data a)ᴴ * data.xHat * Pa data a) := by
              rw [← ev_sub]
      _ = ev ψ (((Xa data a)ᴴ * D) * Pa data a) := by
            congr 1
            rw [(qaRestated data a).2.2]
            dsimp [D]
            rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  have hdiff_abs :
      |(∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
          ∑ a : Outcome, ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a)| ≤
        Real.sqrt (∑ a : Outcome, first a) * Real.sqrt (∑ a : Outcome, second a) := by
    calc
      |(∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
          ∑ a : Outcome, ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a)|
          = |∑ a : Outcome, ev ψ (((Xa data a)ᴴ * D) * Pa data a)| := by
              rw [hdiff_sum]
      _ ≤ ∑ a : Outcome, |ev ψ (((Xa data a)ᴴ * D) * Pa data a)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Outcome, Real.sqrt (first a) * Real.sqrt (second a) := by
            refine Finset.sum_le_sum ?_
            intro a _
            dsimp [first, second]
            simpa [D, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
              ev_abs_mul_le_sqrt ψ ((Xa data a)ᴴ * D) (Pa data a)
      _ ≤ Real.sqrt (∑ a : Outcome, first a) *
            Real.sqrt (∑ a : Outcome, second a) := by
            exact Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
              (f := fun a : Outcome => first a)
              (g := fun a : Outcome => second a)
              (fun a => hfirst_nonneg a) (fun a => hsecond_nonneg a)
  have hsqrt_first : Real.sqrt (∑ a : Outcome, first a) ≤
      Real.sqrt (4 * spectralTruncationError ζ) := by
    exact Real.sqrt_le_sqrt hfirst_le
  have hsqrt_second : Real.sqrt (∑ a : Outcome, second a) ≤ 1 := by
    have h := Real.sqrt_le_sqrt hsecond_le
    simpa using h
  calc
    |(∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
        ev ψ (CFC.sqrt (QTotal data.qLayer))|
        = |(∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
            ∑ a : Outcome, ev ψ ((Xa data a)ᴴ * data.xHat * Pa data a)| := by
            rw [hhat_ev]
    _ ≤ Real.sqrt (∑ a : Outcome, first a) *
          Real.sqrt (∑ a : Outcome, second a) := hdiff_abs
    _ ≤ Real.sqrt (4 * spectralTruncationError ζ) * 1 := by
          exact mul_le_mul hsqrt_first hsqrt_second
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = 2 * zetaQuarterRoot ζ := by
          have hsqrt_rpow :
              Real.sqrt (ζ ^ (1 / (2 : Error))) = zetaQuarterRoot ζ := by
            rw [Real.sqrt_eq_rpow, zetaQuarterRoot, ← Real.rpow_mul hζ]
            congr 1
            ring
          dsimp [spectralTruncationError]
          rw [Real.sqrt_mul (by positivity : 0 ≤ (4 : Error)), hsqrt_rpow]
          ring

/-- **`P` is close to `Q`** (`lem:P-Q-approx`).

The final internal comparison in the paper's repair step is derived from the
primitive `X/XHat/P` identities in `QXPLayerData`, the rank-reduction witness,
and the standard small-error hypotheses.  No closeness bound is stored inside
`QXPLayerData`; the proof below follows the paper's expansion through
`squaredDifference`, `qAlmostProjective`, and `sqrtQCompleteness`. -/
lemma pQApprox {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QXPLayerData Outcome ι)
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error)) :
    RankReductionWitness ψ A ζ data.qLayer →
      SDDOpRel ψ (uniformDistribution Unit)
        (constOpFamily data.qLayer.q)
        (constOpFamily (PFamily data))
        (30 * zetaQuarterRoot ζ) := by
  intro hRank
  let S : Error := ∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)
  have hcross_close : |S - ev ψ (CFC.sqrt (QTotal data.qLayer))| ≤
      2 * zetaQuarterRoot ζ := by
    simpa [S] using q_p_cross_close ψ A ζ data hψ hζ hζ_small hRank
  have hsqrt_complete : ev ψ (CFC.sqrt (QTotal data.qLayer)) ≥
      1 - 12 * zetaQuarterRoot ζ :=
    sqrtQCompleteness ψ A ζ data.qLayer hψ hζ hζ_small hRank
  have hS_lower : S ≥ 1 - 14 * zetaQuarterRoot ζ := by
    have hleft := (abs_le.mp hcross_close).1
    nlinarith
  have hq_mass : ev ψ (QTotal data.qLayer) ≤
      1 + 2 * spectralTruncationError ζ := by
    calc
      ev ψ (QTotal data.qLayer)
          ≤ ev ψ ((((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
              (1 : MIPStarRE.Quantum.Op ι)) := ev_mono ψ _ _ hRank.total_le
      _ = 1 + 2 * spectralTruncationError ζ := by
            simpa [ev_one_of_isNormalized ψ hψ] using
              ev_scale ψ (1 + 2 * spectralTruncationError ζ)
                (1 : MIPStarRE.Quantum.Op ι)
  have hp_mass : (∑ a : Outcome, ev ψ (Pa data a)) ≤ 1 :=
    pa_mass_le_one data ψ hψ
  have hcross_symm :
      (∑ a : Outcome, ev ψ (Pa data a * Qa data.qLayer a)) = S := by
    dsimp [S]
    refine Finset.sum_congr rfl ?_
    intro a _
    exact ev_mul_comm_of_psd ψ (Pa data a) (Qa data.qLayer a)
      (pa_nonneg data a) (hRank.outcome_nonneg a)
  have hq_sum :
      (∑ a : Outcome, ev ψ (Qa data.qLayer a)) = ev ψ (QTotal data.qLayer) := by
    calc
      (∑ a : Outcome, ev ψ (Qa data.qLayer a))
          = ev ψ (∑ a : Outcome, Qa data.qLayer a) := by
              exact (ev_sum ψ (Qa data.qLayer)).symm
      _ = ev ψ (QTotal data.qLayer) := by rw [hRank.sum_eq_total]
  have hqsddeq :
      qSDDOp ψ data.qLayer.q (PFamily data) =
        ev ψ (QTotal data.qLayer) + (∑ a : Outcome, ev ψ (Pa data a)) -
          S - S := by
    unfold qSDDOp qSDDCore
    calc
      (∑ a : Outcome,
          ev ψ (((data.qLayer.q.outcome a - (PFamily data).outcome a)ᴴ) *
            (data.qLayer.q.outcome a - (PFamily data).outcome a)))
          = ∑ a : Outcome,
              (ev ψ (Qa data.qLayer a) + ev ψ (Pa data a) -
                ev ψ (Qa data.qLayer a * Pa data a) -
                ev ψ (Pa data a * Qa data.qLayer a)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              have hQaH : (Qa data.qLayer a)ᴴ = Qa data.qLayer a :=
                (hRank.projective a).isHermitian.eq
              have hPaH : (Pa data a)ᴴ = Pa data a := pa_hermitian data a
              have hQaSq : Qa data.qLayer a * Qa data.qLayer a = Qa data.qLayer a :=
                (hRank.projective a).idempotent
              have hPaSq : Pa data a * Pa data a = Pa data a := pa_idempotent data a
              calc
                ev ψ (((data.qLayer.q.outcome a - (PFamily data).outcome a)ᴴ) *
                    (data.qLayer.q.outcome a - (PFamily data).outcome a))
                    = ev ψ (((Qa data.qLayer a - Pa data a)ᴴ) *
                        (Qa data.qLayer a - Pa data a)) := by
                        rfl
                _ = ev ψ ((Qa data.qLayer a + Pa data a) -
                        Qa data.qLayer a * Pa data a -
                        Pa data a * Qa data.qLayer a) := by
                        congr 1
                        rw [Matrix.conjTranspose_sub, hQaH, hPaH]
                        calc
                          (Qa data.qLayer a - Pa data a) *
                              (Qa data.qLayer a - Pa data a)
                              = Qa data.qLayer a * Qa data.qLayer a -
                                  Qa data.qLayer a * Pa data a -
                                  Pa data a * Qa data.qLayer a +
                                  Pa data a * Pa data a := by
                                  noncomm_ring
                          _ = (Qa data.qLayer a + Pa data a) -
                                  Qa data.qLayer a * Pa data a -
                                  Pa data a * Qa data.qLayer a := by
                                  rw [hQaSq, hPaSq]
                                  noncomm_ring
                _ = ev ψ (Qa data.qLayer a) + ev ψ (Pa data a) -
                    ev ψ (Qa data.qLayer a * Pa data a) -
                    ev ψ (Pa data a * Qa data.qLayer a) := by
                    rw [ev_sub, ev_sub, ev_add]
      _ = (∑ a : Outcome, ev ψ (Qa data.qLayer a)) +
            (∑ a : Outcome, ev ψ (Pa data a)) -
            (∑ a : Outcome, ev ψ (Qa data.qLayer a * Pa data a)) -
            (∑ a : Outcome, ev ψ (Pa data a * Qa data.qLayer a)) := by
            simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = ev ψ (QTotal data.qLayer) + (∑ a : Outcome, ev ψ (Pa data a)) -
            S - S := by
            rw [hq_sum, hcross_symm]
  have hqSDD_bound : qSDDOp ψ data.qLayer.q (PFamily data) ≤
      30 * zetaQuarterRoot ζ := by
    calc
      qSDDOp ψ data.qLayer.q (PFamily data)
          = ev ψ (QTotal data.qLayer) + (∑ a : Outcome, ev ψ (Pa data a)) -
              S - S := hqsddeq
      _ ≤ (1 + 2 * spectralTruncationError ζ) + 1 -
              (1 - 14 * zetaQuarterRoot ζ) -
              (1 - 14 * zetaQuarterRoot ζ) := by
            nlinarith
      _ = 2 * spectralTruncationError ζ + 28 * zetaQuarterRoot ζ := by ring
      _ ≤ 30 * zetaQuarterRoot ζ := by
            have hε_le := spectralTruncationError_le_zetaQuarterRoot ζ hζ hζ_small
            nlinarith
  constructor
  simpa [sddErrorOp, avgOver, uniformDistribution, constOpFamily] using hqSDD_bound

/-- Apply `lem:P-Q-approx` to the canonical sigma-space QXP layer obtained
from a rank-reduction witness.

The theorem keeps the SVD/polar data for `Xhat` explicit, but removes the
remaining bookkeeping needed to use `pQApprox`: the rank-reduction witness is
transported to the sigma-space layer, and the resulting `QXPLayerData` is the
canonical one built from `sigmaFinRangeEmbedding`. -/
lemma pQApprox_ofRankReductionSigmaRangeAndSvdIdentities
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))]
    (xHat : Matrix (ULift (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))) ι ℂ)
    (xHat_coisometry : xHat * xHatᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))))
    (xHat_mixed :
      (sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective)ᴴ * xHat =
        CFC.sqrt (QTotal qLayer))
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error)) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = sigmaRangeQLayer qLayer.q,
        hq ▸ data.x =
          (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
            sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective) ∧
        hq ▸ data.xHat =
          (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from xHat) ∧
        SDDOpRel ψ (uniformDistribution Unit)
          (constOpFamily data.qLayer.q)
          (constOpFamily (PFamily data))
          (30 * zetaQuarterRoot ζ) := by
  classical
  let data : QXPLayerData Outcome ι :=
    QXPLayerData.ofSigmaRangeAndSvdIdentities (q := qLayer.q)
      hRank.projective hRank.sum_eq_total xHat xHat_coisometry xHat_mixed
  refine ⟨data, rfl, rfl, rfl, ?_⟩
  exact pQApprox ψ A ζ data hψ hζ hζ_small hRank.toSigmaRangeQLayer

/-- Apply `lem:P-Q-approx` to the positive-Gram sigma-space QXP layer.

This is the constructor-facing form of the local `Q -> X -> Xhat -> P` stage.
The rank-reduction witness supplies the sigma-space `X`; the positive-Gram
polar construction supplies `Xhat`; and the theorem concludes the paper's
`P`-versus-`Q` approximation without any external SVD data. -/
lemma pQApprox_ofRankReductionSigmaRangePositiveGram
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))]
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error)) :
    ∃ xHat : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))) ι ℂ,
      xHat * xHatᴴ =
          (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
            (fun a : Outcome => (qLayer.q.outcome a).rank)))) ∧
        (sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective)ᴴ * xHat =
            CFC.sqrt (QTotal qLayer) ∧
          ∃ data : QXPLayerData Outcome ι,
            ∃ hq : data.qLayer = sigmaRangeQLayer qLayer.q,
              hq ▸ data.x =
                  (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
                    sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective) ∧
                hq ▸ data.xHat =
                    (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
                      xHat) ∧
                  SDDOpRel ψ (uniformDistribution Unit)
                    (constOpFamily data.qLayer.q)
                    (constOpFamily (PFamily data))
                    (30 * zetaQuarterRoot ζ) := by
  obtain ⟨xHat, hxHat_coisometry, hxHat_mixed, data, hq, hx, hxHat⟩ :=
    exists_qxpLayerData_ofRankReductionSigmaRangePositiveGram hRank
  refine ⟨xHat, hxHat_coisometry, hxHat_mixed, data, hq, hx, hxHat, ?_⟩
  exact pQApprox ψ A ζ data hψ hζ hζ_small
    (hq.symm ▸ hRank.toSigmaRangeQLayer)

/-- Apply `lem:P-Q-approx` to the positive-Gram sigma-space QXP layer, and
also record coisometry of the original sigma embedding `X`.

The additional hypothesis is the subnormalization of the projective `Q` family.
Under this hypothesis the range basis vectors chosen for distinct outcomes are
orthogonal, so the finite sigma-range embedding has orthonormal rows.  This is
the construction-level coisometry condition later used to preserve the fresh
option-completion row and hence to obtain the QXP-internal comparison
`Q_none ≤ P_none`.  An additional source-to-`Q` comparison is still required to
recover `(optionCompletion A).outcome none ≤ P.outcome none`; see
`docs/reports/issue-1642-restrictsome-residual-domination-obstruction.md`.
-/
lemma pQApprox_ofRankReductionSigmaRangePositiveGram_with_x_coisometry
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    (hsum_le_one :
      (∑ a : Outcome, qLayer.q.outcome a) ≤ (1 : MIPStarRE.Quantum.Op ι))
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))]
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error)) :
    ∃ xHat : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))) ι ℂ,
      xHat * xHatᴴ =
          (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
            (fun a : Outcome => (qLayer.q.outcome a).rank)))) ∧
        (sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective)ᴴ * xHat =
            CFC.sqrt (QTotal qLayer) ∧
          ∃ data : QXPLayerData Outcome ι,
            ∃ hq : data.qLayer = sigmaRangeQLayer qLayer.q,
              hq ▸ data.x =
                  (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
                    sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective) ∧
                hq ▸ data.xHat =
                    (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
                      xHat) ∧
                  data.x * data.xᴴ =
                    (1 : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier) ∧
                    SDDOpRel ψ (uniformDistribution Unit)
                      (constOpFamily data.qLayer.q)
                      (constOpFamily (PFamily data))
                      (30 * zetaQuarterRoot ζ) := by
  obtain ⟨xHat, hxHat_coisometry, hxHat_mixed, data, hq, hx, hxHat, hx_coisometry⟩ :=
    exists_qxpLayerData_ofRankReductionSigmaRangePositiveGram_with_x_coisometry
      hRank hsum_le_one
  refine ⟨xHat, hxHat_coisometry, hxHat_mixed, data, hq, hx, hxHat,
    hx_coisometry, ?_⟩
  exact pQApprox ψ A ζ data hψ hζ hζ_small
    (hq.symm ▸ hRank.toSigmaRangeQLayer)

/-- Apply `lem:P-Q-approx` to unitary-group rectangular SVD data and the
positive-square characterization of the middle factor.

The square SVD factors are represented as elements of `Matrix.unitaryGroup`;
hence the unitarity laws are not separate hypotheses. -/
lemma pQApprox_ofRankReductionSigmaRangeAndRectangularSvdSquareRootUnitaryGroupWithCarrier
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))]
    (U : Matrix.unitaryGroup (sigmaRangeQLayer qLayer.q).auxSpace.carrier ℂ)
    (V : Matrix.unitaryGroup ι ℂ)
    (S Iro : Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ)
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op (sigmaRangeQLayer qLayer.q).auxSpace.carrier))
    (hx : sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective =
      (U : Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier
        (sigmaRangeQLayer qLayer.q).auxSpace.carrier ℂ) *
      S * (V : Matrix ι ι ℂ)ᴴ)
    (hMiddle_nonneg :
      0 ≤ (V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ)
    (hMiddle_sq :
      ((V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ) *
        ((V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ) =
          QTotal qLayer)
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error)) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = sigmaRangeQLayer qLayer.q,
        hq ▸ data.x =
          (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
            sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective) ∧
        hq ▸ data.xHat =
          (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
            (U : Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier
              (sigmaRangeQLayer qLayer.q).auxSpace.carrier ℂ) *
            Iro * (V : Matrix ι ι ℂ)ᴴ) ∧
        SDDOpRel ψ (uniformDistribution Unit)
          (constOpFamily data.qLayer.q)
          (constOpFamily (PFamily data))
          (30 * zetaQuarterRoot ζ) := by
  obtain ⟨data, hq, hdata_x, hdata_xHat⟩ :=
    exists_qxpLayerData_ofRankReductionSigmaRangeAndRectangularSvdSqrtWithCarrier
      hRank U V S Iro hIro hx hMiddle_nonneg hMiddle_sq
  refine ⟨data, hq, hdata_x, hdata_xHat, ?_⟩
  exact pQApprox ψ A ζ data hψ hζ hζ_small
    (hq.symm ▸ hRank.toSigmaRangeQLayer)

/-- Apply `lem:P-Q-approx` to unitary-group rectangular SVD data and the
positive-square characterization of the middle factor.

The square SVD factors are represented as elements of `Matrix.unitaryGroup`;
hence the unitarity laws are not separate hypotheses. -/
lemma pQApprox_ofRankReductionSigmaRangeAndRectangularSvdSquareRootUnitaryGroup
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))]
    (U : Matrix.unitaryGroup (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))) ℂ)
    (V : Matrix.unitaryGroup ι ℂ)
    (S Iro : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))) ι ℂ)
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))))
    (hx : sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective =
      (U : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))
        (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
          (fun a : Outcome => (qLayer.q.outcome a).rank))) ℂ) *
      S * (V : Matrix ι ι ℂ)ᴴ)
    (hMiddle_nonneg :
      0 ≤ (V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ)
    (hMiddle_sq :
      ((V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ) *
        ((V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ) =
          QTotal qLayer)
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_small : ζ ≤ 1 / (4 : Error)) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = sigmaRangeQLayer qLayer.q,
        hq ▸ data.x =
          (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
            sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective) ∧
        hq ▸ data.xHat =
          (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
            (U : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
              (fun a : Outcome => (qLayer.q.outcome a).rank)))
              (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
                (fun a : Outcome => (qLayer.q.outcome a).rank))) ℂ) *
            Iro * (V : Matrix ι ι ℂ)ᴴ) ∧
        SDDOpRel ψ (uniformDistribution Unit)
          (constOpFamily data.qLayer.q)
          (constOpFamily (PFamily data))
          (30 * zetaQuarterRoot ζ) :=
  pQApprox_ofRankReductionSigmaRangeAndRectangularSvdSquareRootUnitaryGroupWithCarrier
    ψ A ζ hRank U V S Iro hIro hx hMiddle_nonneg hMiddle_sq hψ hζ hζ_small

end

end MIPStarRE.LDT.MakingMeasurementsProjective
