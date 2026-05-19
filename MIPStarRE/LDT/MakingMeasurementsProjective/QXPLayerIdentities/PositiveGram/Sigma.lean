import Mathlib.Analysis.InnerProductSpace.GramMatrix
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities.PositiveGram.Completion

/-!
# Section 5 — Positive-Gram sigma-space specialization

Application of the positive-Gram polar construction to the canonical
sigma-space layer obtained from a rank-reduction witness.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe uOutcome uι

noncomputable section

/-- Explicit positive-Gram polar extension from chosen row-extension data.

The existential construction of `Xhat` first chooses an embedding of the
positive spectral subspace into the auxiliary row space, then chooses a unitary
`U` extending the normalized image rows and a rectangular coisometry `W`
extending the right singular rows.  This theorem records the deterministic
matrix produced from those choices, namely `Uᵀ * W`, together with the two QXP
identities it satisfies.

The explicit form is useful when a later argument needs to impose additional
structure on the chosen rows, such as fresh option-completion row preservation
used to derive the QXP-internal comparison `Q_none ≤ P_none`. -/
theorem xHat_of_positive_gram_spectrum_choices
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian) (hQ_pos : Q.PosSemidef)
    (hgram : Xᴴ * X = Q)
    (e : {i : ι // 0 < hQ.eigenvalues i} ↪ μ)
    (U : Matrix μ μ ℂ) (W : Matrix μ ι ℂ)
    (hU_left : U * Uᴴ = (1 : Matrix μ μ ℂ))
    (hU_right : Uᴴ * U = (1 : Matrix μ μ ℂ))
    (hU_rows :
      ∀ (i : {i : ι // 0 < hQ.eigenvalues i}) (r : μ),
        U (e i) r = positiveGramSpectrumImageRows X Q hQ i r)
    (hW : W * Wᴴ = (1 : Matrix μ μ ℂ))
    (hW_rows :
      ∀ (i : {i : ι // 0 < hQ.eigenvalues i}) (r : ι),
        W (e i) r = positiveGramSpectrumRightRows Q hQ i r) :
    (Uᵀ * W) * (Uᵀ * W)ᴴ = (1 : Matrix μ μ ℂ) ∧
      Xᴴ * (Uᵀ * W) = CFC.sqrt Q := by
  constructor
  · exact transpose_unitary_mul_rectangular_coisometry U W hU_right hW
  · exact positive_gram_polar_extension_mixed_eq_sqrt X Q hQ hQ_pos hgram e
      U W hU_left hU_rows hW_rows

/-- Existence of the polar-extension `Xhat` from a positive Gram factorization.

If `Q = X†X` is positive semidefinite and the row dimension is at most the
column dimension, the positive spectral rows of `Q` determine a rectangular
coisometry `Xhat` satisfying the two primitive QXP identities:
`Xhat Xhat† = I` and `X† Xhat = sqrt Q`. -/
theorem exists_xHat_of_positive_gram_spectrum
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι]
    [NonUnitalContinuousFunctionalCalculus ℝ (Matrix ι ι ℂ) IsSelfAdjoint]
    (X : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hQ : Q.IsHermitian) (hQ_pos : Q.PosSemidef)
    (hgram : Xᴴ * X = Q)
    (hcard : Fintype.card μ ≤ Fintype.card ι) :
    ∃ xHat : Matrix μ ι ℂ,
      xHat * xHatᴴ = (1 : Matrix μ μ ℂ) ∧
        Xᴴ * xHat = CFC.sqrt Q := by
  classical
  obtain ⟨e, U, hU_left, hU_right, hU_rows⟩ :=
    exists_unitary_with_positive_gram_spectrum_rows_of_card X Q hQ hgram
  obtain ⟨W, hW, hW_rows⟩ :=
    exists_rectangular_coisometry_with_positive_gram_spectrum_right_rows Q hQ e hcard
  have hchoices := xHat_of_positive_gram_spectrum_choices X Q hQ hQ_pos hgram e
    U W hU_left hU_right hU_rows hW hW_rows
  refine ⟨Uᵀ * W, ?_, ?_⟩
  · exact hchoices.1
  · exact hchoices.2

/-- Sigma-range specialization of the positive-Gram `Xhat` construction.

For a rank-reduction witness, the canonical sigma-space embedding satisfies
`X†X = Q`.  The stored total-rank bound supplies the rectangular dimension
hypothesis, so the positive-Gram construction produces the `Xhat` required by
the QXP data package. -/
theorem exists_xHat_of_sigmaFinRangeEmbedding_positiveGram
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))] :
    ∃ xHat : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))) ι ℂ,
      xHat * xHatᴴ =
        (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
          (fun a : Outcome => (qLayer.q.outcome a).rank)))) ∧
        (sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective)ᴴ * xHat =
          CFC.sqrt (QTotal qLayer) := by
  classical
  let X : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))) ι ℂ :=
    sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective
  have hgram : Xᴴ * X = QTotal qLayer := by
    simpa [X, QTotal] using
      sigmaFinRangeEmbedding_gram_right qLayer.q hRank.projective hRank.sum_eq_total
  have hQ_pos : (QTotal qLayer).PosSemidef := by
    have hX_gram :
        Matrix.gram ℂ (fun j : ι => WithLp.toLp 2 fun r => X r j) = Xᴴ * X := by
      ext i j
      simp [Matrix.gram, Matrix.mul_apply, Matrix.conjTranspose_apply,
        EuclideanSpace.inner_toLp_toLp, dotProduct, mul_comm]
    rw [← hgram]
    rw [← hX_gram]
    exact Matrix.posSemidef_gram ℂ _
  have hQ : (QTotal qLayer).IsHermitian := hQ_pos.isHermitian
  have hcard :
      Fintype.card (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank))) ≤ Fintype.card ι := by
    exact hRank.toSigmaRangeQLayer.auxDim_le
  simpa [X] using
    exists_xHat_of_positive_gram_spectrum X (QTotal qLayer) hQ hQ_pos hgram hcard

/-- Produce the canonical sigma-space QXP layer from the positive-Gram `Xhat`.

This removes the last explicit `Xhat` input from the sigma-space constructor:
the rank-reduction witness supplies the projective `Q` layer and the
rectangular dimension bound, while
`exists_xHat_of_sigmaFinRangeEmbedding_positiveGram` supplies the coisometry
and mixed square-root identities. -/
theorem exists_qxpLayerData_ofRankReductionSigmaRangePositiveGram
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))] :
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
                    xHat) := by
  obtain ⟨xHat, hxHat_coisometry, hxHat_mixed⟩ :=
    exists_xHat_of_sigmaFinRangeEmbedding_positiveGram hRank
  let data : QXPLayerData Outcome ι :=
    QXPLayerData.ofSigmaRangeAndSvdIdentities (q := qLayer.q)
      hRank.projective hRank.sum_eq_total xHat hxHat_coisometry hxHat_mixed
  exact ⟨xHat, hxHat_coisometry, hxHat_mixed, data, rfl, rfl, rfl⟩

end

end MIPStarRE.LDT.MakingMeasurementsProjective
