import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerData

/-!
# Section 5 — Rectangular SVD constructors for Q/X/XHat/P data

Rectangular-SVD matrix identities and constructors for the paper's
`Q/X/XHat/P` intermediate layer.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe uOutcome uι

noncomputable section

/-- The row-coisometry identity for the rectangular SVD choice of `Xhat`.

If `U` and `V` are unitary in the directions used below, and if the rectangular
identity factor `Iro` has orthonormal rows, then the paper's matrix
`U * Iro * Vᴴ` also has orthonormal rows.  This is the elementary matrix
calculation behind `lem:X-hat-squared`. -/
theorem rectangularSvd_xHat_coisometry
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (U : Matrix μ μ ℂ) (V : Matrix ι ι ℂ)
    (Iro : Matrix μ ι ℂ)
    (hU_left : U * Uᴴ = (1 : Matrix μ μ ℂ))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ = (1 : Matrix μ μ ℂ)) :
    (U * Iro * Vᴴ) * (U * Iro * Vᴴ)ᴴ = (1 : Matrix μ μ ℂ) := by
  calc
    (U * Iro * Vᴴ) * (U * Iro * Vᴴ)ᴴ =
        U * (Iro * Iroᴴ) * Uᴴ := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
          simp only [Matrix.conjTranspose_conjTranspose]
          have hVcollapse : Vᴴ * (V * (Iroᴴ * Uᴴ)) = Iroᴴ * Uᴴ := by
            rw [← Matrix.mul_assoc, hV_right, Matrix.one_mul]
          calc
            U * Iro * Vᴴ * (V * (Iroᴴ * Uᴴ)) =
                U * Iro * (Vᴴ * (V * (Iroᴴ * Uᴴ))) := by
                  simp [Matrix.mul_assoc]
            _ = U * Iro * (Iroᴴ * Uᴴ) := by rw [hVcollapse]
            _ = U * (Iro * Iroᴴ) * Uᴴ := by simp [Matrix.mul_assoc]
    _ = U * Uᴴ := by rw [hIro, Matrix.mul_one]
    _ = 1 := hU_left

/-- The mixed product obtained by multiplying the rectangular SVD formulae.

This lemma contains only the matrix algebra.  The spectral identification of the
right hand side with a square root is supplied separately, since downstream
constructors usually know the square root in the form `CFC.sqrt Q`. -/
theorem rectangularSvd_xHat_mixed_raw
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι]
    (x : Matrix μ ι ℂ)
    (U : Matrix μ μ ℂ) (V : Matrix ι ι ℂ)
    (S Iro : Matrix μ ι ℂ)
    (hU_right : Uᴴ * U = (1 : Matrix μ μ ℂ))
    (hx : x = U * S * Vᴴ) :
    xᴴ * (U * Iro * Vᴴ) = V * (Sᴴ * Iro) * Vᴴ := by
  calc
    xᴴ * (U * Iro * Vᴴ) =
        V * (Sᴴ * Iro) * Vᴴ := by
          rw [hx, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
          simp only [Matrix.conjTranspose_conjTranspose]
          have hUcollapse : Uᴴ * (U * (Iro * Vᴴ)) = Iro * Vᴴ := by
            rw [← Matrix.mul_assoc, hU_right, Matrix.one_mul]
          calc
            V * (Sᴴ * Uᴴ) * (U * Iro * Vᴴ) =
                V * Sᴴ * (Uᴴ * (U * (Iro * Vᴴ))) := by
                  simp [Matrix.mul_assoc]
            _ = V * Sᴴ * (Iro * Vᴴ) := by rw [hUcollapse]
            _ = V * (Sᴴ * Iro) * Vᴴ := by simp [Matrix.mul_assoc]

/-- A positive operator whose square is `Q` is the CFC square root of `Q`.

This is the uniqueness of the positive square root, stated in the matrix
language used in the projectivization layer. -/
theorem eq_sqrt_of_sq_of_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B Q : Matrix ι ι ℂ)
    (hB_nonneg : 0 ≤ B)
    (hB_sq : B * B = Q) :
    B = CFC.sqrt Q := by
  exact (CFC.sqrt_unique hB_sq hB_nonneg).symm

/-- The square-root identification for the middle factor in the rectangular SVD
calculation.

If the middle operator `V * (Sᴴ * Iro) * Vᴴ` is positive and its square is the
target operator `Q`, then it is the positive square root of `Q`.  This is the
spectral input which turns the raw SVD calculation into the paper's identity
`X† Xhat = sqrt Q`. -/
theorem rectangularSvd_middle_eq_sqrt_of_square
    {μ ι : Type*} [Fintype μ] [Fintype ι] [DecidableEq ι]
    (V : Matrix ι ι ℂ) (S Iro : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hMiddle_nonneg : 0 ≤ V * (Sᴴ * Iro) * Vᴴ)
    (hMiddle_sq :
      (V * (Sᴴ * Iro) * Vᴴ) * (V * (Sᴴ * Iro) * Vᴴ) = Q) :
    V * (Sᴴ * Iro) * Vᴴ = CFC.sqrt Q := by
  exact eq_sqrt_of_sq_of_nonneg (V * (Sᴴ * Iro) * Vᴴ) Q hMiddle_nonneg hMiddle_sq

/-- The mixed rectangular SVD identity with the target square root supplied as
an external operator `Q`.

This is the form compatible with the QXP constructors, where the spectral input
is naturally stated as `CFC.sqrt (QTotal qLayer)` rather than by rewriting
through the right Gram matrix of `X`. -/
theorem rectangularSvd_xHat_mixed_of_sqrtQ
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (x : Matrix μ ι ℂ)
    (U : Matrix μ μ ℂ) (V : Matrix ι ι ℂ)
    (S Iro : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hU_right : Uᴴ * U = (1 : Matrix μ μ ℂ))
    (hx : x = U * S * Vᴴ)
    (hSqrt : V * (Sᴴ * Iro) * Vᴴ = CFC.sqrt Q) :
    xᴴ * (U * Iro * Vᴴ) = CFC.sqrt Q := by
  rw [rectangularSvd_xHat_mixed_raw x U V S Iro hU_right hx, hSqrt]

/-- The mixed rectangular SVD identity in the right Gram form. -/
theorem rectangularSvd_xHat_mixed
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (x : Matrix μ ι ℂ)
    (U : Matrix μ μ ℂ) (V : Matrix ι ι ℂ)
    (S Iro : Matrix μ ι ℂ)
    (hU_right : Uᴴ * U = (1 : Matrix μ μ ℂ))
    (hx : x = U * S * Vᴴ)
    (hSqrt : V * (Sᴴ * Iro) * Vᴴ = CFC.sqrt (xᴴ * x)) :
    xᴴ * (U * Iro * Vᴴ) = CFC.sqrt (xᴴ * x) := by
  exact rectangularSvd_xHat_mixed_of_sqrtQ x U V S Iro (xᴴ * x) hU_right hx hSqrt

/-- The rectangular SVD data determine a candidate `Xhat` and its two primitive
identities.

This is the local existence form of the paper's construction
`\widehat X = U I_{m \times d} V^\dagger`: once the rectangular SVD data and
the spectral square-root identification are supplied, the coisometry and mixed
square-root identities follow by matrix algebra. The witness is exactly
`U * Iro * Vᴴ`; the existential packaging is used only to match the paper's
construction of a named matrix `\widehat X`. -/
theorem exists_xHat_of_rectangularSvd
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (x : Matrix μ ι ℂ)
    (U : Matrix μ μ ℂ) (V : Matrix ι ι ℂ)
    (S Iro : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hU_left : U * Uᴴ = (1 : Matrix μ μ ℂ))
    (hU_right : Uᴴ * U = (1 : Matrix μ μ ℂ))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ = (1 : Matrix μ μ ℂ))
    (hx : x = U * S * Vᴴ)
    (hSqrt : V * (Sᴴ * Iro) * Vᴴ = CFC.sqrt Q) :
    ∃ xHat : Matrix μ ι ℂ,
      xHat = U * Iro * Vᴴ ∧
        xHat * xHatᴴ = (1 : Matrix μ μ ℂ) ∧
          xᴴ * xHat = CFC.sqrt Q := by
  refine ⟨U * Iro * Vᴴ, rfl, ?_, ?_⟩
  · exact rectangularSvd_xHat_coisometry U V Iro hU_left hV_right hIro
  · exact rectangularSvd_xHat_mixed_of_sqrtQ x U V S Iro Q hU_right hx hSqrt

/-- Assemble `QXPLayerData` from a rank-reduction witness and the SVD
identities for `Xhat`.

The rank-reduction witness supplies the projectivity of each `Q_a` and the
identity `∑_a Q_a = Q`.  The remaining hypotheses are exactly the local
matrix-decomposition data for `Q_a = X† T_a X` and the two SVD-derived
identities for the chosen `Xhat`.  Thus this constructor removes the
rank-reduction fields from the caller's obligations.  The rectangular
SVD/polar decomposition that provides `xHat` is now produced by the
sigma-range route (PR #1237).  The remaining end-to-end gap is the broader
`SpectralTruncation` / `ProjectivizationRepair` /
`OrthonormalizationInput` chain (issue #1032, #1359). -/
noncomputable def QXPLayerData.ofRankReductionAndSvdIdentities
    {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    (x : Matrix qLayer.auxSpace.carrier ι ℂ)
    (xHat : Matrix qLayer.auxSpace.carrier ι ℂ)
    (qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x)
    (xHat_coisometry :
      xHat * xHatᴴ = (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (xHat_mixed : xᴴ * xHat = CFC.sqrt (QTotal qLayer)) :
    QXPLayerData Outcome ι :=
  QXPLayerData.ofQLayerAndSvdIdentities qLayer hRank.projective hRank.sum_eq_total
    x xHat qa_eq xHat_coisometry xHat_mixed

/-- Assemble `QXPLayerData` from a rank-reduction witness and rectangular SVD
data for `X`.

The matrix `Xhat` is no longer a separate input: it is the paper's
`U I_{m \times d} V^\dagger`.  The coisometry and mixed square-root fields of
`QXPLayerData` are derived from the rectangular SVD identities above.

The two hypotheses on `U` record the two unitary directions used by these
algebraic lemmas. For a square finite-dimensional matrix they are equivalent,
but keeping both avoids inserting an additional linear-algebra conversion into
the rectangular-SVD interface. -/
noncomputable def QXPLayerData.ofRankReductionAndRectangularSvd
    {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    (x : Matrix qLayer.auxSpace.carrier ι ℂ)
    (U : Matrix qLayer.auxSpace.carrier qLayer.auxSpace.carrier ℂ)
    (V : Matrix ι ι ℂ)
    (S Iro : Matrix qLayer.auxSpace.carrier ι ℂ)
    (qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x)
    (hU_left : U * Uᴴ =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hU_right : Uᴴ * U =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hx : x = U * S * Vᴴ)
    (hSqrt : V * (Sᴴ * Iro) * Vᴴ = CFC.sqrt (QTotal qLayer)) :
    QXPLayerData Outcome ι :=
  QXPLayerData.ofRankReductionAndSvdIdentities hRank x (U * Iro * Vᴴ) qa_eq
    (rectangularSvd_xHat_coisometry U V Iro hU_left hV_right hIro)
    (rectangularSvd_xHat_mixed_of_sqrtQ x U V S Iro (QTotal qLayer)
      hU_right hx hSqrt)

/-- Assemble `QXPLayerData` from rectangular SVD data whose middle factor is
specified by the positivity and square equation characterizing `sqrt Q`.

This is the form closest to the proof in the paper: after multiplying the SVD
identities, the operator `V * (Sᴴ * Iro) * Vᴴ` is identified as the positive
square root of the total `Q` operator by uniqueness of the CFC square root. -/
noncomputable def QXPLayerData.ofRankReductionAndRectangularSvdSquareRoot
    {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    (x : Matrix qLayer.auxSpace.carrier ι ℂ)
    (U : Matrix qLayer.auxSpace.carrier qLayer.auxSpace.carrier ℂ)
    (V : Matrix ι ι ℂ)
    (S Iro : Matrix qLayer.auxSpace.carrier ι ℂ)
    (qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x)
    (hU_left : U * Uᴴ =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hU_right : Uᴴ * U =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hx : x = U * S * Vᴴ)
    (hMiddle_nonneg : 0 ≤ V * (Sᴴ * Iro) * Vᴴ)
    (hMiddle_sq :
      (V * (Sᴴ * Iro) * Vᴴ) * (V * (Sᴴ * Iro) * Vᴴ) = QTotal qLayer) :
    QXPLayerData Outcome ι :=
  QXPLayerData.ofRankReductionAndRectangularSvd hRank x U V S Iro qa_eq
    hU_left hU_right hV_right hIro hx
    (rectangularSvd_middle_eq_sqrt_of_square V S Iro (QTotal qLayer)
      hMiddle_nonneg hMiddle_sq)

/-- Existence form of
`QXPLayerData.ofRankReductionAndSvdIdentities`, matching the data-package shape
used by the QXP repair layer.

The produced data keeps the supplied `qLayer`, `x`, and `xHat` judgmentally
visible up to transport along the recorded `qLayer` equality. -/
theorem exists_qxpLayerData_ofRankReductionAndSvdIdentities
    {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    (x : Matrix qLayer.auxSpace.carrier ι ℂ)
    (xHat : Matrix qLayer.auxSpace.carrier ι ℂ)
    (qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x)
    (xHat_coisometry :
      xHat * xHatᴴ = (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (xHat_mixed : xᴴ * xHat = CFC.sqrt (QTotal qLayer)) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = qLayer,
        hq ▸ data.x = x ∧ hq ▸ data.xHat = xHat :=
  ⟨QXPLayerData.ofRankReductionAndSvdIdentities hRank x xHat qa_eq
      xHat_coisometry xHat_mixed, rfl, rfl, rfl⟩

/-- Existence form of `QXPLayerData.ofRankReductionAndRectangularSvd`.

The produced data stores the supplied `Q`-layer and matrix `X`, and its
`Xhat` field is exactly the rectangular SVD expression
`U I_{m \times d} V^\dagger`. -/
theorem exists_qxpLayerData_ofRankReductionAndRectangularSvd
    {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    (x : Matrix qLayer.auxSpace.carrier ι ℂ)
    (U : Matrix qLayer.auxSpace.carrier qLayer.auxSpace.carrier ℂ)
    (V : Matrix ι ι ℂ)
    (S Iro : Matrix qLayer.auxSpace.carrier ι ℂ)
    (qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x)
    (hU_left : U * Uᴴ =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hU_right : Uᴴ * U =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hx : x = U * S * Vᴴ)
    (hSqrt : V * (Sᴴ * Iro) * Vᴴ = CFC.sqrt (QTotal qLayer)) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = qLayer,
        hq ▸ data.x = x ∧ hq ▸ data.xHat = U * Iro * Vᴴ :=
  ⟨QXPLayerData.ofRankReductionAndRectangularSvd hRank x U V S Iro qa_eq
      hU_left hU_right hV_right hIro hx hSqrt, rfl, rfl, rfl⟩

/-- Existence form of
`QXPLayerData.ofRankReductionAndRectangularSvdSquareRoot`.

The stored `Xhat` is the same rectangular SVD expression as in
`QXPLayerData.ofRankReductionAndRectangularSvd`; only the square-root input has
been replaced by its positive-square characterization. -/
theorem exists_qxpLayerData_ofRankReductionAndRectangularSvdSquareRoot
    {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    (x : Matrix qLayer.auxSpace.carrier ι ℂ)
    (U : Matrix qLayer.auxSpace.carrier qLayer.auxSpace.carrier ℂ)
    (V : Matrix ι ι ℂ)
    (S Iro : Matrix qLayer.auxSpace.carrier ι ℂ)
    (qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x)
    (hU_left : U * Uᴴ =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hU_right : Uᴴ * U =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hx : x = U * S * Vᴴ)
    (hMiddle_nonneg : 0 ≤ V * (Sᴴ * Iro) * Vᴴ)
    (hMiddle_sq :
      (V * (Sᴴ * Iro) * Vᴴ) * (V * (Sᴴ * Iro) * Vᴴ) = QTotal qLayer) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = qLayer,
        hq ▸ data.x = x ∧ hq ▸ data.xHat = U * Iro * Vᴴ :=
  ⟨QXPLayerData.ofRankReductionAndRectangularSvdSquareRoot hRank x U V S Iro
      qa_eq hU_left hU_right hV_right hIro hx hMiddle_nonneg hMiddle_sq,
    rfl, rfl, rfl⟩

/-- Assemble the canonical sigma-space `Q/X/Xhat/P` layer directly from
rectangular SVD data.

The auxiliary space, projective measurement, and matrix `X` are the finite
sigma-space construction attached to the projective family `q`.  The only
remaining inputs are the rectangular SVD matrices and their unitary,
rectangular-identity, and square-root laws. -/
noncomputable def QXPLayerData.ofSigmaRangeAndRectangularSvd
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (q : OpFamily Outcome ι)
    (qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (q.outcome a))
    (q_sum_eq_total : ∑ a : Outcome, q.outcome a = q.total)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))]
    (U : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank)))
      (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank))) ℂ)
    (V : Matrix ι ι ℂ)
    (S Iro : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))) ι ℂ)
    (hU_left : U * Uᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank)))))
    (hU_right : Uᴴ * U =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank)))))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank)))))
    (hx : sigmaFinRangeEmbedding q.outcome qa_projective = U * S * Vᴴ)
    (hSqrt : V * (Sᴴ * Iro) * Vᴴ = CFC.sqrt q.total) :
    QXPLayerData Outcome ι :=
  QXPLayerData.ofSigmaRangeAndSvdIdentities (q := q)
    qa_projective q_sum_eq_total (U * Iro * Vᴴ)
    (rectangularSvd_xHat_coisometry U V Iro hU_left hV_right hIro)
    (rectangularSvd_xHat_mixed_of_sqrtQ
      (sigmaFinRangeEmbedding q.outcome qa_projective) U V S Iro q.total
      hU_right hx hSqrt)

/-- Assemble the canonical sigma-space `Q/X/Xhat/P` layer from rectangular SVD
data whose middle factor is characterized as a positive square root. -/
noncomputable def QXPLayerData.ofSigmaRangeAndRectangularSvdSquareRoot
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (q : OpFamily Outcome ι)
    (qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (q.outcome a))
    (q_sum_eq_total : ∑ a : Outcome, q.outcome a = q.total)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))]
    (U : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank)))
      (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank))) ℂ)
    (V : Matrix ι ι ℂ)
    (S Iro : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))) ι ℂ)
    (hU_left : U * Uᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank)))))
    (hU_right : Uᴴ * U =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank)))))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank)))))
    (hx : sigmaFinRangeEmbedding q.outcome qa_projective = U * S * Vᴴ)
    (hMiddle_nonneg : 0 ≤ V * (Sᴴ * Iro) * Vᴴ)
    (hMiddle_sq :
      (V * (Sᴴ * Iro) * Vᴴ) * (V * (Sᴴ * Iro) * Vᴴ) = q.total) :
    QXPLayerData Outcome ι :=
  QXPLayerData.ofSigmaRangeAndRectangularSvd (q := q)
    qa_projective q_sum_eq_total U V S Iro
      hU_left hU_right hV_right hIro hx
      (rectangularSvd_middle_eq_sqrt_of_square V S Iro q.total
        hMiddle_nonneg hMiddle_sq)

/-- Rank-reduction existence form for the canonical sigma-space QXP layer from
rectangular SVD data.

This is the paper-facing version of the `Q -> X -> Xhat -> P` producer: the
rank-reduction witness fixes the projective `Q` layer and the sigma-space
matrix `X`, while the supplied rectangular SVD data determine `Xhat`. -/
theorem exists_qxpLayerData_ofRankReductionSigmaRangeAndRectangularSvd
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))]
    (U : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank)))
      (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank))) ℂ)
    (V : Matrix ι ι ℂ)
    (S Iro : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))) ι ℂ)
    (hU_left : U * Uᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))))
    (hU_right : Uᴴ * U =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))))
    (hx : sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective = U * S * Vᴴ)
    (hSqrt : V * (Sᴴ * Iro) * Vᴴ = CFC.sqrt (QTotal qLayer)) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = sigmaRangeQLayer qLayer.q,
        hq ▸ data.x =
            (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
              sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective) ∧
          hq ▸ data.xHat =
            (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
              U * Iro * Vᴴ) := by
  classical
  exact
    ⟨QXPLayerData.ofSigmaRangeAndRectangularSvd (q := qLayer.q)
      hRank.projective hRank.sum_eq_total U V S Iro
        hU_left hU_right hV_right hIro hx hSqrt,
      rfl, rfl, rfl⟩

/-- Rank-reduction existence form for the canonical sigma-space QXP layer when
the rectangular SVD middle factor is given by its positive-square
characterization. -/
theorem exists_qxpLayerData_ofRankReductionSigmaRangeAndRectangularSvdSquareRoot
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))]
    (U : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank)))
      (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank))) ℂ)
    (V : Matrix ι ι ℂ)
    (S Iro : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (qLayer.q.outcome a).rank))) ι ℂ)
    (hU_left : U * Uᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))))
    (hU_right : Uᴴ * U =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))))
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (qLayer.q.outcome a).rank)))))
    (hx : sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective = U * S * Vᴴ)
    (hMiddle_nonneg : 0 ≤ V * (Sᴴ * Iro) * Vᴴ)
    (hMiddle_sq :
      (V * (Sᴴ * Iro) * Vᴴ) * (V * (Sᴴ * Iro) * Vᴴ) = QTotal qLayer) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = sigmaRangeQLayer qLayer.q,
        hq ▸ data.x =
            (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
              sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective) ∧
          hq ▸ data.xHat =
            (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
              U * Iro * Vᴴ) := by
  classical
  exact
    ⟨QXPLayerData.ofSigmaRangeAndRectangularSvdSquareRoot (q := qLayer.q)
      hRank.projective hRank.sum_eq_total U V S Iro
        hU_left hU_right hV_right hIro hx hMiddle_nonneg hMiddle_sq,
      rfl, rfl, rfl⟩

end

end MIPStarRE.LDT.MakingMeasurementsProjective
