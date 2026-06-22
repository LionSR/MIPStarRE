import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.AlmostProjective

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

/-- Left multiplication by a unitary group element preserves rectangular row
coisometries.

If `W W† = I`, then `(U W)(U W)† = I`.  This is the square-unitary part of
the paper's calculation of `lem:X-hat-squared`. -/
theorem unitaryGroup_mul_rectangular_coisometry
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι]
    (U : Matrix.unitaryGroup μ ℂ) (W : Matrix μ ι ℂ)
    (hW : W * Wᴴ = (1 : Matrix μ μ ℂ)) :
    ((U : Matrix μ μ ℂ) * W) * ((U : Matrix μ μ ℂ) * W)ᴴ =
      (1 : Matrix μ μ ℂ) := by
  have hU : (U : Matrix μ μ ℂ) * (U : Matrix μ μ ℂ)ᴴ = (1 : Matrix μ μ ℂ) := by
    change (U : Matrix μ μ ℂ) *
      ((star U : Matrix.unitaryGroup μ ℂ) : Matrix μ μ ℂ) = 1
    exact Unitary.coe_mul_star_self U
  calc
    ((U : Matrix μ μ ℂ) * W) * ((U : Matrix μ μ ℂ) * W)ᴴ =
        (U : Matrix μ μ ℂ) * (W * Wᴴ) * (U : Matrix μ μ ℂ)ᴴ := by
          rw [Matrix.conjTranspose_mul]
          simp [Matrix.mul_assoc]
    _ = (U : Matrix μ μ ℂ) * (U : Matrix μ μ ℂ)ᴴ := by
          rw [hW, Matrix.mul_one]
    _ = 1 := hU

/-- Right multiplication by the adjoint of a unitary group element preserves
rectangular row coisometries.

If `W W† = I`, then `(W V†)(W V†)† = I`.  This is the right-square-unitary
part of the paper's calculation of `lem:X-hat-squared`. -/
theorem rectangular_coisometry_mul_conjTranspose_unitaryGroup
    {μ ι : Type*} [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (W : Matrix μ ι ℂ) (V : Matrix.unitaryGroup ι ℂ)
    (hW : W * Wᴴ = (1 : Matrix μ μ ℂ)) :
    (W * (V : Matrix ι ι ℂ)ᴴ) * (W * (V : Matrix ι ι ℂ)ᴴ)ᴴ =
      (1 : Matrix μ μ ℂ) := by
  have hV : (V : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ) = (1 : Matrix ι ι ℂ) := by
    change (((star V : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ) *
      (V : Matrix ι ι ℂ)) = 1
    exact Unitary.coe_star_mul_self V
  calc
    (W * (V : Matrix ι ι ℂ)ᴴ) * (W * (V : Matrix ι ι ℂ)ᴴ)ᴴ =
        W * (((V : Matrix ι ι ℂ)ᴴ * (V : Matrix ι ι ℂ)) * Wᴴ) := by
          rw [Matrix.conjTranspose_mul]
          simp [Matrix.mul_assoc]
    _ = W * Wᴴ := by rw [hV, Matrix.one_mul]
    _ = 1 := hW

/-- The row-coisometry identity for the rectangular SVD choice of `Xhat`,
with the square factors represented as unitary group elements. -/
theorem rectangularSvd_xHat_coisometry_unitaryGroup
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup μ ℂ) (V : Matrix.unitaryGroup ι ℂ)
    (Iro : Matrix μ ι ℂ)
    (hIro : Iro * Iroᴴ = (1 : Matrix μ μ ℂ)) :
    ((U : Matrix μ μ ℂ) * Iro * (V : Matrix ι ι ℂ)ᴴ) *
        ((U : Matrix μ μ ℂ) * Iro * (V : Matrix ι ι ℂ)ᴴ)ᴴ =
      (1 : Matrix μ μ ℂ) := by
  simpa [Matrix.mul_assoc] using
    unitaryGroup_mul_rectangular_coisometry U
      (Iro * (V : Matrix ι ι ℂ)ᴴ)
      (rectangular_coisometry_mul_conjTranspose_unitaryGroup Iro V hIro)

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

/-- The mixed product obtained by multiplying the rectangular SVD formulae,
with the left square factor represented as a unitary group element. -/
theorem rectangularSvd_xHat_mixed_raw_unitaryGroup
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι]
    (x : Matrix μ ι ℂ)
    (U : Matrix.unitaryGroup μ ℂ) (V : Matrix ι ι ℂ)
    (S Iro : Matrix μ ι ℂ)
    (hx : x = (U : Matrix μ μ ℂ) * S * Vᴴ) :
    xᴴ * ((U : Matrix μ μ ℂ) * Iro * Vᴴ) = V * (Sᴴ * Iro) * Vᴴ :=
  rectangularSvd_xHat_mixed_raw x (U : Matrix μ μ ℂ) V S Iro
    (Unitary.coe_star_mul_self U) hx

/-- The first mixed product obtained from the rectangular SVD formulae.

This is the first identity in the paper's `lem:X-times-X-hat`, written in the
rectangular notation used by the formalization.  If
`X = U * S * Vᴴ` and `Xhat = U * Iro * Vᴴ`, then
`X * Xhatᴴ = U * (S * Iroᴴ) * Uᴴ`.  The middle factor `S * Iroᴴ` is the
formal counterpart of the square matrix `Σ_{m × m}` appearing in the paper. -/
theorem rectangularSvd_x_mul_xHat_conjTranspose_raw
    {μ ι : Type*} [Fintype μ] [Fintype ι] [DecidableEq ι]
    (x : Matrix μ ι ℂ)
    (U : Matrix μ μ ℂ) (V : Matrix ι ι ℂ)
    (S Iro : Matrix μ ι ℂ)
    (hV_right : Vᴴ * V = (1 : Matrix ι ι ℂ))
    (hx : x = U * S * Vᴴ) :
    x * (U * Iro * Vᴴ)ᴴ = U * (S * Iroᴴ) * Uᴴ := by
  calc
    x * (U * Iro * Vᴴ)ᴴ =
        U * (S * Iroᴴ) * Uᴴ := by
          rw [hx, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
          simp only [Matrix.conjTranspose_conjTranspose]
          have hVcollapse : Vᴴ * (V * (Iroᴴ * Uᴴ)) = Iroᴴ * Uᴴ := by
            rw [← Matrix.mul_assoc, hV_right, Matrix.one_mul]
          calc
            U * S * Vᴴ * (V * (Iroᴴ * Uᴴ)) =
                U * S * (Vᴴ * (V * (Iroᴴ * Uᴴ))) := by
                  simp [Matrix.mul_assoc]
            _ = U * S * (Iroᴴ * Uᴴ) := by rw [hVcollapse]
            _ = U * (S * Iroᴴ) * Uᴴ := by simp [Matrix.mul_assoc]

/-- The first mixed product obtained from the rectangular SVD formulae, with
the right square factor represented as a unitary group element. -/
theorem rectangularSvd_x_mul_xHat_conjTranspose_raw_unitaryGroup
    {μ ι : Type*} [Fintype μ] [Fintype ι] [DecidableEq ι]
    (x : Matrix μ ι ℂ)
    (U : Matrix μ μ ℂ) (V : Matrix.unitaryGroup ι ℂ)
    (S Iro : Matrix μ ι ℂ)
    (hx : x = U * S * (V : Matrix ι ι ℂ)ᴴ) :
    x * (U * Iro * (V : Matrix ι ι ℂ)ᴴ)ᴴ = U * (S * Iroᴴ) * Uᴴ :=
  rectangularSvd_x_mul_xHat_conjTranspose_raw x U (V : Matrix ι ι ℂ) S Iro
    (Unitary.coe_star_mul_self V) hx

/-- A positive operator whose square is `Q` is the CFC square root of `Q`.

This is the uniqueness of the positive square root, stated in the matrix
language used in the projectivization layer. -/
theorem eq_sqrt_of_sq_of_nonneg
    {ι : Type*} [Fintype ι]
    [NonUnitalContinuousFunctionalCalculus ℝ (Matrix ι ι ℂ) IsSelfAdjoint]
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
    {μ ι : Type*} [Fintype μ] [Fintype ι]
    [NonUnitalContinuousFunctionalCalculus ℝ (Matrix ι ι ℂ) IsSelfAdjoint]
    (V : Matrix ι ι ℂ) (S Iro : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hMiddle_nonneg : 0 ≤ V * (Sᴴ * Iro) * Vᴴ)
    (hMiddle_sq :
      (V * (Sᴴ * Iro) * Vᴴ) * (V * (Sᴴ * Iro) * Vᴴ) = Q) :
    V * (Sᴴ * Iro) * Vᴴ = CFC.sqrt Q := by
  exact eq_sqrt_of_sq_of_nonneg (V * (Sᴴ * Iro) * Vᴴ) Q hMiddle_nonneg hMiddle_sq

/-- The mixed rectangular SVD identity with the left square factor represented
as a unitary group element and the target square root supplied as an external
operator `Q`. -/
theorem rectangularSvd_xHat_mixed_of_sqrtQ_unitaryGroup
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι]
    [NonUnitalContinuousFunctionalCalculus ℝ (Matrix ι ι ℂ) IsSelfAdjoint]
    (x : Matrix μ ι ℂ)
    (U : Matrix.unitaryGroup μ ℂ) (V : Matrix ι ι ℂ)
    (S Iro : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hx : x = (U : Matrix μ μ ℂ) * S * Vᴴ)
    (hSqrt : V * (Sᴴ * Iro) * Vᴴ = CFC.sqrt Q) :
    xᴴ * ((U : Matrix μ μ ℂ) * Iro * Vᴴ) = CFC.sqrt Q := by
  rw [rectangularSvd_xHat_mixed_raw_unitaryGroup x U V S Iro hx, hSqrt]

/-- The rectangular SVD data determine a candidate `Xhat` and its two primitive
identities, with the square factors represented as unitary group elements. -/
theorem exists_xHat_of_rectangularSvd_unitaryGroup
    {μ ι : Type*} [Fintype μ] [DecidableEq μ] [Fintype ι] [DecidableEq ι]
    (x : Matrix μ ι ℂ)
    (U : Matrix.unitaryGroup μ ℂ) (V : Matrix.unitaryGroup ι ℂ)
    (S Iro : Matrix μ ι ℂ) (Q : Matrix ι ι ℂ)
    (hIro : Iro * Iroᴴ = (1 : Matrix μ μ ℂ))
    (hx : x = (U : Matrix μ μ ℂ) * S * (V : Matrix ι ι ℂ)ᴴ)
    (hSqrt : (V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ =
      CFC.sqrt Q) :
    ∃ xHat : Matrix μ ι ℂ,
      xHat = (U : Matrix μ μ ℂ) * Iro * (V : Matrix ι ι ℂ)ᴴ ∧
        xHat * xHatᴴ = (1 : Matrix μ μ ℂ) ∧
          xᴴ * xHat = CFC.sqrt Q := by
  refine ⟨(U : Matrix μ μ ℂ) * Iro * (V : Matrix ι ι ℂ)ᴴ, rfl, ?_, ?_⟩
  · exact rectangularSvd_xHat_coisometry_unitaryGroup U V Iro hIro
  · exact rectangularSvd_xHat_mixed_of_sqrtQ_unitaryGroup x U
      (V : Matrix ι ι ℂ) S Iro Q hx hSqrt

/-- Assemble `QXPLayerData` from a rank-reduction witness and the SVD
identities for `Xhat`.

The rank-reduction witness supplies the projectivity of each `Q_a` and the
identity `∑_a Q_a = Q`.  The remaining hypotheses are exactly the local
matrix-decomposition data for `Q_a = X† T_a X` and the two SVD-derived
identities for the chosen `Xhat`.  Thus this constructor removes the
rank-reduction fields from the caller's obligations.  The rectangular
SVD/polar decomposition that provides `xHat` is supplied by the
sigma-range / rectangular polar-decomposition route, which provides the
unitary and coisometry factors from the positive spectral subspace of `Q`.
The end-to-end chain through the rounding-to-projectors, rank-reduction,
and orthogonalization lemmas remains to be closed upstream. -/
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

/-- Assemble `QXPLayerData` from rank-reduction data and rectangular SVD data
whose square factors are represented as Mathlib unitary-group elements.

The left and right unitarity laws are carried by the type of `U` and `V`; the
only remaining rectangular law is the coisometry of `Iro`. -/
noncomputable def QXPLayerData.ofRankReductionAndRectangularSvdUnitaryGroup
    {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    (x : Matrix qLayer.auxSpace.carrier ι ℂ)
    (U : Matrix.unitaryGroup qLayer.auxSpace.carrier ℂ)
    (V : Matrix.unitaryGroup ι ℂ)
    (S Iro : Matrix qLayer.auxSpace.carrier ι ℂ)
    (qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x)
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hx : x = (U : Matrix qLayer.auxSpace.carrier qLayer.auxSpace.carrier ℂ) *
      S * (V : Matrix ι ι ℂ)ᴴ)
    (hSqrt : (V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ =
      CFC.sqrt (QTotal qLayer)) :
    QXPLayerData Outcome ι :=
  QXPLayerData.ofRankReductionAndSvdIdentities hRank x
    ((U : Matrix qLayer.auxSpace.carrier qLayer.auxSpace.carrier ℂ) *
      Iro * (V : Matrix ι ι ℂ)ᴴ)
    qa_eq
    (rectangularSvd_xHat_coisometry_unitaryGroup U V Iro hIro)
    (rectangularSvd_xHat_mixed_of_sqrtQ_unitaryGroup x U
      (V : Matrix ι ι ℂ) S Iro (QTotal qLayer) hx hSqrt)

/-- Assemble `QXPLayerData` from unitary-group rectangular SVD data whose
middle factor is characterized as the positive square root of `Q`.

The unitarity of the square factors is represented by
`Matrix.unitaryGroup`, while the square-root identification is supplied by
positivity and the square equation for the middle factor. -/
noncomputable def QXPLayerData.ofRankReductionAndRectangularSvdSquareRootUnitaryGroup
    {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    {qLayer : QLayerData Outcome ι}
    (hRank : RankReductionWitness ψ A ζ qLayer)
    (x : Matrix qLayer.auxSpace.carrier ι ℂ)
    (U : Matrix.unitaryGroup qLayer.auxSpace.carrier ℂ)
    (V : Matrix.unitaryGroup ι ℂ)
    (S Iro : Matrix qLayer.auxSpace.carrier ι ℂ)
    (qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x)
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op qLayer.auxSpace.carrier))
    (hx : x = (U : Matrix qLayer.auxSpace.carrier qLayer.auxSpace.carrier ℂ) *
      S * (V : Matrix ι ι ℂ)ᴴ)
    (hMiddle_nonneg :
      0 ≤ (V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ)
    (hMiddle_sq :
      ((V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ) *
        ((V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ) =
          QTotal qLayer) :
    QXPLayerData Outcome ι :=
  QXPLayerData.ofRankReductionAndRectangularSvdUnitaryGroup hRank x U V S Iro
    qa_eq hIro hx
    (rectangularSvd_middle_eq_sqrt_of_square (V : Matrix ι ι ℂ) S Iro
      (QTotal qLayer) hMiddle_nonneg hMiddle_sq)

/-- Assemble the canonical sigma-space `Q/X/Xhat/P` layer from rectangular SVD
data whose square factors are `Matrix.unitaryGroup` elements.

The unitarity hypotheses for `U` and `V` are carried by their types. -/
noncomputable def QXPLayerData.ofSigmaRangeAndRectangularSvdUnitaryGroupWithCarrier
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (q : OpFamily Outcome ι)
    (qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (q.outcome a))
    (q_sum_eq_total : ∑ a : Outcome, q.outcome a = q.total)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))]
    (U : Matrix.unitaryGroup (sigmaRangeQLayer q).auxSpace.carrier ℂ)
    (V : Matrix.unitaryGroup ι ℂ)
    (S Iro : Matrix (sigmaRangeQLayer q).auxSpace.carrier ι ℂ)
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op (sigmaRangeQLayer q).auxSpace.carrier))
    (hx : sigmaFinRangeEmbedding q.outcome qa_projective =
      (U : Matrix (sigmaRangeQLayer q).auxSpace.carrier
        (sigmaRangeQLayer q).auxSpace.carrier ℂ) *
      S * (V : Matrix ι ι ℂ)ᴴ)
    (hSqrt : (V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ =
      CFC.sqrt q.total) :
    QXPLayerData Outcome ι :=
  QXPLayerData.ofSigmaRangeAndSvdIdentities (q := q)
    qa_projective q_sum_eq_total
    ((U : Matrix (sigmaRangeQLayer q).auxSpace.carrier
      (sigmaRangeQLayer q).auxSpace.carrier ℂ) *
      Iro * (V : Matrix ι ι ℂ)ᴴ)
    (rectangularSvd_xHat_coisometry_unitaryGroup U V Iro hIro)
    (rectangularSvd_xHat_mixed_of_sqrtQ_unitaryGroup
      (sigmaFinRangeEmbedding q.outcome qa_projective) U
      (V : Matrix ι ι ℂ) S Iro q.total hx hSqrt)

/-- Assemble the canonical sigma-space `Q/X/Xhat/P` layer from rectangular SVD
data whose square factors are `Matrix.unitaryGroup` elements.

The unitarity hypotheses for `U` and `V` are carried by their types. -/
noncomputable def QXPLayerData.ofSigmaRangeAndRectangularSvdUnitaryGroup
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (q : OpFamily Outcome ι)
    (qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (q.outcome a))
    (q_sum_eq_total : ∑ a : Outcome, q.outcome a = q.total)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))]
    (U : Matrix.unitaryGroup (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))) ℂ)
    (V : Matrix.unitaryGroup ι ℂ)
    (S Iro : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))) ι ℂ)
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank)))))
    (hx : sigmaFinRangeEmbedding q.outcome qa_projective =
      (U : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank)))
        (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
          (fun a : Outcome => (q.outcome a).rank))) ℂ) *
      S * (V : Matrix ι ι ℂ)ᴴ)
    (hSqrt : (V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ =
      CFC.sqrt q.total) :
    QXPLayerData Outcome ι :=
  QXPLayerData.ofSigmaRangeAndRectangularSvdUnitaryGroupWithCarrier (q := q)
    qa_projective q_sum_eq_total U V S Iro hIro hx hSqrt

/-- Assemble the canonical sigma-space `Q/X/Xhat/P` layer from unitary-group
rectangular SVD data whose middle factor is characterized as a positive square
root. -/
noncomputable def QXPLayerData.ofSigmaRangeAndRectangularSvdSquareRootUnitaryGroupWithCarrier
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (q : OpFamily Outcome ι)
    (qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (q.outcome a))
    (q_sum_eq_total : ∑ a : Outcome, q.outcome a = q.total)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))]
    (U : Matrix.unitaryGroup (sigmaRangeQLayer q).auxSpace.carrier ℂ)
    (V : Matrix.unitaryGroup ι ℂ)
    (S Iro : Matrix (sigmaRangeQLayer q).auxSpace.carrier ι ℂ)
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op (sigmaRangeQLayer q).auxSpace.carrier))
    (hx : sigmaFinRangeEmbedding q.outcome qa_projective =
      (U : Matrix (sigmaRangeQLayer q).auxSpace.carrier
        (sigmaRangeQLayer q).auxSpace.carrier ℂ) *
      S * (V : Matrix ι ι ℂ)ᴴ)
    (hMiddle_nonneg :
      0 ≤ (V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ)
    (hMiddle_sq :
      ((V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ) *
        ((V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ) = q.total) :
    QXPLayerData Outcome ι :=
  QXPLayerData.ofSigmaRangeAndRectangularSvdUnitaryGroupWithCarrier (q := q)
    qa_projective q_sum_eq_total U V S Iro hIro hx
      (rectangularSvd_middle_eq_sqrt_of_square (V : Matrix ι ι ℂ) S Iro q.total
        hMiddle_nonneg hMiddle_sq)

/-- Assemble the canonical sigma-space `Q/X/Xhat/P` layer from unitary-group
rectangular SVD data whose middle factor is characterized as a positive square
root. -/
noncomputable def QXPLayerData.ofSigmaRangeAndRectangularSvdSquareRootUnitaryGroup
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (q : OpFamily Outcome ι)
    (qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (q.outcome a))
    (q_sum_eq_total : ∑ a : Outcome, q.outcome a = q.total)
    [Nonempty (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))]
    (U : Matrix.unitaryGroup (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))) ℂ)
    (V : Matrix.unitaryGroup ι ℂ)
    (S Iro : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
      (fun a : Outcome => (q.outcome a).rank))) ι ℂ)
    (hIro : Iro * Iroᴴ =
      (1 : MIPStarRE.Quantum.Op (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank)))))
    (hx : sigmaFinRangeEmbedding q.outcome qa_projective =
      (U : Matrix (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
        (fun a : Outcome => (q.outcome a).rank)))
        (ULift.{uι} (FiniteHilbertSpace.sigmaFinCarrier
          (fun a : Outcome => (q.outcome a).rank))) ℂ) *
      S * (V : Matrix ι ι ℂ)ᴴ)
    (hMiddle_nonneg :
      0 ≤ (V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ)
    (hMiddle_sq :
      ((V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ) *
        ((V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ) = q.total) :
    QXPLayerData Outcome ι :=
  QXPLayerData.ofSigmaRangeAndRectangularSvdSquareRootUnitaryGroupWithCarrier
    (q := q) qa_projective q_sum_eq_total U V S Iro
      hIro hx hMiddle_nonneg hMiddle_sq

/-- Rank-reduction existence form for the canonical sigma-space QXP layer from
unitary-group rectangular SVD data. -/
theorem exists_qxpLayerData_ofRankReductionSigmaRangeAndRectangularSvdUnitaryGroupWithCarrier
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
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
    (hSqrt : (V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ =
      CFC.sqrt (QTotal qLayer)) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = sigmaRangeQLayer qLayer.q,
        hq ▸ data.x =
            (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
              sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective) ∧
          hq ▸ data.xHat =
            (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
              (U : Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier
                (sigmaRangeQLayer qLayer.q).auxSpace.carrier ℂ) *
              Iro * (V : Matrix ι ι ℂ)ᴴ) := by
  classical
  exact
    ⟨QXPLayerData.ofSigmaRangeAndRectangularSvdUnitaryGroupWithCarrier (q := qLayer.q)
      hRank.projective hRank.sum_eq_total U V S Iro hIro hx hSqrt,
      rfl, rfl, rfl⟩

/-- Rank-reduction existence form for the canonical sigma-space QXP layer from
unitary-group rectangular SVD data. -/
theorem exists_qxpLayerData_ofRankReductionSigmaRangeAndRectangularSvdUnitaryGroup
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
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
    (hSqrt : (V : Matrix ι ι ℂ) * (Sᴴ * Iro) * (V : Matrix ι ι ℂ)ᴴ =
      CFC.sqrt (QTotal qLayer)) :
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
              Iro * (V : Matrix ι ι ℂ)ᴴ) :=
  exists_qxpLayerData_ofRankReductionSigmaRangeAndRectangularSvdUnitaryGroupWithCarrier
    hRank U V S Iro hIro hx hSqrt

/-- Rank-reduction existence form for the canonical sigma-space QXP layer from
unitary-group rectangular SVD data whose middle factor is characterized as a
positive square root. -/
theorem exists_qxpLayerData_ofRankReductionSigmaRangeAndRectangularSvdSqrtWithCarrier
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
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
          QTotal qLayer) :
    ∃ data : QXPLayerData Outcome ι,
      ∃ hq : data.qLayer = sigmaRangeQLayer qLayer.q,
        hq ▸ data.x =
            (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
              sigmaFinRangeEmbedding qLayer.q.outcome hRank.projective) ∧
          hq ▸ data.xHat =
            (show Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier ι ℂ from
              (U : Matrix (sigmaRangeQLayer qLayer.q).auxSpace.carrier
                (sigmaRangeQLayer qLayer.q).auxSpace.carrier ℂ) *
              Iro * (V : Matrix ι ι ℂ)ᴴ) := by
  classical
  exact
    ⟨QXPLayerData.ofSigmaRangeAndRectangularSvdSquareRootUnitaryGroupWithCarrier
      (q := qLayer.q) hRank.projective hRank.sum_eq_total U V S Iro
        hIro hx hMiddle_nonneg hMiddle_sq,
      rfl, rfl, rfl⟩

/-- Rank-reduction existence form for the canonical sigma-space QXP layer from
unitary-group rectangular SVD data whose middle factor is characterized as a
positive square root. -/
theorem exists_qxpLayerData_ofRankReductionSigmaRangeAndRectangularSvdSquareRootUnitaryGroup
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
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
          QTotal qLayer) :
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
              Iro * (V : Matrix ι ι ℂ)ᴴ) :=
  exists_qxpLayerData_ofRankReductionSigmaRangeAndRectangularSvdSqrtWithCarrier
    hRank U V S Iro hIro hx hMiddle_nonneg hMiddle_sq

end

end MIPStarRE.LDT.MakingMeasurementsProjective
