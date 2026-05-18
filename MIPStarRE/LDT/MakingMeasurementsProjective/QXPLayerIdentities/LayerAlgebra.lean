import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities.PositiveGram

/-!
# Section 5 — Q/X/XHat/P algebraic identities

Algebraic identities for the `Q/X/XHat/P` layer, including the
restatements of `Q_a`, `P_a`, the mixed product, and projectivity of `P`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe uOutcome uι

noncomputable section

/-- **`X_a = T_a X`** (`lem:xa-t`). -/
lemma xa_t {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Xa data a = Ta data.qLayer a * data.x := by
  rfl

/-- **`Q_a` restated** (`lem:qa-restated`).

Rewrites the paper's operator `Q_a` in terms of `X_a`, `X`, and `T_a`. -/
lemma qaRestated {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Qa data.qLayer a = (Xa data a)ᴴ * Xa data a ∧
      Qa data.qLayer a = data.xᴴ * Ta data.qLayer a * data.x ∧
      Qa data.qLayer a = (Xa data a)ᴴ * data.x := by
  have hTa : (Ta data.qLayer a)ᴴ = Ta data.qLayer a := by
    simpa [Ta] using ProjMeas.outcome_hermitian data.qLayer.t a
  constructor
  · calc
      Qa data.qLayer a = data.xᴴ * Ta data.qLayer a * data.x := data.qa_eq a
      _ = (Xa data a)ᴴ * Xa data a := by
        symm
        calc
          (Xa data a)ᴴ * Xa data a =
              data.xᴴ * Ta data.qLayer a * (Ta data.qLayer a * data.x) := by
                simp [Xa, Matrix.conjTranspose_mul, hTa, Matrix.mul_assoc]
          _ = data.xᴴ * Ta data.qLayer a * data.x := by
                simpa [Matrix.mul_assoc] using
                  congrArg (fun M => data.xᴴ * (M * data.x)) (data.qLayer.t.proj a)
  · constructor
    · exact data.qa_eq a
    · calc
        Qa data.qLayer a = data.xᴴ * Ta data.qLayer a * data.x := data.qa_eq a
        _ = (Xa data a)ᴴ * data.x := by
          simp [Xa, Matrix.conjTranspose_mul, hTa]

/-- If the original `X` rows are already coisometric and the mixed product
`X† XHat` agrees with the Gram operator `X† X`, then the polar replacement
`XHat` is equal to `X`.

This is the algebraic form of the observation used in the residual-domination
route: on a part where the row block already lies in the unit singular
subspace, the `XHat` replacement does not change it. -/
lemma xHat_eq_x_of_x_mul_conjTranspose_eq_one_of_mixed_eq_gram {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι)
    (hx_left :
      data.x * data.xᴴ =
        (1 : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier))
    (hmixed : data.xᴴ * data.xHat = data.xᴴ * data.x) :
    data.xHat = data.x := by
  calc
    data.xHat =
        (1 : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier) * data.xHat := by
      simp
    _ = (data.x * data.xᴴ) * data.xHat := by rw [hx_left]
    _ = data.x * (data.xᴴ * data.xHat) := by simp [Matrix.mul_assoc]
    _ = data.x * (data.xᴴ * data.x) := by rw [hmixed]
    _ = (data.x * data.xᴴ) * data.x := by simp [Matrix.mul_assoc]
    _ = (1 : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier) * data.x := by
      rw [hx_left]
    _ = data.x := by simp

/-- Row-block form of
`xHat_eq_x_of_x_mul_conjTranspose_eq_one_of_mixed_eq_gram`. -/
lemma xHatA_eq_xa_of_x_mul_conjTranspose_eq_one_of_mixed_eq_gram {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome)
    (hx_left :
      data.x * data.xᴴ =
        (1 : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier))
    (hmixed : data.xᴴ * data.xHat = data.xᴴ * data.x) :
    XHatA data a = Xa data a := by
  rw [XHatA, Xa,
    xHat_eq_x_of_x_mul_conjTranspose_eq_one_of_mixed_eq_gram data hx_left hmixed]

/-- If the original `X` rows are already coisometric, then the polar
replacement `XHat` is equal to `X`.

Indeed, `X X† = I` makes the Gram operator `X† X` idempotent.  Since this Gram
operator is positive, its positive square root is itself; the stored mixed
identity `X† XHat = sqrt (X† X)` therefore reduces to the hypothesis of
`xHat_eq_x_of_x_mul_conjTranspose_eq_one_of_mixed_eq_gram`. -/
lemma xHat_eq_x_of_x_mul_conjTranspose_eq_one {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι)
    (hx_left :
      data.x * data.xᴴ =
        (1 : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier)) :
    data.xHat = data.x := by
  have hgram_sq :
      (data.xᴴ * data.x) * (data.xᴴ * data.x) = data.xᴴ * data.x := by
    calc
      (data.xᴴ * data.x) * (data.xᴴ * data.x) =
          data.xᴴ * (data.x * data.xᴴ) * data.x := by
            simp [Matrix.mul_assoc]
      _ = data.xᴴ *
          ((1 : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier) * data.x) := by
            rw [hx_left]
            simp
      _ = data.xᴴ * data.x := by simp
  have hgram_nonneg : 0 ≤ data.xᴴ * data.x :=
    (Matrix.posSemidef_conjTranspose_mul_self data.x).nonneg
  have hsqrt :
      CFC.sqrt (data.xᴴ * data.x) = data.xᴴ * data.x :=
    CFC.sqrt_unique hgram_sq hgram_nonneg
  have hmixed : data.xᴴ * data.xHat = data.xᴴ * data.x := by
    calc
      data.xᴴ * data.xHat = CFC.sqrt (QTotal data.qLayer) := data.xHat_mixed
      _ = CFC.sqrt (data.xᴴ * data.x) := by rw [← data.x_gram_right]
      _ = data.xᴴ * data.x := hsqrt
  exact xHat_eq_x_of_x_mul_conjTranspose_eq_one_of_mixed_eq_gram data hx_left hmixed

/-- Row-block form of `xHat_eq_x_of_x_mul_conjTranspose_eq_one`. -/
lemma xHatA_eq_xa_of_x_mul_conjTranspose_eq_one {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome)
    (hx_left :
      data.x * data.xᴴ =
        (1 : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier)) :
    XHatA data a = Xa data a := by
  rw [XHatA, Xa, xHat_eq_x_of_x_mul_conjTranspose_eq_one data hx_left]

/-- The total `Q` operator in a QXP layer is Hermitian.

This follows from `lem:X-squared`: the total operator is the right Gram matrix
`X†X`.  The statement gives downstream spectral arguments a canonical
Hermitian witness for `QTotal data.qLayer`. -/
lemma qtotal_isHermitian_of_x_squared {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (QTotal data.qLayer).IsHermitian := by
  rw [← data.x_gram_right]
  exact Matrix.isHermitian_conjTranspose_mul_self data.x

/-- The total `Q` operator in a QXP layer is positive semidefinite.

This is the positivity companion to `qtotal_isHermitian_of_x_squared`; after
`QTotal` is identified with the Gram matrix `X†X`, positivity follows from the
standard Gram-matrix argument. -/
lemma qtotal_posSemidef_of_x_squared {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (QTotal data.qLayer).PosSemidef := by
  rw [← data.x_gram_right]
  exact Matrix.posSemidef_conjTranspose_mul_self data.x

/-- The spectral eigenvalues of the total `Q` operator are nonnegative.

This is the scalar form of `qtotal_posSemidef_of_x_squared` used when the
rectangular polar construction separates the positive and zero spectral
subspaces. -/
lemma qtotal_eigenvalues_nonneg_of_x_squared {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (i : ι) :
    0 ≤ (qtotal_isHermitian_of_x_squared data).eigenvalues i :=
  (qtotal_posSemidef_of_x_squared data).eigenvalues_nonneg i

/-- QXP-layer form of the positive-Gram row extension theorem.

For the matrix `X` stored in a QXP layer, the positive spectral part of
`Q = X†X` determines normalized image rows.  These rows can be placed in
distinct auxiliary coordinates and then completed to a square unitary matrix on
the auxiliary Hilbert space. -/
theorem exists_unitary_with_qxp_positive_gram_spectrum_rows {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    ∃ e : {i : ι // 0 < (qtotal_isHermitian_of_x_squared data).eigenvalues i} ↪
        data.qLayer.auxSpace.carrier,
      ∃ U : Matrix data.qLayer.auxSpace.carrier data.qLayer.auxSpace.carrier ℂ,
        U * Uᴴ =
            (1 : Matrix data.qLayer.auxSpace.carrier data.qLayer.auxSpace.carrier ℂ) ∧
          Uᴴ * U =
            (1 : Matrix data.qLayer.auxSpace.carrier data.qLayer.auxSpace.carrier ℂ) ∧
            ∀ (i : {i : ι // 0 < (qtotal_isHermitian_of_x_squared data).eigenvalues i})
                (r : data.qLayer.auxSpace.carrier),
              U (e i) r =
                positiveGramSpectrumImageRows data.x (QTotal data.qLayer)
                  (qtotal_isHermitian_of_x_squared data) i r := by
  exact exists_unitary_with_positive_gram_spectrum_rows_of_card data.x
    (QTotal data.qLayer) (qtotal_isHermitian_of_x_squared data) data.x_gram_right

/-- **`X`-expression to `Q`-expression** (`lem:X-expression-to-Q-expression`).

Converts the quadratic error term in `X X† - I` to the corresponding
`Q_a Q Q_a - Q_a` expression. -/
lemma xExpressionToQExpression {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    (Xa data a)ᴴ *
        ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1)) *
        Xa data a =
      Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
        Qa data.qLayer a := by
  have hQaSq : Qa data.qLayer a * Qa data.qLayer a = Qa data.qLayer a := by
    exact (data.qa_projective a).idempotent
  have hQaXa : (Xa data a)ᴴ * Xa data a = Qa data.qLayer a := by
    exact (qaRestated data a).1.symm
  have hQaLeft : (Xa data a)ᴴ * data.x = Qa data.qLayer a := by
    exact (qaRestated data a).2.2.symm
  have hQaRight : data.xᴴ * Xa data a = Qa data.qLayer a := by
    simpa [Xa, Matrix.mul_assoc] using (data.qa_eq a).symm
  calc
    (Xa data a)ᴴ *
        ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1)) *
        Xa data a =
      ((Xa data a)ᴴ * ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1))) *
        Xa data a := by
          rw [Matrix.mul_assoc]
    _ = ((Xa data a)ᴴ *
          (data.x * data.xᴴ * (data.x * data.xᴴ) + (-2 • (data.x * data.xᴴ) + 1))) *
        Xa data a := by
          congr 1
          noncomm_ring
    _ =
        (Xa data a)ᴴ * data.x * (data.xᴴ * data.x * (data.xᴴ * Xa data a)) +
          (-2 • ((Xa data a)ᴴ * data.x * (data.xᴴ * Xa data a)) +
            (Xa data a)ᴴ * Xa data a) := by
          rw [Matrix.mul_assoc]
          rw [Matrix.add_mul, Matrix.add_mul]
          rw [Matrix.mul_add, Matrix.mul_add]
          have hneg :
              (Xa data a)ᴴ * ((-(data.x * data.xᴴ) + -(data.x * data.xᴴ)) * Xa data a) =
                -((Xa data a)ᴴ * (data.x * (data.xᴴ * Xa data a))) +
                  -((Xa data a)ᴴ * (data.x * (data.xᴴ * Xa data a))) := by
            rw [Matrix.add_mul]
            rw [Matrix.mul_add]
            simp [Matrix.mul_assoc]
          simp [Matrix.mul_assoc, two_smul, hneg]
    _ = Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
        Qa data.qLayer a := by
      simp only [Matrix.mul_assoc, hQaXa, hQaLeft, hQaRight, data.x_gram_right, hQaSq,
        Int.reduceNeg, neg_smul, zsmul_eq_mul, Int.cast_ofNat]
      noncomm_ring
    _ = Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
        Qa data.qLayer a := by
      noncomm_ring

/-- **`P_a` restated** (`lem:pa-restated`).

Rewrites `P_a` in terms of `XHat`, `XHat_a`, and `T_a`. -/
lemma paRestated {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
      Pa data a = data.xHatᴴ * Ta data.qLayer a * data.xHat ∧
      Pa data a = (XHatA data a)ᴴ * data.xHat := by
  constructor
  · -- The first conjunct is definitional from `Pa`.
    rfl
  · have hTa : (Ta data.qLayer a)ᴴ = Ta data.qLayer a := by
      simpa [Ta] using ProjMeas.outcome_hermitian data.qLayer.t a
    have hXHatA : (XHatA data a)ᴴ = data.xHatᴴ * Ta data.qLayer a := by
      calc
        (XHatA data a)ᴴ = (Ta data.qLayer a * data.xHat)ᴴ := by rfl
        _ = data.xHatᴴ * (Ta data.qLayer a)ᴴ := by
              simp [Matrix.conjTranspose_mul]
        _ = data.xHatᴴ * Ta data.qLayer a := by rw [hTa]
    calc
      Pa data a = data.xHatᴴ * Ta data.qLayer a * data.xHat := by rfl
      _ = (XHatA data a)ᴴ * data.xHat := by rw [hXHatA]

/-- The `P_a` operator is the right Gram matrix of the corresponding
`XHat_a` row block.

This is the row-block form of `paRestated`: the auxiliary projector `T_a` is
idempotent, so inserting the second copy of `T_a` does not change the
operator. -/
lemma pa_eq_xHatA_adjoint_mul_xHatA {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Pa data a = (XHatA data a)ᴴ * XHatA data a := by
  have hTa : (Ta data.qLayer a)ᴴ = Ta data.qLayer a := by
    simpa [Ta] using ProjMeas.outcome_hermitian data.qLayer.t a
  have hTa_proj : Ta data.qLayer a * Ta data.qLayer a = Ta data.qLayer a := by
    simpa [Ta] using data.qLayer.t.proj a
  calc
    Pa data a = data.xHatᴴ * Ta data.qLayer a * data.xHat := by rfl
    _ = data.xHatᴴ * (Ta data.qLayer a * Ta data.qLayer a) * data.xHat := by
          rw [hTa_proj]
    _ = (XHatA data a)ᴴ * XHatA data a := by
          simp [XHatA, Matrix.conjTranspose_mul, hTa, Matrix.mul_assoc]

/-- If the `XHat` construction preserves one row block, then the corresponding
`Q` and `P` outcomes agree.

This lemma isolates the construction-level obligation needed for the fresh
outcome in the option-completed orthonormalization step. -/
lemma qa_eq_pa_of_xHatA_eq_xa {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome)
    (hrow : XHatA data a = Xa data a) :
    Qa data.qLayer a = Pa data a := by
  calc
    Qa data.qLayer a = (Xa data a)ᴴ * Xa data a := (qaRestated data a).1
    _ = (XHatA data a)ᴴ * XHatA data a := by rw [hrow]
    _ = Pa data a := (pa_eq_xHatA_adjoint_mul_xHatA data a).symm

/-- Fresh-outcome domination follows from preservation of the fresh row block
in the option-completed QXP layer.

The remaining construction-level task for the monotone-total route is thus
reduced to proving `XHat_none = X_none` for the concrete positive-Gram
construction of `XHat`. -/
lemma fresh_outcome_le_of_xHatA_eq_xa {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData (Option Outcome) ι)
    (hrow : XHatA data none = Xa data none) :
    data.qLayer.q.outcome none ≤ Pa data none :=
  le_of_eq (qa_eq_pa_of_xHatA_eq_xa data none hrow)

private lemma xHat_mixed_adjoint {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    data.xHatᴴ * data.x = CFC.sqrt (QTotal data.qLayer) := by
  calc
    data.xHatᴴ * data.x = (data.xᴴ * data.xHat)ᴴ := by
      simp [Matrix.conjTranspose_mul]
    _ = (CFC.sqrt (QTotal data.qLayer))ᴴ := by rw [data.xHat_mixed]
    _ = CFC.sqrt (QTotal data.qLayer) := by
      simpa using
        (Matrix.nonneg_iff_posSemidef.mp
          (CFC.sqrt_nonneg (QTotal data.qLayer))).isHermitian.eq

private lemma xxHat_isHermitian {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (data.x * data.xHatᴴ)ᴴ = data.x * data.xHatᴴ := by
  calc
    (data.x * data.xHatᴴ)ᴴ = data.xHat * data.xᴴ := by
      simp [Matrix.conjTranspose_mul]
    _ = data.xHat * (data.xᴴ * data.xHat) * data.xHatᴴ := by
      calc
        data.xHat * data.xᴴ = data.xHat * (data.xᴴ * (data.xHat * data.xHatᴴ)) := by
          rw [data.xHat_coisometry]
          simp
        _ = data.xHat * (data.xᴴ * data.xHat) * data.xHatᴴ := by
          simp [Matrix.mul_assoc]
    _ = data.xHat * (data.xHatᴴ * data.x) * data.xHatᴴ := by
      rw [data.xHat_mixed, ← xHat_mixed_adjoint data]
    _ = (data.xHat * data.xHatᴴ) * data.x * data.xHatᴴ := by
      simp [Matrix.mul_assoc]
    _ = data.x * data.xHatᴴ := by
      simp [data.xHat_coisometry]

private lemma xxHat_sq {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (data.x * data.xHatᴴ) * (data.x * data.xHatᴴ) = data.x * data.xᴴ := by
  calc
    (data.x * data.xHatᴴ) * (data.x * data.xHatᴴ)
        = data.x * (data.xHatᴴ * data.x) * data.xHatᴴ := by
            simp [Matrix.mul_assoc]
    _ = data.x * (data.xᴴ * data.xHat) * data.xHatᴴ := by
          rw [xHat_mixed_adjoint data, data.xHat_mixed]
    _ = data.x * data.xᴴ := by
          simp [Matrix.mul_assoc, data.xHat_coisometry]

private lemma xxHat_nonneg {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    0 ≤ data.x * data.xHatᴴ := by
  have hsqrt_nonneg : 0 ≤ CFC.sqrt (QTotal data.qLayer) :=
    CFC.sqrt_nonneg (QTotal data.qLayer)
  calc
    0 ≤ data.xHat * CFC.sqrt (QTotal data.qLayer) * data.xHatᴴ := by
      exact
        (Matrix.PosSemidef.mul_mul_conjTranspose_same
          (Matrix.nonneg_iff_posSemidef.mp hsqrt_nonneg)
          data.xHat).nonneg
    _ = data.xHat * (data.xHatᴴ * data.x) * data.xHatᴴ := by
      rw [← xHat_mixed_adjoint data]
    _ = (data.xHat * data.xHatᴴ) * data.x * data.xHatᴴ := by
      simp [Matrix.mul_assoc]
    _ = data.x * data.xHatᴴ := by
      simp [data.xHat_coisometry]

/-- The adjoint mixed product `Xhat† X` equals the positive square root of
`Q`.

This is the adjoint form of the stored identity `X† Xhat = sqrt Q`.  It is
used to identify the operator `Y = X Xhat†` in the proof of
`lem:squared-difference`. -/
lemma xHat_adjoint_mul_x_eq_sqrt {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    data.xHatᴴ * data.x = CFC.sqrt (QTotal data.qLayer) :=
  xHat_mixed_adjoint data

/-- The operator `X Xhat†` is Hermitian in a QXP layer. -/
lemma x_mul_xHat_adjoint_isHermitian {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (data.x * data.xHatᴴ)ᴴ = data.x * data.xHatᴴ :=
  xxHat_isHermitian data

/-- The square of `X Xhat†` is `X X†` in a QXP layer. -/
lemma x_mul_xHat_adjoint_sq {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (data.x * data.xHatᴴ) * (data.x * data.xHatᴴ) = data.x * data.xᴴ :=
  xxHat_sq data

/-- The operator `X Xhat†` is positive semidefinite in a QXP layer. -/
lemma x_mul_xHat_adjoint_nonneg {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    0 ≤ data.x * data.xHatᴴ :=
  xxHat_nonneg data

/-- **Squared difference** (`lem:squared-difference`).

Bounds the defect between `X` and `XHat` by the squared defect of `X X†`
from the auxiliary identity. -/
lemma squaredDifference {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (data.x - data.xHat) * (data.x - data.xHat)ᴴ ≤
      (data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1) := by
  let Y : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier := data.x * data.xHatᴴ
  have hY_sub :
      (data.x - data.xHat) * (data.x - data.xHat)ᴴ = (Y - 1) * (Y - 1) := by
    have hYh : Yᴴ = Y := by
      simpa [Y] using x_mul_xHat_adjoint_isHermitian data
    have hYadj : data.xHat * data.xᴴ = Y := by
      simpa [Y, Matrix.conjTranspose_mul] using hYh
    have hYsq : data.x * data.xᴴ = Y * Y := by
      simpa [Y] using (x_mul_xHat_adjoint_sq data).symm
    calc
      (data.x - data.xHat) * (data.x - data.xHat)ᴴ
          = (data.x - data.xHat) * (data.xᴴ - data.xHatᴴ) := by
              simp
      _ = data.x * (data.xᴴ - data.xHatᴴ) - data.xHat * (data.xᴴ - data.xHatᴴ) := by
            conv_lhs => rw [Matrix.sub_mul]
      _ = (data.x * data.xᴴ - data.x * data.xHatᴴ) -
            (data.xHat * data.xᴴ - data.xHat * data.xHatᴴ) := by
              conv_lhs => rw [Matrix.mul_sub, Matrix.mul_sub]
      _ = data.x * data.xᴴ - data.x * data.xHatᴴ - data.xHat * data.xᴴ +
            data.xHat * data.xHatᴴ := by
              abel
      _ = data.x * data.xᴴ - Y - Y + 1 := by
            simp [Y, hYadj, data.xHat_coisometry]
      _ = Y * Y - Y - Y + 1 := by rw [hYsq]
      _ = (Y - 1) * (Y - 1) := by
            noncomm_ring
  have hY_nonneg : 0 ≤ Y := by
    simpa [Y] using x_mul_xHat_adjoint_nonneg data
  have hYsq :
      Y * Y = data.x * data.xᴴ := by
    simpa [Y] using x_mul_xHat_adjoint_sq data
  have hY_herm : Yᴴ = Y := by
    simpa [Y] using x_mul_xHat_adjoint_isHermitian data
  have hYm1_herm : (Y - 1)ᴴ = Y - 1 := by
    simp [hY_herm]
  have hYp1_nonneg : 0 ≤ Y + 1 := add_nonneg hY_nonneg zero_le_one
  have hYp1_comm : Commute (Y + 1) Y := by
    change (Y + 1) * Y = Y * (Y + 1)
    simp [mul_add, add_mul]
  have hYp1_mul_nonneg : 0 ≤ (Y + 1) * Y := by
    exact Commute.mul_nonneg hYp1_nonneg hY_nonneg hYp1_comm
  have h_one_le_sq :
      (1 : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier) ≤ (Y + 1) * (Y + 1) := by
    have hYp1_le_sq : Y + 1 ≤ (Y + 1) * (Y + 1) := by
      apply sub_nonneg.mp
      calc
        (Y + 1) * (Y + 1) - (Y + 1) = (Y + 1) * ((Y + 1) - 1) := by
          rw [mul_sub]
          simp
        _ = (Y + 1) * Y := by simp
        _ ≥ 0 := hYp1_mul_nonneg
    exact le_trans (by simpa using add_le_add_right hY_nonneg 1) hYp1_le_sq
  have h_main :
      (Y - 1) * (Y - 1) ≤ (Y - 1) * ((Y + 1) * (Y + 1)) * (Y - 1) := by
    simpa [Matrix.mul_assoc] using
      MIPStarRE.Quantum.sandwich_mono (M := Y - 1) hYm1_herm h_one_le_sq
  have h_comm_pm : Commute (Y - 1) (Y + 1) := by
    change (Y - 1) * (Y + 1) = (Y + 1) * (Y - 1)
    simp [sub_eq_add_neg, mul_add, add_mul, add_assoc, add_left_comm, add_comm]
  calc
    (data.x - data.xHat) * (data.x - data.xHat)ᴴ = (Y - 1) * (Y - 1) := hY_sub
    _ ≤ (Y - 1) * ((Y + 1) * (Y + 1)) * (Y - 1) := h_main
    _ = ((Y - 1) * (Y + 1)) * ((Y - 1) * (Y + 1)) := by
          rw [← Matrix.mul_assoc, h_comm_pm.eq, Matrix.mul_assoc, Matrix.mul_assoc]
    _ = (Y * Y - 1) * (Y * Y - 1) := by
          congr 1 <;> noncomm_ring
    _ = (data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1) := by simp [hYsq]

/-- The sum of the QXP `P`-operators is the Gram operator `XHat† XHat`.

This is the total-mass identity for the canonical projective submeasurement
produced from the Q/X/XHat/P layer. -/
lemma sum_pa_eq_xHat_adjoint_mul_xHat {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (∑ a, Pa data a) = data.xHatᴴ * data.xHat := by
  classical
  have hsum_aux (s : Finset Outcome) :
      Finset.sum s (fun a => Pa data a) =
        data.xHatᴴ * (Finset.sum s fun a => Ta data.qLayer a) * data.xHat := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
        simp [Pa, Matrix.mul_assoc, Matrix.add_mul, Matrix.mul_add]
  calc
    (∑ a, Pa data a) = data.xHatᴴ * (∑ a, Ta data.qLayer a) * data.xHat := by
      simpa using hsum_aux Finset.univ
    _ = data.xHatᴴ * data.xHat := by
      simpa [Ta] using
        congrArg (fun M => data.xHatᴴ * M * data.xHat) data.qLayer.t.sum_eq

/-- **Projectivity of `P`** (`lem:P-projectivity`).

The family `P_a` built from `XHat` and `T_a` is a projective
submeasurement. -/
lemma pProjectivity {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    ∃ P : ProjSubMeas Outcome ι,
      ∀ a : Outcome, P.outcome a = Pa data a := by
  classical
  refine ⟨{
    outcome := Pa data
    total := ∑ a, Pa data a
    outcome_pos := ?_
    sum_eq_total := by simp
    total_le_one := ?_
    proj := ?_
  }, ?_⟩
  · intro a
    exact
      (Matrix.PosSemidef.conjTranspose_mul_mul_same
        (Matrix.nonneg_iff_posSemidef.mp (data.qLayer.t.toMeasurement.outcome_pos a))
        data.xHat).nonneg
  · let X : MIPStarRE.Quantum.Op ι := data.xHatᴴ * data.xHat
    have hX_sq : X * X = X := by
      dsimp [X]
      calc
        (data.xHatᴴ * data.xHat) * (data.xHatᴴ * data.xHat)
            = data.xHatᴴ * (data.xHat * data.xHatᴴ) * data.xHat := by
                simp [Matrix.mul_assoc]
        _ = data.xHatᴴ * data.xHat := by
              simp [data.xHat_coisometry]
    have hX_herm : Xᴴ = X := by
      dsimp [X]
      simp [Matrix.conjTranspose_mul]
    have hX_proj : MIPStarRE.Quantum.IsProj X :=
      { isHermitian := hX_herm
        idempotent := hX_sq }
    have h_one_sub_X_nonneg : 0 ≤ 1 - X := by
      exact hX_proj.isStarProjection.one_sub_nonneg
    have hsum :
        (∑ a, Pa data a) = X := by
      simpa [X] using sum_pa_eq_xHat_adjoint_mul_xHat data
    rw [hsum]
    exact sub_nonneg.mp h_one_sub_X_nonneg
  · intro a
    calc
      Pa data a * Pa data a
          = data.xHatᴴ * Ta data.qLayer a * (data.xHat * data.xHatᴴ) *
              Ta data.qLayer a * data.xHat := by
                simp [Pa, Matrix.mul_assoc]
      _ = data.xHatᴴ * Ta data.qLayer a * Ta data.qLayer a * data.xHat := by
            simp [data.xHat_coisometry, Matrix.mul_assoc]
      _ = data.xHatᴴ * Ta data.qLayer a * data.xHat := by
            simp [Ta, data.qLayer.t.proj a, Matrix.mul_assoc]
      _ = Pa data a := rfl
  · intro a
    rfl

/-- The canonical projective submeasurement obtained from the Q/X/XHat/P
layer. Its outcomes are the paper's operators `P_a`. -/
noncomputable def qxpProjSubMeas {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    ProjSubMeas Outcome ι :=
  Classical.choose (pProjectivity data)

@[simp] lemma qxpProjSubMeas_outcome {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    (qxpProjSubMeas data).outcome a = Pa data a :=
  Classical.choose_spec (pProjectivity data) a

/-- The total of the canonical QXP projective submeasurement is `XHat† XHat`.

This exposes the total-mass identity implicit in `pProjectivity`, which is
needed when comparing the repaired projective family to the source
submeasurement in later monotonicity arguments. -/
lemma qxpProjSubMeas_total_eq_xHat_adjoint_mul_xHat {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (qxpProjSubMeas data).toSubMeas.total = data.xHatᴴ * data.xHat := by
  calc
    (qxpProjSubMeas data).toSubMeas.total
        = ∑ a, (qxpProjSubMeas data).outcome a :=
            (qxpProjSubMeas data).sum_eq_total.symm
    _ = ∑ a, Pa data a := by
          simp [qxpProjSubMeas_outcome]
    _ = data.xHatᴴ * data.xHat := sum_pa_eq_xHat_adjoint_mul_xHat data

/-- The expectation of the QXP projective total is the sum of the expectations
of the paper projectors `P_a`. -/
lemma qxpProjSubMeas_total_ev_eq_sum_pa_ev {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (ψ : QuantumState ι) :
    ev ψ (qxpProjSubMeas data).toSubMeas.total =
      ∑ a : Outcome, ev ψ (Pa data a) := by
  calc
    ev ψ (qxpProjSubMeas data).toSubMeas.total
        = ev ψ (∑ a, (qxpProjSubMeas data).outcome a) := by
            rw [(qxpProjSubMeas data).sum_eq_total]
    _ = ∑ a : Outcome, ev ψ ((qxpProjSubMeas data).outcome a) := ev_sum ψ _
    _ = ∑ a : Outcome, ev ψ (Pa data a) := by
          simp [qxpProjSubMeas_outcome]

/-- Outcomewise domination of the QXP projectors implies domination of the
total operator.

This is the summation form of the monotone-total invariant needed downstream:
once the concrete repair proves `P_a ≤ A_a` for every outcome, the canonical
QXP projective total is bounded by the source submeasurement total. -/
lemma qxpProjSubMeas_total_le_of_outcome_le {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (A : SubMeas Outcome ι)
    (hpoint : ∀ a : Outcome, Pa data a ≤ A.outcome a) :
    (qxpProjSubMeas data).toSubMeas.total ≤ A.total := by
  calc
    (qxpProjSubMeas data).toSubMeas.total
        = ∑ a, (qxpProjSubMeas data).outcome a :=
            (qxpProjSubMeas data).sum_eq_total.symm
    _ = ∑ a, Pa data a := by
          simp [qxpProjSubMeas_outcome]
    _ ≤ ∑ a, A.outcome a := Finset.sum_le_sum fun a _ => hpoint a
    _ = A.total := A.sum_eq_total

/-- Expectation form of a supplied QXP total-operator comparison. -/
private lemma qxpProjSubMeas_total_ev_le_of_total_le {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (data : QXPLayerData Outcome ι) (A : SubMeas Outcome ι)
    (hTotal : (qxpProjSubMeas data).toSubMeas.total ≤ A.total) :
    ev ψ (qxpProjSubMeas data).toSubMeas.total ≤ ev ψ A.total :=
  ev_mono ψ _ _ hTotal

/-- Right-register expectation form of a supplied QXP total-operator comparison. -/
private lemma qxpProjSubMeas_rightTensor_total_ev_le_of_total_le {Outcome : Type*}
    {ιLeft ι : Type*} [Fintype ιLeft] [DecidableEq ιLeft]
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ιLeft × ι))
    (data : QXPLayerData Outcome ι) (A : SubMeas Outcome ι)
    (hTotal : (qxpProjSubMeas data).toSubMeas.total ≤ A.total) :
    ev ψ (rightTensor (ι₁ := ιLeft) (qxpProjSubMeas data).toSubMeas.total) ≤
      ev ψ (rightTensor (ι₁ := ιLeft) A.total) :=
  ev_mono ψ _ _ <| rightTensor_mono hTotal

/-- Left-register expectation form of a supplied QXP total-operator comparison. -/
private lemma qxpProjSubMeas_leftTensor_total_ev_le_of_total_le {Outcome : Type*}
    {ι ιRight : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ιRight] [DecidableEq ιRight] [Fintype Outcome]
    (ψ : QuantumState (ι × ιRight))
    (data : QXPLayerData Outcome ι) (A : SubMeas Outcome ι)
    (hTotal : (qxpProjSubMeas data).toSubMeas.total ≤ A.total) :
    ev ψ (leftTensor (ι₂ := ιRight) (qxpProjSubMeas data).toSubMeas.total) ≤
      ev ψ (leftTensor (ι₂ := ιRight) A.total) :=
  ev_mono ψ _ _ <| leftTensor_mono hTotal

/-- Outcomewise domination of the QXP projectors gives the corresponding scalar
expectation comparison for the total operator. -/
lemma qxpProjSubMeas_total_ev_le_of_outcome_le {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (data : QXPLayerData Outcome ι) (A : SubMeas Outcome ι)
    (hpoint : ∀ a : Outcome, Pa data a ≤ A.outcome a) :
    ev ψ (qxpProjSubMeas data).toSubMeas.total ≤ ev ψ A.total :=
  qxpProjSubMeas_total_ev_le_of_total_le ψ data A
    (qxpProjSubMeas_total_le_of_outcome_le data A hpoint)

/-- Outcomewise domination of the QXP projectors gives the corresponding
right-register expectation comparison.

The proof is only the operator inequality from
`qxpProjSubMeas_total_le_of_outcome_le`, followed by monotonicity of right
tensor placement and of the state expectation. -/
lemma qxpProjSubMeas_rightTensor_total_ev_le_of_outcome_le {Outcome : Type*}
    {ιLeft ι : Type*} [Fintype ιLeft] [DecidableEq ιLeft]
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ιLeft × ι))
    (data : QXPLayerData Outcome ι) (A : SubMeas Outcome ι)
    (hpoint : ∀ a : Outcome, Pa data a ≤ A.outcome a) :
    ev ψ (rightTensor (ι₁ := ιLeft) (qxpProjSubMeas data).toSubMeas.total) ≤
      ev ψ (rightTensor (ι₁ := ιLeft) A.total) :=
  qxpProjSubMeas_rightTensor_total_ev_le_of_total_le ψ data A
    (qxpProjSubMeas_total_le_of_outcome_le data A hpoint)

/-- Outcomewise domination of the QXP projectors gives the corresponding
left-register expectation comparison.

The proof is the same operator comparison as in
`qxpProjSubMeas_total_le_of_outcome_le`, transported through left tensor
placement and then evaluated in the ambient state. -/
lemma qxpProjSubMeas_leftTensor_total_ev_le_of_outcome_le {Outcome : Type*}
    {ι ιRight : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ιRight] [DecidableEq ιRight] [Fintype Outcome]
    (ψ : QuantumState (ι × ιRight))
    (data : QXPLayerData Outcome ι) (A : SubMeas Outcome ι)
    (hpoint : ∀ a : Outcome, Pa data a ≤ A.outcome a) :
    ev ψ (leftTensor (ι₂ := ιRight) (qxpProjSubMeas data).toSubMeas.total) ≤
      ev ψ (leftTensor (ι₂ := ιRight) A.total) :=
  qxpProjSubMeas_leftTensor_total_ev_le_of_total_le ψ data A
    (qxpProjSubMeas_total_le_of_outcome_le data A hpoint)

/-- Total-domination invariant for the QXP repair.

This proposition is the construction-level operator comparison required by the
paper-tight monotone-total route: the canonical projective family obtained from
the QXP layer has total operator bounded by the source submeasurement total.
It is deliberately stronger than state-dependent-distance closeness and should
be proved from the concrete repair, not inferred from the orthonormalization
error estimate alone. -/
structure QXPLayerTotalDomination {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (A : SubMeas Outcome ι) : Prop where
  /-- The projective QXP total is bounded by the source submeasurement total. -/
  total_le : (qxpProjSubMeas data).toSubMeas.total ≤ A.total

namespace QXPLayerTotalDomination

/-- Outcomewise operator domination is a sufficient way to prove the QXP
total-domination invariant. -/
theorem of_outcome_le {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    {data : QXPLayerData Outcome ι} {A : SubMeas Outcome ι}
    (hpoint : ∀ a : Outcome, Pa data a ≤ A.outcome a) :
    QXPLayerTotalDomination data A where
  total_le := qxpProjSubMeas_total_le_of_outcome_le data A hpoint

/-- A QXP total-domination witness gives the scalar expectation comparison for
the total operators. -/
theorem ev_total_le {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    {ψ : QuantumState ι}
    {data : QXPLayerData Outcome ι} {A : SubMeas Outcome ι}
    (hdom : QXPLayerTotalDomination data A) :
    ev ψ (qxpProjSubMeas data).toSubMeas.total ≤ ev ψ A.total :=
  qxpProjSubMeas_total_ev_le_of_total_le ψ data A hdom.total_le

/-- A QXP total-domination witness gives the scalar right-register comparison
used by the final-fields transport. -/
theorem rightTensor_total_ev_le {Outcome : Type*}
    {ιLeft ι : Type*} [Fintype ιLeft] [DecidableEq ιLeft]
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    {ψ : QuantumState (ιLeft × ι)}
    {data : QXPLayerData Outcome ι} {A : SubMeas Outcome ι}
    (hdom : QXPLayerTotalDomination data A) :
    ev ψ (rightTensor (ι₁ := ιLeft) (qxpProjSubMeas data).toSubMeas.total) ≤
      ev ψ (rightTensor (ι₁ := ιLeft) A.total) :=
  qxpProjSubMeas_rightTensor_total_ev_le_of_total_le ψ data A hdom.total_le

/-- A QXP total-domination witness gives the scalar left-register comparison. -/
theorem leftTensor_total_ev_le {Outcome : Type*}
    {ι ιRight : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ιRight] [DecidableEq ιRight] [Fintype Outcome]
    {ψ : QuantumState (ι × ιRight)}
    {data : QXPLayerData Outcome ι} {A : SubMeas Outcome ι}
    (hdom : QXPLayerTotalDomination data A) :
    ev ψ (leftTensor (ι₂ := ιRight) (qxpProjSubMeas data).toSubMeas.total) ≤
      ev ψ (leftTensor (ι₂ := ιRight) A.total) :=
  qxpProjSubMeas_leftTensor_total_ev_le_of_total_le ψ data A hdom.total_le

end QXPLayerTotalDomination

end

end MIPStarRE.LDT.MakingMeasurementsProjective
