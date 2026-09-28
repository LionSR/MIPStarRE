import MIPStarRE.LDT.Test.MainTheorem.Simplified.Rounding

/-!
# Point-rounding operator estimate

The estimate is the two-vector squared triangle inequality applied after
filtering one tensor factor by a projector. It keeps the rounding error
linear, as required for the simplified final exponent.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of `thm:main-formal`,
  paragraph following equation `short-rounding-error`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Test

/-- A left projective filter does not increase right-register squared
distance. The first right effect is arbitrary, while the second is
projective. -/
theorem projective_filter_rounding_bound
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (P : MIPStarRE.Quantum.Op ιA)
    (G Q : MIPStarRE.Quantum.Op ιB)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hPproj : P * P = P)
    (hG0 : 0 ≤ G) (hG1 : G ≤ 1)
    (hQ0 : 0 ≤ Q) (hQproj : Q * Q = Q) :
    ev ψ (opTensor P Q) ≤
      2 * (ev ψ (opTensor P G) +
        ev ψ ((rightTensor (ι₁ := ιA) (Q - G))ᴴ *
          rightTensor (ι₁ := ιA) (Q - G))) := by
  let X : MIPStarRE.Quantum.Op (ιA × ιB) := opTensor P Q
  let Y : MIPStarRE.Quantum.Op (ιA × ιB) := opTensor P G
  have hX0 : 0 ≤ X := opTensor_nonneg hP0 hQ0
  have hY0 : 0 ≤ Y := opTensor_nonneg hP0 hG0
  have hXproj : X * X = X := by
    simp [X, opTensor_mul, hPproj, hQproj]
  have hPself : Pᴴ = P := by simpa using hP0.isHermitian.eq
  have hGself : Gᴴ = G := by simpa using hG0.isHermitian.eq
  have hQself : Qᴴ = Q := by simpa using hQ0.isHermitian.eq
  have hXself : Xᴴ = X := by simpa using hX0.isHermitian.eq
  have hYself : Yᴴ = Y := by simpa using hY0.isHermitian.eq
  have hXnorm : ev ψ ((X - 0)ᴴ * (X - 0)) = ev ψ X := by
    simp [hXself, hXproj]
  have hYnorm : ev ψ ((Y - 0)ᴴ * (Y - 0)) ≤ ev ψ Y := by
    simpa [Y, hYself, opTensor_mul, hPproj] using
      (ev_mono ψ (opTensor P (G * G)) (opTensor P G)
        (opTensor_mono_right hP0 (MIPStarRE.Quantum.sq_le_self hG0 hG1)))
  have hD0 : 0 ≤ (Q - G) * (Q - G) := by
    have hD : (Q - G)ᴴ = Q - G := by
      simp [hQself, hGself]
    simpa only [hD] using
      (Matrix.posSemidef_conjTranspose_mul_self (Q - G)).nonneg
  have hdiff : X - Y = opTensor P (Q - G) := by
    simpa only [X, Y, opTensor] using
      (MIPStarRE.Quantum.kronecker_sub_right (A := P) (B₁ := Q) (B₂ := G))
  have hdiffNorm :
      ev ψ ((X - Y)ᴴ * (X - Y)) ≤
        ev ψ ((rightTensor (ι₁ := ιA) (Q - G))ᴴ *
          rightTensor (ι₁ := ιA) (Q - G)) := by
    rw [hdiff]
    have hD : (Q - G)ᴴ = Q - G := by
      simp [hQself, hGself]
    have hleft :
        (opTensor P (Q - G))ᴴ * opTensor P (Q - G) =
          opTensor P ((Q - G) * (Q - G)) := by
      have hconj : (opTensor P (Q - G))ᴴ = opTensor Pᴴ (Q - G)ᴴ :=
        Matrix.conjTranspose_kronecker P (Q - G)
      rw [hconj, hPself, hD, opTensor_mul, hPproj]
    have hright :
        (rightTensor (ι₁ := ιA) (Q - G))ᴴ *
          rightTensor (ι₁ := ιA) (Q - G) =
          rightTensor (ι₁ := ιA) ((Q - G) * (Q - G)) := by
      rw [rightTensor_conjTranspose, hD, rightTensor_mul_rightTensor]
    rw [hleft, hright]
    exact ev_mono ψ _ _ (opTensor_mono_left hP1 hD0)
  have htriangle := ev_diff_triangle ψ X Y 0
  rw [hXnorm] at htriangle
  nlinarith

/-- The tensor-reversed filter estimate for rounding a left-register
measurement against a right-register projective point outcome. -/
theorem projective_filter_rounding_bound_left
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (P : MIPStarRE.Quantum.Op ιB)
    (G Q : MIPStarRE.Quantum.Op ιA)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hPproj : P * P = P)
    (hG0 : 0 ≤ G) (hG1 : G ≤ 1)
    (hQ0 : 0 ≤ Q) (hQproj : Q * Q = Q) :
    ev ψ (opTensor Q P) ≤
      2 * (ev ψ (opTensor G P) +
        ev ψ ((leftTensor (ι₂ := ιB) (Q - G))ᴴ *
          leftTensor (ι₂ := ιB) (Q - G))) := by
  let X : MIPStarRE.Quantum.Op (ιA × ιB) := opTensor Q P
  let Y : MIPStarRE.Quantum.Op (ιA × ιB) := opTensor G P
  have hX0 : 0 ≤ X := opTensor_nonneg hQ0 hP0
  have hY0 : 0 ≤ Y := opTensor_nonneg hG0 hP0
  have hXproj : X * X = X := by
    simp [X, opTensor_mul, hPproj, hQproj]
  have hGself : Gᴴ = G := by simpa using hG0.isHermitian.eq
  have hQself : Qᴴ = Q := by simpa using hQ0.isHermitian.eq
  have hXself : Xᴴ = X := by simpa using hX0.isHermitian.eq
  have hYself : Yᴴ = Y := by simpa using hY0.isHermitian.eq
  have hXnorm : ev ψ ((X - 0)ᴴ * (X - 0)) = ev ψ X := by
    simp [hXself, hXproj]
  have hYnorm : ev ψ ((Y - 0)ᴴ * (Y - 0)) ≤ ev ψ Y := by
    simpa [Y, hYself, opTensor_mul, hPproj] using
      (ev_mono ψ (opTensor (G * G) P) (opTensor G P)
        (opTensor_mono_left (MIPStarRE.Quantum.sq_le_self hG0 hG1) hP0))
  have hD : (Q - G)ᴴ = Q - G := by
    simp [hQself, hGself]
  have hD0 : 0 ≤ (Q - G) * (Q - G) := by
    simpa only [hD] using
      (Matrix.posSemidef_conjTranspose_mul_self (Q - G)).nonneg
  have hdiff : X - Y = opTensor (Q - G) P := by
    simpa only [X, Y] using opTensor_sub_left Q G P
  have hdiffNorm :
      ev ψ ((X - Y)ᴴ * (X - Y)) ≤
        ev ψ ((leftTensor (ι₂ := ιB) (Q - G))ᴴ *
          leftTensor (ι₂ := ιB) (Q - G)) := by
    rw [hdiff]
    have hconj : (opTensor (Q - G) P)ᴴ = opTensor (Q - G)ᴴ Pᴴ :=
      Matrix.conjTranspose_kronecker (Q - G) P
    have hPself : Pᴴ = P := by simpa using hP0.isHermitian.eq
    have hleft :
        (opTensor (Q - G) P)ᴴ * opTensor (Q - G) P =
          opTensor ((Q - G) * (Q - G)) P := by
      rw [hconj, hPself, hD, opTensor_mul, hPproj]
    have hright :
        (leftTensor (ι₂ := ιB) (Q - G))ᴴ *
          leftTensor (ι₂ := ιB) (Q - G) =
          leftTensor (ι₂ := ιB) ((Q - G) * (Q - G)) := by
      rw [leftTensor_conjTranspose, hD, leftTensor_mul_leftTensor]
    rw [hleft, hright]
    exact ev_mono ψ _ _ (opTensor_mono_right hD0 hP1)
  have htriangle := ev_diff_triangle ψ X Y 0
  rw [hXnorm] at htriangle
  nlinarith

end MIPStarRE.LDT.Test
