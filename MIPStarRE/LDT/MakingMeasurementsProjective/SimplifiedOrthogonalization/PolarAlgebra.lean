import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.PolarExtension

/-!
# Algebra of the polar-coordinate construction

These identities isolate the operator algebra used after the global rank
allocation.  They apply to any square polar factor and coordinate projection.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`,
  `eq:polar-coordinate-identity` and `eq:orthogonalization-decomposition`.
- `references/ldt-paper/orthonormalization.tex`, Section 5.
-/

open scoped MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

/-- The coordinate compression identity for a square polar factor `X = U T`
with self-adjoint positive part `T`. -/
theorem polar_coordinate_identity {ι : Type*} [Fintype ι]
    (X U T E : Matrix ι ι ℂ) (hX : X = U * T) (hT : Tᴴ = T) :
    T * (Uᴴ * E * U) * T = Xᴴ * E * X := by
  rw [hX, Matrix.conjTranspose_mul, hT]
  noncomm_ring

/-- Exact decomposition of the rounded effect error, using the compression
identity `T P T = Q M`. -/
theorem orthogonalization_decomposition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M Q P T : Matrix ι ι ℂ) (hcompression : T * P * T = Q * M) :
    M - P = (1 - Q) * M + (T - 1) * P * T + P * (T - 1) := by
  calc
    M - P = (1 - Q) * M + Q * M - P := by noncomm_ring
    _ = (1 - Q) * M + T * P * T - P := by rw [hcompression]
    _ = (1 - Q) * M + (T - 1) * P * T + P * (T - 1) := by noncomm_ring

/-- The compressed square defect is the difference between a compressed
operator and its square. -/
theorem compressed_square_defect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T P : Matrix ι ι ℂ) (hP : P * P = P) :
    T * P * (1 - T * T) * P * T =
      T * P * T - (T * P * T) * (T * P * T) := by
  calc
    T * P * (1 - T * T) * P * T =
        T * (P * P) * T - (T * P * T) * (T * P * T) := by noncomm_ring
    _ = T * P * T - (T * P * T) * (T * P * T) := by rw [hP]

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
