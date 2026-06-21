import MIPStarRE.LDT.SelfImprovement.MatrixRealization.Base

/-!
# Section 9 — Canonical matrix SDP primal block form

This module contains the canonical block Hilbert space, diagonal-block
operators, primal slack block, and extraction of paper primal submeasurements
from feasible canonical primal matrices.

## References

- `references/ldt-paper/self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder


/-- The block index set for the canonical primal SDP.

The `some g` blocks carry the primal operators `T_g`.  The `none` block is the
slack block `S` in the canonical equality constraint
`∑_g T_g + S = I`. -/
abbrev MatrixSdpCanonicalBlockIndex (params : Parameters) [FieldModel params.q] :=
  Option (Polynomial params)

/-- The finite Hilbert space carrying the canonical block primal variable. -/
noncomputable def matrixSdpCanonicalBlockHilbertSpace (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) : FiniteHilbertSpace where
  carrier := MatrixSdpCanonicalBlockIndex params × model.space.carrier
  instFintype := inferInstance
  instDecidableEq := inferInstance
  instNonempty := inferInstance

/-- The diagonal block of a canonical primal matrix. -/
def matrixSdpCanonicalDiagonalBlock (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (b : MatrixSdpCanonicalBlockIndex params) : MatrixOperator model.space :=
  fun i j => X (b, i) (b, j)

/-- The operator-valued canonical equality constraint `∑_b X_{bb} = I`.

The paper states the same constraint as the scalar family
`Tr(D_{ij}^† X) = b_{ij}` for all matrix units `D_{ij}` and then identifies it
with the operator equation `∑_b X_{bb} = I`. This definition records the
left-hand operator of that equivalent equation. -/
noncomputable def matrixSdpCanonicalConstraintOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    MatrixOperator model.space :=
  ∑ b : MatrixSdpCanonicalBlockIndex params,
    matrixSdpCanonicalDiagonalBlock params model X b

/-- The block-diagonal matrix with prescribed diagonal blocks. -/
noncomputable def matrixSdpCanonicalBlockDiagonal (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) :=
  Matrix.reindex
    (Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params))
    (Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params))
    (Matrix.blockDiagonal B)

/-- The canonical SDP block layout is the Mathlib block-diagonal layout after
commuting the matrix-space index with the block index. -/
theorem matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) :
    matrixSdpCanonicalBlockDiagonal params model B =
      Matrix.reindex
        (Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params))
        (Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params))
        (Matrix.blockDiagonal B) :=
  rfl

/-- The canonical block-diagonal construction sends the zero family to the zero
operator. -/
@[simp] theorem matrixSdpCanonicalBlockDiagonal_zero
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    matrixSdpCanonicalBlockDiagonal params model
        (0 : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) =
      (0 : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) := by
  let e := Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params)
  rw [matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal]
  change (Matrix.reindexAlgEquiv ℂ ℂ e)
      (Matrix.blockDiagonal
        (0 : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space)) = 0
  rw [Matrix.blockDiagonal_zero]
  exact map_zero (Matrix.reindexAlgEquiv ℂ ℂ e)

/-- Entrywise form of the canonical block-diagonal matrix.

This is the old case-split presentation, now derived from Mathlib's
`Matrix.blockDiagonal` through the index reordering used by
`matrixSdpCanonicalBlockDiagonal`. -/
@[simp] theorem matrixSdpCanonicalBlockDiagonal_apply
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space)
    (b c : MatrixSdpCanonicalBlockIndex params) (i j : model.space.carrier) :
    matrixSdpCanonicalBlockDiagonal params model B (b, i) (c, j) =
      if b = c then B b i j else 0 := by
  by_cases hbc : b = c
  · subst c
    simp [matrixSdpCanonicalBlockDiagonal]
  · simpa [matrixSdpCanonicalBlockDiagonal, hbc] using
      (Matrix.blockDiagonal_apply_ne B i j hbc)

/-- The canonical block diagonal with identity on every block is the identity
operator on the canonical block Hilbert space. -/
@[simp] theorem matrixSdpCanonicalBlockDiagonal_one
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    matrixSdpCanonicalBlockDiagonal params model
        (fun _ : MatrixSdpCanonicalBlockIndex params =>
          (1 : MatrixOperator model.space)) =
      (1 : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) := by
  let e := Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params)
  rw [matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal]
  change (Matrix.reindexAlgEquiv ℂ ℂ e)
      (Matrix.blockDiagonal (fun _ : MatrixSdpCanonicalBlockIndex params =>
        (1 : MatrixOperator model.space))) = 1
  have hone :
      Matrix.blockDiagonal (fun _ : MatrixSdpCanonicalBlockIndex params =>
          (1 : MatrixOperator model.space)) =
        (1 : Matrix (model.space.carrier × MatrixSdpCanonicalBlockIndex params)
          (model.space.carrier × MatrixSdpCanonicalBlockIndex params) ℂ) := by
    simpa [Pi.one_def] using
      (Matrix.blockDiagonal_one (o := MatrixSdpCanonicalBlockIndex params)
        (m := model.space.carrier) (α := ℂ))
  rw [hone]
  exact map_one (Matrix.reindexAlgEquiv ℂ ℂ e)

/-- Addition of canonical block-diagonal operators is blockwise addition. -/
@[simp] theorem matrixSdpCanonicalBlockDiagonal_add
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B D : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) :
    matrixSdpCanonicalBlockDiagonal params model (fun b => B b + D b) =
      matrixSdpCanonicalBlockDiagonal params model B +
        matrixSdpCanonicalBlockDiagonal params model D := by
  let e := Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params)
  rw [matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal,
    matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal,
    matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal]
  change (Matrix.reindexAlgEquiv ℂ ℂ e)
      (Matrix.blockDiagonal (fun b => B b + D b)) =
    (Matrix.reindexAlgEquiv ℂ ℂ e) (Matrix.blockDiagonal B) +
      (Matrix.reindexAlgEquiv ℂ ℂ e) (Matrix.blockDiagonal D)
  have hadd :
      Matrix.blockDiagonal (fun b => B b + D b) =
        Matrix.blockDiagonal B + Matrix.blockDiagonal D := by
    change Matrix.blockDiagonal (B + D) =
      Matrix.blockDiagonal B + Matrix.blockDiagonal D
    exact Matrix.blockDiagonal_add B D
  rw [hadd]
  exact map_add (Matrix.reindexAlgEquiv ℂ ℂ e)
    (Matrix.blockDiagonal B) (Matrix.blockDiagonal D)

/-- Negation of canonical block-diagonal operators is blockwise negation. -/
@[simp] theorem matrixSdpCanonicalBlockDiagonal_neg
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) :
    matrixSdpCanonicalBlockDiagonal params model (fun b => -B b) =
      -matrixSdpCanonicalBlockDiagonal params model B := by
  let e := Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params)
  rw [matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal,
    matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal]
  change (Matrix.reindexAlgEquiv ℂ ℂ e)
      (Matrix.blockDiagonal (fun b => -B b)) =
    -(Matrix.reindexAlgEquiv ℂ ℂ e) (Matrix.blockDiagonal B)
  have hneg :
      Matrix.blockDiagonal (fun b => -B b) = -Matrix.blockDiagonal B := by
    change Matrix.blockDiagonal (-B) = -Matrix.blockDiagonal B
    exact Matrix.blockDiagonal_neg B
  rw [hneg]
  exact map_neg (Matrix.reindexAlgEquiv ℂ ℂ e) (Matrix.blockDiagonal B)

/-- Subtraction of canonical block-diagonal operators is blockwise subtraction. -/
@[simp] theorem matrixSdpCanonicalBlockDiagonal_sub
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B D : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) :
    matrixSdpCanonicalBlockDiagonal params model (fun b => B b - D b) =
      matrixSdpCanonicalBlockDiagonal params model B -
        matrixSdpCanonicalBlockDiagonal params model D := by
  let e := Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params)
  rw [matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal,
    matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal,
    matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal]
  change (Matrix.reindexAlgEquiv ℂ ℂ e)
      (Matrix.blockDiagonal (fun b => B b - D b)) =
    (Matrix.reindexAlgEquiv ℂ ℂ e) (Matrix.blockDiagonal B) -
      (Matrix.reindexAlgEquiv ℂ ℂ e) (Matrix.blockDiagonal D)
  have hsub :
      Matrix.blockDiagonal (fun b => B b - D b) =
        Matrix.blockDiagonal B - Matrix.blockDiagonal D := by
    change Matrix.blockDiagonal (B - D) =
      Matrix.blockDiagonal B - Matrix.blockDiagonal D
    exact Matrix.blockDiagonal_sub B D
  rw [hsub]
  exact map_sub (Matrix.reindexAlgEquiv ℂ ℂ e)
    (Matrix.blockDiagonal B) (Matrix.blockDiagonal D)

/-- Scalar multiplication of canonical block-diagonal operators is blockwise
scalar multiplication. -/
@[simp] theorem matrixSdpCanonicalBlockDiagonal_smul
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (c : ℂ)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) :
    matrixSdpCanonicalBlockDiagonal params model (fun b => c • B b) =
      c • matrixSdpCanonicalBlockDiagonal params model B := by
  let e := Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params)
  rw [matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal,
    matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal]
  change (Matrix.reindexLinearEquiv ℂ ℂ e e)
      (Matrix.blockDiagonal (fun b => c • B b)) =
    c • (Matrix.reindexLinearEquiv ℂ ℂ e e) (Matrix.blockDiagonal B)
  have hsmul :
      Matrix.blockDiagonal (fun b => c • B b) =
        c • Matrix.blockDiagonal B := by
    change Matrix.blockDiagonal (c • B) = c • Matrix.blockDiagonal B
    exact Matrix.blockDiagonal_smul c B
  rw [hsmul]
  exact (Matrix.reindexLinearEquiv ℂ ℂ e e).map_smul c (Matrix.blockDiagonal B)

/-- Subtracting the identity from a canonical block-diagonal operator subtracts
the identity from each diagonal block. -/
theorem matrixSdpCanonicalBlockDiagonal_sub_one
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) :
    matrixSdpCanonicalBlockDiagonal params model B -
        (1 : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) =
      matrixSdpCanonicalBlockDiagonal params model
        (fun b => B b - (1 : MatrixOperator model.space)) := by
  rw [← matrixSdpCanonicalBlockDiagonal_one params model]
  rw [← matrixSdpCanonicalBlockDiagonal_sub]

/-- A canonical block-diagonal operator is positive semidefinite when all of its
diagonal matrix blocks are positive semidefinite. -/
theorem matrixSdpCanonicalBlockDiagonal_nonneg (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space)
    (hB : ∀ b, 0 ≤ B b) :
    0 ≤ matrixSdpCanonicalBlockDiagonal params model B := by
  classical
  rw [matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal]
  refine Matrix.nonneg_iff_posSemidef.mpr ?_
  rw [Matrix.reindex_apply]
  exact (Matrix.posSemidef_submatrix_equiv
    (M := Matrix.blockDiagonal B)
    (Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params)).symm).2
    (Matrix.nonneg_iff_posSemidef.mp (Matrix.blockDiagonal_nonneg B hB))

/-- A canonical block-diagonal operator is positive semidefinite exactly when
all of its diagonal matrix blocks are positive semidefinite. -/
theorem matrixSdpCanonicalBlockDiagonal_nonneg_iff
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) :
    0 ≤ matrixSdpCanonicalBlockDiagonal params model B ↔
      ∀ b, 0 ≤ B b := by
  classical
  constructor
  · intro hB b
    let e := Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params)
    have hblock : 0 ≤ Matrix.blockDiagonal B := by
      refine Matrix.nonneg_iff_posSemidef.mpr ?_
      have hreindexed :
          (Matrix.reindex e e (Matrix.blockDiagonal B)).PosSemidef := by
        refine Matrix.nonneg_iff_posSemidef.mp ?_
        rw [← matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal params model B]
        exact hB
      exact (Matrix.posSemidef_submatrix_equiv
        (M := Matrix.blockDiagonal B) e.symm).1 hreindexed
    exact (Matrix.blockDiagonal_nonneg_iff B).mp hblock b
  · exact matrixSdpCanonicalBlockDiagonal_nonneg params model B

@[simp] theorem matrixSdpCanonicalDiagonalBlock_blockDiagonal (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space)
    (b : MatrixSdpCanonicalBlockIndex params) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalBlockDiagonal params model B) b =
      B b := by
  ext i j
  simp [matrixSdpCanonicalDiagonalBlock, matrixSdpCanonicalBlockDiagonal]

/-- The canonical equality constraint of a block-diagonal matrix is the sum of
its diagonal blocks. -/
theorem matrixSdpCanonicalConstraintOperator_blockDiagonal (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) :
    matrixSdpCanonicalConstraintOperator params model
        (matrixSdpCanonicalBlockDiagonal params model B) =
      ∑ b : MatrixSdpCanonicalBlockIndex params, B b := by
  simp [matrixSdpCanonicalConstraintOperator]

/-- The trace of a canonical block matrix is the sum of the traces of its
diagonal blocks. -/
theorem matrixSdpCanonical_trace_eq_sum_diagonalBlock
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    Matrix.trace X =
      ∑ b : MatrixSdpCanonicalBlockIndex params,
        Matrix.trace (matrixSdpCanonicalDiagonalBlock params model X b) := by
  simp only [Matrix.trace, Matrix.diag_apply, matrixSdpCanonicalDiagonalBlock]
  change (∑ x : MatrixSdpCanonicalBlockIndex params × model.space.carrier, X x x) =
    ∑ b : MatrixSdpCanonicalBlockIndex params,
      ∑ i : model.space.carrier, X (b, i) (b, i)
  rw [Fintype.sum_prod_type]

/-- The trace pairing of two canonical block-diagonal operators is the sum of
the trace pairings of their diagonal blocks. -/
theorem matrixSdpCanonicalBlockDiagonal_trace_mul (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B D : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) :
    Matrix.trace
        (matrixSdpCanonicalBlockDiagonal params model B *
          matrixSdpCanonicalBlockDiagonal params model D) =
      ∑ b : MatrixSdpCanonicalBlockIndex params, Matrix.trace (B b * D b) := by
  let e := Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params)
  rw [matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal,
    matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal]
  change Matrix.trace
      ((Matrix.reindexAlgEquiv ℂ ℂ e) (Matrix.blockDiagonal B) *
        (Matrix.reindexAlgEquiv ℂ ℂ e) (Matrix.blockDiagonal D)) =
    ∑ b : MatrixSdpCanonicalBlockIndex params, Matrix.trace (B b * D b)
  rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ e)
    (Matrix.blockDiagonal B) (Matrix.blockDiagonal D)]
  simp only [Matrix.coe_reindexAlgEquiv]
  rw [Matrix.trace_reindex, Matrix.trace_blockDiagonal_mul]

/-- The diagonal block of a product with a canonical block-diagonal operator on
the left depends only on the corresponding diagonal block of the right factor. -/
theorem matrixSdpCanonicalDiagonalBlock_blockDiagonal_mul_left (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (b : MatrixSdpCanonicalBlockIndex params) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalBlockDiagonal params model B * X) b =
      B b * matrixSdpCanonicalDiagonalBlock params model X b := by
  classical
  ext i j
  unfold matrixSdpCanonicalDiagonalBlock
  simp only [Matrix.mul_apply, matrixSdpCanonicalBlockDiagonal]
  change (∑ y : MatrixSdpCanonicalBlockIndex params × model.space.carrier,
      (if b = y.1 then B b i y.2 else 0) * X y (b, j)) =
    ∑ k : model.space.carrier, B b i k * X (b, k) (b, j)
  rw [Fintype.sum_prod_type]
  calc
    ∑ x : MatrixSdpCanonicalBlockIndex params,
        ∑ y : model.space.carrier, (if b = x then B b i y else 0) * X (x, y) (b, j)
        = ∑ x : MatrixSdpCanonicalBlockIndex params,
          (if b = x then ∑ y : model.space.carrier, B b i y * X (x, y) (b, j) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            by_cases hx : b = x <;> simp [hx]
    _ = ∑ k : model.space.carrier, B b i k * X (b, k) (b, j) := by
          simp

/-- The trace pairing of a canonical block-diagonal operator with an arbitrary
canonical matrix depends only on the diagonal blocks of the latter.

This is the block calculation used in the converse direction of the canonical
primal SDP identification: when the objective operator is block diagonal, the
off-diagonal blocks of a feasible canonical matrix do not contribute to the
objective value. -/
theorem matrixSdpCanonicalBlockDiagonal_trace_mul_left (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    Matrix.trace (matrixSdpCanonicalBlockDiagonal params model B * X) =
      ∑ b : MatrixSdpCanonicalBlockIndex params,
        Matrix.trace (B b * matrixSdpCanonicalDiagonalBlock params model X b) := by
  rw [matrixSdpCanonical_trace_eq_sum_diagonalBlock]
  simp [matrixSdpCanonicalDiagonalBlock_blockDiagonal_mul_left]

/-- The diagonal block of a product with a canonical block-diagonal operator on
the right depends only on the corresponding diagonal block of the left factor. -/
theorem matrixSdpCanonicalDiagonalBlock_mul_blockDiagonal_right (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space)
    (b : MatrixSdpCanonicalBlockIndex params) :
    matrixSdpCanonicalDiagonalBlock params model
        (X * matrixSdpCanonicalBlockDiagonal params model B) b =
      matrixSdpCanonicalDiagonalBlock params model X b * B b := by
  classical
  ext i j
  unfold matrixSdpCanonicalDiagonalBlock
  simp only [Matrix.mul_apply, matrixSdpCanonicalBlockDiagonal]
  change (∑ y : MatrixSdpCanonicalBlockIndex params × model.space.carrier,
      X (b, i) y * (if y.1 = b then B y.1 y.2 j else 0)) =
    ∑ k : model.space.carrier, X (b, i) (b, k) * B b k j
  rw [Fintype.sum_prod_type]
  calc
    ∑ x : MatrixSdpCanonicalBlockIndex params,
        ∑ y : model.space.carrier,
          X (b, i) (x, y) * (if x = b then B x y j else 0)
        = ∑ x : MatrixSdpCanonicalBlockIndex params,
          (if x = b then
            ∑ y : model.space.carrier, X (b, i) (x, y) * B x y j
          else 0) := by
            refine Finset.sum_congr rfl ?_
            intro x _
            by_cases hx : x = b <;> simp [hx]
    _ = ∑ k : model.space.carrier, X (b, i) (b, k) * B b k j := by
          simp

/-- The product of two canonical block-diagonal operators is the canonical
block-diagonal operator obtained by multiplying corresponding blocks. -/
theorem matrixSdpCanonicalBlockDiagonal_mul (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B D : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space) :
    matrixSdpCanonicalBlockDiagonal params model B *
        matrixSdpCanonicalBlockDiagonal params model D =
      matrixSdpCanonicalBlockDiagonal params model (fun b => B b * D b) := by
  let e := Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params)
  rw [matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal,
    matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal,
    matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal]
  change
    (Matrix.reindexAlgEquiv ℂ ℂ e) (Matrix.blockDiagonal B) *
        (Matrix.reindexAlgEquiv ℂ ℂ e) (Matrix.blockDiagonal D) =
      (Matrix.reindexAlgEquiv ℂ ℂ e)
        (Matrix.blockDiagonal (fun b => B b * D b))
  rw [← map_mul (Matrix.reindexAlgEquiv ℂ ℂ e)
    (Matrix.blockDiagonal B) (Matrix.blockDiagonal D)]
  congr
  rw [Matrix.blockDiagonal_mul]

/-- The primal slack block `S = I - ∑_g T_g`. -/
noncomputable def matrixSdpCanonicalSlackOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    MatrixOperator model.space :=
  1 - ∑ g : Polynomial params, T.effect g

/-- The slack block of a matrix submeasurement is positive semidefinite. -/
theorem matrixSdpCanonicalSlackOperator_nonneg (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    0 ≤ matrixSdpCanonicalSlackOperator params model T := by
  exact sub_nonneg.mpr T.sum_le_one

/-- The block family associated to the paper primal variable and its slack. -/
noncomputable def matrixSdpCanonicalPrimalBlockFamily (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space
  | none => matrixSdpCanonicalSlackOperator params model T
  | some g => T.effect g

@[simp] theorem matrixSdpCanonicalPrimalBlockFamily_none (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    matrixSdpCanonicalPrimalBlockFamily params model T none =
      matrixSdpCanonicalSlackOperator params model T :=
  rfl

@[simp] theorem matrixSdpCanonicalPrimalBlockFamily_some (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (g : Polynomial params) :
    matrixSdpCanonicalPrimalBlockFamily params model T (some g) = T.effect g :=
  rfl

/-- The canonical block matrix associated to the paper primal submeasurement. -/
noncomputable def matrixSdpCanonicalPrimalBlockMatrix (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) :=
  matrixSdpCanonicalBlockDiagonal params model
    (matrixSdpCanonicalPrimalBlockFamily params model T)

/-- The polynomial diagonal blocks of the canonical primal matrix are the
paper primal operators `T_g`. -/
theorem matrixSdpCanonicalDiagonalBlock_primalBlockMatrix_some
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (g : Polynomial params) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalPrimalBlockMatrix params model T) (some g) =
      T.effect g := by
  simp [matrixSdpCanonicalPrimalBlockMatrix]

/-- The extra diagonal block of the canonical primal matrix is the slack
operator `I - ∑_g T_g`. -/
theorem matrixSdpCanonicalDiagonalBlock_primalBlockMatrix_none
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalPrimalBlockMatrix params model T) none =
      matrixSdpCanonicalSlackOperator params model T := by
  simp [matrixSdpCanonicalPrimalBlockMatrix]

/-- The canonical block matrix associated to a paper primal submeasurement is
positive semidefinite. -/
theorem matrixSdpCanonicalPrimalBlockMatrix_nonneg
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    0 ≤ matrixSdpCanonicalPrimalBlockMatrix params model T := by
  rw [matrixSdpCanonicalPrimalBlockMatrix]
  refine matrixSdpCanonicalBlockDiagonal_nonneg params model
    (matrixSdpCanonicalPrimalBlockFamily params model T) ?_
  intro b
  cases b with
  | none =>
      exact matrixSdpCanonicalSlackOperator_nonneg params model T
  | some g =>
      exact T.pos g

/-- The canonical block matrix associated to a submeasurement satisfies the
canonical equality constraint `∑_g T_g + S = I`. -/
theorem matrixSdpCanonicalConstraintOperator_primalBlockMatrix
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    matrixSdpCanonicalConstraintOperator params model
        (matrixSdpCanonicalPrimalBlockMatrix params model T) =
      1 := by
  rw [matrixSdpCanonicalPrimalBlockMatrix,
    matrixSdpCanonicalConstraintOperator_blockDiagonal]
  rw [Fintype.sum_option]
  simp [matrixSdpCanonicalSlackOperator]

/-- Feasibility for the canonical primal block SDP: the block variable is
positive semidefinite and satisfies the equality constraint
`X_{none,none} + ∑_g X_{gg} = I`. -/
structure MatrixSdpCanonicalPrimalFeasible (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) : Prop where
  /-- The canonical primal matrix variable is positive semidefinite. -/
  nonnegative : 0 ≤ X
  /-- The diagonal-block equality constraint holds. -/
  constraintEqOne : matrixSdpCanonicalConstraintOperator params model X = 1

/-- A paper primal submeasurement determines a feasible point of the canonical
block primal SDP by adjoining the slack block `I - ∑_g T_g`. -/
theorem matrixSdpCanonicalPrimalBlockMatrix_feasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    MatrixSdpCanonicalPrimalFeasible params model
      (matrixSdpCanonicalPrimalBlockMatrix params model T) where
  nonnegative := matrixSdpCanonicalPrimalBlockMatrix_nonneg params model T
  constraintEqOne := matrixSdpCanonicalConstraintOperator_primalBlockMatrix params model T

/-- Every diagonal block `X_{bb}` of a positive canonical primal matrix is
positive semidefinite.

This is the formal version of the paper's assertion that, from `X ≥ 0`, each
principal block `X_{ii}` is positive. -/
theorem matrixSdpCanonicalDiagonalBlock_nonneg
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    (hX : 0 ≤ X)
    (b : MatrixSdpCanonicalBlockIndex params) :
    0 ≤ matrixSdpCanonicalDiagonalBlock params model X b := by
  refine Matrix.nonneg_iff_posSemidef.mpr ?_
  have hpos : Matrix.PosSemidef X := Matrix.nonneg_iff_posSemidef.mp hX
  change Matrix.PosSemidef
    (Matrix.submatrix X
      (fun i : model.space.carrier => (b, i))
      (fun i : model.space.carrier => (b, i)))
  exact hpos.submatrix (fun i : model.space.carrier => (b, i))

/-- The polynomial diagonal blocks of a feasible canonical primal matrix form a
submeasurement total.

The canonical constraint gives `X_{none,none} + ∑_g X_{gg} = I`; since the
slack block `X_{none,none}` is positive, the polynomial blocks satisfy
`∑_g X_{gg} ≤ I`. -/
theorem matrixSdpCanonicalPrimalFeasible_sum_diagonalBlock_some_le_one
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    ∑ g : Polynomial params,
        matrixSdpCanonicalDiagonalBlock params model X (some g) ≤
      1 := by
  have hsum :
      matrixSdpCanonicalDiagonalBlock params model X none +
          ∑ g : Polynomial params,
            matrixSdpCanonicalDiagonalBlock params model X (some g) =
        1 := by
    simpa [matrixSdpCanonicalConstraintOperator, Fintype.sum_option] using
      hX.constraintEqOne
  have hslack :
      0 ≤ matrixSdpCanonicalDiagonalBlock params model X none :=
    matrixSdpCanonicalDiagonalBlock_nonneg params model hX.nonnegative none
  calc
    ∑ g : Polynomial params,
        matrixSdpCanonicalDiagonalBlock params model X (some g)
        ≤ matrixSdpCanonicalDiagonalBlock params model X none +
            ∑ g : Polynomial params,
              matrixSdpCanonicalDiagonalBlock params model X (some g) := by
          simpa using add_le_add_right hslack
            (∑ g : Polynomial params,
              matrixSdpCanonicalDiagonalBlock params model X (some g))
    _ = 1 := hsum

/-- The paper primal submeasurement extracted from a feasible canonical primal
matrix by setting `T_g = X_{gg}` on the polynomial blocks. -/
noncomputable def matrixSdpCanonicalExtractedPrimalSubmeasurement
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space where
  effect g := matrixSdpCanonicalDiagonalBlock params model X (some g)
  pos g := matrixSdpCanonicalDiagonalBlock_nonneg params model hX.nonnegative (some g)
  sum_le_one := matrixSdpCanonicalPrimalFeasible_sum_diagonalBlock_some_le_one
    params model hX

@[simp] theorem matrixSdpCanonicalExtractedPrimalSubmeasurement_effect
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (g : Polynomial params) :
    (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX).effect g =
      matrixSdpCanonicalDiagonalBlock params model X (some g) :=
  rfl

/-- The slack block of the submeasurement extracted from a feasible canonical
matrix is the original canonical slack diagonal block. -/
theorem matrixSdpCanonicalSlackOperator_extractedPrimalSubmeasurement
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    matrixSdpCanonicalSlackOperator params model
        (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX) =
      matrixSdpCanonicalDiagonalBlock params model X none := by
  have hsum :
      matrixSdpCanonicalDiagonalBlock params model X none +
          ∑ g : Polynomial params,
            matrixSdpCanonicalDiagonalBlock params model X (some g) =
        1 := by
    simpa [matrixSdpCanonicalConstraintOperator, Fintype.sum_option] using
      hX.constraintEqOne
  unfold matrixSdpCanonicalSlackOperator
  calc
    1 -
        ∑ g : Polynomial params,
          (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX).effect g =
        1 - ∑ g : Polynomial params,
          matrixSdpCanonicalDiagonalBlock params model X (some g) := by
          rfl
    _ = matrixSdpCanonicalDiagonalBlock params model X none := by
          rw [← hsum]
          abel

@[simp] theorem matrixSdpCanonicalDiagonalBlock_primalBlockMatrix_extracted_some
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (g : Polynomial params) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalPrimalBlockMatrix params model
          (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX))
        (some g) =
      matrixSdpCanonicalDiagonalBlock params model X (some g) := by
  simp [matrixSdpCanonicalPrimalBlockMatrix]

@[simp] theorem matrixSdpCanonicalDiagonalBlock_primalBlockMatrix_extracted_none
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalPrimalBlockMatrix params model
          (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX))
        none =
      matrixSdpCanonicalDiagonalBlock params model X none := by
  simpa [matrixSdpCanonicalPrimalBlockMatrix] using
    matrixSdpCanonicalSlackOperator_extractedPrimalSubmeasurement params model X hX

/-- Replacing a feasible canonical matrix by the canonical block matrix of its
extracted paper submeasurement preserves every diagonal block. -/
theorem matrixSdpCanonicalDiagonalBlock_primalBlockMatrix_extracted
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (b : MatrixSdpCanonicalBlockIndex params) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalPrimalBlockMatrix params model
          (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX))
        b =
      matrixSdpCanonicalDiagonalBlock params model X b := by
  cases b with
  | none =>
      exact matrixSdpCanonicalDiagonalBlock_primalBlockMatrix_extracted_none
        params model X hX
  | some g =>
      exact matrixSdpCanonicalDiagonalBlock_primalBlockMatrix_extracted_some
        params model X hX g

/-- A feasible canonical primal matrix determines a paper primal
submeasurement with effects `T_g = X_{gg}`. -/
theorem matrixSdpCanonicalPrimalFeasible_extracts_submeasurement
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    ∃ T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space,
      ∀ g : Polynomial params,
        T.effect g = matrixSdpCanonicalDiagonalBlock params model X (some g) := by
  refine ⟨matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX, ?_⟩
  intro g
  rfl


end MIPStarRE.LDT.SelfImprovement
