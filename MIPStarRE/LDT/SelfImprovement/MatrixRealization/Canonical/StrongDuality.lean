import MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical

/-!
# Section 9 — Canonical SDP strong duality

This module proves strong duality for the canonical finite-dimensional matrix
SDP used in the self-improvement argument.  It supplies explicit primal and dual
feasible points, compactness and attainment of primal maximizers and dual
minimizers, weak-duality bounds, a separation argument for zero gap, and the
canonical optimal pair consumed by the Section 9 SDP slackness statement.

## References

- `references/ldt-paper/self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open Filter
open scoped BigOperators MatrixOrder Matrix ComplexOrder Matrix.Norms.Elementwise Topology

/-- The canonical primal SDP has a feasible point, supplied by the explicit
strict primal submeasurement. -/
theorem matrixSdpCanonicalPrimalFeasible_nonempty
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
      MatrixSdpCanonicalPrimalFeasible params model X :=
  ⟨matrixSdpCanonicalPrimalBlockMatrix params model
      (matrixSdpStrictPrimalSubmeasurement params model),
    matrixSdpCanonicalStrictPrimalBlockMatrix_feasible params model⟩

/-- The uniform strict-primal Slater weight is positive.

This is a Slater-interiority prerequisite for the canonical primal SDP, not an
optimality or zero-gap theorem. -/
theorem sdpStrictPrimalWeight_pos
    (params : Parameters) [FieldModel params.q] :
    0 < sdpStrictPrimalWeight params := by
  have hcard : 0 < (Fintype.card (Polynomial params) : Error) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨sdpDistinguishedPolynomial params⟩)
  unfold sdpStrictPrimalWeight
  positivity

/-- The uniform strict-primal Slater weight is at most the slack coefficient
`1/2`.

This bound is only a feasibility-interiority prerequisite for the canonical
primal SDP; it does not assert optimality or strong duality. -/
theorem sdpStrictPrimalWeight_le_half
    (params : Parameters) [FieldModel params.q] :
    sdpStrictPrimalWeight params ≤ 1 / 2 := by
  have hcardNat : 1 ≤ Fintype.card (Polynomial params) := by
    exact Nat.succ_le_of_lt
      (Fintype.card_pos_iff.mpr ⟨sdpDistinguishedPolynomial params⟩)
  have hcard : (1 : Error) ≤ Fintype.card (Polynomial params) := by
    exact_mod_cast hcardNat
  have hden : 0 < (2 : Error) * Fintype.card (Polynomial params) := by
    positivity
  unfold sdpStrictPrimalWeight
  rw [div_le_iff₀ hden]
  nlinarith

/-- The canonical strict-primal block matrix dominates the positive scalar
multiple of the identity determined by the uniform Slater weight.

This is the strict-primal Slater lower bound needed as a prerequisite for a
finite-dimensional SDP theorem; it is not an optimality or zero-gap statement. -/
theorem matrixSdpCanonicalStrictPrimalBlockMatrix_weight_le
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    (sdpStrictPrimalWeight params : Error) •
        (1 : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) ≤
      matrixSdpCanonicalPrimalBlockMatrix params model
        (matrixSdpStrictPrimalSubmeasurement params model) := by
  rw [← sub_nonneg]
  let T := matrixSdpStrictPrimalSubmeasurement params model
  let w := sdpStrictPrimalWeight params
  let B := matrixSdpCanonicalPrimalBlockFamily params model T
  have hsub :
      matrixSdpCanonicalPrimalBlockMatrix params model T -
          w • (1 : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) =
        matrixSdpCanonicalBlockDiagonal params model
          (fun b => B b - w • (1 : MatrixOperator model.space)) := by
    ext x y
    rcases x with ⟨b, i⟩
    rcases y with ⟨c, j⟩
    by_cases hbc : b = c
    · subst c
      by_cases hij : i = j
      · subst j
        change (if b = b then B b i i else 0) -
            w • (if (b, i) = (b, i) then (1 : ℂ) else 0) =
          (if b = b then (B b - w • (1 : MatrixOperator model.space)) i i else 0)
        simp [Matrix.sub_apply, Matrix.smul_apply]
      · change (if b = b then B b i j else 0) -
            w • (if (b, i) = (b, j) then (1 : ℂ) else 0) =
          (if b = b then (B b - w • (1 : MatrixOperator model.space)) i j else 0)
        simp [Matrix.sub_apply, Matrix.smul_apply, Prod.ext_iff, hij]
    · change (if b = c then B b i j else 0) -
          w • (if (b, i) = (c, j) then (1 : ℂ) else 0) =
        (if b = c then (B b - w • (1 : MatrixOperator model.space)) i j else 0)
      simp [Prod.ext_iff, hbc]
  rw [show matrixSdpCanonicalPrimalBlockMatrix params model
        (matrixSdpStrictPrimalSubmeasurement params model) =
      matrixSdpCanonicalPrimalBlockMatrix params model T by rfl]
  rw [show (sdpStrictPrimalWeight params : Error) •
        (1 : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) =
      w • (1 : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) by rfl]
  rw [hsub]
  refine matrixSdpCanonicalBlockDiagonal_nonneg params model
    (fun b => B b - w • (1 : MatrixOperator model.space)) ?_
  intro b
  cases b with
  | none =>
      have hslack : B none = (1 / 2 : Error) • (1 : MatrixOperator model.space) := by
        simpa [B, T, matrixSdpCanonicalPrimalBlockMatrix] using
          matrixSdpCanonicalStrictPrimalBlockMatrix_slack_half params model
      change 0 ≤ B none - w • (1 : MatrixOperator model.space)
      rw [hslack]
      have hscalar :
          (1 / 2 : Error) • (1 : MatrixOperator model.space) -
              w • (1 : MatrixOperator model.space) =
            ((1 / 2 : Error) - w) • (1 : MatrixOperator model.space) := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [Matrix.sub_apply, Matrix.smul_apply]
        · simp [Matrix.sub_apply, Matrix.smul_apply, hij]
      rw [hscalar]
      exact smul_nonneg (sub_nonneg.mpr (sdpStrictPrimalWeight_le_half params))
        (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : MatrixOperator model.space))
  | some g =>
      have hblock : B (some g) = w • (1 : MatrixOperator model.space) := by
        simp [B, T, matrixSdpStrictPrimalSubmeasurement, sdpStrictPrimalSubMeas, w]
      change 0 ≤ B (some g) - w • (1 : MatrixOperator model.space)
      rw [hblock, sub_self]

/-- The paper-form canonical dual feasibility inequalities are nonempty,
supplied by the explicit strict dual witness. -/
theorem matrixSdpCanonicalDualFeasible_nonempty
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∃ Z : MatrixOperator model.space,
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g :=
  ⟨matrixSdpStrictDualWitness model,
    matrixSdpStrictDualWitness_dualFeasible params model⟩

/-- The canonical equality-constraint operator preserves trace. -/
theorem matrixSdpCanonicalConstraintOperator_trace_eq
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    Matrix.trace (matrixSdpCanonicalConstraintOperator params model X) =
      Matrix.trace X := by
  classical
  unfold Matrix.trace matrixSdpCanonicalConstraintOperator matrixSdpCanonicalDiagonalBlock
  simp only [Matrix.diag_apply, Matrix.sum_apply]
  change (∑ i : model.space.carrier,
      ∑ b : MatrixSdpCanonicalBlockIndex params, X (b, i) (b, i)) =
    ∑ x : MatrixSdpCanonicalBlockIndex params × model.space.carrier, X x x
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- A PSD canonical primal variable is norm-controlled by the real trace of its
constraint image. -/
theorem matrixSdpCanonicalNonnegative_norm_le_constraint_trace_re
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : 0 ≤ X) :
    ‖X‖ ≤ Complex.re
      (Matrix.trace (matrixSdpCanonicalConstraintOperator params model X)) := by
  rw [matrixSdpCanonicalConstraintOperator_trace_eq params model X]
  exact MIPStarRE.Quantum.norm_le_trace_re_of_nonneg hX

/-- A feasible canonical primal matrix has trace equal to the base Hilbert-space dimension. -/
theorem matrixSdpCanonicalPrimalFeasible_trace_eq
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    Matrix.trace X = (Fintype.card model.space.carrier : ℂ) := by
  calc
    Matrix.trace X = Matrix.trace (matrixSdpCanonicalConstraintOperator params model X) := by
      exact (matrixSdpCanonicalConstraintOperator_trace_eq params model X).symm
    _ = Matrix.trace (1 : MatrixOperator model.space) := by rw [hX.constraintEqOne]
    _ = (Fintype.card model.space.carrier : ℂ) := by rw [Matrix.trace_one]

/-- Feasible canonical primal matrices have uniformly bounded elementwise norm. -/
theorem matrixSdpCanonicalPrimalFeasible_norm_le
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    ‖X‖ ≤ (Fintype.card model.space.carrier : ℝ) := by
  have hnorm := MIPStarRE.Quantum.norm_le_trace_re_of_nonneg hX.nonnegative
  rw [matrixSdpCanonicalPrimalFeasible_trace_eq params model X hX] at hnorm
  simpa using hnorm

/-- The feasible set of the canonical primal SDP is bounded in the elementwise matrix norm. -/
theorem matrixSdpCanonicalPrimalFeasible_isBounded
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    Bornology.IsBounded
      {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) |
        MatrixSdpCanonicalPrimalFeasible params model X} := by
  rw [isBounded_iff_forall_norm_le]
  exact ⟨(Fintype.card model.space.carrier : ℝ), fun X hX =>
    matrixSdpCanonicalPrimalFeasible_norm_le params model X hX⟩

/-- The canonical primal equality-constraint operator is continuous. -/
theorem continuous_matrixSdpCanonicalConstraintOperator
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    Continuous fun X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) =>
      matrixSdpCanonicalConstraintOperator params model X := by
  classical
  unfold matrixSdpCanonicalConstraintOperator matrixSdpCanonicalDiagonalBlock
  exact continuous_finset_sum Finset.univ fun b _ =>
    continuous_matrix fun i j => continuous_apply_apply (b, i) (b, j)

/-- The positive-semidefinite cone of finite matrix operators is closed. -/
theorem isClosed_matrixOperator_nonnegative
    (H : FiniteHilbertSpace) :
    IsClosed {X : MatrixOperator H | 0 ≤ X} := by
  classical
  let ι := H.carrier
  have hhermitian : IsClosed {X : Matrix ι ι ℂ | X.IsHermitian} := by
    simpa [Matrix.IsHermitian] using
      isClosed_eq (Continuous.matrix_conjTranspose continuous_id) continuous_id
  have hquadratic : IsClosed
      {X : Matrix ι ι ℂ |
        ∀ x : ι →₀ ℂ,
          0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * X i j * xj} := by
    rw [show
        {X : Matrix ι ι ℂ |
          ∀ x : ι →₀ ℂ,
            0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * X i j * xj} =
        ⋂ x : ι →₀ ℂ,
          {X : Matrix ι ι ℂ |
            0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * X i j * xj} by
      ext X
      simp]
    refine isClosed_iInter fun x => ?_
    have hquad : Continuous fun X : Matrix ι ι ℂ =>
        x.sum fun i xi => x.sum fun j xj => star xi * X i j * xj := by
      simp only [Finsupp.sum]
      exact continuous_finset_sum x.support fun i _ =>
        continuous_finset_sum x.support fun j _ =>
          ((continuous_const.mul (continuous_apply_apply i j)).mul continuous_const)
    exact isClosed_le continuous_const hquad
  have hpsd : IsClosed {X : Matrix ι ι ℂ | X.PosSemidef} := by
    rw [show {X : Matrix ι ι ℂ | X.PosSemidef} =
        {X : Matrix ι ι ℂ | X.IsHermitian} ∩
          {X : Matrix ι ι ℂ |
            ∀ x : ι →₀ ℂ,
              0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * X i j * xj} by
      ext X
      rfl]
    exact hhermitian.inter hquadratic
  rw [show
      {X : MatrixOperator H | 0 ≤ X} =
      {X : Matrix ι ι ℂ | X.PosSemidef} by
    ext X
    exact Matrix.nonneg_iff_posSemidef]
  exact hpsd

/-- The positive-semidefinite operators on a finite Hilbert space form a proper cone. -/
noncomputable def matrixOperatorNonnegativeProperCone
    (H : FiniteHilbertSpace) :
    ProperCone ℝ (MatrixOperator H) where
  toSubmodule := PointedCone.positive ℝ (MatrixOperator H)
  isClosed' := by
    simpa using isClosed_matrixOperator_nonnegative H

@[simp]
theorem mem_matrixOperatorNonnegativeProperCone
    (H : FiniteHilbertSpace) (X : MatrixOperator H) :
    X ∈ matrixOperatorNonnegativeProperCone H ↔ 0 ≤ X :=
  Iff.rfl

/-- The positive-semidefinite cone of finite matrix operators is convex. -/
theorem matrixOperator_nonnegative_convex
    (H : FiniteHilbertSpace) :
    Convex ℝ {X : MatrixOperator H | 0 ≤ X} := by
  rw [convex_iff_add_mem]
  intro X hX Y hY a b ha hb _hab
  change 0 ≤ a • X + b • Y
  exact add_nonneg (smul_nonneg ha (show 0 ≤ X from hX))
    (smul_nonneg hb (show 0 ≤ Y from hY))

/-- The canonical primal equality-constraint operator preserves real affine combinations. -/
theorem matrixSdpCanonicalConstraintOperator_affine_combination
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X Y : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (a b : ℝ) :
    matrixSdpCanonicalConstraintOperator params model (a • X + b • Y) =
      a • matrixSdpCanonicalConstraintOperator params model X +
        b • matrixSdpCanonicalConstraintOperator params model Y := by
  classical
  ext i j
  unfold matrixSdpCanonicalConstraintOperator matrixSdpCanonicalDiagonalBlock
  simp only [Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply]
  rw [Finset.sum_add_distrib]
  have hsumX : (∑ x, a • X (x, i) (x, j)) = a • (∑ x, X (x, i) (x, j)) := by
    rw [Fintype.sum_option]
    conv_rhs => rw [Fintype.sum_option]
    have hsome : (∑ x, a • X (some x, i) (some x, j)) =
        a • (∑ x, X (some x, i) (some x, j)) := by
      simpa using (Finset.smul_sum (s := Finset.univ)
        (f := fun x => X (some x, i) (some x, j)) (r := a)).symm
    rw [hsome]
    module
  have hsumY : (∑ x, b • Y (x, i) (x, j)) = b • (∑ x, Y (x, i) (x, j)) := by
    rw [Fintype.sum_option]
    conv_rhs => rw [Fintype.sum_option]
    have hsome : (∑ x, b • Y (some x, i) (some x, j)) =
        b • (∑ x, Y (some x, i) (some x, j)) := by
      simpa using (Finset.smul_sum (s := Finset.univ)
        (f := fun x => Y (some x, i) (some x, j)) (r := b)).symm
    rw [hsome]
    module
  rw [hsumX, hsumY]

/-- The feasible set of the canonical primal SDP is convex. -/
theorem matrixSdpCanonicalPrimalFeasible_convex
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    Convex ℝ
      {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) |
        MatrixSdpCanonicalPrimalFeasible params model X} := by
  rw [convex_iff_add_mem]
  intro X hX Y hY a b ha hb hab
  refine ⟨?_, ?_⟩
  · change 0 ≤ a • X + b • Y
    exact add_nonneg (smul_nonneg ha hX.nonnegative) (smul_nonneg hb hY.nonnegative)
  · rw [matrixSdpCanonicalConstraintOperator_affine_combination,
      hX.constraintEqOne, hY.constraintEqOne]
    ext i j
    by_cases hij : i = j
    · subst j
      simpa [Matrix.one_apply] using (show (a : ℂ) + (b : ℂ) = 1 by exact_mod_cast hab)
    · simp [hij]

/-- Each paper-form dual slack preserves real affine combinations. -/
theorem matrixSdpDualSlackOperator_affine_combination
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z W : MatrixOperator model.space) (g : Polynomial params)
    (a b : ℝ) (hab : a + b = 1) :
    matrixSdpDualSlackOperator params model (a • Z + b • W) g =
      a • matrixSdpDualSlackOperator params model Z g +
        b • matrixSdpDualSlackOperator params model W g := by
  unfold matrixSdpDualSlackOperator
  calc
    a • Z + b • W - matrixAveragedPointOperator params model g =
        a • Z + b • W - (a + b) • matrixAveragedPointOperator params model g := by
      conv_lhs =>
        rw [show matrixAveragedPointOperator params model g =
            (a + b) • matrixAveragedPointOperator params model g by
          rw [hab]
          ext i j
          simp]
    _ = a • (Z - matrixAveragedPointOperator params model g) +
        b • (W - matrixAveragedPointOperator params model g) := by
      module

/-- The paper-form canonical dual feasible set is convex. -/
theorem matrixSdpCanonicalDualFeasible_convex
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    Convex ℝ
      {Z : MatrixOperator model.space |
        ∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g} := by
  rw [convex_iff_add_mem]
  intro Z hZ W hW a b ha hb hab g
  rw [matrixSdpDualSlackOperator_affine_combination params model Z W g a b hab]
  exact add_nonneg (smul_nonneg ha (hZ g)) (smul_nonneg hb (hW g))

/-- A canonical block-diagonal operator is Hermitian when all diagonal blocks are
Hermitian. -/
theorem matrixSdpCanonicalBlockDiagonal_isHermitian
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (B : MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space)
    (hB : ∀ b, (B b).IsHermitian) :
    (matrixSdpCanonicalBlockDiagonal params model B).IsHermitian := by
  rw [matrixSdpCanonicalBlockDiagonal_eq_reindex_blockDiagonal]
  exact (Matrix.isHermitian_blockDiagonal_iff.mpr hB).reindex
    (Equiv.prodComm model.space.carrier (MatrixSdpCanonicalBlockIndex params))

/-- The canonical dual block operator is Hermitian when the paper dual matrix is
Hermitian. -/
theorem matrixSdpCanonicalDualOperator_isHermitian
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hZ : Z.IsHermitian) :
    (matrixSdpCanonicalDualOperator params model Z).IsHermitian := by
  rw [matrixSdpCanonicalDualOperator]
  exact matrixSdpCanonicalBlockDiagonal_isHermitian params model
    (matrixSdpCanonicalDualOperatorBlockFamily params model Z) fun _ => hZ

/-- The canonical objective block operator is Hermitian. -/
theorem matrixSdpCanonicalObjectiveOperator_isHermitian
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    (matrixSdpCanonicalObjectiveOperator params model).IsHermitian := by
  rw [matrixSdpCanonicalObjectiveOperator]
  refine matrixSdpCanonicalBlockDiagonal_isHermitian params model
    (matrixSdpCanonicalObjectiveBlockFamily params model) ?_
  intro b
  cases b with
  | none => simp [matrixSdpCanonicalObjectiveBlockFamily]
  | some g =>
      exact (Matrix.nonneg_iff_posSemidef.mp
        (matrixAveragedPointOperator_nonneg params model g)).isHermitian

/-- The canonical dual slack block operator is Hermitian when the paper dual
matrix is Hermitian. -/
theorem matrixSdpCanonicalDualOperator_sub_objectiveOperator_isHermitian
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hZ : Z.IsHermitian) :
    (matrixSdpCanonicalDualOperator params model Z -
      matrixSdpCanonicalObjectiveOperator params model).IsHermitian :=
  (matrixSdpCanonicalDualOperator_isHermitian params model Z hZ).sub
    (matrixSdpCanonicalObjectiveOperator_isHermitian params model)

/-- The canonical dual block trace pairing equals the paper dual trace pairing
against the canonical constraint image. -/
theorem matrixSdpCanonicalDualOperator_trace_constraint
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (Z : MatrixOperator model.space) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalDualOperator params model Z * X)) =
      Complex.re (Matrix.trace
        (Z * matrixSdpCanonicalConstraintOperator params model X)) := by
  congr 1
  rw [matrixSdpCanonicalDualOperator]
  rw [matrixSdpCanonicalBlockDiagonal_trace_mul_left]
  simp only [matrixSdpCanonicalDualOperatorBlockFamily_apply]
  rw [← Matrix.trace_sum]
  rw [← Finset.mul_sum]
  rfl

/-- The canonical equality-constraint image of a positive canonical primal
matrix is positive semidefinite. -/
theorem matrixSdpCanonicalConstraintOperator_nonneg_of_nonnegative
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    (hX : 0 ≤ X) :
    0 ≤ matrixSdpCanonicalConstraintOperator params model X := by
  unfold matrixSdpCanonicalConstraintOperator
  exact Finset.sum_nonneg fun b _ =>
    matrixSdpCanonicalDiagonalBlock_nonneg params model hX b

/-- The canonical equality-constraint image of a positive canonical primal
matrix is Hermitian. -/
theorem matrixSdpCanonicalConstraintOperator_isHermitian_of_nonnegative
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    (hX : 0 ≤ X) :
    (matrixSdpCanonicalConstraintOperator params model X).IsHermitian :=
  (Matrix.nonneg_iff_posSemidef.mp
    (matrixSdpCanonicalConstraintOperator_nonneg_of_nonnegative params model hX)).isHermitian

/-- A trace-pairing separator against every positive semidefinite canonical primal
matrix can be converted into the paper-form dual feasibility inequalities.

This is a separator-conversion lemma for the later zero-gap argument, not the
strong-duality theorem itself. -/
theorem matrixSdpCanonicalDualConstraint_nonneg_of_trace_pairing_nonneg
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hHerm :
      (matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model).IsHermitian)
    (htrace :
      ∀ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
        0 ≤ X →
          0 ≤ Complex.re (Matrix.trace
            ((matrixSdpCanonicalDualOperator params model Z -
                matrixSdpCanonicalObjectiveOperator params model) * X))) :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model Z g := by
  have hcanonical :
      0 ≤ matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model :=
    MIPStarRE.Quantum.nonneg_of_trace_mul_nonneg_of_isHermitian hHerm htrace
  exact matrixSdpDualFeasible_of_canonicalDualConstraint_nonneg params model Z hcanonical

/-- The feasible set of the canonical primal SDP is closed. -/
theorem matrixSdpCanonicalPrimalFeasible_isClosed
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    IsClosed
      {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) |
        MatrixSdpCanonicalPrimalFeasible params model X} := by
  classical
  have hnonneg : IsClosed
      {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) | 0 ≤ X} :=
    isClosed_matrixOperator_nonnegative (matrixSdpCanonicalBlockHilbertSpace params model)
  have hconstraint : IsClosed
      {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) |
        matrixSdpCanonicalConstraintOperator params model X = (1 : MatrixOperator model.space)} :=
    isClosed_eq (continuous_matrixSdpCanonicalConstraintOperator params model) continuous_const
  rw [show
      {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) |
        MatrixSdpCanonicalPrimalFeasible params model X} =
      {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) | 0 ≤ X} ∩
        {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) |
          matrixSdpCanonicalConstraintOperator params model X =
            (1 : MatrixOperator model.space)} by
    ext X
    constructor
    · intro hX
      exact ⟨hX.nonnegative, hX.constraintEqOne⟩
    · intro hX
      exact ⟨hX.1, hX.2⟩]
  exact hnonneg.inter hconstraint

/-- The paper-form canonical dual feasible set is closed. -/
theorem matrixSdpCanonicalDualFeasible_isClosed
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    IsClosed
      {Z : MatrixOperator model.space |
        ∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g} := by
  classical
  rw [show
      {Z : MatrixOperator model.space |
        ∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g} =
      ⋂ g : Polynomial params,
        {Z : MatrixOperator model.space |
          0 ≤ matrixSdpDualSlackOperator params model Z g} by
    ext Z
    simp]
  refine isClosed_iInter fun g => ?_
  have hslack : Continuous fun Z : MatrixOperator model.space =>
      matrixSdpDualSlackOperator params model Z g := by
    unfold matrixSdpDualSlackOperator
    exact continuous_id.sub continuous_const
  simpa [Set.preimage] using
    (isClosed_matrixOperator_nonnegative model.space).preimage hslack

/-- The paper-form canonical dual objective is continuous. -/
theorem continuous_matrixSdpDualObjective
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    Continuous fun Z : MatrixOperator model.space => matrixSdpDualObjective model Z := by
  unfold matrixSdpDualObjective
  exact Complex.continuous_re.comp continuous_id.matrix_trace

/-- The strict-witness-bounded dual feasible sublevel is closed. -/
theorem matrixSdpCanonicalDualFeasibleSublevel_isClosed
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    IsClosed
      {Z : MatrixOperator model.space |
        (∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
        matrixSdpDualObjective model Z ≤
          matrixSdpDualObjective model (matrixSdpStrictDualWitness model)} := by
  have hfeasible := matrixSdpCanonicalDualFeasible_isClosed params model
  have hsublevel : IsClosed
      {Z : MatrixOperator model.space |
        matrixSdpDualObjective model Z ≤
          matrixSdpDualObjective model (matrixSdpStrictDualWitness model)} :=
    isClosed_le (continuous_matrixSdpDualObjective params model) continuous_const
  rw [show
      {Z : MatrixOperator model.space |
        (∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
        matrixSdpDualObjective model Z ≤
          matrixSdpDualObjective model (matrixSdpStrictDualWitness model)} =
      {Z : MatrixOperator model.space |
        ∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g} ∩
      {Z : MatrixOperator model.space |
        matrixSdpDualObjective model Z ≤
          matrixSdpDualObjective model (matrixSdpStrictDualWitness model)} by
    ext Z
    rfl]
  exact hfeasible.inter hsublevel

/-- The strict-witness-bounded dual feasible sublevel is norm-bounded. -/
theorem matrixSdpCanonicalDualFeasibleSublevel_isBounded
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    Bornology.IsBounded
      {Z : MatrixOperator model.space |
        (∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
        matrixSdpDualObjective model Z ≤
          matrixSdpDualObjective model (matrixSdpStrictDualWitness model)} := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨matrixSdpDualObjective model (matrixSdpStrictDualWitness model), fun Z hZ => ?_⟩
  calc
    ‖Z‖ ≤ Complex.re (Matrix.trace Z) :=
      MIPStarRE.Quantum.norm_le_trace_re_of_nonneg
        (matrixSdpDualPositive_of_dualFeasible params model Z hZ.1)
    _ = matrixSdpDualObjective model Z := by rfl
    _ ≤ matrixSdpDualObjective model (matrixSdpStrictDualWitness model) := hZ.2

/-- The strict-witness-bounded dual feasible sublevel is compact. -/
theorem matrixSdpCanonicalDualFeasibleSublevel_isCompact
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    IsCompact
      {Z : MatrixOperator model.space |
        (∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
        matrixSdpDualObjective model Z ≤
          matrixSdpDualObjective model (matrixSdpStrictDualWitness model)} :=
  Metric.isCompact_of_isClosed_isBounded
    (matrixSdpCanonicalDualFeasibleSublevel_isClosed params model)
    (matrixSdpCanonicalDualFeasibleSublevel_isBounded params model)

/-- The paper-form canonical dual objective attains its minimum on the feasible set. -/
theorem matrixSdpCanonicalDualObjective_exists_isMinOn
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∃ Z : MatrixOperator model.space,
      (∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
      ∀ W : MatrixOperator model.space,
        (∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model W g) →
        matrixSdpDualObjective model Z ≤ matrixSdpDualObjective model W := by
  let c := matrixSdpDualObjective model (matrixSdpStrictDualWitness model)
  let S : Set (MatrixOperator model.space) :=
    {Z | (∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
      matrixSdpDualObjective model Z ≤ c}
  have hScompact : IsCompact S := by
    simpa [S, c] using matrixSdpCanonicalDualFeasibleSublevel_isCompact params model
  have hSne : S.Nonempty := by
    refine ⟨matrixSdpStrictDualWitness model, ?_⟩
    exact ⟨matrixSdpStrictDualWitness_dualFeasible params model, le_rfl⟩
  obtain ⟨Z, hZS, hZmin⟩ := hScompact.exists_isMinOn hSne
    (continuous_matrixSdpDualObjective params model).continuousOn
  refine ⟨Z, hZS.1, fun W hW => ?_⟩
  by_cases hWc : matrixSdpDualObjective model W ≤ c
  · exact hZmin ⟨hW, hWc⟩
  · have hcW : c ≤ matrixSdpDualObjective model W := le_of_not_ge hWc
    exact hZS.2.trans hcW

/-- The feasible set of the canonical primal SDP is compact. -/
theorem matrixSdpCanonicalPrimalFeasible_isCompact
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    IsCompact
      {X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) |
        MatrixSdpCanonicalPrimalFeasible params model X} :=
  Metric.isCompact_of_isClosed_isBounded
    (matrixSdpCanonicalPrimalFeasible_isClosed params model)
    (matrixSdpCanonicalPrimalFeasible_isBounded params model)

/-- The canonical primal objective is continuous. -/
theorem continuous_matrixSdpCanonicalPrimalObjective
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    Continuous fun X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) =>
      Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X)) := by
  have hmul :
      Continuous fun X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) =>
        matrixSdpCanonicalObjectiveOperator params model * X :=
    continuous_const.mul continuous_id
  exact Complex.continuous_re.comp hmul.matrix_trace

/-- The canonical equality-constraint operator as a continuous real-linear map. -/
noncomputable def matrixSdpCanonicalConstraintOperatorCLM
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) →L[ℝ]
      MatrixOperator model.space :=
  ContinuousLinearMap.mk
    { toFun := matrixSdpCanonicalConstraintOperator params model
      map_add' := by
        classical
        intro X Y
        ext i j
        unfold matrixSdpCanonicalConstraintOperator matrixSdpCanonicalDiagonalBlock
        simp only [Matrix.sum_apply, Matrix.add_apply]
        exact Finset.sum_add_distrib
      map_smul' := by
        classical
        intro r X
        ext i j
        unfold matrixSdpCanonicalConstraintOperator matrixSdpCanonicalDiagonalBlock
        simp only [Matrix.sum_apply, Matrix.smul_apply]
        exact (Finset.smul_sum (s := Finset.univ)
          (f := fun b : MatrixSdpCanonicalBlockIndex params => X (b, i) (b, j))
          (r := r)).symm }
    (continuous_matrixSdpCanonicalConstraintOperator params model)

@[simp]
theorem matrixSdpCanonicalConstraintOperatorCLM_apply
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    matrixSdpCanonicalConstraintOperatorCLM params model X =
      matrixSdpCanonicalConstraintOperator params model X :=
  rfl

/-- The canonical primal objective as a continuous real-linear functional. -/
noncomputable def matrixSdpCanonicalPrimalObjectiveCLM
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) →L[ℝ] ℝ :=
  ContinuousLinearMap.mk
    { toFun := fun X =>
        Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X))
      map_add' := by
        intro X Y
        rw [Matrix.mul_add, Matrix.trace_add, Complex.add_re]
      map_smul' := by
        intro r X
        rw [Matrix.mul_smul, Matrix.trace_smul]
        exact Complex.smul_re r
          (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X)) }
    (continuous_matrixSdpCanonicalPrimalObjective params model)

@[simp]
theorem matrixSdpCanonicalPrimalObjectiveCLM_apply
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    matrixSdpCanonicalPrimalObjectiveCLM params model X =
      Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X)) :=
  rfl

/-- The map sending a primal matrix to its constraint image and objective value. -/
noncomputable def matrixSdpCanonicalPrimalConeMap
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) →L[ℝ]
      MatrixOperator model.space × ℝ :=
  (matrixSdpCanonicalConstraintOperatorCLM params model).prod
    (matrixSdpCanonicalPrimalObjectiveCLM params model)

@[simp]
theorem matrixSdpCanonicalPrimalConeMap_apply
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :
    matrixSdpCanonicalPrimalConeMap params model X =
      (matrixSdpCanonicalConstraintOperator params model X,
        Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X))) :=
  rfl

/-- The closed image cone of positive semidefinite canonical primal matrices under
the constraint-objective map. -/
noncomputable def matrixSdpCanonicalPrimalImageCone
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ProperCone ℝ (MatrixOperator model.space × ℝ) :=
  (matrixOperatorNonnegativeProperCone (matrixSdpCanonicalBlockHilbertSpace params model)).map
    (matrixSdpCanonicalPrimalConeMap params model)

/-- An actual positive semidefinite canonical primal matrix maps into the closed
canonical primal image cone. -/
theorem matrixSdpCanonicalPrimalImageCone_mem_of_nonnegative
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : 0 ≤ X) :
    (matrixSdpCanonicalConstraintOperator params model X,
        Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X))) ∈
      matrixSdpCanonicalPrimalImageCone params model := by
  rw [← matrixSdpCanonicalPrimalConeMap_apply params model X]
  rw [matrixSdpCanonicalPrimalImageCone, ProperCone.mem_map]
  exact subset_closure <| by
    exact (PointedCone.mem_map).2 ⟨X, by simpa using hX, rfl⟩

/-- A feasible canonical primal matrix maps to the image-cone point with
constraint component equal to the identity. -/
theorem matrixSdpCanonicalPrimalImageCone_mem_of_feasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    ((1 : MatrixOperator model.space),
        Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X))) ∈
      matrixSdpCanonicalPrimalImageCone params model := by
  simpa [hX.constraintEqOne] using
    matrixSdpCanonicalPrimalImageCone_mem_of_nonnegative params model X hX.nonnegative

/-- On the identity constraint fiber, the closed primal image cone contains
exactly the objective values of feasible canonical primal matrices. -/
theorem matrixSdpCanonicalPrimalImageCone_identity_mem_iff_exists_feasible_objective
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) (t : ℝ) :
    ((1 : MatrixOperator model.space), t) ∈
        matrixSdpCanonicalPrimalImageCone params model ↔
      ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
        MatrixSdpCanonicalPrimalFeasible params model X ∧
          Complex.re (Matrix.trace
            (matrixSdpCanonicalObjectiveOperator params model * X)) = t := by
  classical
  constructor
  · intro hmem
    rw [matrixSdpCanonicalPrimalImageCone, ProperCone.mem_map] at hmem
    obtain ⟨u, hu_mem, hu_tendsto⟩ := mem_closure_iff_seq_limit.mp hmem
    have hu_witness : ∀ n : ℕ,
        ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
          X ∈ (matrixOperatorNonnegativeProperCone
            (matrixSdpCanonicalBlockHilbertSpace params model)).toPointedCone ∧
          (matrixSdpCanonicalPrimalConeMap params model :
            MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) →ₗ[ℝ]
              MatrixOperator model.space × ℝ) X = u n := by
      intro n
      exact PointedCone.mem_map.mp (hu_mem n)
    choose X hXcone hmap using hu_witness
    have hXnonneg : ∀ n : ℕ, 0 ≤ X n := by
      intro n
      simpa using hXcone n
    have hmapCLM : ∀ n : ℕ,
        matrixSdpCanonicalPrimalConeMap params model (X n) = u n := by
      intro n
      simpa using hmap n
    let dimR : ℝ := Fintype.card model.space.carrier
    let R : ℝ := dimR + 1
    let s : Set (MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) :=
      {Y | 0 ≤ Y ∧ ‖Y‖ ≤ R}
    have hsBounded : Bornology.IsBounded s := by
      rw [isBounded_iff_forall_norm_le]
      exact ⟨R, fun Y hY => hY.2⟩
    have hcoords :=
      (Prod.tendsto_iff u ((1 : MatrixOperator model.space), t)).mp hu_tendsto
    have htrace_cont : Continuous fun Y : MatrixOperator model.space =>
        Complex.re (Matrix.trace Y) :=
      Complex.continuous_re.comp continuous_id.matrix_trace
    have htrace_tendsto_u :
        Tendsto (fun n : ℕ => Complex.re (Matrix.trace ((u n).1))) atTop
          (𝓝 (Fintype.card model.space.carrier : ℝ)) := by
      simpa [Matrix.trace_one] using
        (htrace_cont.tendsto (1 : MatrixOperator model.space)).comp hcoords.1
    have htrace_tendsto :
        Tendsto
          (fun n : ℕ => Complex.re (Matrix.trace
            (matrixSdpCanonicalConstraintOperator params model (X n)))) atTop
          (𝓝 dimR) := by
      have htrace_eq :
          (fun n : ℕ => Complex.re (Matrix.trace
            (matrixSdpCanonicalConstraintOperator params model (X n)))) =
            fun n : ℕ => Complex.re (Matrix.trace ((u n).1)) := by
        funext n
        rw [← hmapCLM n]
        rfl
      rw [htrace_eq]
      simpa [dimR] using htrace_tendsto_u
    have hdim_lt_R : dimR < R := by
      simp [R]
    have heventTrace : ∀ᶠ n : ℕ in atTop,
        Complex.re (Matrix.trace
          (matrixSdpCanonicalConstraintOperator params model (X n))) < R :=
      htrace_tendsto.eventually (Iio_mem_nhds hdim_lt_R)
    have heventS : ∀ᶠ n : ℕ in atTop, X n ∈ s := by
      filter_upwards [heventTrace] with n hn
      refine ⟨hXnonneg n, ?_⟩
      exact (matrixSdpCanonicalNonnegative_norm_le_constraint_trace_re
        params model (X n) (hXnonneg n)).trans (le_of_lt hn)
    obtain ⟨X₀, _hX₀closure, k, hkmono, hX₀tendsto⟩ :=
      tendsto_subseq_of_frequently_bounded hsBounded heventS.frequently
    have hX₀nonneg : 0 ≤ X₀ :=
      (isClosed_matrixOperator_nonnegative
        (matrixSdpCanonicalBlockHilbertSpace params model)).mem_of_tendsto
        hX₀tendsto (Eventually.of_forall fun n => hXnonneg (k n))
    have hmap_tendsto_X₀ :
        Tendsto
          (fun n : ℕ => matrixSdpCanonicalPrimalConeMap params model (X (k n)))
          atTop (𝓝 (matrixSdpCanonicalPrimalConeMap params model X₀)) :=
      ((matrixSdpCanonicalPrimalConeMap params model).continuous.tendsto X₀).comp
        hX₀tendsto
    have hu_subseq_tendsto :
        Tendsto (u ∘ k) atTop (𝓝 ((1 : MatrixOperator model.space), t)) :=
      hu_tendsto.comp hkmono.tendsto_atTop
    have hmap_tendsto_identity :
        Tendsto
          (fun n : ℕ => matrixSdpCanonicalPrimalConeMap params model (X (k n)))
          atTop (𝓝 ((1 : MatrixOperator model.space), t)) := by
      have hfun :
          (fun n : ℕ => matrixSdpCanonicalPrimalConeMap params model (X (k n))) =
            u ∘ k := by
        funext n
        exact hmapCLM (k n)
      rw [hfun]
      exact hu_subseq_tendsto
    have hlimit :
        matrixSdpCanonicalPrimalConeMap params model X₀ =
          ((1 : MatrixOperator model.space), t) :=
      tendsto_nhds_unique hmap_tendsto_X₀ hmap_tendsto_identity
    have hconstraint :
        matrixSdpCanonicalConstraintOperator params model X₀ =
          (1 : MatrixOperator model.space) := by
      have := congrArg Prod.fst hlimit
      simpa [matrixSdpCanonicalPrimalConeMap_apply] using this
    have hobjective :
        Complex.re (Matrix.trace
            (matrixSdpCanonicalObjectiveOperator params model * X₀)) = t := by
      have := congrArg Prod.snd hlimit
      simpa [matrixSdpCanonicalPrimalConeMap_apply] using this
    exact ⟨X₀, ⟨hX₀nonneg, hconstraint⟩, hobjective⟩
  · rintro ⟨X, hX, hobj⟩
    simpa [hobj] using matrixSdpCanonicalPrimalImageCone_mem_of_feasible params model X hX

/-- If `Xmax` maximizes the canonical primal objective and `t` is strictly above
its value, then the identity-fiber point with objective coordinate `t` is not in
the closed primal image cone. -/
theorem matrixSdpCanonicalPrimalImageCone_notMem_identity_of_primalMax_lt
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    {Xmax : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)}
    {t : ℝ}
    (_hXmax : MatrixSdpCanonicalPrimalFeasible params model Xmax)
    (hmax : ∀ Y : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
      MatrixSdpCanonicalPrimalFeasible params model Y →
        Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * Y)) ≤
        Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * Xmax)))
    (hlt : Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model * Xmax)) < t) :
    ((1 : MatrixOperator model.space), t) ∉
      matrixSdpCanonicalPrimalImageCone params model := by
  intro hmem
  obtain ⟨Y, hY, hYobj⟩ :=
    (matrixSdpCanonicalPrimalImageCone_identity_mem_iff_exists_feasible_objective
      params model t).mp hmem
  have ht_le : t ≤ Complex.re (Matrix.trace
      (matrixSdpCanonicalObjectiveOperator params model * Xmax)) := by
    simpa [hYobj] using hmax Y hY
  exact (not_lt_of_ge ht_le) hlt

/-- A point outside the canonical primal image cone has a continuous real-linear
separator. -/
theorem matrixSdpCanonicalPrimalImageCone_separation_of_notMem
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    {y : MatrixOperator model.space × ℝ}
    (hy : y ∉ matrixSdpCanonicalPrimalImageCone params model) :
    ∃ f : StrongDual ℝ (MatrixOperator model.space × ℝ),
      (∀ z ∈ matrixSdpCanonicalPrimalImageCone params model, 0 ≤ f z) ∧ f y < 0 :=
  (matrixSdpCanonicalPrimalImageCone params model).hyperplane_separation_point hy

/-- The constraint-coordinate part of a separator on the product space.

This is only product-functional decomposition through the left product
inclusion.  It does not represent the matrix-coordinate functional by a
trace-pairing matrix. -/
noncomputable def matrixSdpCanonicalSeparatorConstraintFunctional
    {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    (φ : StrongDual ℝ (MatrixOperator model.space × ℝ)) :
    StrongDual ℝ (MatrixOperator model.space) :=
  φ.comp (ContinuousLinearMap.inl ℝ (MatrixOperator model.space) ℝ)

/-- The scalar objective-coordinate coefficient of a separator on the product space.

This is only product-functional decomposition through the right product
inclusion.  It does not represent the matrix-coordinate functional by a
trace-pairing matrix. -/
noncomputable def matrixSdpCanonicalSeparatorObjectiveCoefficient
    {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    (φ : StrongDual ℝ (MatrixOperator model.space × ℝ)) : ℝ :=
  (φ.comp (ContinuousLinearMap.inr ℝ (MatrixOperator model.space) ℝ)) (1 : ℝ)

/-- A separator on the constraint-objective product is the sum of its two
product-coordinate components.

This is only product-functional decomposition.  It does not represent the
matrix-coordinate functional by a trace-pairing matrix. -/
theorem matrixSdpCanonicalSeparator_decompose
    {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    (φ : StrongDual ℝ (MatrixOperator model.space × ℝ))
    (Y : MatrixOperator model.space) (t : ℝ) :
    φ (Y, t) =
      matrixSdpCanonicalSeparatorConstraintFunctional φ Y +
        t * matrixSdpCanonicalSeparatorObjectiveCoefficient φ := by
  rw [← ContinuousLinearMap.comp_inl_add_comp_inr φ (Y, t)]
  simp only [matrixSdpCanonicalSeparatorConstraintFunctional,
    matrixSdpCanonicalSeparatorObjectiveCoefficient]
  congr 1
  simpa using
    ((φ.comp (ContinuousLinearMap.inr ℝ (MatrixOperator model.space) ℝ)).map_smul
      t (1 : ℝ))

/-- Nonnegativity of a separator on the primal image cone, evaluated on the
constraint-objective image of a positive canonical primal matrix.

This uses only product-functional decomposition of the separator.  It does not
represent the matrix-coordinate functional by a trace-pairing matrix. -/
theorem matrixSdpCanonicalSeparator_nonneg_on_primalConeMap
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (φ : StrongDual ℝ (MatrixOperator model.space × ℝ))
    (hφ : ∀ z ∈ matrixSdpCanonicalPrimalImageCone params model, 0 ≤ φ z)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : 0 ≤ X) :
    0 ≤
      matrixSdpCanonicalSeparatorConstraintFunctional φ
        (matrixSdpCanonicalConstraintOperator params model X) +
      Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model * X)) *
        matrixSdpCanonicalSeparatorObjectiveCoefficient φ := by
  have hmem := matrixSdpCanonicalPrimalImageCone_mem_of_nonnegative params model X hX
  have hnonneg := hφ _ hmem
  rwa [matrixSdpCanonicalSeparator_decompose] at hnonneg

/-- If a separator is nonnegative on a cone point but negative at a point with
the same constraint coordinate and larger objective coordinate, then its
objective coefficient is negative.

This is only product-functional decomposition of the separator.  It does not
represent the matrix-coordinate functional by a trace-pairing matrix. -/
theorem matrixSdpCanonicalSeparatorObjectiveCoefficient_neg_of_above
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (φ : StrongDual ℝ (MatrixOperator model.space × ℝ))
    {Y : MatrixOperator model.space} {s t : ℝ}
    (hφ : ∀ z ∈ matrixSdpCanonicalPrimalImageCone params model, 0 ≤ φ z)
    (hYs : (Y, s) ∈ matrixSdpCanonicalPrimalImageCone params model)
    (hYt : φ (Y, t) < 0)
    (hst : s < t) :
    matrixSdpCanonicalSeparatorObjectiveCoefficient φ < 0 := by
  have hs_nonneg :
      0 ≤
        matrixSdpCanonicalSeparatorConstraintFunctional φ Y +
          s * matrixSdpCanonicalSeparatorObjectiveCoefficient φ := by
    have hnonneg := hφ (Y, s) hYs
    rwa [matrixSdpCanonicalSeparator_decompose] at hnonneg
  have ht_neg :
      matrixSdpCanonicalSeparatorConstraintFunctional φ Y +
          t * matrixSdpCanonicalSeparatorObjectiveCoefficient φ < 0 := by
    rwa [matrixSdpCanonicalSeparator_decompose] at hYt
  by_contra hnot
  have hcoeff_nonneg : 0 ≤ matrixSdpCanonicalSeparatorObjectiveCoefficient φ :=
    le_of_not_gt hnot
  have hmul :
      s * matrixSdpCanonicalSeparatorObjectiveCoefficient φ ≤
        t * matrixSdpCanonicalSeparatorObjectiveCoefficient φ :=
    mul_le_mul_of_nonneg_right (le_of_lt hst) hcoeff_nonneg
  nlinarith

/-- A feasible primal matrix whose objective value lies strictly below the
separated product point forces the separator objective coefficient to be
negative.

This is only product-functional decomposition of the separator.  It does not
represent the matrix-coordinate functional by a trace-pairing matrix. -/
theorem matrixSdpCanonicalSeparatorObjectiveCoefficient_neg_of_feasible_lt
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (φ : StrongDual ℝ (MatrixOperator model.space × ℝ))
    {t : ℝ}
    (hφ : ∀ z ∈ matrixSdpCanonicalPrimalImageCone params model, 0 ≤ φ z)
    (hsep : φ ((1 : MatrixOperator model.space), t) < 0)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (hXlt : Complex.re (Matrix.trace
      (matrixSdpCanonicalObjectiveOperator params model * X)) < t) :
    matrixSdpCanonicalSeparatorObjectiveCoefficient φ < 0 :=
  matrixSdpCanonicalSeparatorObjectiveCoefficient_neg_of_above params model φ hφ
    (matrixSdpCanonicalPrimalImageCone_mem_of_feasible params model X hX) hsep hXlt

/-- The constraint-coordinate separator normalized by a negative objective coefficient.

This is only a continuous real-linear functional on the constraint-operator
space.  It does not represent the functional by a trace-pairing matrix. -/
noncomputable def matrixSdpCanonicalNormalizedSeparatorFunctional
    {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    (φ : StrongDual ℝ (MatrixOperator model.space × ℝ)) :
    StrongDual ℝ (MatrixOperator model.space) :=
  ((-matrixSdpCanonicalSeparatorObjectiveCoefficient φ)⁻¹) •
    matrixSdpCanonicalSeparatorConstraintFunctional φ

@[simp]
theorem matrixSdpCanonicalNormalizedSeparatorFunctional_apply
    {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    (φ : StrongDual ℝ (MatrixOperator model.space × ℝ))
    (Y : MatrixOperator model.space) :
    matrixSdpCanonicalNormalizedSeparatorFunctional φ Y =
      ((-matrixSdpCanonicalSeparatorObjectiveCoefficient φ)⁻¹) *
        matrixSdpCanonicalSeparatorConstraintFunctional φ Y := by
  rfl

/-- A separator whose objective-coordinate coefficient is negative gives a
normalized continuous real-linear functional dominating the canonical objective
on every positive semidefinite primal cone point.

This remains a functional-level statement.  It does not represent the
normalized separator by a trace-pairing matrix. -/
theorem matrixSdpCanonicalObjective_le_normalizedSeparator_on_primalConeMap
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (φ : StrongDual ℝ (MatrixOperator model.space × ℝ))
    (hφ : ∀ z ∈ matrixSdpCanonicalPrimalImageCone params model, 0 ≤ φ z)
    (hcoeff : matrixSdpCanonicalSeparatorObjectiveCoefficient φ < 0)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : 0 ≤ X) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model * X)) ≤
      matrixSdpCanonicalNormalizedSeparatorFunctional φ
        (matrixSdpCanonicalConstraintOperator params model X) := by
  have hpositiveCoeff : 0 < -matrixSdpCanonicalSeparatorObjectiveCoefficient φ :=
    neg_pos.mpr hcoeff
  have hnonneg :=
    matrixSdpCanonicalSeparator_nonneg_on_primalConeMap params model φ hφ X hX
  have hmul :
      Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * X)) *
          (-matrixSdpCanonicalSeparatorObjectiveCoefficient φ) ≤
        matrixSdpCanonicalSeparatorConstraintFunctional φ
          (matrixSdpCanonicalConstraintOperator params model X) := by
    nlinarith
  rw [matrixSdpCanonicalNormalizedSeparatorFunctional_apply]
  exact (le_inv_mul_iff₀' hpositiveCoeff).mpr hmul

/-- On a feasible canonical primal matrix, the normalized separator bounds the
canonical objective at the identity constraint value.

This is only a continuous real-linear functional bound; it does not represent
the normalized separator by a trace-pairing matrix. -/
theorem matrixSdpCanonicalObjective_le_normalizedSeparator_of_feasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (φ : StrongDual ℝ (MatrixOperator model.space × ℝ))
    (hφ : ∀ z ∈ matrixSdpCanonicalPrimalImageCone params model, 0 ≤ φ z)
    (hcoeff : matrixSdpCanonicalSeparatorObjectiveCoefficient φ < 0)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model * X)) ≤
      matrixSdpCanonicalNormalizedSeparatorFunctional φ
        (1 : MatrixOperator model.space) := by
  simpa [hX.constraintEqOne] using
    matrixSdpCanonicalObjective_le_normalizedSeparator_on_primalConeMap
      params model φ hφ hcoeff X hX.nonnegative

/-- A separator negative at `(1, t)` places its normalized constraint-coordinate
functional below `t` at the identity.

This is only a continuous real-linear functional inequality.  It does not
represent the normalized separator by a trace-pairing matrix. -/
theorem matrixSdpCanonicalNormalizedSeparatorFunctional_lt_of_sep
    {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    (φ : StrongDual ℝ (MatrixOperator model.space × ℝ))
    {t : ℝ}
    (hsep : φ ((1 : MatrixOperator model.space), t) < 0)
    (hcoeff : matrixSdpCanonicalSeparatorObjectiveCoefficient φ < 0) :
    matrixSdpCanonicalNormalizedSeparatorFunctional φ
      (1 : MatrixOperator model.space) < t := by
  have hpositiveCoeff : 0 < -matrixSdpCanonicalSeparatorObjectiveCoefficient φ :=
    neg_pos.mpr hcoeff
  have hsepDecomposed :
      matrixSdpCanonicalSeparatorConstraintFunctional φ (1 : MatrixOperator model.space) +
          t * matrixSdpCanonicalSeparatorObjectiveCoefficient φ < 0 := by
    rwa [matrixSdpCanonicalSeparator_decompose] at hsep
  have hlt :
      matrixSdpCanonicalSeparatorConstraintFunctional φ (1 : MatrixOperator model.space) <
        t * (-matrixSdpCanonicalSeparatorObjectiveCoefficient φ) := by
    nlinarith
  rw [matrixSdpCanonicalNormalizedSeparatorFunctional_apply]
  exact (inv_mul_lt_iff₀ hpositiveCoeff).mpr (by simpa [mul_comm] using hlt)

/-- The Hermitian matrix representing the normalized separator functional under
the real trace pairing. -/
noncomputable def matrixSdpCanonicalNormalizedSeparatorDualMatrix
    {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    (φ : StrongDual ℝ (MatrixOperator model.space × ℝ)) :
    MatrixOperator model.space :=
  MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM
    (matrixSdpCanonicalNormalizedSeparatorFunctional φ)

/-- The matrix representing the normalized separator is Hermitian. -/
theorem matrixSdpCanonicalNormalizedSeparatorDualMatrix_isHermitian
    {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    (φ : StrongDual ℝ (MatrixOperator model.space × ℝ)) :
    (matrixSdpCanonicalNormalizedSeparatorDualMatrix φ).IsHermitian :=
  MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM_isHermitian
    (matrixSdpCanonicalNormalizedSeparatorFunctional φ)

/-- On Hermitian inputs, the normalized separator functional is the real trace
pairing against its Hermitian representing matrix. -/
theorem matrixSdpCanonicalNormalizedSeparatorFunctional_eq_trace_dualMatrix
    {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    (φ : StrongDual ℝ (MatrixOperator model.space × ℝ))
    {Y : MatrixOperator model.space} (hY : Y.IsHermitian) :
    matrixSdpCanonicalNormalizedSeparatorFunctional φ Y =
      Complex.re (Matrix.trace
        (matrixSdpCanonicalNormalizedSeparatorDualMatrix φ * Y)) := by
  simpa [matrixSdpCanonicalNormalizedSeparatorDualMatrix] using
    MIPStarRE.Quantum.hermitianTracePairingMatrixOfRealCLM_apply_of_isHermitian
      (matrixSdpCanonicalNormalizedSeparatorFunctional φ) hY

/-- The normalized separator matrix dominates the canonical objective on every
positive canonical primal cone point. -/
theorem matrixSdpCanonicalObjective_le_normalizedSeparatorDualMatrix_on_nonnegative
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (φ : StrongDual ℝ (MatrixOperator model.space × ℝ))
    (hφ : ∀ z ∈ matrixSdpCanonicalPrimalImageCone params model, 0 ≤ φ z)
    (hcoeff : matrixSdpCanonicalSeparatorObjectiveCoefficient φ < 0)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : 0 ≤ X) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model * X)) ≤
      Complex.re (Matrix.trace
        (matrixSdpCanonicalDualOperator params model
          (matrixSdpCanonicalNormalizedSeparatorDualMatrix φ) * X)) := by
  have hle :=
    matrixSdpCanonicalObjective_le_normalizedSeparator_on_primalConeMap
      params model φ hφ hcoeff X hX
  have hconstraintHerm :
      (matrixSdpCanonicalConstraintOperator params model X).IsHermitian :=
    matrixSdpCanonicalConstraintOperator_isHermitian_of_nonnegative params model hX
  rw [matrixSdpCanonicalNormalizedSeparatorFunctional_eq_trace_dualMatrix
    φ hconstraintHerm] at hle
  rwa [matrixSdpCanonicalDualOperator_trace_constraint]

/-- The normalized separator matrix is paper-form dual feasible. -/
theorem matrixSdpCanonicalNormalizedSeparatorDualMatrix_dualFeasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (φ : StrongDual ℝ (MatrixOperator model.space × ℝ))
    (hφ : ∀ z ∈ matrixSdpCanonicalPrimalImageCone params model, 0 ≤ φ z)
    (hcoeff : matrixSdpCanonicalSeparatorObjectiveCoefficient φ < 0) :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model
        (matrixSdpCanonicalNormalizedSeparatorDualMatrix φ) g := by
  let Z := matrixSdpCanonicalNormalizedSeparatorDualMatrix φ
  refine matrixSdpCanonicalDualConstraint_nonneg_of_trace_pairing_nonneg
    params model Z ?_ ?_
  · exact matrixSdpCanonicalDualOperator_sub_objectiveOperator_isHermitian
      params model Z (matrixSdpCanonicalNormalizedSeparatorDualMatrix_isHermitian φ)
  · intro X hX
    have hle :
        Complex.re (Matrix.trace
            (matrixSdpCanonicalObjectiveOperator params model * X)) ≤
          Complex.re (Matrix.trace
            (matrixSdpCanonicalDualOperator params model Z * X)) := by
      simpa [Z] using
        matrixSdpCanonicalObjective_le_normalizedSeparatorDualMatrix_on_nonnegative
          params model φ hφ hcoeff X hX
    rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
    exact sub_nonneg.mpr hle

/-- The normalized separator matrix has dual objective below the separated
objective coordinate. -/
theorem matrixSdpCanonicalNormalizedSeparatorDualMatrix_dualObjective_lt_of_sep
    {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    (φ : StrongDual ℝ (MatrixOperator model.space × ℝ))
    {t : ℝ}
    (hsep : φ ((1 : MatrixOperator model.space), t) < 0)
    (hcoeff : matrixSdpCanonicalSeparatorObjectiveCoefficient φ < 0) :
    matrixSdpDualObjective model
        (matrixSdpCanonicalNormalizedSeparatorDualMatrix φ) < t := by
  have hlt :=
    matrixSdpCanonicalNormalizedSeparatorFunctional_lt_of_sep φ hsep hcoeff
  have hI : (1 : MatrixOperator model.space).IsHermitian := Matrix.isHermitian_one
  rw [matrixSdpCanonicalNormalizedSeparatorFunctional_eq_trace_dualMatrix φ hI] at hlt
  simpa [matrixSdpDualObjective] using hlt

/-- The canonical primal objective attains a maximum on the feasible set. -/
theorem matrixSdpCanonicalPrimalObjective_exists_isMaxOn
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
      MatrixSdpCanonicalPrimalFeasible params model X ∧
        ∀ Y : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
          MatrixSdpCanonicalPrimalFeasible params model Y →
            Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * Y)) ≤
              Complex.re (Matrix.trace (matrixSdpCanonicalObjectiveOperator params model * X)) := by
  obtain ⟨X, hX, hmax⟩ :=
    (matrixSdpCanonicalPrimalFeasible_isCompact params model).exists_isMaxOn
      (Set.nonempty_def.mpr (matrixSdpCanonicalPrimalFeasible_nonempty params model))
      (continuous_matrixSdpCanonicalPrimalObjective params model).continuousOn
  exact ⟨X, hX, fun Y hY => hmax hY⟩

/-- The canonical primal maximizer and dual minimizer exist, and their attained
values satisfy weak duality. This packages the attained optima but is not the
zero-gap strong-duality theorem. -/
theorem matrixSdpCanonicalPrimalDualOptima_exist
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
      ∃ Z : MatrixOperator model.space,
        MatrixSdpCanonicalPrimalFeasible params model X ∧
        (∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
        (∀ Y : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
          MatrixSdpCanonicalPrimalFeasible params model Y →
            Complex.re (Matrix.trace
              (matrixSdpCanonicalObjectiveOperator params model * Y)) ≤
              Complex.re (Matrix.trace
                (matrixSdpCanonicalObjectiveOperator params model * X))) ∧
        (∀ W : MatrixOperator model.space,
          (∀ g : Polynomial params,
            0 ≤ matrixSdpDualSlackOperator params model W g) →
          matrixSdpDualObjective model Z ≤ matrixSdpDualObjective model W) ∧
        Complex.re (Matrix.trace
          (matrixSdpCanonicalObjectiveOperator params model * X)) ≤
          matrixSdpDualObjective model Z := by
  obtain ⟨X, hX, hXmax⟩ :=
    matrixSdpCanonicalPrimalObjective_exists_isMaxOn params model
  obtain ⟨Z, hZ, hZmin⟩ :=
    matrixSdpCanonicalDualObjective_exists_isMinOn params model
  refine ⟨X, Z, hX, hZ, hXmax, hZmin, ?_⟩
  exact matrixSdpCanonicalWeakDuality params model X hX Z
    (matrixSdpCanonicalDualConstraint_nonneg_of_dualFeasible params model Z hZ)

/-- The canonical matrix SDP has a primal-dual optimal pair with zero duality
gap.

This is the finite-dimensional strong-duality conclusion used in the paper's
Section 9 SDP argument.  The proof combines compact attainment, separation of
the closed primal image cone, and the trace-pairing representation of the
normalized separator; it does not add an auxiliary dominance hypothesis on the
dual matrix. -/
theorem matrixSdpCanonicalStrongDuality
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∃ X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model),
      ∃ Z : MatrixOperator model.space,
        MatrixSdpCanonicalPrimalFeasible params model X ∧
        (∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
        Complex.re (Matrix.trace
            (matrixSdpCanonicalObjectiveOperator params model * X)) =
          matrixSdpDualObjective model Z := by
  obtain ⟨X, Z, hX, hZ, hXmax, hZmin, hweak⟩ :=
    matrixSdpCanonicalPrimalDualOptima_exist params model
  let p : ℝ := Complex.re (Matrix.trace
    (matrixSdpCanonicalObjectiveOperator params model * X))
  let d : ℝ := matrixSdpDualObjective model Z
  have hd_le_p : d ≤ p := by
    by_contra hnot
    have hp_lt_d : p < d := lt_of_not_ge hnot
    let t : ℝ := (p + d) / 2
    have hp_lt_t : p < t := by
      dsimp [t]
      nlinarith
    have ht_lt_d : t < d := by
      dsimp [t]
      nlinarith
    have hnotMem :
        ((1 : MatrixOperator model.space), t) ∉
          matrixSdpCanonicalPrimalImageCone params model := by
      refine matrixSdpCanonicalPrimalImageCone_notMem_identity_of_primalMax_lt
        params model hX ?_ ?_
      · intro Y hY
        simpa [p] using hXmax Y hY
      · simpa [p] using hp_lt_t
    obtain ⟨φ, hφ_nonneg, hsep⟩ :=
      matrixSdpCanonicalPrimalImageCone_separation_of_notMem params model hnotMem
    have hcoeff : matrixSdpCanonicalSeparatorObjectiveCoefficient φ < 0 :=
      matrixSdpCanonicalSeparatorObjectiveCoefficient_neg_of_feasible_lt
        params model φ hφ_nonneg hsep X hX (by simpa [p] using hp_lt_t)
    let W := matrixSdpCanonicalNormalizedSeparatorDualMatrix φ
    have hWdual :
        ∀ g : Polynomial params,
          0 ≤ matrixSdpDualSlackOperator params model W g := by
      simpa [W] using
        matrixSdpCanonicalNormalizedSeparatorDualMatrix_dualFeasible
          params model φ hφ_nonneg hcoeff
    have hWobj_lt : matrixSdpDualObjective model W < t := by
      simpa [W] using
        matrixSdpCanonicalNormalizedSeparatorDualMatrix_dualObjective_lt_of_sep
          φ hsep hcoeff
    have hd_le_W : d ≤ matrixSdpDualObjective model W := by
      simpa [d] using hZmin W hWdual
    nlinarith
  refine ⟨X, Z, hX, hZ, ?_⟩
  have hp_le_d : p ≤ d := by
    simpa [p, d] using hweak
  have hp_eq_d : p = d := le_antisymm hp_le_d hd_le_p
  simpa [p, d] using hp_eq_d

/-- The canonical objective block operator is positive semidefinite. -/
theorem matrixSdpCanonicalObjectiveOperator_nonneg
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    0 ≤ matrixSdpCanonicalObjectiveOperator params model := by
  rw [matrixSdpCanonicalObjectiveOperator]
  refine matrixSdpCanonicalBlockDiagonal_nonneg params model
    (matrixSdpCanonicalObjectiveBlockFamily params model) ?_
  intro b
  cases b with
  | none => simp [matrixSdpCanonicalObjectiveBlockFamily]
  | some g => exact matrixAveragedPointOperator_nonneg params model g

/-- The canonical objective has nonnegative trace pairing with every feasible
canonical primal matrix. -/
theorem matrixSdpCanonicalObjective_trace_nonneg
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    0 ≤ Complex.re (Matrix.trace
      (matrixSdpCanonicalObjectiveOperator params model * X)) :=
  MIPStarRE.Quantum.trace_mul_nonneg_of_nonneg
    (matrixSdpCanonicalObjectiveOperator_nonneg params model) hX.nonnegative

/-- Every feasible canonical primal objective is bounded above by the explicit
strict-dual objective. -/
theorem matrixSdpCanonicalObjective_trace_le_strictDualObjective
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model * X)) ≤
      matrixSdpDualObjective model (matrixSdpStrictDualWitness model) :=
  matrixSdpCanonicalWeakDuality params model X hX
    (matrixSdpStrictDualWitness model)
    (matrixSdpCanonicalStrictDualConstraint_nonneg params model)

/-- The explicit strict-primal canonical objective is bounded above by every
paper-form dual-feasible objective. -/
theorem matrixSdpCanonicalStrictPrimalObjective_le_dualObjective
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model *
          matrixSdpCanonicalPrimalBlockMatrix params model
            (matrixSdpStrictPrimalSubmeasurement params model))) ≤
      matrixSdpDualObjective model Z :=
  matrixSdpCanonicalWeakDuality params model
    (matrixSdpCanonicalPrimalBlockMatrix params model
      (matrixSdpStrictPrimalSubmeasurement params model))
    (matrixSdpCanonicalStrictPrimalBlockMatrix_feasible params model) Z
    (matrixSdpCanonicalDualConstraint_nonneg_of_dualFeasible params model Z hdual)

end MIPStarRE.LDT.SelfImprovement
