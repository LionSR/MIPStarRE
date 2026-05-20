import MIPStarRE.LDT.SelfImprovement.MatrixRealization.Canonical

/-!
# Section 9 -- Canonical SDP strong-duality preliminaries

This module contains the feasibility, compactness, closedness, convexity, and
objective-continuity lemmas used in the finite-dimensional strong-duality
argument for the canonical matrix SDP.

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

end MIPStarRE.LDT.SelfImprovement
