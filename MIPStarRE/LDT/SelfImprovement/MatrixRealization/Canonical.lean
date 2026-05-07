import MIPStarRE.LDT.SelfImprovement.MatrixRealization.CanonicalPrimal

/-!
# Section 9 — Canonical matrix SDP dual and slackness layer

This module contains the canonical objective and dual operators, the dual slack
block identities, and the slack-block saturation step used to extract the
paper-form primal normalization.  The optimal-witness packages built from these
canonical facts live in `MatrixRealization/Canonical/Witness.lean`.

## References

- `references/ldt-paper/self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-- The canonical objective matrix `C = diag(A_g, 0)` in the paper's block SDP. -/
noncomputable def matrixSdpCanonicalObjectiveBlockFamily (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space
  | none => 0
  | some g => matrixAveragedPointOperator params model g

/-- The canonical objective operator of the block SDP. -/
noncomputable def matrixSdpCanonicalObjectiveOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) :=
  matrixSdpCanonicalBlockDiagonal params model
    (matrixSdpCanonicalObjectiveBlockFamily params model)

@[simp] theorem matrixSdpCanonicalObjectiveBlockFamily_none (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    matrixSdpCanonicalObjectiveBlockFamily params model none = 0 :=
  rfl

@[simp] theorem matrixSdpCanonicalObjectiveBlockFamily_some (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) :
    matrixSdpCanonicalObjectiveBlockFamily params model (some g) =
      matrixAveragedPointOperator params model g :=
  rfl

@[simp] theorem matrixSdpCanonicalDiagonalBlock_objectiveOperator_none
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalObjectiveOperator params model) none =
      0 := by
  simp [matrixSdpCanonicalObjectiveOperator]

@[simp] theorem matrixSdpCanonicalDiagonalBlock_objectiveOperator_some
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalObjectiveOperator params model) (some g) =
      matrixAveragedPointOperator params model g := by
  simp [matrixSdpCanonicalObjectiveOperator]

/-- The block family representing the canonical dual operator associated to a
paper dual variable `Z`.

In the paper calculation this is
`∑_{i,j} z_{ij} D_{ij}`, which is the block-diagonal matrix with the same
operator `Z` on every canonical block. -/
noncomputable def matrixSdpCanonicalDualOperatorBlockFamily (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) :
    MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space :=
  fun _ => Z

/-- The canonical dual operator corresponding to a paper dual variable `Z`. -/
noncomputable def matrixSdpCanonicalDualOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) :
    MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model) :=
  matrixSdpCanonicalBlockDiagonal params model
    (matrixSdpCanonicalDualOperatorBlockFamily params model Z)

@[simp] theorem matrixSdpCanonicalDualOperatorBlockFamily_apply
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (b : MatrixSdpCanonicalBlockIndex params) :
    matrixSdpCanonicalDualOperatorBlockFamily params model Z b = Z :=
  rfl

@[simp] theorem matrixSdpCanonicalDiagonalBlock_dualOperator
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (b : MatrixSdpCanonicalBlockIndex params) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalDualOperator params model Z) b =
      Z := by
  simp [matrixSdpCanonicalDualOperator]

/-- The block family for the canonical dual slack operator.

It has polynomial blocks `Z - A_g` and slack block `Z`, exactly as in the
canonical dual constraint obtained from the paper SDP. -/
noncomputable def matrixSdpCanonicalDualSlackBlockFamily (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) :
    MatrixSdpCanonicalBlockIndex params → MatrixOperator model.space
  | none => Z
  | some g => matrixSdpDualSlackOperator params model Z g

@[simp] theorem matrixSdpCanonicalDualSlackBlockFamily_none (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) :
    matrixSdpCanonicalDualSlackBlockFamily params model Z none = Z :=
  rfl

@[simp] theorem matrixSdpCanonicalDualSlackBlockFamily_some (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (g : Polynomial params) :
    matrixSdpCanonicalDualSlackBlockFamily params model Z (some g) =
      matrixSdpDualSlackOperator params model Z g :=
  rfl

/-- The canonical dual slack is the difference between the canonical dual
operator and the canonical objective operator. -/
theorem matrixSdpCanonicalDualOperator_sub_objectiveOperator
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) :
    matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model =
      matrixSdpCanonicalBlockDiagonal params model
        (matrixSdpCanonicalDualSlackBlockFamily params model Z) := by
  ext x y
  rcases x with ⟨b, i⟩
  rcases y with ⟨c, j⟩
  by_cases hbc : b = c
  · subst c
    cases b with
    | none =>
        simp [matrixSdpCanonicalDualOperator, matrixSdpCanonicalObjectiveOperator,
          matrixSdpCanonicalBlockDiagonal]
    | some g =>
        simp [matrixSdpCanonicalDualOperator, matrixSdpCanonicalObjectiveOperator,
          matrixSdpCanonicalBlockDiagonal, matrixSdpDualSlackOperator]
  · simp [matrixSdpCanonicalDualOperator, matrixSdpCanonicalObjectiveOperator,
      matrixSdpCanonicalBlockDiagonal, hbc]

/-- The canonical dual slack block matrix is positive semidefinite under paper
dual feasibility.

The canonical dual constraint for the block SDP is the positivity of the block
diagonal operator with blocks `Z - A_g` on the polynomial summands and `Z` on
the slack summand.  The polynomial blocks are precisely the paper dual
feasibility inequalities, while the slack block follows from the same
inequalities because the averaged point operators are positive. -/
theorem matrixSdpCanonicalDualSlackBlockDiagonal_nonneg_of_dualFeasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g) :
    0 ≤ matrixSdpCanonicalBlockDiagonal params model
      (matrixSdpCanonicalDualSlackBlockFamily params model Z) := by
  refine matrixSdpCanonicalBlockDiagonal_nonneg params model
    (matrixSdpCanonicalDualSlackBlockFamily params model Z) ?_
  intro b
  cases b with
  | none =>
      simpa [matrixSdpCanonicalDualSlackBlockFamily] using
        matrixSdpDualPositive_of_dualFeasible params model Z hdual
  | some g =>
      simpa [matrixSdpCanonicalDualSlackBlockFamily] using hdual g

/-- Positivity of the canonical dual slack block matrix is equivalent to the
paper dual feasibility inequalities `Z ≥ A_g`. -/
theorem matrixSdpCanonicalDualSlackBlockDiagonal_nonneg_iff_dualFeasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) :
    0 ≤ matrixSdpCanonicalBlockDiagonal params model
        (matrixSdpCanonicalDualSlackBlockFamily params model Z) ↔
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g := by
  constructor
  · intro hcanonical g
    have hblocks :=
      (matrixSdpCanonicalBlockDiagonal_nonneg_iff params model
        (matrixSdpCanonicalDualSlackBlockFamily params model Z)).mp hcanonical
    simpa using hblocks (some g)
  · exact matrixSdpCanonicalDualSlackBlockDiagonal_nonneg_of_dualFeasible params model Z

/-- The canonical dual constraint for `Z` is equivalent to the paper dual
constraints `Z ≥ A_g`. -/
theorem matrixSdpCanonicalDualConstraint_nonneg_iff_dualFeasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) :
    0 ≤ matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model ↔
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g := by
  rw [matrixSdpCanonicalDualOperator_sub_objectiveOperator]
  exact matrixSdpCanonicalDualSlackBlockDiagonal_nonneg_iff_dualFeasible params model Z

/-- Paper dual feasibility implies feasibility of the canonical block dual
constraint. -/
theorem matrixSdpCanonicalDualConstraint_nonneg_of_dualFeasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g) :
    0 ≤ matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model :=
  (matrixSdpCanonicalDualConstraint_nonneg_iff_dualFeasible params model Z).mpr hdual

/-- Feasibility of the canonical block dual constraint recovers the paper dual
inequalities. -/
theorem matrixSdpDualFeasible_of_canonicalDualConstraint_nonneg
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hcanonical :
      0 ≤ matrixSdpCanonicalDualOperator params model Z -
        matrixSdpCanonicalObjectiveOperator params model) :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model Z g :=
  (matrixSdpCanonicalDualConstraint_nonneg_iff_dualFeasible params model Z).mp hcanonical

/-- The paper's strict dual witness `Z = 2I` is feasible for the canonical dual
constraint. -/
theorem matrixSdpCanonicalStrictDualConstraint_nonneg
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    0 ≤ matrixSdpCanonicalDualOperator params model (matrixSdpStrictDualWitness model) -
        matrixSdpCanonicalObjectiveOperator params model :=
  matrixSdpCanonicalDualConstraint_nonneg_of_dualFeasible params model
    (matrixSdpStrictDualWitness model)
    (matrixSdpStrictDualWitness_dualFeasible params model)

/-- Every canonical dual-slack block of the strict dual witness dominates the
identity. -/
theorem one_le_matrixSdpCanonicalStrictDualSlackBlockFamily
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (b : MatrixSdpCanonicalBlockIndex params) :
    (1 : MatrixOperator model.space) ≤
      matrixSdpCanonicalDualSlackBlockFamily params model
        (matrixSdpStrictDualWitness model) b := by
  cases b with
  | none =>
      exact one_le_matrixSdpStrictDualWitness model
  | some g =>
      exact one_le_matrixSdpStrictDualWitness_dualSlack params model g

/-- The canonical strict dual slack dominates the identity on the block Hilbert
space. -/
theorem one_le_matrixSdpCanonicalStrictDualConstraint
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    (1 : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) ≤
      matrixSdpCanonicalDualOperator params model (matrixSdpStrictDualWitness model) -
        matrixSdpCanonicalObjectiveOperator params model := by
  rw [← sub_nonneg]
  rw [matrixSdpCanonicalDualOperator_sub_objectiveOperator]
  let B :=
    matrixSdpCanonicalDualSlackBlockFamily params model (matrixSdpStrictDualWitness model)
  have hsub :
      matrixSdpCanonicalBlockDiagonal params model B -
          (1 : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) =
        matrixSdpCanonicalBlockDiagonal params model
          (fun b => B b - (1 : MatrixOperator model.space)) := by
    ext x y
    rcases x with ⟨b, i⟩
    rcases y with ⟨c, j⟩
    by_cases hbc : b = c
    · subst c
      by_cases hij : i = j
      · subst j
        simp [B, matrixSdpCanonicalBlockDiagonal]
      · simp [B, matrixSdpCanonicalBlockDiagonal, hij]
    · simp [B, matrixSdpCanonicalBlockDiagonal, hbc]
  rw [hsub]
  refine matrixSdpCanonicalBlockDiagonal_nonneg params model
    (fun b => B b - (1 : MatrixOperator model.space)) ?_
  intro b
  exact sub_nonneg.mpr
    (one_le_matrixSdpCanonicalStrictDualSlackBlockFamily params model b)

/-- The canonical block matrix associated to the strict primal witness is
feasible for the canonical primal SDP. -/
theorem matrixSdpCanonicalStrictPrimalBlockMatrix_feasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixSdpCanonicalPrimalFeasible params model
      (matrixSdpCanonicalPrimalBlockMatrix params model
        (matrixSdpStrictPrimalSubmeasurement params model)) :=
  matrixSdpCanonicalPrimalBlockMatrix_feasible params model
    (matrixSdpStrictPrimalSubmeasurement params model)

/-- The slack block of the strict primal canonical matrix is `(1/2)I`. -/
theorem matrixSdpCanonicalStrictPrimalBlockMatrix_slack_half
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalPrimalBlockMatrix params model
          (matrixSdpStrictPrimalSubmeasurement params model)) none =
      ((1 / 2 : Error) • (1 : MatrixOperator model.space)) := by
  rw [matrixSdpCanonicalDiagonalBlock_primalBlockMatrix_none,
    matrixSdpCanonicalSlackOperator,
    matrixSdpStrictPrimalSubmeasurement_sum_effect]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
    norm_num
  · simp [hij]

/-- Canonical block-SDP feasible bounds supplied by the explicit paper
Slater-type witnesses.

This is not an optimality statement.  It records the primal canonical
feasibility of the uniform family, the strict slack block `(1/2)I`, the
canonical dual constraint for `Z = 2I`, and the corresponding paper dual
feasibility data. -/
structure MatrixSdpCanonicalFeasibleBounds (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) : Prop where
  primalFeasible :
    MatrixSdpCanonicalPrimalFeasible params model
      (matrixSdpCanonicalPrimalBlockMatrix params model
        (matrixSdpStrictPrimalSubmeasurement params model))
  primalSlackHalf :
    matrixSdpCanonicalDiagonalBlock params model
        (matrixSdpCanonicalPrimalBlockMatrix params model
          (matrixSdpStrictPrimalSubmeasurement params model)) none =
      ((1 / 2 : Error) • (1 : MatrixOperator model.space))
  canonicalDualFeasible :
    0 ≤ matrixSdpCanonicalDualOperator params model (matrixSdpStrictDualWitness model) -
        matrixSdpCanonicalObjectiveOperator params model
  paperDualFeasible :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model (matrixSdpStrictDualWitness model) g
  paperDualSlackDominatesIdentity :
    ∀ g : Polynomial params,
      (1 : MatrixOperator model.space) ≤
        matrixSdpDualSlackOperator params model (matrixSdpStrictDualWitness model) g
  dualDominatesIdentity :
    (1 : MatrixOperator model.space) ≤ matrixSdpStrictDualWitness model
  canonicalDualSlackDominatesIdentity :
    (1 : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) ≤
      matrixSdpCanonicalDualOperator params model (matrixSdpStrictDualWitness model) -
        matrixSdpCanonicalObjectiveOperator params model

/-- The explicit uniform primal witness and `Z=2I` give the canonical feasible
bounds used before applying finite-dimensional SDP strong duality. -/
theorem matrixSdpCanonicalFeasibleBounds_canonical
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixSdpCanonicalFeasibleBounds params model where
  primalFeasible := matrixSdpCanonicalStrictPrimalBlockMatrix_feasible params model
  primalSlackHalf := matrixSdpCanonicalStrictPrimalBlockMatrix_slack_half params model
  canonicalDualFeasible := matrixSdpCanonicalStrictDualConstraint_nonneg params model
  paperDualFeasible := matrixSdpStrictDualWitness_dualFeasible params model
  paperDualSlackDominatesIdentity :=
    one_le_matrixSdpStrictDualWitness_dualSlack params model
  dualDominatesIdentity := one_le_matrixSdpStrictDualWitness model
  canonicalDualSlackDominatesIdentity :=
    one_le_matrixSdpCanonicalStrictDualConstraint params model

/-- The canonical block objective evaluated on the block matrix associated to a
paper primal submeasurement is the paper primal objective.

The paper writes this as `Tr(C† X)`.  In the present canonical model the
objective blocks are the averaged point operators, hence Hermitian measurement
effects averaged over points; the without-dagger trace pairing used here is the
same expression in this Hermitian case. -/
theorem matrixSdpCanonicalObjective_trace_primalBlockMatrix
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model *
          matrixSdpCanonicalPrimalBlockMatrix params model T)) =
      matrixSdpPrimalObjective params model T := by
  rw [matrixSdpCanonicalObjectiveOperator, matrixSdpCanonicalPrimalBlockMatrix]
  rw [matrixSdpCanonicalBlockDiagonal_trace_mul]
  rw [Fintype.sum_option]
  simp only [matrixSdpCanonicalObjectiveBlockFamily_none,
    matrixSdpCanonicalPrimalBlockFamily_none, zero_mul, Matrix.trace_zero,
    matrixSdpCanonicalObjectiveBlockFamily_some, matrixSdpCanonicalPrimalBlockFamily_some,
    zero_add, Complex.re_sum]
  unfold matrixSdpPrimalObjective matrixSdpPrimalContributionOperator
  rw [Matrix.trace_sum]
  simp only [Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro g _
  rw [Matrix.trace_mul_comm]

/-- The strict primal canonical matrix has the paper primal objective of the
strict primal submeasurement. -/
theorem matrixSdpCanonicalStrictPrimalBlockMatrix_objective
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model *
          matrixSdpCanonicalPrimalBlockMatrix params model
            (matrixSdpStrictPrimalSubmeasurement params model))) =
      matrixSdpPrimalObjective params model
        (matrixSdpStrictPrimalSubmeasurement params model) :=
  matrixSdpCanonicalObjective_trace_primalBlockMatrix params model
    (matrixSdpStrictPrimalSubmeasurement params model)

/-- The canonical block objective evaluated on an arbitrary feasible canonical
primal matrix is the paper primal objective of its extracted submeasurement.

This is the converse objective identity to
`matrixSdpCanonicalObjective_trace_primalBlockMatrix`: once a canonical feasible
matrix `X` is given, reading the polynomial diagonal blocks as `T_g = X_{gg}`
preserves the SDP objective value. -/
theorem matrixSdpCanonicalObjective_trace_extractedPrimalSubmeasurement
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model * X)) =
      matrixSdpPrimalObjective params model
        (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX) := by
  rw [matrixSdpCanonicalObjectiveOperator]
  rw [matrixSdpCanonicalBlockDiagonal_trace_mul_left]
  rw [Fintype.sum_option]
  simp only [matrixSdpCanonicalObjectiveBlockFamily_none, zero_mul, Matrix.trace_zero,
    matrixSdpCanonicalObjectiveBlockFamily_some, zero_add, Complex.re_sum]
  unfold matrixSdpPrimalObjective matrixSdpPrimalContributionOperator
  rw [Matrix.trace_sum]
  simp only [Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro g _
  rw [matrixSdpCanonicalExtractedPrimalSubmeasurement_effect]
  rw [Matrix.trace_mul_comm]

/-- Replacing a feasible canonical matrix by the canonical block matrix of the
extracted paper submeasurement preserves the canonical objective value. -/
theorem matrixSdpCanonicalObjective_trace_primalBlockMatrix_extracted
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X) :
    Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model *
          matrixSdpCanonicalPrimalBlockMatrix params model
            (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX))) =
      Complex.re (Matrix.trace
        (matrixSdpCanonicalObjectiveOperator params model * X)) := by
  rw [matrixSdpCanonicalObjective_trace_primalBlockMatrix]
  rw [matrixSdpCanonicalObjective_trace_extractedPrimalSubmeasurement]

/-- The diagonal block of a canonical primal-dual slack product is the product
of the corresponding primal diagonal block and canonical dual slack block. -/
theorem matrixSdpCanonicalDiagonalBlock_mul_dualSlack
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (Z : MatrixOperator model.space)
    (b : MatrixSdpCanonicalBlockIndex params) :
    matrixSdpCanonicalDiagonalBlock params model
        (X * (matrixSdpCanonicalDualOperator params model Z -
          matrixSdpCanonicalObjectiveOperator params model)) b =
      matrixSdpCanonicalDiagonalBlock params model X b *
        matrixSdpCanonicalDualSlackBlockFamily params model Z b := by
  rw [matrixSdpCanonicalDualOperator_sub_objectiveOperator]
  exact matrixSdpCanonicalDiagonalBlock_mul_blockDiagonal_right params model X
    (matrixSdpCanonicalDualSlackBlockFamily params model Z) b

/-- The concrete complementary-slackness defect `T_g (Z - A_g)`. -/
noncomputable def matrixSdpComplementarySlacknessDefect (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space)
    (g : Polynomial params) : MatrixOperator model.space :=
  (T.effect g) * matrixSdpDualSlackOperator params model Z g

/-- Multiplying the canonical primal block matrix by the canonical dual slack
keeps only the blockwise products.

This is the formal block-diagonal calculation behind the paper's passage from
canonical complementary slackness to the equations
`T_g (Z - A_g) = 0`. -/
theorem matrixSdpCanonicalPrimalBlockMatrix_mul_dualSlack
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) :
    matrixSdpCanonicalPrimalBlockMatrix params model T *
        (matrixSdpCanonicalDualOperator params model Z -
          matrixSdpCanonicalObjectiveOperator params model) =
      matrixSdpCanonicalBlockDiagonal params model
        (fun b =>
          matrixSdpCanonicalPrimalBlockFamily params model T b *
            matrixSdpCanonicalDualSlackBlockFamily params model Z b) := by
  rw [matrixSdpCanonicalDualOperator_sub_objectiveOperator,
    matrixSdpCanonicalPrimalBlockMatrix,
    matrixSdpCanonicalBlockDiagonal_mul]

/-- If a feasible canonical primal matrix satisfies canonical complementary
slackness, then the block-diagonal matrix obtained from its polynomial diagonal
blocks also satisfies canonical complementary slackness.

This is the formal version of the reduction in the SDP proof which permits one
to replace an optimal canonical matrix by its block-diagonal part. -/
theorem matrixSdpCanonicalPrimalBlockMatrix_extracted_mul_dualSlack_of_canonical
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (Z : MatrixOperator model.space)
    (hcanonical :
      X * (matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model) =
        0) :
    matrixSdpCanonicalPrimalBlockMatrix params model
          (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX) *
        (matrixSdpCanonicalDualOperator params model Z -
          matrixSdpCanonicalObjectiveOperator params model) =
      0 := by
  rw [matrixSdpCanonicalPrimalBlockMatrix_mul_dualSlack]
  ext x y
  rcases x with ⟨b, i⟩
  rcases y with ⟨c, j⟩
  by_cases hbc : b = c
  · subst c
    have hentry :
        (matrixSdpCanonicalDiagonalBlock params model X b *
            matrixSdpCanonicalDualSlackBlockFamily params model Z b) i j = 0 := by
      have hblock :=
        congrArg (fun Y => matrixSdpCanonicalDiagonalBlock params model Y b)
          hcanonical
      change matrixSdpCanonicalDiagonalBlock params model
          (X * (matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model)) b =
        matrixSdpCanonicalDiagonalBlock params model 0 b at hblock
      rw [matrixSdpCanonicalDiagonalBlock_mul_dualSlack] at hblock
      simpa [matrixSdpCanonicalDiagonalBlock] using congrFun (congrFun hblock i) j
    cases b with
    | none =>
        simpa [matrixSdpCanonicalBlockDiagonal, matrixSdpCanonicalPrimalBlockFamily,
          matrixSdpCanonicalSlackOperator_extractedPrimalSubmeasurement] using hentry
    | some g =>
        simpa [matrixSdpCanonicalBlockDiagonal, matrixSdpCanonicalPrimalBlockFamily] using
          hentry
  · simp [matrixSdpCanonicalBlockDiagonal, hbc]

/-- Canonical complementary slackness implies the paper-form defect equation
`T_g (Z - A_g) = 0` on each polynomial block. -/
theorem matrixSdpComplementarySlacknessDefect_of_canonical
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space)
    (hcanonical :
      matrixSdpCanonicalPrimalBlockMatrix params model T *
          (matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model) =
        0)
    (g : Polynomial params) :
    matrixSdpComplementarySlacknessDefect params model T Z g = 0 := by
  have hblock :=
    congrArg
      (fun X => matrixSdpCanonicalDiagonalBlock params model X (some g))
      hcanonical
  rw [matrixSdpCanonicalPrimalBlockMatrix_mul_dualSlack] at hblock
  simpa [matrixSdpComplementarySlacknessDefect, matrixSdpCanonicalDiagonalBlock] using
    hblock

/-- Canonical complementary slackness for a feasible canonical matrix gives
the paper-form defect equation for the extracted paper primal submeasurement. -/
theorem matrixSdpComplementarySlacknessDefect_extracted_of_canonical
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (Z : MatrixOperator model.space)
    (hcanonical :
      X * (matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model) =
        0)
    (g : Polynomial params) :
    matrixSdpComplementarySlacknessDefect params model
        (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX) Z g =
      0 :=
  matrixSdpComplementarySlacknessDefect_of_canonical params model
    (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX) Z
    (matrixSdpCanonicalPrimalBlockMatrix_extracted_mul_dualSlack_of_canonical
      params model X hX Z hcanonical) g

/-- Canonical complementary slackness also gives the slack-block equation
`S Z = 0`, where `S = I - ∑_g T_g`. -/
theorem matrixSdpCanonicalSlack_mul_dual_of_complementarySlackness
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space)
    (hcanonical :
      matrixSdpCanonicalPrimalBlockMatrix params model T *
          (matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model) =
        0) :
    matrixSdpCanonicalSlackOperator params model T * Z = 0 := by
  have hblock :=
    congrArg
      (fun X => matrixSdpCanonicalDiagonalBlock params model X none)
      hcanonical
  rw [matrixSdpCanonicalPrimalBlockMatrix_mul_dualSlack] at hblock
  simpa [matrixSdpCanonicalDiagonalBlock] using hblock

/-- If the canonical slack block annihilates a dual operator which dominates the
identity, then the slack block itself vanishes.

This is the positivity step used after canonical complementary slackness: the
paper obtains `S Z = 0` for the slack block `S = I - ∑_g T_g`; since the selected
dual satisfies `I ≤ Z`, no non-zero positive slack can remain. -/
theorem matrixSdpCanonicalSlackOperator_eq_zero_of_mul_dual_eq_zero_of_one_le
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space)
    (hSlackDual : matrixSdpCanonicalSlackOperator params model T * Z = 0)
    (hOneLe : (1 : MatrixOperator model.space) ≤ Z) :
    matrixSdpCanonicalSlackOperator params model T = 0 :=
  MIPStarRE.Quantum.eq_zero_of_nonneg_mul_eq_zero_of_one_le
    (matrixSdpCanonicalSlackOperator_nonneg params model T) hOneLe hSlackDual

/-- Vanishing of the canonical slack block is exactly saturation of the paper
primal submeasurement. -/
theorem matrixSdpPrimalTotalEqOne_of_canonicalSlackOperator_eq_zero
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (hSlack : matrixSdpCanonicalSlackOperator params model T = 0) :
    ∑ g : Polynomial params, T.effect g = 1 := by
  have hsub : (1 : MatrixOperator model.space) - ∑ g : Polynomial params, T.effect g = 0 := by
    simpa [matrixSdpCanonicalSlackOperator] using hSlack
  exact (sub_eq_zero.mp hsub).symm

/-- Canonical complementary slackness, together with the dominance condition
`I ≤ Z`, saturates the paper primal submeasurement.

This theorem is the matrix-level form of the paper's passage from the canonical
slack-block equation `S Z = 0` to `S = 0`, hence
`∑_g T_g = I`. -/
theorem matrixSdpPrimalTotalEqOne_of_canonicalComplementarySlackness_of_one_le
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space)
    (hcanonical :
      matrixSdpCanonicalPrimalBlockMatrix params model T *
          (matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model) =
        0)
    (hOneLe : (1 : MatrixOperator model.space) ≤ Z) :
    ∑ g : Polynomial params, T.effect g = 1 := by
  exact matrixSdpPrimalTotalEqOne_of_canonicalSlackOperator_eq_zero params model T
    (matrixSdpCanonicalSlackOperator_eq_zero_of_mul_dual_eq_zero_of_one_le
      params model T Z
      (matrixSdpCanonicalSlack_mul_dual_of_complementarySlackness
        params model T Z hcanonical)
      hOneLe)

/-- Canonical complementary slackness and \(I \le Z\) saturate the extracted
paper primal submeasurement. -/
theorem matrixSdpPrimalTotalEqOne_extracted_of_canonicalComplementarySlackness_of_one_le
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model))
    (hX : MatrixSdpCanonicalPrimalFeasible params model X)
    (Z : MatrixOperator model.space)
    (hcanonical :
      X * (matrixSdpCanonicalDualOperator params model Z -
            matrixSdpCanonicalObjectiveOperator params model) =
        0)
    (hOneLe : (1 : MatrixOperator model.space) ≤ Z) :
    ∑ g : Polynomial params,
        (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX).effect g =
      1 :=
  matrixSdpPrimalTotalEqOne_of_canonicalComplementarySlackness_of_one_le
    params model (matrixSdpCanonicalExtractedPrimalSubmeasurement params model X hX) Z
    (matrixSdpCanonicalPrimalBlockMatrix_extracted_mul_dualSlack_of_canonical
      params model X hX Z hcanonical)
    hOneLe

end MIPStarRE.LDT.SelfImprovement
