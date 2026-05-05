import MIPStarRE.LDT.ExpansionHypercubeGraph.MatrixRealization
import MIPStarRE.LDT.SelfImprovement.Defs

/-!
# Section 9 — Matrix realization

Concrete finite-dimensional matrix realizations of the self-improvement SDP data.

## References

- `references/ldt-paper/self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

/-- A concrete finite-dimensional matrix realization of the SDP data. -/
structure MatrixSdpRealization (params : Parameters) [FieldModel params.q] where
  space : FiniteHilbertSpace
  state : PositiveMatrixState space
  pointMeasurement : Point params → MatrixSubmeasurement (Fq params) space

/-- The matrix-level strict-feasible primal witness
`T_g = (2 |\polyfunc{m}{q}{d}|)^{-1} I`. -/
noncomputable def matrixSdpStrictPrimalSubmeasurement (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space where
  effect := (sdpStrictPrimalSubMeas (ι := model.space.carrier) params).outcome
  pos := (sdpStrictPrimalSubMeas (ι := model.space.carrier) params).outcome_pos
  sum_le_one := by
    simpa [(sdpStrictPrimalSubMeas (ι := model.space.carrier) params).sum_eq_total] using
      (sdpStrictPrimalSubMeas (ι := model.space.carrier) params).total_le_one

/-- The matrix-level strict-feasible primal witness has total mass
`(1/2) I`. -/
theorem matrixSdpStrictPrimalSubmeasurement_sum_effect (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∑ g : Polynomial params,
        (matrixSdpStrictPrimalSubmeasurement params model).effect g =
      ((1 / 2 : Error) • (1 : MatrixOperator model.space)) := by
  calc
    ∑ g : Polynomial params,
        (matrixSdpStrictPrimalSubmeasurement params model).effect g =
        (sdpStrictPrimalSubMeas (ι := model.space.carrier) params).total := by
          simpa [matrixSdpStrictPrimalSubmeasurement] using
            (sdpStrictPrimalSubMeas (ι := model.space.carrier) params).sum_eq_total
    _ = ((1 / 2 : Error) • (1 : MatrixOperator model.space)) :=
        sdpStrictPrimalSubMeas_total (ι := model.space.carrier) params

/-- The paper's matrix-level strict-feasible dual witness `Z = 2I`. -/
noncomputable def matrixSdpStrictDualWitness {params : Parameters} [FieldModel params.q]
    (model : MatrixSdpRealization params) : MatrixOperator model.space :=
  (2 : Error) • (1 : MatrixOperator model.space)

/-- The matrix-level strict-feasible dual witness is positive semidefinite. -/
theorem matrixSdpStrictDualWitness_nonneg {params : Parameters} [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    0 ≤ matrixSdpStrictDualWitness model := by
  unfold matrixSdpStrictDualWitness
  exact smul_nonneg (by norm_num)
    (op_one_nonneg (d := model.space.carrier))

/-- The matrix-level strict-feasible dual witness dominates the identity. -/
theorem one_le_matrixSdpStrictDualWitness {params : Parameters} [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    (1 : MatrixOperator model.space) ≤ matrixSdpStrictDualWitness model := by
  calc
    (1 : MatrixOperator model.space) =
        (1 : Error) • (1 : MatrixOperator model.space) := by simp
    _ ≤ (2 : Error) • (1 : MatrixOperator model.space) :=
        smul_le_smul_of_nonneg_right
          (show (1 : Error) ≤ 2 by norm_num)
          (op_one_nonneg (d := model.space.carrier))

/-- The concrete operator `A^u_{g(u)}` entering the SDP average. -/
def matrixAveragedPointOperatorContribution (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) (u : Point params) : MatrixOperator model.space :=
  (model.pointMeasurement u).effect (g u)

/-- The concrete averaged operator `A_g = E_u A^u_{g(u)}`.

This is defined through the project-wide distributional average
`averageOperatorOverDistribution` so that the submeasurement averaging lemmas
apply directly.  The operator is used only in this matrix realization layer. -/
noncomputable def matrixAveragedPointOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) : MatrixOperator model.space :=
  averageOperatorOverDistribution (uniformDistribution (Point params))
    (matrixAveragedPointOperatorContribution params model g)

/-- The averaged point operator `A_g` is bounded by the identity. -/
theorem matrixAveragedPointOperator_le_one (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) :
    matrixAveragedPointOperator params model g ≤ 1 := by
  let A : SubMeas Unit model.space.carrier :=
    averageUnitSubMeas (ι := model.space.carrier)
      (matrixAveragedPointOperatorContribution params model g)
      (fun u => (model.pointMeasurement u).pos (g u))
      (fun u => by
        calc
          (model.pointMeasurement u).effect (g u)
              ≤ ∑ a : Fq params, (model.pointMeasurement u).effect a :=
                Finset.single_le_sum
                  (fun a _ => (model.pointMeasurement u).pos a)
                  (Finset.mem_univ (g u))
          _ ≤ 1 := (model.pointMeasurement u).sum_le_one)
  simpa [A, matrixAveragedPointOperator, matrixAveragedPointOperatorContribution,
    averageUnitSubMeas_outcome] using
      A.outcome_le_one ()

/-- The averaged point operator `A_g` is positive semidefinite. -/
theorem matrixAveragedPointOperator_nonneg (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (g : Polynomial params) :
    0 ≤ matrixAveragedPointOperator params model g := by
  unfold matrixAveragedPointOperator averageOperatorOverDistribution
  exact Finset.sum_nonneg fun u _ =>
    smul_nonneg ((uniformDistribution (Point params)).nonnegative u)
      ((model.pointMeasurement u).pos (g u))

/-- The concrete primal contribution `T_g A_g`. -/
noncomputable def matrixSdpPrimalContributionOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (g : Polynomial params) : MatrixOperator model.space :=
  (T.effect g) * matrixAveragedPointOperator params model g

/-- The concrete primal objective `Σ_g Re Tr(T_g A_g)`. -/
noncomputable def matrixSdpPrimalObjective (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) : Error :=
  Complex.re (Matrix.trace (∑ g : Polynomial params,
    matrixSdpPrimalContributionOperator params model T g))

/-- The concrete dual objective `Re Tr(Z)`. -/
noncomputable def matrixSdpDualObjective {params : Parameters} [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space) : Error :=
  Complex.re (Matrix.trace Z)

/-- The concrete dual slack operator `Z - A_g`. -/
noncomputable def matrixSdpDualSlackOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (g : Polynomial params) : MatrixOperator model.space :=
  Z - matrixAveragedPointOperator params model g

/-- The matrix-level strict-feasible dual witness `2I` dominates every averaged
point operator. -/
theorem matrixSdpStrictDualWitness_dualFeasible (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model (matrixSdpStrictDualWitness model) g := by
  intro g
  exact sub_nonneg.mpr
    (le_trans (matrixAveragedPointOperator_le_one params model g)
      (one_le_matrixSdpStrictDualWitness model))

/-- Dual feasibility already implies that the dual operator is positive
semidefinite, since every averaged point operator `A_g` is positive. -/
theorem matrixSdpDualPositive_of_dualFeasible (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (Z : MatrixOperator model.space)
    (hdual :
      ∀ g : Polynomial params,
        0 ≤ matrixSdpDualSlackOperator params model Z g) :
    0 ≤ Z := by
  -- Any polynomial would suffice here; the distinguished one is only a
  -- convenient fixed element of the finite polynomial type.
  let g0 : Polynomial params := sdpDistinguishedPolynomial params
  have hAg_nonneg : 0 ≤ matrixAveragedPointOperator params model g0 :=
    matrixAveragedPointOperator_nonneg params model g0
  have hAg_le_Z : matrixAveragedPointOperator params model g0 ≤ Z :=
    sub_nonneg.mp (by simpa [matrixSdpDualSlackOperator] using hdual g0)
  exact hAg_nonneg.trans hAg_le_Z

/-- Matrix-level record of the explicit feasible bounds used in the SDP argument.

The uniform primal family has total `(1/2)I`, while the dual witness `2I`
dominates the identity and is dual feasible. Positivity of the dual witness is
derivable from dual feasibility and the positivity of the averaged point
operators. These are the non-strict matrix inequalities currently recorded in
Lean; the structure is not an optimality statement and does not include
complementary slackness. -/
structure MatrixSdpFeasibleBounds (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) : Prop where
  primalTotalHalf :
    ∑ g : Polynomial params, T.effect g =
      ((1 / 2 : Error) • (1 : MatrixOperator model.space))
  dualDominatesIdentity : (1 : MatrixOperator model.space) ≤ Z
  dualFeasible :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model Z g

/-- The canonical explicit matrix feasible bounds used in the SDP argument. -/
theorem matrixSdpFeasibleBounds_canonical (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) :
    MatrixSdpFeasibleBounds params model
      (matrixSdpStrictPrimalSubmeasurement params model)
      (matrixSdpStrictDualWitness model) where
  primalTotalHalf := matrixSdpStrictPrimalSubmeasurement_sum_effect params model
  dualDominatesIdentity := one_le_matrixSdpStrictDualWitness model
  dualFeasible := matrixSdpStrictDualWitness_dualFeasible params model

/-! ### Canonical block primal form -/

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
  fun x y => if x.1 = y.1 then B x.1 x.2 y.2 else 0

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
        (Matrix.blockDiagonal B) := by
  ext x y
  rcases x with ⟨b, i⟩
  rcases y with ⟨c, j⟩
  simp [matrixSdpCanonicalBlockDiagonal, Matrix.reindex_apply, Matrix.blockDiagonal_apply]

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
  rw [Matrix.trace]
  trans ∑ x : MatrixSdpCanonicalBlockIndex params × model.space.carrier,
      ∑ j : model.space.carrier, B x.1 x.2 j * D x.1 j x.2
  · refine Finset.sum_congr rfl ?_
    intro x _
    simp only [Matrix.diag_apply]
    rw [Matrix.mul_apply]
    change (∑ y : MatrixSdpCanonicalBlockIndex params × model.space.carrier,
        matrixSdpCanonicalBlockDiagonal params model B x y *
          matrixSdpCanonicalBlockDiagonal params model D y x) =
      ∑ j : model.space.carrier, B x.1 x.2 j * D x.1 j x.2
    rw [Fintype.sum_prod_type]
    simp [matrixSdpCanonicalBlockDiagonal]
  · rw [Fintype.sum_prod_type]
    simp [Matrix.trace, Matrix.mul_apply]

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
`∑_g X_{gg} = I`. -/
structure MatrixSdpCanonicalPrimalFeasible (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (X : MatrixOperator (matrixSdpCanonicalBlockHilbertSpace params model)) : Prop where
  /-- The canonical primal matrix variable is positive semidefinite. -/
  nonnegative : 0 ≤ X
  /-- The diagonal-block equality constraint holds. -/
  constraint_eq_one : matrixSdpCanonicalConstraintOperator params model X = 1

/-- A paper primal submeasurement determines a feasible point of the canonical
block primal SDP by adjoining the slack block `I - ∑_g T_g`. -/
theorem matrixSdpCanonicalPrimalBlockMatrix_feasible
    (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    MatrixSdpCanonicalPrimalFeasible params model
      (matrixSdpCanonicalPrimalBlockMatrix params model T) where
  nonnegative := matrixSdpCanonicalPrimalBlockMatrix_nonneg params model T
  constraint_eq_one := matrixSdpCanonicalConstraintOperator_primalBlockMatrix params model T

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

/-- The concrete complementary-slackness defect `T_g (Z - A_g)`. -/
noncomputable def matrixSdpComplementarySlacknessDefect (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space)
    (g : Polynomial params) : MatrixOperator model.space :=
  (T.effect g) * matrixSdpDualSlackOperator params model Z g

/-- Matrix-level witness for an optimal SDP pair. -/
structure MatrixSdpOptimalWitness (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) : Prop where
  primalTotalEqOne :
    ∑ g : Polynomial params, T.effect g = 1
  dualFeasible :
    ∀ g : Polynomial params,
      0 ≤ matrixSdpDualSlackOperator params model Z g
  strongDuality :
    matrixSdpPrimalObjective params model T = matrixSdpDualObjective model Z
  complementarySlackness :
    ∀ g : Polynomial params,
      matrixSdpComplementarySlacknessDefect params model T Z g = 0

/-- Matrix-level optimal SDP witness together with the dominance condition
required by the reduced abstract helper interface.

The paper's dual SDP feasibility gives \(Z \ge A_g\).  The current reduced
abstract interface also asks for \(I \le Z\), because boundedness is expressed
against this dual operator.  This successor package records that extra
dominance for the same optimal dual witness, without changing the matrix
strong-duality statement below. -/
structure MatrixSdpOptimalWitnessWithDominance (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) : Prop where
  toMatrixSdpOptimalWitness :
    MatrixSdpOptimalWitness params model T Z
  dualDominatesIdentity : (1 : MatrixOperator model.space) ≤ Z

/-- Matrix-level statement of the strong-duality output for the SDP.

This is the concrete matrix analogue of `SdpStatementWithSlackness`: it does
not assert that the currently formalized reduced `sdp` witness is optimal.
Instead it records the kind of optimal witness obtained from the paper's
Slater/strong-duality argument.

Grounded by: #1230. -/
structure MatrixSdpStatementWithSlackness (params : Parameters) [FieldModel params.q]
    (model : MatrixSdpRealization params) : Prop where
  witness :
    ∃ T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space,
      ∃ Z : MatrixOperator model.space,
        MatrixSdpOptimalWitness params model T Z

/-- Matrix-level strong-duality statement with the additional dominance
condition needed by the reduced abstract helper interface.

This is the matrix-side target for the downstream bridge into
`SelfImprovementHelperConclusionWithSlackness`: it keeps the same optimal pair
and complementary-slackness data as `MatrixSdpStatementWithSlackness`, and also
records \(I \le Z\) for the selected dual witness. -/
structure MatrixSdpStatementWithSlacknessAndDominance (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params) : Prop where
  witness :
    ∃ T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space,
      ∃ Z : MatrixOperator model.space,
        MatrixSdpOptimalWitnessWithDominance params model T Z

/-- The concrete complementary-slackness equation `T_g Z = T_g A_g`. -/
def matrixSdpComplementarySlacknessEquation (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space)
    (g : Polynomial params) : Prop :=
  T.effect g * Z = T.effect g * matrixAveragedPointOperator params model g

namespace MatrixSdpOptimalWitness

/-- The dual operator in an optimal matrix SDP witness is positive
semidefinite.  This follows from dual feasibility, because the averaged point
operators are positive. -/
theorem dualPositive {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space}
    {Z : MatrixOperator model.space}
    (h : MatrixSdpOptimalWitness params model T Z) :
    0 ≤ Z :=
  matrixSdpDualPositive_of_dualFeasible params model Z h.dualFeasible

/-- An optimal matrix SDP witness whose primal total is the identity determines
a complete matrix measurement. -/
noncomputable def primalMeasurement {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space}
    {Z : MatrixOperator model.space}
    (h : MatrixSdpOptimalWitness params model T Z) :
    MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space :=
  MIPStarRE.Quantum.Measurement.ofSumEqOne T.effect T.pos h.primalTotalEqOne

@[simp] theorem primalMeasurement_effect {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space}
    {Z : MatrixOperator model.space}
    (h : MatrixSdpOptimalWitness params model T Z) (g : Polynomial params) :
    h.primalMeasurement.effect g = T.effect g :=
  rfl

/-- The defect-zero form of complementary slackness is the equation
`T_g Z = T_g A_g`. -/
theorem complementarySlacknessEquation {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    {T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space}
    {Z : MatrixOperator model.space}
    (h : MatrixSdpOptimalWitness params model T Z) (g : Polynomial params) :
    matrixSdpComplementarySlacknessEquation params model T Z g := by
  have hzero :
      T.effect g * Z - T.effect g * matrixAveragedPointOperator params model g = 0 := by
    simpa [matrixSdpComplementarySlacknessDefect, matrixSdpDualSlackOperator,
      Matrix.mul_sub] using h.complementarySlackness g
  exact sub_eq_zero.mp hzero

end MatrixSdpOptimalWitness

namespace MatrixSdpStatementWithSlacknessAndDominance

/-- Forget the additional dominance condition and recover the matrix-level
strong-duality statement with complementary slackness. -/
theorem toMatrixSdpStatementWithSlackness {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    (h : MatrixSdpStatementWithSlacknessAndDominance params model) :
    MatrixSdpStatementWithSlackness params model := by
  obtain ⟨T, Z, hopt⟩ := h.witness
  exact ⟨T, Z, hopt.toMatrixSdpOptimalWitness⟩

end MatrixSdpStatementWithSlacknessAndDominance

namespace MatrixSdpStatementWithSlackness

/-- A matrix strong-duality statement gives a complete primal measurement, a
dual operator, dual feasibility, equality of objective values, and the
complementary-slackness equations in the displayed `T_g Z = T_g A_g` form. -/
theorem exists_measurement_witness {params : Parameters} [FieldModel params.q]
    {model : MatrixSdpRealization params}
    (h : MatrixSdpStatementWithSlackness params model) :
    ∃ T : MatrixMeasurement (DegreeBoundedPolynomialAnswer params) model.space,
      ∃ Z : MatrixOperator model.space,
        0 ≤ Z ∧
        (∀ g : Polynomial params, 0 ≤ matrixSdpDualSlackOperator params model Z g) ∧
        matrixSdpPrimalObjective params model T.toSubmeasurement =
          matrixSdpDualObjective model Z ∧
        ∀ g : Polynomial params,
          T.effect g * Z = T.effect g * matrixAveragedPointOperator params model g := by
  obtain ⟨Tsub, Z, hopt⟩ := h.witness
  refine ⟨hopt.primalMeasurement, Z, hopt.dualPositive, hopt.dualFeasible, ?_, ?_⟩
  · simpa [MatrixSdpOptimalWitness.primalMeasurement] using hopt.strongDuality
  · intro g
    simpa using hopt.complementarySlacknessEquation g

end MatrixSdpStatementWithSlackness

/-- A raw point-indexed matrix outcome family used in the matrix `add-in-u` transfer. -/
abbrev MatrixIndexedPointOutcomeFamily (params : Parameters) [FieldModel params.q]
    (Outcome : Type*) (H : FiniteHilbertSpace) :=
  Point params → Outcome → MatrixOperator H

/-- The concrete sandwiched operator `A^u_{h(u)} T_h A^u_{h(u)}`. -/
noncomputable def matrixSandwichedPolynomialOutcomeOperatorAt (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (u : Point params) (h : Polynomial params) : MatrixOperator model.space :=
  let Au := matrixAveragedPointOperatorContribution params model h u
  Au * (T.effect h) * Au

/-- The averaged concrete sandwiched operator `E_u A^u_{h(u)} T_h A^u_{h(u)}`. -/
noncomputable def matrixAveragedSandwichedPolynomialOutcomeOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (h : Polynomial params) : MatrixOperator model.space :=
  matrixAverageOperator (fun u : Point params =>
    matrixSandwichedPolynomialOutcomeOperatorAt params model T u h)

/-- The matrix left-hand operator in `add-in-u`. -/
noncomputable def matrixAddInULeftOperatorAtPoint {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (S : AddInUSelection params Outcome)
    (u : Point params) : MatrixOperator model.space :=
  ∑ ah ∈ addInUSelectionPairs params S u,
    (M u ah.1) * (H.effect ah.2)

/-- The matrix right-hand operator in `add-in-u`. -/
noncomputable def matrixAddInURightOperatorAtPoint {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (S : AddInUSelection params Outcome)
    (u : Point params) : MatrixOperator model.space :=
  ∑ ah ∈ addInUSelectionPairs params S u,
    let Au := matrixAveragedPointOperatorContribution params model ah.2 u
    Au * (M u ah.1) * Au * (T.effect ah.2)

private noncomputable def matrixAddInUPointAverage (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (f : Point params → MatrixOperator model.space) : Error :=
  finiteAverage (fun u : Point params => Complex.re (matrixExpectation model.state (f u)))

/-- The matrix left-hand expectation in `add-in-u`. -/
noncomputable def matrixAddInULeftQuantity {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (S : AddInUSelection params Outcome) : Error :=
  matrixAddInUPointAverage params model (matrixAddInULeftOperatorAtPoint params model M H S)

/-- The matrix right-hand expectation in `add-in-u`. -/
noncomputable def matrixAddInURightQuantity {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (S : AddInUSelection params Outcome) : Error :=
  matrixAddInUPointAverage params model (matrixAddInURightOperatorAtPoint params model M T S)

/-- The concrete evaluated polynomial family `H_[h(u)=a]`. -/
noncomputable def matrixPolynomialEvaluationOutcomeOperatorAtPoint (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (u : Point params) (a : Fq params) : MatrixOperator model.space :=
  let evalFamily :=
    MIPStarRE.Quantum.Submeasurement.postprocess (M := H) (fun h => h u)
  evalFamily.effect a

/-- The concrete matched operator `Σ_a A^u_a H_[h(u)=a]`. -/
noncomputable def matrixHelperAgreementOperatorAtPoint (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (u : Point params) : MatrixOperator model.space :=
  ∑ a : Fq params,
    (model.pointMeasurement u).effect a *
      matrixPolynomialEvaluationOutcomeOperatorAtPoint params model H u a

/-- The concrete averaged matched operator `E_u Σ_a A^u_a H_[h(u)=a]`. -/
noncomputable def matrixHelperAgreementAverageOperator (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space) :
    MatrixOperator model.space :=
  matrixAverageOperator (fun u : Point params =>
    matrixHelperAgreementOperatorAtPoint params model H u)

/-- The concrete helper boundedness gap `Re τ(ρ (Z - E_u Σ_a A^u_a H_[h(u)=a]))`. -/
noncomputable def matrixHelperBoundednessGap (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) : Error :=
  Complex.re (matrixExpectation model.state
    (Z - matrixHelperAgreementAverageOperator params model H))

/-- The concrete projective residual gap `Re τ(ρ (Z (I - Σ_h H_h)))`. -/
noncomputable def matrixProjectiveResidualGap (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (Z : MatrixOperator model.space) : Error :=
  let total := MIPStarRE.Quantum.Submeasurement.total H
  Complex.re (matrixExpectation model.state (Z * (1 - total)))

/-- Matrix-level version of the `add-in-u` transfer inequality. -/
structure MatrixAddInUTransferStatement {Outcome : Type*} [Fintype Outcome]
    (params : Parameters)
    [FieldModel params.q]
    (model : MatrixSdpRealization params)
    (T : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (M : MatrixIndexedPointOutcomeFamily params Outcome model.space)
    (H : MatrixSubmeasurement (DegreeBoundedPolynomialAnswer params) model.space)
    (eps delta : Error) : Prop where
  transfer :
    ∀ S : AddInUSelection params Outcome,
      |matrixAddInULeftQuantity params model M H S -
          matrixAddInURightQuantity params model M T S| ≤
        addInUError params eps delta

end MIPStarRE.LDT.SelfImprovement
