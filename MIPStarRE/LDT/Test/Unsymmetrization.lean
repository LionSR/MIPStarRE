import MIPStarRE.LDT.Test.SymmetrizationBridge

/-!
# Section 3 — measurement unsymmetrization

This file isolates the role-register measurement extraction used in
`references/ldt-paper/inductive_step.tex` lines 84--105.  If a measurement `G`
acts on the symmetrized local space `Role × ι`, then
`Measurement.extractRole Role.A G` and `Measurement.extractRole Role.B G` are the
paper's principal blocks

`G^A_g = (⟨0| ⊗ I) G_g (|0⟩ ⊗ I)` and
`G^B_g = (⟨1| ⊗ I) G_g (|1⟩ ⊗ I)`.

The extraction preserves POVM completeness.  It deliberately does **not** claim
that arbitrary principal blocks of a projective measurement remain projective;
the paper restores projectivity later via the projectivization step.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- Principal role block of an operator on the symmetrized local space.

For `r = Role.A` this is the Lean matrix form of
`(⟨0| ⊗ I) Y (|0⟩ ⊗ I)`, and for `r = Role.B` it is the analogous `1`-role
block from `inductive_step.tex` lines 86--90. -/
noncomputable def extractRoleBlock {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) (Y : MIPStarRE.Quantum.Op (Role × ι)) :
    MIPStarRE.Quantum.Op ι :=
  Y.submatrix (fun i => (r, i)) (fun i => (r, i))

@[simp] theorem extractRoleBlock_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) (Y : MIPStarRE.Quantum.Op (Role × ι)) (i j : ι) :
    extractRoleBlock r Y i j = Y (r, i) (r, j) :=
  rfl

@[simp] theorem extractRoleBlock_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) :
    extractRoleBlock (ι := ι) r 0 = 0 := by
  ext i j
  rfl

@[simp] theorem extractRoleBlock_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) (X Y : MIPStarRE.Quantum.Op (Role × ι)) :
    extractRoleBlock r (X + Y) = extractRoleBlock r X + extractRoleBlock r Y := by
  ext i j
  rfl

@[simp] theorem extractRoleBlock_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) (X Y : MIPStarRE.Quantum.Op (Role × ι)) :
    extractRoleBlock r (X - Y) = extractRoleBlock r X - extractRoleBlock r Y := by
  ext i j
  rfl

@[simp] theorem extractRoleBlock_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) (c : ℂ) (Y : MIPStarRE.Quantum.Op (Role × ι)) :
    extractRoleBlock r (c • Y) = c • extractRoleBlock r Y := by
  ext i j
  rfl

@[simp] theorem extractRoleBlock_finset_sum {α ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (r : Role) (s : Finset α) (f : α → MIPStarRE.Quantum.Op (Role × ι)) :
    extractRoleBlock r (∑ a ∈ s, f a) = ∑ a ∈ s, extractRoleBlock r (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert, ha, ih]

@[simp] theorem extractRoleBlock_univ_sum {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (r : Role) (f : α → MIPStarRE.Quantum.Op (Role × ι)) :
    extractRoleBlock r (∑ a, f a) = ∑ a, extractRoleBlock r (f a) := by
  exact extractRoleBlock_finset_sum (ι := ι) r Finset.univ f

@[simp] theorem extractRoleBlock_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) :
    extractRoleBlock (ι := ι) r 1 = 1 := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

/-- Principal role blocks preserve positive semidefiniteness. -/
theorem extractRoleBlock_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) {Y : MIPStarRE.Quantum.Op (Role × ι)} (hY : 0 ≤ Y) :
    0 ≤ extractRoleBlock r Y := by
  exact Matrix.nonneg_iff_posSemidef.mpr <|
    (Matrix.nonneg_iff_posSemidef.mp hY).submatrix (fun i => (r, i))

/-- Principal role blocks are monotone for the matrix order. -/
theorem extractRoleBlock_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) {X Y : MIPStarRE.Quantum.Op (Role × ι)} (hXY : X ≤ Y) :
    extractRoleBlock r X ≤ extractRoleBlock r Y := by
  rw [Matrix.le_iff] at hXY ⊢
  simpa [extractRoleBlock_sub] using
    (Matrix.nonneg_iff_posSemidef.mp (Matrix.nonneg_iff_posSemidef.mpr hXY)).submatrix
      (fun i : ι => (r, i))

namespace SubMeas

/-- Extract one role block from every outcome of a submeasurement on `Role × ι`. -/
noncomputable def extractRole {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (r : Role) (A : SubMeas α (Role × ι)) : SubMeas α ι where
  outcome := fun a => extractRoleBlock r (A.outcome a)
  total := extractRoleBlock r A.total
  outcome_pos := by
    intro a
    exact extractRoleBlock_nonneg r (A.outcome_pos a)
  sum_eq_total := by
    simpa using congrArg (extractRoleBlock (ι := ι) r) A.sum_eq_total
  total_le_one := by
    simpa using extractRoleBlock_le r A.total_le_one

@[simp] theorem extractRole_outcome {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (r : Role) (A : SubMeas α (Role × ι)) (a : α) :
    (A.extractRole r).outcome a = extractRoleBlock r (A.outcome a) :=
  rfl

@[simp] theorem extractRole_total {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (r : Role) (A : SubMeas α (Role × ι)) :
    (A.extractRole r).total = extractRoleBlock r A.total :=
  rfl

/-- Role extraction commutes with outcome postprocessing. -/
theorem extractRole_postprocess {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (r : Role) (A : SubMeas α (Role × ι)) (f : α → β) :
    (postprocess A f).extractRole r = postprocess (A.extractRole r) f := by
  classical
  refine SubMeas.ext ?_ rfl
  intro b
  change extractRoleBlock r
      (∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a) =
    ∑ a ∈ Finset.univ.filter (fun a => f a = b),
      extractRoleBlock r (A.outcome a)
  exact
    extractRoleBlock_finset_sum (ι := ι) r
      (Finset.univ.filter (fun a => f a = b)) A.outcome

end SubMeas

namespace Measurement

/-- Extract one role block from every outcome of a POVM on `Role × ι`.

This is the POVM part of the unsymmetrization step in
`inductive_step.tex` lines 91--95. -/
noncomputable def extractRole {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (r : Role) (A : Measurement α (Role × ι)) : Measurement α ι where
  toSubMeas := A.toSubMeas.extractRole r
  total_eq_one := by
    simpa [SubMeas.extractRole] using congrArg (extractRoleBlock (ι := ι) r) A.total_eq_one

@[simp] theorem extractRole_toSubMeas {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (r : Role) (A : Measurement α (Role × ι)) :
    (A.extractRole r).toSubMeas = A.toSubMeas.extractRole r :=
  rfl

@[simp] theorem extractRole_outcome {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (r : Role) (A : Measurement α (Role × ι)) (a : α) :
    (A.extractRole r).outcome a = extractRoleBlock r (A.outcome a) :=
  rfl

end Measurement

/-- Extract the polynomial POVM that acts as the original Alice prover from a
role-register main-induction output. -/
noncomputable def extractRoleAMeasurement {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Measurement (Polynomial params) (Role × ι)) :
    Measurement (Polynomial params) ι :=
  G.extractRole Role.A

/-- Extract the polynomial POVM that acts as the original Bob prover from a
role-register main-induction output. -/
noncomputable def extractRoleBMeasurement {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Measurement (Polynomial params) (Role × ι)) :
    Measurement (Polynomial params) ι :=
  G.extractRole Role.B

@[simp] theorem extractRoleBlock_roleCond_same {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (r : Role) (X : MIPStarRE.Quantum.Op ι) :
    extractRoleBlock r (roleCond r X) = X := by
  ext i j
  cases r <;> simp [extractRoleBlock, roleCond, roleProj, opTensor]

@[simp] theorem extractRoleBlock_roleCond_A_B {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (X : MIPStarRE.Quantum.Op ι) :
    extractRoleBlock Role.A (roleCond Role.B X) = 0 := by
  ext i j
  simp [extractRoleBlock, roleCond, roleProj, opTensor]

@[simp] theorem extractRoleBlock_roleCond_B_A {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (X : MIPStarRE.Quantum.Op ι) :
    extractRoleBlock Role.B (roleCond Role.A X) = 0 := by
  ext i j
  simp [extractRoleBlock, roleCond, roleProj, opTensor]

/-- Extracting the `A` block from a block-diagonal role symmetrization recovers the
left input family. -/
theorem extractRole_symmetrizedIdxProjMeas_A {Question Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (MA MB : IdxProjMeas Question Outcome ι) (q : Question) :
    ((symmetrizedIdxProjMeas MA MB q).toMeasurement.extractRole Role.A).toSubMeas =
      (MA q).toSubMeas := by
  refine SubMeas.ext ?_ ?_
  · intro a
    simp [symmetrizedIdxProjMeas, SubMeas.extractRole]
  · simpa [symmetrizedIdxProjMeas, SubMeas.extractRole] using
      (MA q).total_eq_one.symm

/-- Extracting the `B` block from a block-diagonal role symmetrization recovers the
right input family. -/
theorem extractRole_symmetrizedIdxProjMeas_B {Question Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (MA MB : IdxProjMeas Question Outcome ι) (q : Question) :
    ((symmetrizedIdxProjMeas MA MB q).toMeasurement.extractRole Role.B).toSubMeas =
      (MB q).toSubMeas := by
  refine SubMeas.ext ?_ ?_
  · intro a
    simp [symmetrizedIdxProjMeas, SubMeas.extractRole]
  · simpa [symmetrizedIdxProjMeas, SubMeas.extractRole] using
      (MB q).total_eq_one.symm

/-- Extracting the `A` block of the symmetrized point measurement recovers the
original Alice point measurement. -/
theorem strategySymmetrization_point_extractRole_A {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) (u : Point params) :
    (((strategy.strategySymmetrization).pointMeasurement u).toMeasurement.extractRole
        Role.A).toSubMeas =
      (strategy.pointMeasurementA u).toSubMeas := by
  simpa [ProjStrat.strategySymmetrization, ProjStrat.classicalRoleSymmStrategy,
    ProjStrat.symmetrizedPointMeasurement] using
    extractRole_symmetrizedIdxProjMeas_A strategy.pointMeasurementA strategy.pointMeasurementB u

/-- Extracting the `B` block of the symmetrized point measurement recovers the
original Bob point measurement. -/
theorem strategySymmetrization_point_extractRole_B {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) (u : Point params) :
    (((strategy.strategySymmetrization).pointMeasurement u).toMeasurement.extractRole
        Role.B).toSubMeas =
      (strategy.pointMeasurementB u).toSubMeas := by
  simpa [ProjStrat.strategySymmetrization, ProjStrat.classicalRoleSymmStrategy,
    ProjStrat.symmetrizedPointMeasurement] using
    extractRole_symmetrizedIdxProjMeas_B strategy.pointMeasurementA strategy.pointMeasurementB u

/-- Evaluating a polynomial submeasurement after role extraction agrees with
extracting the role block after point-evaluation postprocessing. -/
theorem polynomialEvaluationFamily_extractRole {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) (G : SubMeas (Polynomial params) (Role × ι)) :
    polynomialEvaluationFamily params (G.extractRole r) =
      fun u => (polynomialEvaluationFamily params G u).extractRole r := by
  funext u
  exact (SubMeas.extractRole_postprocess r G (fun g : Polynomial params => g u)).symm

/-- The measurement-level specialization of `polynomialEvaluationFamily_extractRole`. -/
theorem polynomialEvaluationFamily_measurement_extractRole {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) (G : Measurement (Polynomial params) (Role × ι)) :
    polynomialEvaluationFamily params (G.extractRole r).toSubMeas =
      fun u => (polynomialEvaluationFamily params G.toSubMeas u).extractRole r := by
  exact polynomialEvaluationFamily_extractRole r G.toSubMeas

/-- The paper's unsymmetrized Alice-role POVM attached to a role-register
main-induction output. -/
noncomputable abbrev unsymmetrizedLeftPOVM {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Measurement (Polynomial params) (Role × ι)) :
    Measurement (Polynomial params) ι :=
  extractRoleAMeasurement G

/-- The paper's unsymmetrized Bob-role POVM attached to a role-register
main-induction output. -/
noncomputable abbrev unsymmetrizedRightPOVM {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Measurement (Polynomial params) (Role × ι)) :
    Measurement (Polynomial params) ι :=
  extractRoleBMeasurement G

/-- Named residual package for the Step 3 measurement-unsymmetrization bridge.

The extracted POVMs are not additional fields: they are definitionally
`unsymmetrizedLeftPOVM G` and `unsymmetrizedRightPOVM G`, i.e. the two principal
role blocks of the role-register measurement `G`.  The two remaining proof fields
are exactly the paper's factor-two consistency estimates `eq:cons-a` and
`eq:cons-b` from `inductive_step.tex` lines 97--108.  Keeping them in this small
package lets the final `mainFormal` assembly depend on a precise Step 3 residual
instead of a conclusion-shaped whole-theorem assumption. -/
structure UnsymmetrizationBridgePackage (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι)
    (G : Measurement (Polynomial params) (Role × ι)) (sigma : Error) : Prop where
  /-- The main-induction consistency input on the role-register symmetrized strategy. -/
  symConsistency :
    ConsRel (strategy.strategySymmetrization).state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas)
      sigma
  /-- Paper `eq:cons-b` / lines 97--108: original Alice point measurements are
  consistent with the Bob-role extraction, with the factor-two loss. -/
  pointAConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params (unsymmetrizedRightPOVM G).toSubMeas)
      (2 * sigma)
  /-- Paper `eq:cons-a` / lines 105--108: the Alice-role extraction is consistent
  with original Bob point measurements, with the factor-two loss. -/
  pointBConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params (unsymmetrizedLeftPOVM G).toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      (2 * sigma)

end MIPStarRE.LDT
