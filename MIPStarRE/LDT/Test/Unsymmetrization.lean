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
  roleBlock r Y

@[simp] theorem extractRoleBlock_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) (Y : MIPStarRE.Quantum.Op (Role × ι)) (i j : ι) :
    extractRoleBlock r Y i j = Y (r, i) (r, j) :=
  rfl

@[simp] theorem extractRoleBlock_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) :
    extractRoleBlock (ι := ι) r 0 = 0 :=
  rfl

@[simp] theorem extractRoleBlock_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) (X Y : MIPStarRE.Quantum.Op (Role × ι)) :
    extractRoleBlock r (X + Y) = extractRoleBlock r X + extractRoleBlock r Y :=
  rfl

@[simp] theorem extractRoleBlock_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) (X Y : MIPStarRE.Quantum.Op (Role × ι)) :
    extractRoleBlock r (X - Y) = extractRoleBlock r X - extractRoleBlock r Y :=
  rfl

@[simp] theorem extractRoleBlock_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : Role) (c : ℂ) (Y : MIPStarRE.Quantum.Op (Role × ι)) :
    extractRoleBlock r (c • Y) = c • extractRoleBlock r Y :=
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
  simpa [extractRoleBlock_sub] using hXY.submatrix (fun i : ι => (r, i))

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
  cases r <;> simp [extractRoleBlock, roleBlock, roleCond, roleProj, opTensor]

@[simp] theorem extractRoleBlock_roleCond_A_B {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (X : MIPStarRE.Quantum.Op ι) :
    extractRoleBlock Role.A (roleCond Role.B X) = 0 := by
  ext i j
  simp [extractRoleBlock, roleBlock, roleCond, roleProj, opTensor]

@[simp] theorem extractRoleBlock_roleCond_B_A {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (X : MIPStarRE.Quantum.Op ι) :
    extractRoleBlock Role.B (roleCond Role.A X) = 0 := by
  ext i j
  simp [extractRoleBlock, roleBlock, roleCond, roleProj, opTensor]

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
    (strategy : SameSpaceProjStrat params ι) (u : Point params) :
    (((strategy.strategySymmetrization).pointMeasurement u).toMeasurement.extractRole
        Role.A).toSubMeas =
      (strategy.pointMeasurementA u).toSubMeas := by
  simpa [SameSpaceProjStrat.strategySymmetrization, SameSpaceProjStrat.classicalRoleSymmStrategy,
    SameSpaceProjStrat.symmetrizedPointMeasurement] using
    extractRole_symmetrizedIdxProjMeas_A strategy.pointMeasurementA strategy.pointMeasurementB u

/-- Extracting the `B` block of the symmetrized point measurement recovers the
original Bob point measurement. -/
theorem strategySymmetrization_point_extractRole_B {params : Parameters}
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (u : Point params) :
    (((strategy.strategySymmetrization).pointMeasurement u).toMeasurement.extractRole
        Role.B).toSubMeas =
      (strategy.pointMeasurementB u).toSubMeas := by
  simpa [SameSpaceProjStrat.strategySymmetrization, SameSpaceProjStrat.classicalRoleSymmStrategy,
    SameSpaceProjStrat.symmetrizedPointMeasurement] using
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

/-- Matching mass against an arbitrary role-register measurement only sees its
principal role blocks. -/
theorem qBipartiteMatchMass_roleSymmetrizedMeasurement_left {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (MA MB : Measurement Outcome ι) (G : Measurement Outcome (Role × ι)) :
    qBipartiteMatchMass (classicalRoleSymmState ψ)
        (roleSymmetrizedMeasurement MA MB).toSubMeas G.toSubMeas =
      (qBipartiteMatchMass ψ MA.toSubMeas (G.extractRole Role.B).toSubMeas +
        qBipartiteMatchMass ψ (G.extractRole Role.A).toSubMeas MB.toSubMeas) / 2 := by
  have houtcome : ∀ a : Outcome,
      ev (classicalRoleSymmState ψ)
          (opTensor ((roleSymmetrizedMeasurement MA MB).outcome a) (G.outcome a)) =
        (1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) ((G.extractRole Role.B).outcome a)) +
          (1 / 2 : Error) * ev ψ (opTensor ((G.extractRole Role.A).outcome a) (MB.outcome a)) := by
    intro a
    calc
      ev (classicalRoleSymmState ψ)
          (opTensor ((roleSymmetrizedMeasurement MA MB).outcome a) (G.outcome a))
        = ev (classicalRoleSymmState ψ)
            (opTensor (roleCond Role.A (MA.outcome a)) (G.outcome a) +
              opTensor (roleCond Role.B (MB.outcome a)) (G.outcome a)) := by
              congr 1
              ext i j
              simp [opTensor, add_mul]
      _ = ev (classicalRoleSymmState ψ)
            (opTensor (roleCond Role.A (MA.outcome a)) (G.outcome a)) +
          ev (classicalRoleSymmState ψ)
            (opTensor (roleCond Role.B (MB.outcome a)) (G.outcome a)) := by
              rw [ev_add]
      _ = (1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) ((G.extractRole Role.B).outcome a)) +
          (1 / 2 : Error) * ev ψ (opTensor ((G.extractRole Role.A).outcome a) (MB.outcome a)) := by
            rw [ev_classicalRoleSymmState_opTensor_roleCond_A]
            rw [ev_classicalRoleSymmState_opTensor_roleCond_B]
            rfl
  unfold qBipartiteMatchMass
  calc
    ∑ a : Outcome,
        ev (classicalRoleSymmState ψ)
          (opTensor ((roleSymmetrizedMeasurement MA MB).outcome a) (G.outcome a))
      = ∑ a : Outcome,
          ((1 / 2 : Error) *
              ev ψ (opTensor (MA.outcome a) ((G.extractRole Role.B).outcome a)) +
            (1 / 2 : Error) *
              ev ψ (opTensor ((G.extractRole Role.A).outcome a) (MB.outcome a))) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          exact houtcome a
    _ = (1 / 2 : Error) * ∑ a : Outcome,
          ev ψ (opTensor (MA.outcome a) ((G.extractRole Role.B).outcome a)) +
        (1 / 2 : Error) * ∑ a : Outcome,
          ev ψ (opTensor ((G.extractRole Role.A).outcome a) (MB.outcome a)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (qBipartiteMatchMass ψ MA.toSubMeas (G.extractRole Role.B).toSubMeas +
          qBipartiteMatchMass ψ (G.extractRole Role.A).toSubMeas MB.toSubMeas) / 2 := by
          simp [qBipartiteMatchMass]
          ring

/-- Questionwise unsymmetrization identity: the role-register consistency defect is
the average of the two unsymmetrized defects. -/
theorem qBipartiteConsDefect_roleSymmetrizedMeasurement_left {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (MA MB : Measurement Outcome ι) (G : Measurement Outcome (Role × ι)) :
    qBipartiteConsDefect (classicalRoleSymmState ψ)
        (roleSymmetrizedMeasurement MA MB).toSubMeas G.toSubMeas =
      (qBipartiteConsDefect ψ MA.toSubMeas (G.extractRole Role.B).toSubMeas +
        qBipartiteConsDefect ψ (G.extractRole Role.A).toSubMeas MB.toSubMeas) / 2 := by
  calc
    qBipartiteConsDefect (classicalRoleSymmState ψ)
        (roleSymmetrizedMeasurement MA MB).toSubMeas G.toSubMeas
      = ev (classicalRoleSymmState ψ)
          (1 : MIPStarRE.Quantum.Op ((Role × ι) × (Role × ι))) -
        qBipartiteMatchMass (classicalRoleSymmState ψ)
          (roleSymmetrizedMeasurement MA MB).toSubMeas G.toSubMeas := by
          exact qBipartiteConsDefect_of_measurements (classicalRoleSymmState ψ)
            (roleSymmetrizedMeasurement MA MB) G
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
        (qBipartiteMatchMass ψ MA.toSubMeas (G.extractRole Role.B).toSubMeas +
          qBipartiteMatchMass ψ (G.extractRole Role.A).toSubMeas MB.toSubMeas) / 2 := by
          rw [ev_classicalRoleSymmState_one]
          rw [qBipartiteMatchMass_roleSymmetrizedMeasurement_left]
    _ = ((ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ MA.toSubMeas (G.extractRole Role.B).toSubMeas) +
          (ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
            qBipartiteMatchMass ψ (G.extractRole Role.A).toSubMeas MB.toSubMeas)) / 2 := by
          ring
    _ = (qBipartiteConsDefect ψ MA.toSubMeas (G.extractRole Role.B).toSubMeas +
          qBipartiteConsDefect ψ (G.extractRole Role.A).toSubMeas MB.toSubMeas) / 2 := by
          rw [← qBipartiteConsDefect_of_measurements ψ MA (G.extractRole Role.B)]
          rw [← qBipartiteConsDefect_of_measurements ψ (G.extractRole Role.A) MB]

/-- One questionwise factor-two consequence of the unsymmetrization identity. -/
theorem qBipartiteConsDefect_extractRoleB_le_two_symm {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (MA MB : Measurement Outcome ι) (G : Measurement Outcome (Role × ι)) :
    qBipartiteConsDefect ψ MA.toSubMeas (G.extractRole Role.B).toSubMeas ≤
      2 * qBipartiteConsDefect (classicalRoleSymmState ψ)
        (roleSymmetrizedMeasurement MA MB).toSubMeas G.toSubMeas := by
  have h := qBipartiteConsDefect_roleSymmetrizedMeasurement_left ψ MA MB G
  have hnonneg : 0 ≤ qBipartiteConsDefect ψ (G.extractRole Role.A).toSubMeas MB.toSubMeas :=
    qBipartiteConsDefect_nonneg ψ (G.extractRole Role.A).toSubMeas MB.toSubMeas
  linarith

/-- The other questionwise factor-two consequence of the unsymmetrization identity. -/
theorem qBipartiteConsDefect_extractRoleA_le_two_symm {Outcome ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι))
    (MA MB : Measurement Outcome ι) (G : Measurement Outcome (Role × ι)) :
    qBipartiteConsDefect ψ (G.extractRole Role.A).toSubMeas MB.toSubMeas ≤
      2 * qBipartiteConsDefect (classicalRoleSymmState ψ)
        (roleSymmetrizedMeasurement MA MB).toSubMeas G.toSubMeas := by
  have h := qBipartiteConsDefect_roleSymmetrizedMeasurement_left ψ MA MB G
  have hnonneg : 0 ≤ qBipartiteConsDefect ψ MA.toSubMeas (G.extractRole Role.B).toSubMeas :=
    qBipartiteConsDefect_nonneg ψ MA.toSubMeas (G.extractRole Role.B).toSubMeas
  linarith

/-- Step 3 role-block consistency statement for measurement unsymmetrization.

Paper origin: `references/ldt-paper/inductive_step.tex:84-109`
(`\label{eq:cons-a}` and `\label{eq:cons-b}`).

The extracted POVMs are not additional fields: they are definitionally
`unsymmetrizedLeftPOVM G` and `unsymmetrizedRightPOVM G`, i.e. the two principal
role blocks of the role-register measurement `G`.  The two proof fields are
exactly the paper's factor-two consistency estimates `eq:cons-a` and `eq:cons-b`
from `inductive_step.tex` lines 97--108.  The constructor
`UnsymmetrizationConsistency.ofSymConsistency` proves these two estimates from
the symmetrized role-register consistency estimate. -/
structure UnsymmetrizationConsistency (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι)
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

namespace UnsymmetrizationConsistency

/-- Construct the Step 3 unsymmetrization consistency statement from the role-register
symmetrized consistency estimate.

The proof is the formal version of the paper's factor-two argument: for each
queried point, the role-register consistency defect is the average of the two
principal-block defects, so each block defect is at most twice the symmetrized
one. Averaging over the point distribution gives `eq:cons-a` and `eq:cons-b`. -/
theorem ofSymConsistency (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι)
    (G : Measurement (Polynomial params) (Role × ι)) (sigma : Error)
    (h : ConsRel (strategy.strategySymmetrization).state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement)
      (polynomialEvaluationFamily params G.toSubMeas)
      sigma) :
    UnsymmetrizationConsistency params strategy G sigma := by
  haveI : Nonempty ι := strategy.isNormalized.nonempty.map Prod.fst
  refine
    { symConsistency := h
      pointAConsistency := ?_
      pointBConsistency := ?_ }
  · constructor
    unfold bipartiteConsError
    calc
      avgOver (uniformDistribution (Point params))
          (fun u =>
            qBipartiteConsDefect strategy.state
              ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA) u)
              ((polynomialEvaluationFamily params (unsymmetrizedRightPOVM G).toSubMeas) u))
        ≤ avgOver (uniformDistribution (Point params))
          (fun u =>
            2 * qBipartiteConsDefect (strategy.strategySymmetrization).state
              ((IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement) u)
              ((polynomialEvaluationFamily params G.toSubMeas) u)) := by
            refine avgOver_mono _ _ _ ?_
            intro u
            let Gu : Measurement (Fq params) (Role × ι) :=
              { toSubMeas := (polynomialEvaluationFamily params G.toSubMeas) u
                total_eq_one := by
                  simpa [polynomialEvaluationFamily, evaluateAt, postprocess_total] using
                    G.total_eq_one }
            have hpoint := qBipartiteConsDefect_extractRoleB_le_two_symm strategy.state
              (strategy.pointMeasurementA u).toMeasurement
              (strategy.pointMeasurementB u).toMeasurement Gu
            simpa [Gu, SameSpaceProjStrat.strategySymmetrization,
              SameSpaceProjStrat.classicalRoleSymmStrategy,
              SameSpaceProjStrat.symmetrizedPointMeasurement, roleSymmetrizedMeasurement,
              symmetrizedIdxProjMeas, IdxProjMeas.toIdxSubMeas,
              unsymmetrizedRightPOVM, extractRoleBMeasurement,
              polynomialEvaluationFamily_extractRole,
              polynomialEvaluationFamily_measurement_extractRole]
              using hpoint
      _ = 2 * avgOver (uniformDistribution (Point params))
          (fun u =>
            qBipartiteConsDefect (strategy.strategySymmetrization).state
              ((IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement) u)
              ((polynomialEvaluationFamily params G.toSubMeas) u)) := by
            rw [avgOver_const_mul]
      _ ≤ 2 * sigma := by
            exact mul_le_mul_of_nonneg_left h.offDiagonalBound (by norm_num)
  · constructor
    unfold bipartiteConsError
    calc
      avgOver (uniformDistribution (Point params))
          (fun u =>
            qBipartiteConsDefect strategy.state
              ((polynomialEvaluationFamily params (unsymmetrizedLeftPOVM G).toSubMeas) u)
              ((IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB) u))
        ≤ avgOver (uniformDistribution (Point params))
          (fun u =>
            2 * qBipartiteConsDefect (strategy.strategySymmetrization).state
              ((IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement) u)
              ((polynomialEvaluationFamily params G.toSubMeas) u)) := by
            refine avgOver_mono _ _ _ ?_
            intro u
            let Gu : Measurement (Fq params) (Role × ι) :=
              { toSubMeas := (polynomialEvaluationFamily params G.toSubMeas) u
                total_eq_one := by
                  simpa [polynomialEvaluationFamily, evaluateAt, postprocess_total] using
                    G.total_eq_one }
            have hpoint := qBipartiteConsDefect_extractRoleA_le_two_symm strategy.state
              (strategy.pointMeasurementA u).toMeasurement
              (strategy.pointMeasurementB u).toMeasurement Gu
            simpa [Gu, SameSpaceProjStrat.strategySymmetrization,
              SameSpaceProjStrat.classicalRoleSymmStrategy,
              SameSpaceProjStrat.symmetrizedPointMeasurement, roleSymmetrizedMeasurement,
              symmetrizedIdxProjMeas, IdxProjMeas.toIdxSubMeas,
              unsymmetrizedLeftPOVM, extractRoleAMeasurement,
              polynomialEvaluationFamily_extractRole,
              polynomialEvaluationFamily_measurement_extractRole]
              using hpoint
      _ = 2 * avgOver (uniformDistribution (Point params))
          (fun u =>
            qBipartiteConsDefect (strategy.strategySymmetrization).state
              ((IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement) u)
              ((polynomialEvaluationFamily params G.toSubMeas) u)) := by
            rw [avgOver_const_mul]
      _ ≤ 2 * sigma := by
            exact mul_le_mul_of_nonneg_left h.offDiagonalBound (by norm_num)

end UnsymmetrizationConsistency

end MIPStarRE.LDT
