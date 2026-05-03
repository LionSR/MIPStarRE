import MIPStarRE.LDT.Basic.SubMeasurementCore
import MIPStarRE.LDT.Basic.OperatorExpectations

/-!
# Tensor-placement helper lemmas and sandwich tensor estimates

Tensor-sum commutation, positivity/boundedness preservation,
factoring lemmas, and sandwich-residual estimates used in
the main induction step and polynomial-agreement arguments.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-! ### Tensor-placement helper lemmas -/

/-- Left tensor placement commutes with finite sums. -/
theorem leftTensor_finset_sum {α : Type*}
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (s : Finset α) (f : α → MIPStarRE.Quantum.Op ι₁) :
    Finset.sum s (fun a => leftTensor (ι₂ := ι₂) (f a)) =
      leftTensor (ι₂ := ι₂) (Finset.sum s f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [leftTensor]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
      simp [leftTensor, Matrix.add_kronecker]

/-- Expanding the left-tensor mass of a submeasurement on a bipartite state as
the sum of per-outcome left-tensor expectations.

This is a generic identity at the level of `ev ψ (leftTensor _)`: applying
`SubMeas.sum_eq_total`, pulling `leftTensor` through the finite sum via
`leftTensor_finset_sum`, and distributing `ev` through the sum via
`ev_finset_sum`. Using the definitional equalities
`subMeasMass ψ A.liftLeft = ev ψ A.liftLeft.total = ev ψ (leftTensor A.total)`,
this immediately yields the helper-stage opening
`subMeasMass ψ A.liftLeft = ∑ a, ev ψ (leftTensor (A.outcome a))` used in the
Section 9 / Section 12 calculations. -/
theorem ev_leftTensor_total_eq_sum_outcome {α : Type*} [Fintype α]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (A : SubMeas α ι) :
    ev ψ (leftTensor (ι₂ := ι) A.total) =
      ∑ a : α, ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) := by
  rw [← A.sum_eq_total,
      ← leftTensor_finset_sum (ι₂ := ι) Finset.univ (fun a : α => A.outcome a),
      ev_finset_sum]

/-- Right tensor placement commutes with finite sums. -/
theorem rightTensor_finset_sum {α : Type*}
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (s : Finset α) (f : α → MIPStarRE.Quantum.Op ι₂) :
    Finset.sum s (fun a => rightTensor (ι₁ := ι₁) (f a)) =
      rightTensor (ι₁ := ι₁) (Finset.sum s f) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [rightTensor]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ih]
      simp [rightTensor, Matrix.kronecker_add]

/-- A complex scalar on the left register factors out of a bipartite tensor product.

This is the tensor-placement version of bilinearity of `opTensor`: placing
`c • A` on the left and multiplying by the right placement of `B` equals the
same scalar multiplying `leftTensor A * rightTensor B`. -/
theorem leftTensor_mul_rightTensor_smul_left
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (c : Error) (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    leftTensor (ι₂ := ι₂) ((c : ℂ) • A) * rightTensor (ι₁ := ι₁) B =
      (c : ℂ) • (leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) B) := by
  rw [leftTensor_mul_rightTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
  simpa [opTensor] using Matrix.smul_kronecker (c : ℂ) A B

/-- A complex scalar on the right register factors out of a bipartite tensor product.

This is the tensor-placement version of bilinearity of `opTensor`: placing
`c • B` on the right and multiplying by the left placement of `A` equals the
same scalar multiplying `leftTensor A * rightTensor B`. -/
theorem leftTensor_mul_rightTensor_smul_right
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (c : Error) (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) ((c : ℂ) • B) =
      (c : ℂ) • (leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) B) := by
  rw [leftTensor_mul_rightTensor_eq_opTensor, leftTensor_mul_rightTensor_eq_opTensor]
  simpa [opTensor] using Matrix.kronecker_smul (c : ℂ) A B

/-- A real scalar on the left register factors out of a bipartite tensor product.

This restates `leftTensor_mul_rightTensor_smul_left` for the real scalar action
used by `averageOperatorOverDistribution`, coercing the real scalar to `ℂ` on
the tensor product. -/
theorem leftTensor_mul_rightTensor_real_smul_left
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (c : Error) (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    leftTensor (ι₂ := ι₂) (c • A) * rightTensor (ι₁ := ι₁) B =
      (c : ℂ) • (leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) B) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact leftTensor_mul_rightTensor_smul_left c A B

/-- A real scalar on the right register factors out of a bipartite tensor product.

This restates `leftTensor_mul_rightTensor_smul_right` for the real scalar action
used by `averageOperatorOverDistribution`, coercing the real scalar to `ℂ` on
the tensor product. -/
theorem leftTensor_mul_rightTensor_real_smul_right
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (c : Error) (A : MIPStarRE.Quantum.Op ι₁) (B : MIPStarRE.Quantum.Op ι₂) :
    leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) (c • B) =
      (c : ℂ) • (leftTensor (ι₂ := ι₂) A * rightTensor (ι₁ := ι₁) B) := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact leftTensor_mul_rightTensor_smul_right c A B

/-- Left tensor placement preserves positivity. -/
theorem leftTensor_nonneg
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₁} (hA : 0 ≤ A) :
    0 ≤ leftTensor (ι₂ := ι₂) A := by
  simpa [leftTensor, opTensor] using
    (opTensor_nonneg
      (A := A) (B := (1 : MIPStarRE.Quantum.Op ι₂)) hA
      (zero_le_one : (0 : MIPStarRE.Quantum.Op ι₂) ≤ 1))

/-- Right tensor placement preserves positivity. -/
theorem rightTensor_nonneg
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₂} (hA : 0 ≤ A) :
    0 ≤ rightTensor (ι₁ := ι₁) A := by
  simpa [rightTensor, opTensor] using
    (opTensor_nonneg
      (A := (1 : MIPStarRE.Quantum.Op ι₁)) (B := A)
      (zero_le_one : (0 : MIPStarRE.Quantum.Op ι₁) ≤ 1) hA)

/-- Left tensor placement preserves the operator bound `≤ 1`. -/
theorem leftTensor_le_one
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₁} (hA : A ≤ 1) :
    leftTensor (ι₂ := ι₂) A ≤ 1 := by
  simpa [leftTensor, opTensor] using
    (opTensor_mono_left
      (A₁ := A) (A₂ := (1 : MIPStarRE.Quantum.Op ι₁))
      (B := (1 : MIPStarRE.Quantum.Op ι₂)) hA
      (zero_le_one : (0 : MIPStarRE.Quantum.Op ι₂) ≤ 1))

/-- Right tensor placement preserves the operator bound `≤ 1`. -/
theorem rightTensor_le_one
    {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    {A : MIPStarRE.Quantum.Op ι₂} (hA : A ≤ 1) :
    rightTensor (ι₁ := ι₁) A ≤ 1 := by
  simpa [rightTensor, leftTensor, opTensor] using
    (opTensor_le_leftTensor
      (A := (1 : MIPStarRE.Quantum.Op ι₁)) (B := A)
      (zero_le_one : (0 : MIPStarRE.Quantum.Op ι₁) ≤ 1) hA)

namespace SubMeas

/-- A filtered diagonal tensor sum of two submeasurements is a contraction.

The estimate uses only positivity and the submeasurement total bound on the
left factor, together with the pointwise `≤ 1` bound on the right factor. -/
theorem opTensor_sum_filter_le_one {α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (S T : SubMeas α ι) (P : α → Prop) [DecidablePred P] :
    ∑ x ∈ Finset.univ.filter P, opTensor (S.outcome x) (T.outcome x) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  calc
    ∑ x ∈ Finset.univ.filter P, opTensor (S.outcome x) (T.outcome x)
      ≤ ∑ x ∈ Finset.univ.filter P, leftTensor (ι₂ := ι) (S.outcome x) := by
          refine Finset.sum_le_sum ?_
          intro x _hx
          exact opTensor_le_leftTensor (S.outcome_pos x) (T.outcome_le_one x)
    _ ≤ ∑ x : α, leftTensor (ι₂ := ι) (S.outcome x) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _)
            (fun x _hmem _hnotmem => leftTensor_nonneg (S.outcome_pos x))
    _ = leftTensor (ι₂ := ι) S.total := by
          rw [← S.sum_eq_total]
          rw [leftTensor_finset_sum]
    _ ≤ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          exact leftTensor_le_one S.total_le_one

end SubMeas

/-! ### Sandwich tensor estimates -/

/-- A single tensor summand with a sandwiched left register is nonnegative in
expectation.

The left register `Outer_o * Inner_i * Outer_o` is PSD by sandwich positivity,
and the right-register outcome is PSD, so their tensor product is PSD. -/
theorem sandwichTensorSummand_nonneg
    {α β γ ι : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    (Outer : SubMeas β ι) (Inner : SubMeas α ι) (Right : SubMeas γ ι)
    (o : β) (i : α) (r : γ) :
    0 ≤ ev ψ
      (leftTensor (ι₂ := ι)
          (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
        rightTensor (ι₁ := ι) (Right.outcome r)) := by
  rw [leftTensor_mul_rightTensor_eq_opTensor]
  exact ev_nonneg_of_psd ψ _ <|
    opTensor_nonneg
      (MIPStarRE.Quantum.sandwich_nonneg
        (Inner.outcome_pos i) (Outer.outcome_hermitian o))
      (Right.outcome_pos r)

/-- The residual tensor sum from a sandwiched left-register submeasurement and an
independent right-register submeasurement is at most one in a normalized state.

The operator under the sum factors as
`(∑ o, Outer_o * Inner.total * Outer_o) ⊗ Right.total`; the first factor is
bounded by `1` by the submeasurement axioms and sandwich monotonicity, and the
second factor is also bounded by `1`. -/
theorem sandwichTensor_residual_sum_le_one
    {α β γ ι : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (hnorm : ψ.IsNormalized)
    (Outer : SubMeas β ι) (Inner : SubMeas α ι) (Right : SubMeas γ ι) :
    (∑ ir : α × γ, ∑ o : β,
        ev ψ
          (leftTensor (ι₂ := ι)
              (Outer.outcome o * Inner.outcome ir.1 * Outer.outcome o) *
            rightTensor (ι₁ := ι) (Right.outcome ir.2))) ≤ 1 := by
  let sandwichTotal : MIPStarRE.Quantum.Op ι :=
    ∑ o : β, Outer.outcome o * Inner.total * Outer.outcome o
  have hsandwichTotal_nonneg : 0 ≤ sandwichTotal := by
    exact Finset.sum_nonneg fun o _ =>
      MIPStarRE.Quantum.sandwich_nonneg
        (SubMeas.total_nonneg Inner) (Outer.outcome_hermitian o)
  have hsandwichTotal_le_one : sandwichTotal ≤ 1 := by
    calc
      sandwichTotal
        ≤ ∑ o : β, Outer.outcome o := by
            refine Finset.sum_le_sum ?_
            intro o _
            exact le_trans
              (MIPStarRE.Quantum.sandwich_mono
                (Outer.outcome_hermitian o) Inner.total_le_one)
              (by
                simpa using
                  MIPStarRE.Quantum.sq_le_self
                    (Outer.outcome_pos o) (SubMeas.outcome_le_one Outer o))
      _ = Outer.total := Outer.sum_eq_total
      _ ≤ 1 := Outer.total_le_one
  have hop_sum :
      (∑ ir : α × γ, ∑ o : β,
          leftTensor (ι₂ := ι)
              (Outer.outcome o * Inner.outcome ir.1 * Outer.outcome o) *
            rightTensor (ι₁ := ι) (Right.outcome ir.2)) =
        leftTensor (ι₂ := ι) sandwichTotal * rightTensor (ι₁ := ι) Right.total := by
    calc
      (∑ ir : α × γ, ∑ o : β,
          leftTensor (ι₂ := ι)
              (Outer.outcome o * Inner.outcome ir.1 * Outer.outcome o) *
            rightTensor (ι₁ := ι) (Right.outcome ir.2))
        = ∑ i : α, ∑ r : γ, ∑ o : β,
            leftTensor (ι₂ := ι)
                (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
              rightTensor (ι₁ := ι) (Right.outcome r) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ i : α, ∑ o : β,
            leftTensor (ι₂ := ι)
                (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
              rightTensor (ι₁ := ι) Right.total := by
            refine Finset.sum_congr rfl ?_
            intro i _
            calc
              (∑ r : γ, ∑ o : β,
                  leftTensor (ι₂ := ι)
                      (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
                    rightTensor (ι₁ := ι) (Right.outcome r))
                = ∑ o : β, ∑ r : γ,
                    leftTensor (ι₂ := ι)
                        (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
                      rightTensor (ι₁ := ι) (Right.outcome r) := by
                    rw [Finset.sum_comm]
              _ = ∑ o : β,
                    leftTensor (ι₂ := ι)
                        (Outer.outcome o * Inner.outcome i * Outer.outcome o) *
                      rightTensor (ι₁ := ι) Right.total := by
                    refine Finset.sum_congr rfl ?_
                    intro o _
                    rw [← Matrix.mul_sum]
                    rw [rightTensor_finset_sum (ι₁ := ι) Finset.univ Right.outcome]
                    rw [Right.sum_eq_total]
      _ = (∑ i : α, ∑ o : β,
            leftTensor (ι₂ := ι)
              (Outer.outcome o * Inner.outcome i * Outer.outcome o)) *
            rightTensor (ι₁ := ι) Right.total := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.sum_mul]
      _ = leftTensor (ι₂ := ι) sandwichTotal * rightTensor (ι₁ := ι) Right.total := by
            congr 1
            calc
              ∑ i : α, ∑ o : β,
                  leftTensor (ι₂ := ι)
                    (Outer.outcome o * Inner.outcome i * Outer.outcome o)
                = ∑ o : β, ∑ i : α,
                    leftTensor (ι₂ := ι)
                      (Outer.outcome o * Inner.outcome i * Outer.outcome o) := by
                    rw [Finset.sum_comm]
              _ = ∑ o : β,
                    leftTensor (ι₂ := ι)
                      (∑ i : α,
                        Outer.outcome o * Inner.outcome i * Outer.outcome o) := by
                    refine Finset.sum_congr rfl ?_
                    intro o _
                    rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ]
              _ = leftTensor (ι₂ := ι)
                    (∑ o : β, ∑ i : α,
                      Outer.outcome o * Inner.outcome i * Outer.outcome o) := by
                    rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ]
              _ = leftTensor (ι₂ := ι) sandwichTotal := by
                    congr 1
                    calc
                      ∑ o : β, ∑ i : α,
                          Outer.outcome o * Inner.outcome i * Outer.outcome o
                        = ∑ o : β,
                            Outer.outcome o * Inner.total * Outer.outcome o := by
                            refine Finset.sum_congr rfl ?_
                            intro o _
                            rw [← Matrix.sum_mul, ← Matrix.mul_sum, Inner.sum_eq_total]
                      _ = sandwichTotal := rfl
  calc
    (∑ ir : α × γ, ∑ o : β,
        ev ψ
          (leftTensor (ι₂ := ι)
              (Outer.outcome o * Inner.outcome ir.1 * Outer.outcome o) *
            rightTensor (ι₁ := ι) (Right.outcome ir.2)))
      = ev ψ (∑ ir : α × γ, ∑ o : β,
          leftTensor (ι₂ := ι)
              (Outer.outcome o * Inner.outcome ir.1 * Outer.outcome o) *
            rightTensor (ι₁ := ι) (Right.outcome ir.2)) := by
          rw [ev_sum]
          refine Finset.sum_congr rfl ?_
          intro ir _
          rw [ev_sum]
    _ = ev ψ (leftTensor (ι₂ := ι) sandwichTotal * rightTensor (ι₁ := ι) Right.total) := by
          rw [hop_sum]
    _ ≤ ev ψ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          apply ev_mono ψ _ _
          calc
            leftTensor (ι₂ := ι) sandwichTotal * rightTensor (ι₁ := ι) Right.total
              = opTensor sandwichTotal Right.total := by
                rw [leftTensor_mul_rightTensor_eq_opTensor]
            _ ≤ leftTensor (ι₂ := ι) sandwichTotal :=
                opTensor_le_leftTensor hsandwichTotal_nonneg Right.total_le_one
            _ ≤ 1 := leftTensor_le_one (ι₂ := ι) hsandwichTotal_le_one
    _ = 1 := ev_one_of_isNormalized ψ hnorm

end MIPStarRE.LDT
