import MIPStarRE.LDT.Commutativity.ScalarApproximation.Core
import MIPStarRE.LDT.Commutativity.EvaluatedSliceCommutation.Consequences

/-!
# Basic helpers for the evaluated-slice paper chain

This file contains normalization and finite-reindexing helpers used by the
paper-faithful scalar chain for `lem:comm-data-processed-g`.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Normalization side condition for the paper line-86 insertion.

For fixed evaluated-slice question `q`, this bounds the `closenessOfIP` family
`C_{a,b} = (A_a B_b) \otimes P_b`, where `P` is a projective point
measurement. -/
lemma leftRightTensor_prefix_pointMeasurement_normalization
    {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) (R : ProjMeas β ι) :
    ∑ a : α,
        (∑ b : β,
          leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            rightTensor (ι₁ := ι) (R.outcome b)) *
        (∑ b : β,
          leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            rightTensor (ι₁ := ι) (R.outcome b))ᴴ ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  let D : α → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    ∑ b : β,
      leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
        rightTensor (ι₁ := ι) (R.outcome b)
  have hrow_le : ∀ a : α, D a * (D a)ᴴ ≤ leftTensor (ι₂ := ι) (A.outcome a) := by
    intro a
    have hrow_expand :
        D a * (D a)ᴴ =
          ∑ b : β,
            opTensor (A.outcome a * (B.outcome b * (B.outcome b * A.outcome a)))
              (R.outcome b) := by
      unfold D
      calc
        (∑ b : β,
            leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
              rightTensor (ι₁ := ι) (R.outcome b)) *
            (∑ b : β,
              leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                rightTensor (ι₁ := ι) (R.outcome b))ᴴ
          = (∑ b : β,
            leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
              rightTensor (ι₁ := ι) (R.outcome b)) *
              (∑ c : β,
                (leftTensor (ι₂ := ι) (A.outcome a * B.outcome c) *
                  rightTensor (ι₁ := ι) (R.outcome c))ᴴ) := by
                rw [Matrix.conjTranspose_sum]
        _ = ∑ b : β, ∑ c : β,
              (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                rightTensor (ι₁ := ι) (R.outcome b)) *
              (leftTensor (ι₂ := ι) (A.outcome a * B.outcome c) *
                rightTensor (ι₁ := ι) (R.outcome c))ᴴ := by
                rw [Finset.sum_mul]
                refine Finset.sum_congr rfl ?_
                intro b _
                rw [Finset.mul_sum]
        _ = ∑ b : β,
              (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                rightTensor (ι₁ := ι) (R.outcome b)) *
              (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                rightTensor (ι₁ := ι) (R.outcome b))ᴴ := by
                refine Finset.sum_congr rfl ?_
                intro b _
                rw [Finset.sum_eq_single b]
                · intro c _ hcb
                  have hbc : b ≠ c := fun h => hcb h.symm
                  have horth : R.outcome b * R.outcome c = 0 := R.outcome_orthogonal b c hbc
                  calc
                    (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                        rightTensor (ι₁ := ι) (R.outcome b)) *
                        (leftTensor (ι₂ := ι) (A.outcome a * B.outcome c) *
                          rightTensor (ι₁ := ι) (R.outcome c))ᴴ
                      = opTensor (A.outcome a * B.outcome b) (R.outcome b) *
                          (opTensor (A.outcome a * B.outcome c) (R.outcome c))ᴴ := by
                          rw [leftTensor_mul_rightTensor_eq_opTensor,
                            leftTensor_mul_rightTensor_eq_opTensor]
                    _ = opTensor (A.outcome a * B.outcome b) (R.outcome b) *
                          opTensor ((A.outcome a * B.outcome c)ᴴ) ((R.outcome c)ᴴ) := by
                          rw [conjTranspose_opTensor]
                    _ = opTensor ((A.outcome a * B.outcome b) *
                            ((A.outcome a * B.outcome c)ᴴ))
                          (R.outcome b * (R.outcome c)ᴴ) := by
                          rw [opTensor_mul]
                    _ = 0 := by
                          have hRherm : (R.outcome c)ᴴ = R.outcome c :=
                            R.outcome_hermitian c
                          rw [hRherm, horth]
                          simp [opTensor]
                · simp
        _ = ∑ b : β,
            opTensor (A.outcome a * (B.outcome b * (B.outcome b * A.outcome a)))
              (R.outcome b) := by
                refine Finset.sum_congr rfl ?_
                intro b _
                calc
                  (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                        rightTensor (ι₁ := ι) (R.outcome b)) *
                      (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                        rightTensor (ι₁ := ι) (R.outcome b))ᴴ
                    = opTensor (A.outcome a * B.outcome b) (R.outcome b) *
                        (opTensor (A.outcome a * B.outcome b) (R.outcome b))ᴴ := by
                        rw [leftTensor_mul_rightTensor_eq_opTensor]
                  _ = opTensor (A.outcome a * B.outcome b) (R.outcome b) *
                        opTensor ((A.outcome a * B.outcome b)ᴴ) ((R.outcome b)ᴴ) := by
                        rw [conjTranspose_opTensor]
                  _ = opTensor ((A.outcome a * B.outcome b) *
                          ((A.outcome a * B.outcome b)ᴴ))
                        (R.outcome b * (R.outcome b)ᴴ) := by
                        rw [opTensor_mul]
                  _ = opTensor (A.outcome a * (B.outcome b * (B.outcome b * A.outcome a)))
                        (R.outcome b) := by
                        have hABadj : (A.outcome a * B.outcome b)ᴴ =
                            B.outcome b * A.outcome a := by
                          rw [Matrix.conjTranspose_mul, A.outcome_hermitian a,
                            B.outcome_hermitian b]
                        have hRherm : (R.outcome b)ᴴ = R.outcome b :=
                          R.outcome_hermitian b
                        rw [hABadj, hRherm, R.proj b]
                        congr 1
                        noncomm_ring
    have hbound_terms :
        (∑ b : β,
            opTensor (A.outcome a * (B.outcome b * (B.outcome b * A.outcome a)))
              (R.outcome b)) ≤
          ∑ b : β, opTensor (A.outcome a) (R.outcome b) := by
      refine Finset.sum_le_sum ?_
      intro b _
      apply opTensor_mono_left
      · have hBsq : B.outcome b * B.outcome b ≤ B.outcome b :=
          MIPStarRE.Quantum.sq_le_self (B.outcome_pos b) (B.outcome_le_one b)
        have hleft1 :
            A.outcome a * (B.outcome b * B.outcome b) * A.outcome a ≤
              A.outcome a * B.outcome b * A.outcome a := by
          exact MIPStarRE.Quantum.sandwich_mono (A.outcome_hermitian a) hBsq
        have hleft2 :
            A.outcome a * B.outcome b * A.outcome a ≤
              A.outcome a * (1 : MIPStarRE.Quantum.Op ι) * A.outcome a := by
          exact MIPStarRE.Quantum.sandwich_mono (A.outcome_hermitian a) (B.outcome_le_one b)
        have hleft3 :
            A.outcome a * (1 : MIPStarRE.Quantum.Op ι) * A.outcome a ≤
              A.outcome a := by
          simpa using MIPStarRE.Quantum.sq_le_self (A.outcome_pos a) (A.outcome_le_one a)
        calc
          A.outcome a * (B.outcome b * (B.outcome b * A.outcome a))
              = A.outcome a * (B.outcome b * B.outcome b) * A.outcome a := by
                noncomm_ring
          _ ≤ A.outcome a * B.outcome b * A.outcome a := hleft1
          _ ≤ A.outcome a * (1 : MIPStarRE.Quantum.Op ι) * A.outcome a := hleft2
          _ ≤ A.outcome a := hleft3
      · exact R.outcome_pos b
    have hsum_right :
        (∑ b : β, opTensor (A.outcome a) (R.outcome b)) =
          leftTensor (ι₂ := ι) (A.outcome a) := by
      calc
        (∑ b : β, opTensor (A.outcome a) (R.outcome b))
            = ∑ b : β,
                leftTensor (ι₂ := ι) (A.outcome a) *
                  rightTensor (ι₁ := ι) (R.outcome b) := by
              simp [leftTensor_mul_rightTensor_eq_opTensor]
        _ = leftTensor (ι₂ := ι) (A.outcome a) *
              (∑ b : β, rightTensor (ι₁ := ι) (R.outcome b)) := by
              rw [← Matrix.mul_sum]
        _ = leftTensor (ι₂ := ι) (A.outcome a) *
              rightTensor (ι₁ := ι) (∑ b : β, R.outcome b) := by
              rw [rightTensor_finset_sum]
        _ = leftTensor (ι₂ := ι) (A.outcome a) := by
              rw [R.sum_eq, rightTensor_one]
              simp
    calc
      D a * (D a)ᴴ
          = ∑ b : β,
            opTensor (A.outcome a * (B.outcome b * (B.outcome b * A.outcome a)))
              (R.outcome b) := hrow_expand
      _ ≤ ∑ b : β, opTensor (A.outcome a) (R.outcome b) := hbound_terms
      _ = leftTensor (ι₂ := ι) (A.outcome a) := hsum_right
  calc
    ∑ a : α,
        (∑ b : β,
          leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            rightTensor (ι₁ := ι) (R.outcome b)) *
        (∑ b : β,
          leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            rightTensor (ι₁ := ι) (R.outcome b))ᴴ
      = ∑ a : α, D a * (D a)ᴴ := by rfl
    _ ≤ ∑ a : α, leftTensor (ι₂ := ι) (A.outcome a) := by
          exact Finset.sum_le_sum fun a _ => hrow_le a
    _ = leftTensor (ι₂ := ι) A.total := by
          rw [leftTensor_finset_sum, A.sum_eq_total]
    _ ≤ 1 := leftTensor_le_one (ι₂ := ι) A.total_le_one

/-- Adjoint-side normalization for
`C_{a,b} = (A_a B_b) \otimes R_b`.

This is the side condition needed by `closenessOfIPAdjoint` for the first
reverse `eq:add-an-a` move after paper `eq:gcom10`. -/
lemma leftRightTensor_prefix_pointMeasurement_adjoint_normalization
    {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) (R : ProjMeas β ι) :
    ∑ a : α,
        (∑ b : β,
          leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            rightTensor (ι₁ := ι) (R.outcome b))ᴴ *
        (∑ b : β,
          leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            rightTensor (ι₁ := ι) (R.outcome b)) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  let D : α → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    ∑ b : β,
      leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
        rightTensor (ι₁ := ι) (R.outcome b)
  have hrow_expand : ∀ a : α,
      (D a)ᴴ * D a =
        ∑ b : β,
          opTensor (B.outcome b * (A.outcome a * A.outcome a) * B.outcome b)
            (R.outcome b) := by
    intro a
    unfold D
    calc
      (∑ b : β,
          leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            rightTensor (ι₁ := ι) (R.outcome b))ᴴ *
          (∑ b : β,
            leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
              rightTensor (ι₁ := ι) (R.outcome b))
        = (∑ c : β,
              (leftTensor (ι₂ := ι) (A.outcome a * B.outcome c) *
                rightTensor (ι₁ := ι) (R.outcome c))ᴴ) *
            (∑ b : β,
              leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                rightTensor (ι₁ := ι) (R.outcome b)) := by
              rw [Matrix.conjTranspose_sum]
      _ = ∑ c : β, ∑ b : β,
            (leftTensor (ι₂ := ι) (A.outcome a * B.outcome c) *
              rightTensor (ι₁ := ι) (R.outcome c))ᴴ *
            (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
              rightTensor (ι₁ := ι) (R.outcome b)) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl ?_
              intro c _
              rw [Finset.mul_sum]
      _ = ∑ b : β,
            (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
              rightTensor (ι₁ := ι) (R.outcome b))ᴴ *
            (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
              rightTensor (ι₁ := ι) (R.outcome b)) := by
              refine Finset.sum_congr rfl ?_
              intro c _
              rw [Finset.sum_eq_single c]
              · intro b _ hbc
                have hcb : c ≠ b := fun h => hbc h.symm
                have horth : R.outcome c * R.outcome b = 0 :=
                  R.outcome_orthogonal c b hcb
                calc
                  (leftTensor (ι₂ := ι) (A.outcome a * B.outcome c) *
                      rightTensor (ι₁ := ι) (R.outcome c))ᴴ *
                    (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                      rightTensor (ι₁ := ι) (R.outcome b))
                    = (opTensor (A.outcome a * B.outcome c) (R.outcome c))ᴴ *
                        opTensor (A.outcome a * B.outcome b) (R.outcome b) := by
                        rw [leftTensor_mul_rightTensor_eq_opTensor,
                          leftTensor_mul_rightTensor_eq_opTensor]
                  _ = opTensor ((A.outcome a * B.outcome c)ᴴ) ((R.outcome c)ᴴ) *
                        opTensor (A.outcome a * B.outcome b) (R.outcome b) := by
                        rw [conjTranspose_opTensor]
                  _ = opTensor (((A.outcome a * B.outcome c)ᴴ) *
                          (A.outcome a * B.outcome b))
                        ((R.outcome c)ᴴ * R.outcome b) := by
                        rw [opTensor_mul]
                  _ = 0 := by
                        have hRherm : (R.outcome c)ᴴ = R.outcome c :=
                          R.outcome_hermitian c
                        rw [hRherm, horth]
                        simp [opTensor]
              · simp
      _ = ∑ b : β,
          opTensor (B.outcome b * (A.outcome a * A.outcome a) * B.outcome b)
            (R.outcome b) := by
              refine Finset.sum_congr rfl ?_
              intro b _
              calc
                (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                    rightTensor (ι₁ := ι) (R.outcome b))ᴴ *
                  (leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
                    rightTensor (ι₁ := ι) (R.outcome b))
                  = (opTensor (A.outcome a * B.outcome b) (R.outcome b))ᴴ *
                      opTensor (A.outcome a * B.outcome b) (R.outcome b) := by
                      rw [leftTensor_mul_rightTensor_eq_opTensor]
                _ = opTensor ((A.outcome a * B.outcome b)ᴴ) ((R.outcome b)ᴴ) *
                      opTensor (A.outcome a * B.outcome b) (R.outcome b) := by
                      rw [conjTranspose_opTensor]
                _ = opTensor (((A.outcome a * B.outcome b)ᴴ) *
                        (A.outcome a * B.outcome b))
                      ((R.outcome b)ᴴ * R.outcome b) := by
                      rw [opTensor_mul]
                _ = opTensor (B.outcome b * (A.outcome a * A.outcome a) * B.outcome b)
                      (R.outcome b) := by
                      have hABadj : (A.outcome a * B.outcome b)ᴴ =
                          B.outcome b * A.outcome a := by
                        rw [Matrix.conjTranspose_mul, A.outcome_hermitian a,
                          B.outcome_hermitian b]
                      have hRherm : (R.outcome b)ᴴ = R.outcome b :=
                        R.outcome_hermitian b
                      rw [hABadj, hRherm, R.proj b]
                      congr 1
                      noncomm_ring
  have hsum_sq_le_one :
      ∑ a : α, A.outcome a * A.outcome a ≤ (1 : MIPStarRE.Quantum.Op ι) := by
    calc
      ∑ a : α, A.outcome a * A.outcome a
          ≤ ∑ a : α, A.outcome a := by
            exact Finset.sum_le_sum fun a _ =>
              MIPStarRE.Quantum.sq_le_self (A.outcome_pos a) (A.outcome_le_one a)
      _ = A.total := A.sum_eq_total
      _ ≤ 1 := A.total_le_one
  have hsum_for_b : ∀ b : β,
      ∑ a : α, B.outcome b * (A.outcome a * A.outcome a) * B.outcome b ≤
        B.outcome b := by
    intro b
    calc
      ∑ a : α, B.outcome b * (A.outcome a * A.outcome a) * B.outcome b
          = B.outcome b * (∑ a : α, A.outcome a * A.outcome a) * B.outcome b := by
            rw [← Matrix.sum_mul, ← Matrix.mul_sum]
      _ ≤ B.outcome b * (1 : MIPStarRE.Quantum.Op ι) * B.outcome b := by
            exact MIPStarRE.Quantum.sandwich_mono (B.outcome_hermitian b) hsum_sq_le_one
      _ = B.outcome b * B.outcome b := by simp
      _ ≤ B.outcome b :=
            MIPStarRE.Quantum.sq_le_self (B.outcome_pos b) (B.outcome_le_one b)
  calc
    ∑ a : α,
        (∑ b : β,
          leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            rightTensor (ι₁ := ι) (R.outcome b))ᴴ *
        (∑ b : β,
          leftTensor (ι₂ := ι) (A.outcome a * B.outcome b) *
            rightTensor (ι₁ := ι) (R.outcome b))
      = ∑ a : α, (D a)ᴴ * D a := by rfl
    _ = ∑ b : β, ∑ a : α,
          opTensor (B.outcome b * (A.outcome a * A.outcome a) * B.outcome b)
            (R.outcome b) := by
          calc
            ∑ a : α, (D a)ᴴ * D a
                = ∑ a : α, ∑ b : β,
                    opTensor (B.outcome b * (A.outcome a * A.outcome a) * B.outcome b)
                      (R.outcome b) := by
                  exact Finset.sum_congr rfl fun a _ => hrow_expand a
            _ = ∑ b : β, ∑ a : α,
                    opTensor (B.outcome b * (A.outcome a * A.outcome a) * B.outcome b)
                      (R.outcome b) := by
                  rw [Finset.sum_comm]
    _ ≤ ∑ b : β, opTensor (B.outcome b) (R.outcome b) := by
          refine Finset.sum_le_sum ?_
          intro b _
          calc
            ∑ a : α,
                opTensor (B.outcome b * (A.outcome a * A.outcome a) * B.outcome b)
                  (R.outcome b)
              = opTensor (∑ a : α,
                  B.outcome b * (A.outcome a * A.outcome a) * B.outcome b)
                  (R.outcome b) := by
                  rw [opTensor_sum_left_univ]
            _ ≤ opTensor (B.outcome b) (R.outcome b) := by
                  exact opTensor_mono_left (hsum_for_b b) (R.outcome_pos b)
    _ ≤ ∑ b : β, opTensor (1 : MIPStarRE.Quantum.Op ι) (R.outcome b) := by
          exact Finset.sum_le_sum fun b _ =>
            opTensor_mono_left (B.outcome_le_one b) (R.outcome_pos b)
    _ = 1 := by
          calc
            ∑ b : β, opTensor (1 : MIPStarRE.Quantum.Op ι) (R.outcome b)
                = rightTensor (ι₁ := ι) (∑ b : β, R.outcome b) := by
                  rw [rightTensor_finset_sum]
            _ = 1 := by rw [R.sum_eq, rightTensor_one]

/-- Normalization for `C_{b,a}=A_a B_b` placed on the left tensor factor. -/
lemma leftTensor_pair_prefix_normalization
    {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    ∑ b : β,
        (∑ a : α, leftTensor (ι₂ := ι) (A.outcome a * B.outcome b)) *
        (∑ a : α, leftTensor (ι₂ := ι) (A.outcome a * B.outcome b))ᴴ ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  let T : β → MIPStarRE.Quantum.Op ι := fun b => A.total * B.outcome b
  have hAtotal_herm : A.totalᴴ = A.total :=
    (Matrix.nonneg_iff_posSemidef.mp A.total_nonneg).isHermitian.eq
  have hbase : ∑ b : β, T b * (T b)ᴴ ≤ (1 : MIPStarRE.Quantum.Op ι) := by
    calc
      ∑ b : β, T b * (T b)ᴴ
          = ∑ b : β, A.total * (B.outcome b * B.outcome b) * A.total := by
            refine Finset.sum_congr rfl ?_
            intro b _
            simp only [T, Matrix.conjTranspose_mul, hAtotal_herm, B.outcome_hermitian b]
            simp only [mul_assoc]
      _ ≤ ∑ b : β, A.total * B.outcome b * A.total := by
            exact Finset.sum_le_sum fun b _ =>
              MIPStarRE.Quantum.sandwich_mono hAtotal_herm
                (MIPStarRE.Quantum.sq_le_self (B.outcome_pos b) (B.outcome_le_one b))
      _ = A.total * B.total * A.total := by
            rw [← Matrix.sum_mul, ← Matrix.mul_sum, B.sum_eq_total]
      _ ≤ A.total * (1 : MIPStarRE.Quantum.Op ι) * A.total := by
            exact MIPStarRE.Quantum.sandwich_mono hAtotal_herm B.total_le_one
      _ = A.total * A.total := by simp
      _ ≤ A.total := MIPStarRE.Quantum.sq_le_self A.total_nonneg A.total_le_one
      _ ≤ 1 := A.total_le_one
  calc
    ∑ b : β,
        (∑ a : α, leftTensor (ι₂ := ι) (A.outcome a * B.outcome b)) *
        (∑ a : α, leftTensor (ι₂ := ι) (A.outcome a * B.outcome b))ᴴ
      = ∑ b : β, leftTensor (ι₂ := ι) (T b * (T b)ᴴ) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          have hsum : (∑ a : α, leftTensor (ι₂ := ι) (A.outcome a * B.outcome b)) =
              leftTensor (ι₂ := ι) (T b) := by
            rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ
              (fun a : α => A.outcome a * B.outcome b)]
            rw [← Matrix.sum_mul, A.sum_eq_total]
          rw [hsum]
          have hleft_adj : (leftTensor (ι₂ := ι) (T b))ᴴ = leftTensor (ι₂ := ι) ((T b)ᴴ) := by
            simpa [leftTensor, opTensor] using
              (conjTranspose_opTensor (ι₁ := ι) (ι₂ := ι) (T b) (1 : MIPStarRE.Quantum.Op ι))
          rw [hleft_adj, leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (∑ b : β, T b * (T b)ᴴ) := by
          rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ (fun b => T b * (T b)ᴴ)]
    _ ≤ 1 := leftTensor_le_one (ι₂ := ι) hbase

/-- Adjoint-side version of `leftTensor_pair_prefix_normalization`. -/
lemma leftTensor_pair_prefix_adjoint_normalization
    {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι) :
    ∑ b : β,
        (∑ a : α, leftTensor (ι₂ := ι) (A.outcome a * B.outcome b))ᴴ *
        (∑ a : α, leftTensor (ι₂ := ι) (A.outcome a * B.outcome b)) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  let T : β → MIPStarRE.Quantum.Op ι := fun b => A.total * B.outcome b
  have hAtotal_herm : A.totalᴴ = A.total :=
    (Matrix.nonneg_iff_posSemidef.mp A.total_nonneg).isHermitian.eq
  have hAtotal_sq_le_one : A.total * A.total ≤ (1 : MIPStarRE.Quantum.Op ι) := by
    exact le_trans (MIPStarRE.Quantum.sq_le_self A.total_nonneg A.total_le_one) A.total_le_one
  have hbase : ∑ b : β, (T b)ᴴ * T b ≤ (1 : MIPStarRE.Quantum.Op ι) := by
    calc
      ∑ b : β, (T b)ᴴ * T b
          = ∑ b : β, B.outcome b * (A.total * A.total) * B.outcome b := by
            refine Finset.sum_congr rfl ?_
            intro b _
            simp only [T, Matrix.conjTranspose_mul, hAtotal_herm, B.outcome_hermitian b]
            simp only [mul_assoc]
      _ ≤ ∑ b : β, B.outcome b * (1 : MIPStarRE.Quantum.Op ι) * B.outcome b := by
            exact Finset.sum_le_sum fun b _ =>
              MIPStarRE.Quantum.sandwich_mono (B.outcome_hermitian b) hAtotal_sq_le_one
      _ = ∑ b : β, B.outcome b * B.outcome b := by simp
      _ ≤ ∑ b : β, B.outcome b := by
            exact Finset.sum_le_sum fun b _ =>
              MIPStarRE.Quantum.sq_le_self (B.outcome_pos b) (B.outcome_le_one b)
      _ = B.total := B.sum_eq_total
      _ ≤ 1 := B.total_le_one
  calc
    ∑ b : β,
        (∑ a : α, leftTensor (ι₂ := ι) (A.outcome a * B.outcome b))ᴴ *
        (∑ a : α, leftTensor (ι₂ := ι) (A.outcome a * B.outcome b))
      = ∑ b : β, leftTensor (ι₂ := ι) ((T b)ᴴ * T b) := by
          refine Finset.sum_congr rfl ?_
          intro b _
          have hsum : (∑ a : α, leftTensor (ι₂ := ι) (A.outcome a * B.outcome b)) =
              leftTensor (ι₂ := ι) (T b) := by
            rw [leftTensor_finset_sum (ι₂ := ι) Finset.univ
              (fun a : α => A.outcome a * B.outcome b)]
            rw [← Matrix.sum_mul, A.sum_eq_total]
          rw [hsum]
          have hleft_adj : (leftTensor (ι₂ := ι) (T b))ᴴ = leftTensor (ι₂ := ι) ((T b)ᴴ) := by
            simpa [leftTensor, opTensor] using
              (conjTranspose_opTensor (ι₁ := ι) (ι₂ := ι) (T b) (1 : MIPStarRE.Quantum.Op ι))
          rw [hleft_adj, leftTensor_mul_leftTensor]
    _ = leftTensor (ι₂ := ι) (∑ b : β, (T b)ᴴ * T b) := by
          rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ (fun b => (T b)ᴴ * T b)]
    _ ≤ 1 := leftTensor_le_one (ι₂ := ι) hbase

/-- The total projector of a projective submeasurement absorbs each outcome on the left. -/
lemma projSubMeas_total_mul_outcome_eq_outcome
    {α : Type*} [Fintype α] (A : ProjSubMeas α ι) (a : α) :
    A.total * A.outcome a = A.outcome a := by
  have hright := MIPStarRE.LDT.Preliminaries.projSubMeas_outcome_mul_total_eq_outcome A a
  have htotal_herm : A.totalᴴ = A.total :=
    (Matrix.nonneg_iff_posSemidef.mp A.total_nonneg).isHermitian.eq
  have h := congrArg Matrix.conjTranspose hright
  simpa [Matrix.conjTranspose_mul, A.outcome_hermitian a, htotal_herm] using h

/-- Normalization side condition for the paper line-87 right-register point swap.

For fixed evaluated-slice question `q`, the swap uses the family
`C_{a,b} = (G^{u,x}_a G^{v,y}_b G^x) \otimes I`, represented here as a
left tensor.  The estimate only needs that the two evaluated-slice factors are
submeasurements and that the inserted total `T` is a positive contraction. -/
lemma leftTensor_prefix_total_normalization
    {α β : Type*} [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (T : MIPStarRE.Quantum.Op ι)
    (hT_nonneg : 0 ≤ T) (hT_le_one : T ≤ 1) :
    ∑ ab : α × β,
        leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2 * T) *
          (leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2 * T))ᴴ ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  let X : α × β → MIPStarRE.Quantum.Op ι := fun ab =>
    A.outcome ab.1 * B.outcome ab.2 * T
  have hT_herm : Tᴴ = T :=
    (Matrix.nonneg_iff_posSemidef.mp hT_nonneg).isHermitian.eq
  have hT_sq_le_one : T * T ≤ (1 : MIPStarRE.Quantum.Op ι) := by
    exact le_trans (MIPStarRE.Quantum.sq_le_self hT_nonneg hT_le_one) hT_le_one
  have hterm_le : ∀ a b,
      X (a, b) * (X (a, b))ᴴ ≤
        A.outcome a * (B.outcome b * B.outcome b) * A.outcome a := by
    intro a b
    have hB_sandwich :
        B.outcome b * (T * T) * B.outcome b ≤
          B.outcome b * (1 : MIPStarRE.Quantum.Op ι) * B.outcome b :=
      MIPStarRE.Quantum.sandwich_mono (B.outcome_hermitian b) hT_sq_le_one
    have hA_sandwich :
        A.outcome a * (B.outcome b * (T * T) * B.outcome b) * A.outcome a ≤
          A.outcome a *
            (B.outcome b * (1 : MIPStarRE.Quantum.Op ι) * B.outcome b) *
            A.outcome a :=
      MIPStarRE.Quantum.sandwich_mono (A.outcome_hermitian a) hB_sandwich
    calc
      X (a, b) * (X (a, b))ᴴ
          = A.outcome a * (B.outcome b * (T * T) * B.outcome b) * A.outcome a := by
            simp only [X, Matrix.conjTranspose_mul, hT_herm, A.outcome_hermitian a,
              B.outcome_hermitian b]
            simp only [mul_assoc]
      _ ≤ A.outcome a *
            (B.outcome b * (1 : MIPStarRE.Quantum.Op ι) * B.outcome b) *
            A.outcome a := hA_sandwich
      _ = A.outcome a * (B.outcome b * B.outcome b) * A.outcome a := by
            simp [mul_assoc]
  have hrow_le : ∀ a : α,
      ∑ b : β, X (a, b) * (X (a, b))ᴴ ≤ A.outcome a := by
    intro a
    have hBsq_sum :
        ∑ b : β, B.outcome b * B.outcome b ≤ B.total := by
      calc
        ∑ b : β, B.outcome b * B.outcome b
            ≤ ∑ b : β, B.outcome b := by
              exact Finset.sum_le_sum fun b _ =>
                MIPStarRE.Quantum.sq_le_self (B.outcome_pos b) (B.outcome_le_one b)
        _ = B.total := B.sum_eq_total
    calc
      ∑ b : β, X (a, b) * (X (a, b))ᴴ
          ≤ ∑ b : β, A.outcome a * (B.outcome b * B.outcome b) * A.outcome a := by
            exact Finset.sum_le_sum fun b _ => hterm_le a b
      _ = A.outcome a * (∑ b : β, B.outcome b * B.outcome b) * A.outcome a := by
            rw [← Matrix.sum_mul, ← Matrix.mul_sum]
      _ ≤ A.outcome a * B.total * A.outcome a := by
            exact MIPStarRE.Quantum.sandwich_mono (A.outcome_hermitian a) hBsq_sum
      _ ≤ A.outcome a * (1 : MIPStarRE.Quantum.Op ι) * A.outcome a := by
            exact MIPStarRE.Quantum.sandwich_mono (A.outcome_hermitian a) B.total_le_one
      _ = A.outcome a * A.outcome a := by simp
      _ ≤ A.outcome a :=
            MIPStarRE.Quantum.sq_le_self (A.outcome_pos a) (A.outcome_le_one a)
  have hbase : ∑ ab : α × β, X ab * (X ab)ᴴ ≤ (1 : MIPStarRE.Quantum.Op ι) := by
    calc
      ∑ ab : α × β, X ab * (X ab)ᴴ
          = ∑ a : α, ∑ b : β, X (a, b) * (X (a, b))ᴴ := by
            simpa using
              (Fintype.sum_prod_type' (f := fun a : α => fun b : β =>
                X (a, b) * (X (a, b))ᴴ))
      _ ≤ ∑ a : α, A.outcome a := by
            exact Finset.sum_le_sum fun a _ => hrow_le a
      _ = A.total := A.sum_eq_total
      _ ≤ 1 := A.total_le_one
  calc
    ∑ ab : α × β,
        leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2 * T) *
          (leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2 * T))ᴴ
      = leftTensor (ι₂ := ι) (∑ ab : α × β, X ab * (X ab)ᴴ) := by
          calc
            ∑ ab : α × β,
                leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2 * T) *
                  (leftTensor (ι₂ := ι) (A.outcome ab.1 * B.outcome ab.2 * T))ᴴ
                = ∑ ab : α × β, leftTensor (ι₂ := ι) (X ab * (X ab)ᴴ) := by
                  refine Finset.sum_congr rfl ?_
                  intro ab _
                  have hleft_adj :
                      (leftTensor (ι₂ := ι) (X ab))ᴴ =
                        leftTensor (ι₂ := ι) ((X ab)ᴴ) := by
                    simpa [leftTensor, opTensor] using
                      (conjTranspose_opTensor (ι₁ := ι) (ι₂ := ι) (X ab)
                        (1 : MIPStarRE.Quantum.Op ι))
                  simp [X, hleft_adj, leftTensor_mul_leftTensor]
              _ = leftTensor (ι₂ := ι) (∑ ab : α × β, X ab * (X ab)ᴴ) := by
                  rw [← leftTensor_finset_sum (ι₂ := ι) Finset.univ
                    (fun ab : α × β => X ab * (X ab)ᴴ)]
    _ ≤ 1 := leftTensor_le_one (ι₂ := ι) hbase

set_option maxHeartbeats 800000 in
-- The permutation-invariance rewrite unfolds `qSDDOp` through placed families and
-- normalizes tensor adjoints pointwise; the explicit expansion needs extra budget.
private lemma qSDDOp_rightPlaced_eq_leftPlaced
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (A B : OpFamily Outcome ι) :
    qSDDOp ψ
      (OpFamily.rightPlacedOpFamily (ιA := ι) A)
      (OpFamily.rightPlacedOpFamily (ιA := ι) B) =
    qSDDOp ψ
      (OpFamily.leftPlacedOpFamily (ιB := ι) A)
      (OpFamily.leftPlacedOpFamily (ιB := ι) B) := by
  unfold qSDDOp qSDDCore
  refine Finset.sum_congr rfl ?_
  intro a _
  let D : MIPStarRE.Quantum.Op ι := A.outcome a - B.outcome a
  have hright_diff :
      (OpFamily.rightPlacedOpFamily (ιA := ι) A).outcome a -
        (OpFamily.rightPlacedOpFamily (ιA := ι) B).outcome a =
      rightTensor (ι₁ := ι) D := by
    simpa [OpFamily.rightPlacedOpFamily, rightTensor, opTensor, D] using
      (MIPStarRE.Quantum.kronecker_sub_right
        (A := (1 : MIPStarRE.Quantum.Op ι))
        (B₁ := A.outcome a) (B₂ := B.outcome a))
  have hleft_diff :
      (OpFamily.leftPlacedOpFamily (ιB := ι) A).outcome a -
        (OpFamily.leftPlacedOpFamily (ιB := ι) B).outcome a =
      leftTensor (ι₂ := ι) D := by
    simpa [OpFamily.leftPlacedOpFamily, D] using
      leftTensor_sub (ι₁ := ι) (ι₂ := ι) (A.outcome a) (B.outcome a)
  rw [hright_diff, hleft_diff]
  calc
    ev ψ ((rightTensor (ι₁ := ι) D)ᴴ * rightTensor (ι₁ := ι) D)
        = ev ψ (rightTensor (ι₁ := ι) (Dᴴ * D)) := by
          rw [show (rightTensor (ι₁ := ι) D)ᴴ = rightTensor (ι₁ := ι) Dᴴ by
            simpa [rightTensor, opTensor] using
              (conjTranspose_opTensor (ι₁ := ι) (ι₂ := ι) (1 : MIPStarRE.Quantum.Op ι) D)]
          rw [rightTensor_mul_rightTensor]
    _ = ev ψ (leftTensor (ι₂ := ι) (Dᴴ * D)) := by
          rw [← hperm.swap_ev (Dᴴ * D)]
    _ = ev ψ ((leftTensor (ι₂ := ι) D)ᴴ * leftTensor (ι₂ := ι) D) := by
          rw [show (leftTensor (ι₂ := ι) D)ᴴ = leftTensor (ι₂ := ι) Dᴴ by
            simpa [leftTensor, opTensor] using
              (conjTranspose_opTensor (ι₁ := ι) (ι₂ := ι) D (1 : MIPStarRE.Quantum.Op ι))]
          rw [leftTensor_mul_leftTensor]

set_option maxHeartbeats 3000000 in
-- This right-register variant of the point-swap bridge inlines the placed-family
-- congruence before applying `closenessOfIP`, which is heartbeat-heavy.
lemma evaluatedSlice_phaseFour_pointSwap_right_bound
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hnorm : strategy.state.IsNormalized)
    (hgood : strategy.IsGood eps delta gamma)
    (C : EvaluatedSliceQuestion params →
      EvaluatedSliceOutcome params → MIPStarRE.Quantum.Op (ι × ι))
    (hC : ∀ q, ∑ ab : EvaluatedSliceOutcome params, C q ab * (C q ab)ᴴ ≤ 1) :
    let 𝒟 := uniformDistribution (EvaluatedSliceQuestion params)
    let inserted : EvaluatedSliceQuestion params → Error := fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        ev strategy.state
          (C q ab *
            rightTensor (ι₁ := ι)
              (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
               ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1)))
    let swapped : EvaluatedSliceQuestion params → Error := fun q =>
      ∑ ab : EvaluatedSliceOutcome params,
        ev strategy.state
          (C q ab *
            rightTensor (ι₁ := ι)
              (((evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
               ((evaluatedSlicePointMeas params strategy q.2).outcome ab.2)))
    |avgOver 𝒟 inserted - avgOver 𝒟 swapped| ≤
      6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
  let 𝒟 : Distribution (EvaluatedSliceQuestion params) :=
    uniformDistribution (EvaluatedSliceQuestion params)
  let Rrev : EvaluatedSliceQuestion params →
      EvaluatedSliceOutcome params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q ab => rightTensor (ι₁ := ι)
      (((evaluatedSlicePointMeas params strategy q.2).outcome ab.2) *
        ((evaluatedSlicePointMeas params strategy q.1).outcome ab.1))
  let Rord : EvaluatedSliceQuestion params →
      EvaluatedSliceOutcome params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q ab => rightTensor (ι₁ := ι)
      (((evaluatedSlicePointMeas params strategy q.1).outcome ab.1) *
        ((evaluatedSlicePointMeas params strategy q.2).outcome ab.2))
  let C' : EvaluatedSliceQuestion params → EvaluatedSliceOutcome params → Unit →
      MIPStarRE.Quantum.Op (ι × ι) := fun q ab _ => C q ab
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)
  let Lrev : EvaluatedSliceQuestion params → OpFamily (EvaluatedSliceOutcome params) (ι × ι) :=
    fun q => OpFamily.leftPlacedOpFamily (ιB := ι) <|
      reversedProductOpFamily
        ((strategy.pointMeasurement q.1).toSubMeas : SubMeas (Fq params.next) ι)
        ((strategy.pointMeasurement q.2).toSubMeas : SubMeas (Fq params.next) ι)
  let Lord : EvaluatedSliceQuestion params → OpFamily (EvaluatedSliceOutcome params) (ι × ι) :=
    fun q => OpFamily.leftPlacedOpFamily (ιB := ι) <|
      orderedProductOpFamily
        ((strategy.pointMeasurement q.1).toSubMeas : SubMeas (Fq params.next) ι)
        ((strategy.pointMeasurement q.2).toSubMeas : SubMeas (Fq params.next) ι)
  have hleft :
      SDDOpRel strategy.state 𝒟 Lord Lrev (commutativityPointsError params.next gamma) := by
    simpa [𝒟, Lord, Lrev, pointMeasurementProductLeft, pointMeasurementProductRight,
      EvaluatedSliceQuestion, EvaluatedSliceOutcome, Parameters.next] using
      (commutativityPoints (params := params.next) strategy eps delta gamma hgood)
  have hleft_symm :
      SDDOpRel strategy.state 𝒟 Lrev Lord (commutativityPointsError params.next gamma) := by
    exact sddOpRel_symm strategy.state 𝒟 Lord Lrev
      (commutativityPointsError params.next gamma) hleft
  have hAB : avgOver 𝒟 (fun q => qSDDCore strategy.state (Rrev q) (Rord q)) ≤
      commutativityPointsError params.next gamma := by
    rcases hleft_symm with ⟨h⟩
    calc
      avgOver 𝒟 (fun q => qSDDCore strategy.state (Rrev q) (Rord q))
          = avgOver 𝒟 (fun q => qSDDOp strategy.state (Lrev q) (Lord q)) := by
            apply avgOver_congr
            intro q
            simpa [qSDDOp, Lrev, Lord, Rrev, Rord, evaluatedSlicePointMeas,
              OpFamily.leftPlacedOpFamily, OpFamily.rightPlacedOpFamily,
              reversedProductOpFamily, orderedProductOpFamily, Parameters.next] using
              (qSDDOp_rightPlaced_eq_leftPlaced (ι := ι) strategy.state strategy.permInvState
                (reversedProductOpFamily
                  ((strategy.pointMeasurement q.1).toSubMeas : SubMeas (Fq params.next) ι)
                  ((strategy.pointMeasurement q.2).toSubMeas : SubMeas (Fq params.next) ι))
                (orderedProductOpFamily
                  ((strategy.pointMeasurement q.1).toSubMeas : SubMeas (Fq params.next) ι)
                  ((strategy.pointMeasurement q.2).toSubMeas : SubMeas (Fq params.next) ι)))
      _ ≤ commutativityPointsError params.next gamma := by
            simpa [sddErrorOp] using h
  have hC' :
      ∀ q,
        ∑ ab : EvaluatedSliceOutcome params,
            (∑ _ : Unit, C' q ab ()) * (∑ _ : Unit, C' q ab ())ᴴ ≤ 1 := by
    intro q
    simpa [C'] using hC q
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 Rrev Rord C' (commutativityPointsError params.next gamma) hAB hC'
  have hsqrt32_le_six : Real.sqrt (32 : Error) ≤ 6 := by
    have hsqrt32_nonneg : 0 ≤ Real.sqrt (32 : Error) := Real.sqrt_nonneg _
    nlinarith [Real.sq_sqrt (show 0 ≤ (32 : Error) by positivity)]
  calc
    |avgOver 𝒟
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          ev strategy.state (C q ab * Rrev q ab)) -
      avgOver 𝒟
        (fun q => ∑ ab : EvaluatedSliceOutcome params,
          ev strategy.state (C q ab * Rord q ab))|
      ≤ Real.sqrt (commutativityPointsError params.next gamma) := by
          simpa [𝒟, Rrev, Rord, C'] using hclose
    _ = Real.sqrt (32 : Error) * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
          rw [commutativityPointsError, Parameters.next]
          have hring :
              32 * gamma * (((params.m + 1 : ℕ)) : Error) =
                (32 : Error) * (gamma * (((params.m + 1 : ℕ)) : Error)) := by
            ring
          rw [hring, Real.sqrt_mul (show 0 ≤ (32 : Error) by positivity)]
    _ ≤ 6 * Real.sqrt (gamma * (((params.m + 1 : ℕ)) : Error)) := by
          exact mul_le_mul_of_nonneg_right hsqrt32_le_six (Real.sqrt_nonneg _)



/-- Decompose the uniform average over a next-level point into a height and prefix average. -/
lemma avgOver_uniform_pointNext_decompose
    (params : Parameters) [FieldModel params.q]
    (f : Point params.next → Error) :
    avgOver (uniformDistribution (Point params.next)) f =
      avgOver (uniformDistribution (Fq params))
        (fun x => avgOver (uniformDistribution (Point params))
          (fun u => f (appendPoint params u x))) := by
  simpa using CommutativityPoints.avgOver_uniform_pointNext_decompose params f


/-- The evaluated point family has the same total as the underlying slice
measurement `G` at the sampled height.

This unfolds `evaluatedPointFamily` as postprocessing of `family.meas y`; the
postprocessing total is unchanged, and `hG` identifies the slice with `G y`. -/
lemma evaluatedPointFamily_total_eq_G_total
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (u : Point params.next) :
    ((evaluatedPointFamily params family u).total) =
      (G (pointHeight params u)).total := by
  simp [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
    postprocess_total, hG]

/-- Expand a finite sum in the middle factor of a left-register sandwich.

Linearity of matrix multiplication, left tensor placement, multiplication by a
fixed right-register operator, and `ev` turns
`A (∑ x, B_x) C R ⊗ D` into the corresponding sum of expectations
`∑ x, A B_x C R ⊗ D`. -/
lemma ev_leftTensor_mul_middle_finset_sum
    {α : Type*} (s : Finset α)
    (ψ : QuantumState (ι × ι))
    (A C R D : MIPStarRE.Quantum.Op ι)
    (B : α → MIPStarRE.Quantum.Op ι) :
    ev ψ
        (leftTensor (ι₂ := ι) (((A * (∑ x ∈ s, B x) * C) * R)) *
          rightTensor (ι₁ := ι) D) =
      ∑ x ∈ s,
        ev ψ
          (leftTensor (ι₂ := ι) (((A * B x * C) * R)) *
            rightTensor (ι₁ := ι) D) := by
  classical
  have hinner :
      ((A * (∑ x ∈ s, B x) * C) * R) =
        ∑ x ∈ s, ((A * B x * C) * R) := by
    simp [Matrix.mul_sum, Finset.sum_mul, mul_assoc]
  calc
    ev ψ
        (leftTensor (ι₂ := ι) (((A * (∑ x ∈ s, B x) * C) * R)) *
          rightTensor (ι₁ := ι) D)
        = ev ψ
            (leftTensor (ι₂ := ι) (∑ x ∈ s, ((A * B x * C) * R)) *
              rightTensor (ι₁ := ι) D) := by rw [hinner]
    _ = ev ψ
          ((∑ x ∈ s, leftTensor (ι₂ := ι) (((A * B x * C) * R))) *
            rightTensor (ι₁ := ι) D) := by
          rw [leftTensor_finset_sum (ι₂ := ι)]
    _ = ev ψ
          (∑ x ∈ s,
            leftTensor (ι₂ := ι) (((A * B x * C) * R) ) *
              rightTensor (ι₁ := ι) D) := by
          rw [Finset.sum_mul]
    _ = ∑ x ∈ s,
          ev ψ
            (leftTensor (ι₂ := ι) (((A * B x * C) * R)) *
              rightTensor (ι₁ := ι) D) := by
          rw [ev_finset_sum]


/-- Evaluating the slice family at an appended point is postprocessing the slice
measurement by the fiber `{g | g u = a}`. -/
lemma evaluatedPointFamily_appendPoint_outcome
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (hG : ∀ x, G x = (family.meas x).toSubMeas)
    (x : Fq params) (u : Point params) (a : Fq params) :
    (evaluatedPointFamily params family (appendPoint params u x)).outcome a =
      ∑ g ∈ Finset.univ.filter (fun g : Polynomial params => g u = a),
        (G x).outcome g := by
  simp [evaluatedPointFamily, IdxPolyFamily.evaluatedAtNextPoint, evaluateAt,
    postprocess, hG, truncatePoint_appendPoint, pointHeight_appendPoint]

end MIPStarRE.LDT.Commutativity
