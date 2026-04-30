import MIPStarRE.LDT.CommutativityPoints.Approximation

/-!
# Section 10 commutativity points: shared helpers core

Shared reindexing and tensor-placement helpers used by the Section 10
commutativity-of-points argument.

## References

- arXiv:2009.12982, Section 10 (commutativity of the point measurements).
-/

namespace MIPStarRE.LDT.CommutativityPoints

open MIPStarRE.LDT.GlobalVariance (PointPairQuestion)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix MatrixOrder ComplexOrder BigOperators
/-! ## Shared reindexing and tensor-placement helpers -/

private lemma qSDDOp_symm
    {Outcome : Type*}
    (ψ : QuantumState ι) [Fintype Outcome]
    (A B : OpFamily Outcome ι) :
    qSDDOp ψ A B = qSDDOp ψ B A := by
  let F : Outcome → MIPStarRE.Quantum.Op ι := fun a => A.outcome a - B.outcome a
  let G : Outcome → MIPStarRE.Quantum.Op ι := fun a => B.outcome a - A.outcome a
  have hFG : F = fun a => -G a := by
    funext a
    dsimp [F, G]
    abel
  unfold qSDDOp qSDDCore
  change ∑ a : Outcome, ev ψ ((F a)ᴴ * F a) = ∑ a : Outcome, ev ψ ((G a)ᴴ * G a)
  rw [hFG]
  refine Finset.sum_congr rfl ?_
  intro a _
  change ev ψ ((-G a)ᴴ * (-G a)) = ev ψ ((G a)ᴴ * G a)
  simp

lemma sddOpRel_symm
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ : Error) :
    SDDOpRel ψ 𝒟 A B δ →
      SDDOpRel ψ 𝒟 B A δ := by
  intro ⟨h⟩
  constructor
  simpa [sddErrorOp, qSDDOp_symm] using h

/-- Reindexing the outcome type of both operator families preserves `qSDDOp`. -/
lemma qSDDOp_reindex
    {Outcome Outcome' : Type*}
    [Fintype Outcome] [Fintype Outcome']
    (e : Outcome ≃ Outcome')
    (ψ : QuantumState ι)
    (A B : OpFamily Outcome ι) :
    qSDDOp ψ A B =
      qSDDOp ψ
        ({ outcome := fun a' => A.outcome (e.symm a')
           total := A.total } : OpFamily Outcome' ι)
        ({ outcome := fun a' => B.outcome (e.symm a')
           total := B.total } : OpFamily Outcome' ι) := by
  unfold qSDDOp qSDDCore
  calc
    ∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))
      = ∑ a' : Outcome',
          ev ψ
            ((A.outcome (e.symm a') - B.outcome (e.symm a'))ᴴ *
              (A.outcome (e.symm a') - B.outcome (e.symm a'))) := by
          exact Fintype.sum_equiv e
            (fun a =>
              ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a)))
            (fun a' =>
              ev ψ
                ((A.outcome (e.symm a') - B.outcome (e.symm a'))ᴴ *
                  (A.outcome (e.symm a') - B.outcome (e.symm a'))))
            (by
              intro a
              simp)
    _ = qSDDOp ψ
          ({ outcome := fun a' => A.outcome (e.symm a')
             total := A.total } : OpFamily Outcome' ι)
          ({ outcome := fun a' => B.outcome (e.symm a')
             total := B.total } : OpFamily Outcome' ι) := by
          rfl

/-- Reindexing the outcome type of both indexed families preserves `SDDOpRel`. -/
lemma sddOpRel_reindex
    {Question Outcome Outcome' : Type*}
    [Fintype Outcome] [Fintype Outcome']
    (e : Outcome ≃ Outcome')
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ : Error) :
    SDDOpRel ψ 𝒟 A B δ →
      SDDOpRel ψ 𝒟
        (fun q =>
          ({ outcome := fun a' => (A q).outcome (e.symm a')
             total := (A q).total } : OpFamily Outcome' ι))
        (fun q =>
          ({ outcome := fun a' => (B q).outcome (e.symm a')
             total := (B q).total } : OpFamily Outcome' ι))
        δ := by
  intro ⟨h⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver 𝒟
        (fun q =>
          qSDDOp ψ
            ({ outcome := fun a' => (A q).outcome (e.symm a')
               total := (A q).total } : OpFamily Outcome' ι)
            ({ outcome := fun a' => (B q).outcome (e.symm a')
               total := (B q).total } : OpFamily Outcome' ι))
      = avgOver 𝒟 (fun q => qSDDOp ψ (A q) (B q)) := by
          apply avgOver_congr
          intro q
          rw [qSDDOp_reindex e ψ (A q) (B q)]
    _ ≤ δ := h

/-- Pointwise equality of outcomes preserves `SDDOpRel`. -/
lemma sddOpRel_congr_outcome
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B A' B' : IdxOpFamily Question Outcome ι) (δ : Error)
    (hA : ∀ q a, (A q).outcome a = (A' q).outcome a)
    (hB : ∀ q a, (B q).outcome a = (B' q).outcome a) :
    SDDOpRel ψ 𝒟 A B δ →
      SDDOpRel ψ 𝒟 A' B' δ := by
  intro ⟨h⟩
  constructor
  unfold sddErrorOp at *
  calc
    avgOver 𝒟 (fun q => qSDDOp ψ (A' q) (B' q))
      = avgOver 𝒟 (fun q => qSDDOp ψ (A q) (B q)) := by
          apply avgOver_congr
          intro q
          unfold qSDDOp qSDDCore
          apply Finset.sum_congr rfl
          intro a _
          rw [hA q a, hB q a]
    _ ≤ δ := h

lemma subMeas_sum_adjoint_mul_le_one
    {Outcome : Type*}
    [Fintype Outcome]
    (A : SubMeas Outcome ι) :
    ∑ a : Outcome, (A.outcome a)ᴴ * A.outcome a ≤ 1 := by
  calc
    ∑ a : Outcome, (A.outcome a)ᴴ * A.outcome a
      = ∑ a : Outcome, A.outcome a * A.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [SubMeas.outcome_hermitian]
    _ ≤ ∑ a : Outcome, A.outcome a := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact MIPStarRE.Quantum.sq_le_self (A.outcome_pos a) (A.outcome_le_one a)
    _ = A.total := A.sum_eq_total
    _ ≤ 1 := A.total_le_one

/-- Multiplying a left lift with a left-placed family stays on the left tensor factor. -/
lemma liftLeft_mul_leftPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftLeft).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b =
      leftTensor (A.outcome a * B.outcome b) := by
  calc
    (A.liftLeft).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b
      = leftTensor (A.outcome a) * leftTensor (B.outcome b) := by
          rfl
    _ = leftTensor (A.outcome a * B.outcome b) := by
          rw [leftTensor_mul_leftTensor]

/-- Multiplying a left lift with a right-placed family gives the tensor product. -/
lemma liftLeft_mul_rightPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftLeft).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b =
      opTensor (A.outcome a) (B.outcome b) := by
  calc
    (A.liftLeft).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b
      = leftTensor (A.outcome a) * rightTensor (B.outcome b) := by
          rfl
    _ = opTensor (A.outcome a) (B.outcome b) := by
          rw [leftTensor_mul_rightTensor_eq_opTensor]

/-- Multiplying a right lift with a left-placed family gives the tensor product. -/
lemma liftRight_mul_leftPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftRight).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b =
      opTensor (B.outcome b) (A.outcome a) := by
  calc
    (A.liftRight).outcome a * (OpFamily.leftPlacedOpFamily B.toOpFamily).outcome b
      = rightTensor (A.outcome a) * leftTensor (B.outcome b) := by
          rfl
    _ = opTensor (B.outcome b) (A.outcome a) := by
          rw [rightTensor_mul_leftTensor_eq_opTensor]

/-- Multiplying a right lift with a right-placed family stays on the right tensor factor. -/
lemma liftRight_mul_rightPlaced_outcome
    {α β : Type*}
    [Fintype α] [Fintype β]
    (A : SubMeas α ι) (B : SubMeas β ι)
    (a : α) (b : β) :
    (A.liftRight).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b =
      rightTensor (A.outcome a * B.outcome b) := by
  calc
    (A.liftRight).outcome a * (OpFamily.rightPlacedOpFamily B.toOpFamily).outcome b
      = rightTensor (A.outcome a) * rightTensor (B.outcome b) := by
          rfl
    _ = rightTensor (A.outcome a * B.outcome b) := by
          rw [rightTensor_mul_rightTensor]

end MIPStarRE.LDT.CommutativityPoints
