import MIPStarRE.LDT.Test.StrategyBiProj
import MIPStarRE.LDT.Test.StrategyFailures

/-!
# Role-Register Averaging: Branch Equalities

This module proves the role-register branch equalities for heterogeneous
projective strategies.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

open MIPStarRE.Quantum

namespace ProjStrat

private theorem rolePairProj_mul_eq_zero_of_ne (rL rR sL sR : Role)
    (h : (rL, rR) ≠ (sL, sR)) :
    rolePairProj rL rR * rolePairProj sL sR = 0 := by
  rw [rolePairProj, rolePairProj, opTensor_mul]
  cases rL <;> cases rR <;> cases sL <;> cases sR <;>
    simp [opTensor] at h ⊢

theorem rolePairDirectSumCond_mul_eq_zero_of_ne {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (rL rR sL sR : Role)
    (X Y : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB))
    (h : (rL, rR) ≠ (sL, sR)) :
    rolePairDirectSumCond rL rR X * rolePairDirectSumCond sL sR Y = 0 := by
  unfold rolePairDirectSumCond
  let e := roleRegisterPairLocalEquiv ιA ιB
  change (Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj rL rR) X) *
      (Matrix.reindexAlgEquiv ℂ ℂ e) (opTensor (rolePairProj sL sR) Y) = 0
  rw [← Matrix.reindexAlgEquiv_mul (R := ℂ) (A := ℂ) e]
  rw [opTensor_mul, rolePairProj_mul_eq_zero_of_ne rL rR sL sR h]
  simp [opTensor]

theorem ev_roleRegisterSymmState_rolePairDirectSumCond_AA {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (X : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    ev (roleRegisterSymmState ψ) (rolePairDirectSumCond Role.A Role.A X) = 0 := by
  unfold ev roleRegisterSymmState
  change Complex.re (MIPStarRE.Quantum.normalizedTrace (((roleRegisterDensityScale ιA ιB : ℂ) •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
      (roleRegisterDensityScale ιA ιB : ℂ) •
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density))) *
        rolePairDirectSumCond Role.A Role.A X)) = 0
  rw [Matrix.add_mul, MIPStarRE.Quantum.normalizedTrace_add]
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [rolePairDirectSumCond_mul_eq_zero_of_ne Role.A Role.B Role.A Role.A
      (localPairABBlock ψ.density) X (by decide)]
  rw [rolePairDirectSumCond_mul_eq_zero_of_ne Role.B Role.A Role.A Role.A
      (localPairBABlock (heterogeneousSwapDensity ψ.density)) X (by decide)]
  simp

theorem ev_roleRegisterSymmState_rolePairDirectSumCond_BB {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (X : MIPStarRE.Quantum.Op
      (LocalCarrierSum ιA ιB × LocalCarrierSum ιA ιB)) :
    ev (roleRegisterSymmState ψ) (rolePairDirectSumCond Role.B Role.B X) = 0 := by
  unfold ev roleRegisterSymmState
  change Complex.re (MIPStarRE.Quantum.normalizedTrace (((roleRegisterDensityScale ιA ιB : ℂ) •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
      (roleRegisterDensityScale ιA ιB : ℂ) •
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density))) *
        rolePairDirectSumCond Role.B Role.B X)) = 0
  rw [Matrix.add_mul, MIPStarRE.Quantum.normalizedTrace_add]
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [rolePairDirectSumCond_mul_eq_zero_of_ne Role.A Role.B Role.B Role.B
      (localPairABBlock ψ.density) X (by decide)]
  rw [rolePairDirectSumCond_mul_eq_zero_of_ne Role.B Role.A Role.B Role.B
      (localPairBABlock (heterogeneousSwapDensity ψ.density)) X (by decide)]
  simp

private lemma opTensor_roleBlock_eq_rolePairDirectSumCond_sum {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A B C D : MIPStarRE.Quantum.Op (LocalCarrierSum ιA ιB)) :
    opTensor (roleBlock A B) (roleBlock C D) =
      rolePairDirectSumCond Role.A Role.A (opTensor A C) +
        rolePairDirectSumCond Role.A Role.B (opTensor A D) +
          (rolePairDirectSumCond Role.B Role.A (opTensor B C) +
            rolePairDirectSumCond Role.B Role.B (opTensor B D)) := by
  ext x y
  rcases x with ⟨⟨rx, ix⟩, ⟨sx, jx⟩⟩
  rcases y with ⟨⟨ry, iy⟩, ⟨sy, jy⟩⟩
  cases rx <;> cases sx <;> cases ry <;> cases sy <;>
    simp [opTensor, rolePairDirectSumCond, rolePairProj, roleProj,
      roleRegisterPairLocalEquiv]

private lemma localPairABBlock_mul_opTensor_localDirectSumBlocks {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : MIPStarRE.Quantum.Op (ιA × ιB))
    (A : MIPStarRE.Quantum.Op ιA) (Bfill : MIPStarRE.Quantum.Op ιB)
    (Afill : MIPStarRE.Quantum.Op ιA) (D : MIPStarRE.Quantum.Op ιB) :
    localPairABBlock X *
        opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock Afill D) =
      localPairABBlock (X * opTensor A D) := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ with
  | inl i =>
      cases x₂ with
      | inl j =>
          cases y₁ <;> cases y₂ <;> simp [localPairABBlock, Matrix.mul_apply]
      | inr j =>
          cases y₁ with
          | inl i' =>
              cases y₂ with
              | inl j' =>
                  rw [Matrix.mul_apply, Fintype.sum_prod_type]
                  simp [localPairABBlock, opTensor]
              | inr j' =>
                  rw [Matrix.mul_apply, Fintype.sum_prod_type]
                  simp only [Fintype.sum_sum_type, localPairABBlock, opTensor,
                    localDirectSumBlock, Matrix.of_apply, zero_mul, Finset.sum_const_zero,
                    zero_add, add_zero]
                  exact (Fintype.sum_prod_type'
                    (f := fun x : ιA => fun y : ιB =>
                      X (i, j) (x, y) * (A x i' * D y j'))).symm
          | inr i' =>
              cases y₂ <;>
                rw [Matrix.mul_apply, Fintype.sum_prod_type] <;>
                simp [localPairABBlock, opTensor]
  | inr i =>
      cases x₂ <;> cases y₁ <;> cases y₂ <;>
        simp [localPairABBlock, Matrix.mul_apply]

private lemma localPairBABlock_mul_opTensor_localDirectSumBlocks {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (X : MIPStarRE.Quantum.Op (ιB × ιA))
    (B : MIPStarRE.Quantum.Op ιB) (Afill : MIPStarRE.Quantum.Op ιA)
    (A : MIPStarRE.Quantum.Op ιA) (Bfill : MIPStarRE.Quantum.Op ιB) :
    localPairBABlock X *
        opTensor (localDirectSumBlock Afill B) (localDirectSumBlock A Bfill) =
      localPairBABlock (X * opTensor B A) := by
  ext x y
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  cases x₁ with
  | inl i =>
      cases x₂ <;> cases y₁ <;> cases y₂ <;>
        simp [localPairBABlock, Matrix.mul_apply]
  | inr i =>
      cases x₂ with
      | inl j =>
          cases y₁ with
          | inl i' =>
              cases y₂ <;>
                rw [Matrix.mul_apply, Fintype.sum_prod_type] <;>
                simp [localPairBABlock, opTensor]
          | inr i' =>
              cases y₂ with
              | inl j' =>
                  rw [Matrix.mul_apply, Fintype.sum_prod_type]
                  simp only [Fintype.sum_sum_type, localPairBABlock, opTensor,
                    localDirectSumBlock, Matrix.of_apply, zero_mul, Finset.sum_const_zero,
                    zero_add, add_zero]
                  exact (Fintype.sum_prod_type'
                    (f := fun x : ιB => fun y : ιA =>
                      X (i, j) (x, y) * (B x i' * A y j'))).symm
              | inr j' =>
                  rw [Matrix.mul_apply, Fintype.sum_prod_type]
                  simp [localPairBABlock, opTensor]
      | inr j =>
          cases y₁ <;> cases y₂ <;> simp [localPairBABlock, Matrix.mul_apply]

private lemma ev_roleRegisterSymmState_rolePair_AB_localDirectSumBlocks
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (A : MIPStarRE.Quantum.Op ιA) (Bfill : MIPStarRE.Quantum.Op ιB)
    (Afill : MIPStarRE.Quantum.Op ιA) (D : MIPStarRE.Quantum.Op ιB) :
    ev (roleRegisterSymmState ψ)
        (rolePairDirectSumCond Role.A Role.B
          (opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock Afill D))) =
      (1 / 2 : Error) * ev ψ (opTensor A D) := by
  unfold ev roleRegisterSymmState
  change Complex.re (MIPStarRE.Quantum.normalizedTrace (((roleRegisterDensityScale ιA ιB : ℂ) •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
      (roleRegisterDensityScale ιA ιB : ℂ) •
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density))) *
        rolePairDirectSumCond Role.A Role.B
          (opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock Afill D)))) =
    (1 / 2 : Error) * ev ψ (opTensor A D)
  rw [Matrix.add_mul, MIPStarRE.Quantum.normalizedTrace_add]
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [rolePairDirectSumCond_mul_same, rolePairDirectSumCond_BA_mul_AB]
  rw [localPairABBlock_mul_opTensor_localDirectSumBlocks]
  rw [MIPStarRE.Quantum.normalizedTrace_smul, MIPStarRE.Quantum.normalizedTrace_smul]
  simp only [MIPStarRE.Quantum.normalizedTrace_zero, mul_zero, add_zero]
  rw [normalizedTrace_rolePairDirectSumCond, normalizedTrace_localPairABBlock]
  let T := MIPStarRE.Quantum.normalizedTrace (ψ.density * opTensor A D)
  let R : ℂ :=
    (Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ) /
      ((Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ^ (2 : ℕ))
  have hA : (Fintype.card ιA : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card ιB : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hscalar :
      (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * R) = (1 / 2 : ℂ) := by
    subst R
    unfold roleRegisterDensityScale
    field_simp [hA, hB, hS, Nat.cast_pow, Nat.cast_mul]
    norm_num [Nat.cast_pow, Nat.cast_mul]
    field_simp [hA, hB]
    ring_nf
  change Complex.re ((roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T))) =
    (1 / 2 : Error) * ev ψ (opTensor A D)
  rw [show ev ψ (opTensor A D) = Complex.re T by rfl]
  rw [show (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T)) =
      ((roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * R)) * T by
    ring]
  rw [hscalar]
  norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

private lemma ev_roleRegisterSymmState_rolePair_BA_localDirectSumBlocks
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (B : MIPStarRE.Quantum.Op ιB) (Afill : MIPStarRE.Quantum.Op ιA)
    (A : MIPStarRE.Quantum.Op ιA) (Bfill : MIPStarRE.Quantum.Op ιB) :
    ev (roleRegisterSymmState ψ)
        (rolePairDirectSumCond Role.B Role.A
          (opTensor (localDirectSumBlock Afill B) (localDirectSumBlock A Bfill))) =
      (1 / 2 : Error) * ev ψ (opTensor A B) := by
  unfold ev roleRegisterSymmState
  change Complex.re (MIPStarRE.Quantum.normalizedTrace (((roleRegisterDensityScale ιA ιB : ℂ) •
      rolePairDirectSumCond Role.A Role.B (localPairABBlock ψ.density) +
      (roleRegisterDensityScale ιA ιB : ℂ) •
        rolePairDirectSumCond Role.B Role.A
          (localPairBABlock (heterogeneousSwapDensity ψ.density))) *
        rolePairDirectSumCond Role.B Role.A
          (opTensor (localDirectSumBlock Afill B) (localDirectSumBlock A Bfill)))) =
    (1 / 2 : Error) * ev ψ (opTensor A B)
  rw [Matrix.add_mul, MIPStarRE.Quantum.normalizedTrace_add]
  rw [smul_mul_assoc, smul_mul_assoc]
  rw [rolePairDirectSumCond_AB_mul_BA, rolePairDirectSumCond_mul_same]
  rw [localPairBABlock_mul_opTensor_localDirectSumBlocks]
  rw [← heterogeneousSwapDensity_opTensor]
  rw [← heterogeneousSwapDensity_mul]
  rw [MIPStarRE.Quantum.normalizedTrace_smul, MIPStarRE.Quantum.normalizedTrace_smul]
  simp only [MIPStarRE.Quantum.normalizedTrace_zero, mul_zero, zero_add]
  rw [normalizedTrace_rolePairDirectSumCond, normalizedTrace_localPairBABlock,
    normalizedTrace_heterogeneousSwapDensity]
  let T := MIPStarRE.Quantum.normalizedTrace (ψ.density * opTensor A B)
  let R : ℂ :=
    (Fintype.card ιA : ℂ) * (Fintype.card ιB : ℂ) /
      ((Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ^ (2 : ℕ))
  have hA : (Fintype.card ιA : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hB : (Fintype.card ιB : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hS : (Fintype.card (LocalCarrierSum ιA ιB) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hscalar :
      (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * R) = (1 / 2 : ℂ) := by
    subst R
    unfold roleRegisterDensityScale
    field_simp [hA, hB, hS, Nat.cast_pow, Nat.cast_mul]
    norm_num [Nat.cast_pow, Nat.cast_mul]
    field_simp [hA, hB]
    ring_nf
  change Complex.re ((roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T))) =
    (1 / 2 : Error) * ev ψ (opTensor A B)
  rw [show ev ψ (opTensor A B) = Complex.re T by rfl]
  rw [show (roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * (R * T)) =
      ((roleRegisterDensityScale ιA ιB : ℂ) * ((1 / 4 : ℂ) * R)) * T by
    ring]
  rw [hscalar]
  norm_num [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

private lemma ev_roleRegisterSymmState_roleBlock_localDirectSumBlocks
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (A C Afill Cfill : MIPStarRE.Quantum.Op ιA)
    (B D Bfill Dfill : MIPStarRE.Quantum.Op ιB) :
    ev (roleRegisterSymmState ψ)
        (opTensor
          (roleBlock (localDirectSumBlock A Bfill) (localDirectSumBlock Afill B))
          (roleBlock (localDirectSumBlock C Dfill) (localDirectSumBlock Cfill D))) =
      (1 / 2 : Error) * ev ψ (opTensor A D) +
        (1 / 2 : Error) * ev ψ (opTensor C B) := by
  calc
    ev (roleRegisterSymmState ψ)
        (opTensor
          (roleBlock (localDirectSumBlock A Bfill) (localDirectSumBlock Afill B))
          (roleBlock (localDirectSumBlock C Dfill) (localDirectSumBlock Cfill D)))
      = ev (roleRegisterSymmState ψ)
          (rolePairDirectSumCond Role.A Role.A
              (opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock C Dfill)) +
            rolePairDirectSumCond Role.A Role.B
              (opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock Cfill D)) +
              (rolePairDirectSumCond Role.B Role.A
                (opTensor (localDirectSumBlock Afill B) (localDirectSumBlock C Dfill)) +
                rolePairDirectSumCond Role.B Role.B
                  (opTensor (localDirectSumBlock Afill B)
                    (localDirectSumBlock Cfill D)))) := by
          rw [opTensor_roleBlock_eq_rolePairDirectSumCond_sum]
    _ =
        ev (roleRegisterSymmState ψ)
          (rolePairDirectSumCond Role.A Role.A
              (opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock C Dfill))) +
          ev (roleRegisterSymmState ψ)
            (rolePairDirectSumCond Role.A Role.B
              (opTensor (localDirectSumBlock A Bfill) (localDirectSumBlock Cfill D))) +
            (ev (roleRegisterSymmState ψ)
              (rolePairDirectSumCond Role.B Role.A
                (opTensor (localDirectSumBlock Afill B) (localDirectSumBlock C Dfill))) +
              ev (roleRegisterSymmState ψ)
                (rolePairDirectSumCond Role.B Role.B
                  (opTensor (localDirectSumBlock Afill B)
                    (localDirectSumBlock Cfill D)))) := by
          repeat rw [ev_add]
    _ = 0 + (1 / 2 : Error) * ev ψ (opTensor A D) +
            ((1 / 2 : Error) * ev ψ (opTensor C B) + 0) := by
          rw [ev_roleRegisterSymmState_rolePairDirectSumCond_AA,
            ev_roleRegisterSymmState_rolePair_AB_localDirectSumBlocks,
            ev_roleRegisterSymmState_rolePair_BA_localDirectSumBlocks,
            ev_roleRegisterSymmState_rolePairDirectSumCond_BB]
    _ = (1 / 2 : Error) * ev ψ (opTensor A D) +
        (1 / 2 : Error) * ev ψ (opTensor C B) := by
          ring

private lemma ev_roleRegisterSymmState_roleRegisterProjMeas_outcome
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (MA NA : ProjMeas Outcome ιA) (MB NB : ProjMeas Outcome ιB)
    (a : Outcome) :
    ev (roleRegisterSymmState ψ)
        (opTensor ((roleRegisterProjMeas MA MB).outcome a)
          ((roleRegisterProjMeas NA NB).outcome a)) =
      (1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
        (1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a)) := by
  let fillerA : ProjMeas Outcome ιA := ProjMeas.trivialDistinguishedOutcome default
  let fillerB : ProjMeas Outcome ιB := ProjMeas.trivialDistinguishedOutcome default
  calc
    ev (roleRegisterSymmState ψ)
        (opTensor ((roleRegisterProjMeas MA MB).outcome a)
          ((roleRegisterProjMeas NA NB).outcome a))
      = ev (roleRegisterSymmState ψ)
          (rolePairDirectSumCond Role.A Role.A
              (opTensor
                (localDirectSumBlock (MA.outcome a) (fillerB.outcome a))
                (localDirectSumBlock (NA.outcome a) (fillerB.outcome a))) +
            rolePairDirectSumCond Role.A Role.B
              (opTensor
                (localDirectSumBlock (MA.outcome a) (fillerB.outcome a))
                (localDirectSumBlock (fillerA.outcome a) (NB.outcome a))) +
              (rolePairDirectSumCond Role.B Role.A
                (opTensor
                  (localDirectSumBlock (fillerA.outcome a) (MB.outcome a))
                  (localDirectSumBlock (NA.outcome a) (fillerB.outcome a))) +
                rolePairDirectSumCond Role.B Role.B
                  (opTensor
                    (localDirectSumBlock (fillerA.outcome a) (MB.outcome a))
                    (localDirectSumBlock (fillerA.outcome a) (NB.outcome a))))) := by
          congr 1
          simp [roleRegisterProjMeas, opTensor_roleBlock_eq_rolePairDirectSumCond_sum,
            fillerA, fillerB]
    _ =
        ev (roleRegisterSymmState ψ)
          (rolePairDirectSumCond Role.A Role.A
              (opTensor
                (localDirectSumBlock (MA.outcome a) (fillerB.outcome a))
                (localDirectSumBlock (NA.outcome a) (fillerB.outcome a)))) +
          ev (roleRegisterSymmState ψ)
            (rolePairDirectSumCond Role.A Role.B
              (opTensor
                (localDirectSumBlock (MA.outcome a) (fillerB.outcome a))
                (localDirectSumBlock (fillerA.outcome a) (NB.outcome a)))) +
            (ev (roleRegisterSymmState ψ)
              (rolePairDirectSumCond Role.B Role.A
                (opTensor
                  (localDirectSumBlock (fillerA.outcome a) (MB.outcome a))
                  (localDirectSumBlock (NA.outcome a) (fillerB.outcome a)))) +
              ev (roleRegisterSymmState ψ)
                (rolePairDirectSumCond Role.B Role.B
                  (opTensor
                    (localDirectSumBlock (fillerA.outcome a) (MB.outcome a))
                    (localDirectSumBlock (fillerA.outcome a) (NB.outcome a))))) := by
          repeat rw [ev_add]
    _ = 0 +
          (1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
            ((1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a)) +
              0) := by
          rw [ev_roleRegisterSymmState_rolePairDirectSumCond_AA,
            ev_roleRegisterSymmState_rolePair_AB_localDirectSumBlocks,
            ev_roleRegisterSymmState_rolePair_BA_localDirectSumBlocks,
            ev_roleRegisterSymmState_rolePairDirectSumCond_BB]
    _ = (1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
        (1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a)) := by
          ring

private lemma postprocess_roleRegisterProjMeas_outcome
    {α β ιA ιB : Type*}
    [Inhabited α] [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (MA : ProjMeas α ιA) (MB : ProjMeas α ιB) (f : α → β) (b : β) :
    (postprocess ((roleRegisterProjMeas MA MB).toSubMeas) f).outcome b =
      roleBlock
        (localDirectSumBlock ((ProjMeas.postprocess MA f).outcome b)
          ((ProjMeas.postprocess
            (ProjMeas.trivialDistinguishedOutcome (ι := ιB) (default : α)) f).outcome b))
        (localDirectSumBlock
          ((ProjMeas.postprocess
            (ProjMeas.trivialDistinguishedOutcome (ι := ιA) (default : α)) f).outcome b)
          ((ProjMeas.postprocess MB f).outcome b)) := by
  classical
  rw [SubMeas.postprocess_outcome]
  simp only [roleRegisterProjMeas, roleBlockProjMeas_outcome,
    localDirectSumProjMeas_outcome, ProjMeas.postprocess_toSubMeas,
    SubMeas.postprocess_outcome]
  rw [roleBlock_finset_sum]
  rw [localDirectSumBlock_finset_sum, localDirectSumBlock_finset_sum]

private lemma ev_roleRegisterSymmState_point_postprocessedLine_outcome
    {α β ιA ιB : Type*}
    [Inhabited α] [Inhabited β] [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (PA : ProjMeas β ιA) (PB : ProjMeas β ιB)
    (LA : ProjMeas α ιA) (LB : ProjMeas α ιB)
    (f : α → β) (b : β) :
    ev (roleRegisterSymmState ψ)
        (opTensor ((roleRegisterProjMeas PA PB).outcome b)
          ((postprocess ((roleRegisterProjMeas LA LB).toSubMeas) f).outcome b)) =
      (1 / 2 : Error) *
          ev ψ (opTensor (PA.outcome b) ((ProjMeas.postprocess LB f).outcome b)) +
        (1 / 2 : Error) *
          ev ψ (opTensor ((ProjMeas.postprocess LA f).outcome b) (PB.outcome b)) := by
  let fillerAβ : ProjMeas β ιA := ProjMeas.trivialDistinguishedOutcome default
  let fillerBβ : ProjMeas β ιB := ProjMeas.trivialDistinguishedOutcome default
  rw [postprocess_roleRegisterProjMeas_outcome]
  change ev (roleRegisterSymmState ψ)
      (opTensor
        (roleBlock (localDirectSumBlock (PA.outcome b) (fillerBβ.outcome b))
          (localDirectSumBlock (fillerAβ.outcome b) (PB.outcome b)))
        (roleBlock
          (localDirectSumBlock ((ProjMeas.postprocess LA f).outcome b)
            ((ProjMeas.postprocess
              (ProjMeas.trivialDistinguishedOutcome (ι := ιB) (default : α)) f).outcome b))
          (localDirectSumBlock
            ((ProjMeas.postprocess
              (ProjMeas.trivialDistinguishedOutcome (ι := ιA) (default : α)) f).outcome b)
            ((ProjMeas.postprocess LB f).outcome b)))) =
    (1 / 2 : Error) *
        ev ψ (opTensor (PA.outcome b) ((ProjMeas.postprocess LB f).outcome b)) +
      (1 / 2 : Error) *
        ev ψ (opTensor ((ProjMeas.postprocess LA f).outcome b) (PB.outcome b))
  exact ev_roleRegisterSymmState_roleBlock_localDirectSumBlocks ψ
    (PA.outcome b) ((ProjMeas.postprocess LA f).outcome b)
    (fillerAβ.outcome b)
    ((ProjMeas.postprocess
      (ProjMeas.trivialDistinguishedOutcome (ι := ιA) (default : α)) f).outcome b)
    (PB.outcome b) ((ProjMeas.postprocess LB f).outcome b)
    (fillerBβ.outcome b)
    ((ProjMeas.postprocess
      (ProjMeas.trivialDistinguishedOutcome (ι := ιB) (default : α)) f).outcome b)

private lemma qBipartiteMatchMass_roleRegister_point_postprocessedLine_eq_average
    {α β ιA ιB : Type*}
    [Inhabited α] [Inhabited β] [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (PA : ProjMeas β ιA) (PB : ProjMeas β ιB)
    (LA : ProjMeas α ιA) (LB : ProjMeas α ιB) (f : α → β) :
    qBipartiteMatchMass (roleRegisterSymmState ψ)
        (roleRegisterProjMeas PA PB).toSubMeas
        ((ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toSubMeas) =
      (qBipartiteMatchMass ψ PA.toSubMeas (ProjMeas.postprocess LB f).toSubMeas +
        qBipartiteMatchMass ψ (ProjMeas.postprocess LA f).toSubMeas PB.toSubMeas) / 2 := by
  unfold qBipartiteMatchMass
  calc
    ∑ b : β,
        ev (roleRegisterSymmState ψ)
          (opTensor ((roleRegisterProjMeas PA PB).outcome b)
            (((ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toSubMeas).outcome b))
      = ∑ b : β,
          ((1 / 2 : Error) *
              ev ψ (opTensor (PA.outcome b) ((ProjMeas.postprocess LB f).outcome b)) +
            (1 / 2 : Error) *
              ev ψ (opTensor ((ProjMeas.postprocess LA f).outcome b) (PB.outcome b))) := by
            refine Finset.sum_congr rfl ?_
            intro b _
            exact ev_roleRegisterSymmState_point_postprocessedLine_outcome
              ψ PA PB LA LB f b
    _ = (1 / 2 : Error) *
          ∑ b : β, ev ψ (opTensor (PA.outcome b) ((ProjMeas.postprocess LB f).outcome b)) +
        (1 / 2 : Error) *
          ∑ b : β, ev ψ (opTensor ((ProjMeas.postprocess LA f).outcome b) (PB.outcome b)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ =
        (∑ b : β, ev ψ (opTensor (PA.outcome b) ((ProjMeas.postprocess LB f).outcome b)) +
          ∑ b : β, ev ψ (opTensor ((ProjMeas.postprocess LA f).outcome b)
            (PB.outcome b))) / 2 := by
          ring

private lemma qBipartiteConsDefect_roleRegister_point_postprocessedLine_eq_average
    {α β ιA ιB : Type*}
    [Inhabited α] [Inhabited β] [Fintype α] [Fintype β]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (PA : ProjMeas β ιA) (PB : ProjMeas β ιB)
    (LA : ProjMeas α ιA) (LB : ProjMeas α ιB) (f : α → β) :
    qBipartiteConsDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas PA PB).toSubMeas
        ((ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toSubMeas) =
      (qBipartiteConsDefect ψ PA.toSubMeas (ProjMeas.postprocess LB f).toSubMeas +
        qBipartiteConsDefect ψ (ProjMeas.postprocess LA f).toSubMeas PB.toSubMeas) / 2 := by
  calc
    qBipartiteConsDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas PA PB).toSubMeas
        ((ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toSubMeas)
      = ev (roleRegisterSymmState ψ)
          (1 : MIPStarRE.Quantum.Op
            (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB)) -
          qBipartiteMatchMass (roleRegisterSymmState ψ)
            (roleRegisterProjMeas PA PB).toSubMeas
            ((ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toSubMeas) := by
            exact qBipartiteConsDefect_of_measurements (roleRegisterSymmState ψ)
              (roleRegisterProjMeas PA PB).toMeasurement
              (ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toMeasurement
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
          qBipartiteMatchMass (roleRegisterSymmState ψ)
            (roleRegisterProjMeas PA PB).toSubMeas
            ((ProjMeas.postprocess (roleRegisterProjMeas LA LB) f).toSubMeas) := by
            rw [ev_one_of_isNormalized (roleRegisterSymmState ψ)
              (roleRegisterSymmState_isNormalized ψ hψ), ev_one_of_isNormalized ψ hψ]
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
          ((qBipartiteMatchMass ψ PA.toSubMeas
              (ProjMeas.postprocess LB f).toSubMeas +
            qBipartiteMatchMass ψ (ProjMeas.postprocess LA f).toSubMeas
              PB.toSubMeas) / 2) := by
            rw [qBipartiteMatchMass_roleRegister_point_postprocessedLine_eq_average]
    _ = ((ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
            qBipartiteMatchMass ψ PA.toSubMeas
              (ProjMeas.postprocess LB f).toSubMeas) +
          (ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
            qBipartiteMatchMass ψ (ProjMeas.postprocess LA f).toSubMeas
              PB.toSubMeas)) / 2 := by
            ring
    _ = (qBipartiteConsDefect ψ PA.toSubMeas
            (ProjMeas.postprocess LB f).toSubMeas +
          qBipartiteConsDefect ψ (ProjMeas.postprocess LA f).toSubMeas
            PB.toSubMeas) / 2 := by
            rw [← qBipartiteConsDefect_of_measurements ψ PA.toMeasurement
              (ProjMeas.postprocess LB f).toMeasurement]
            rw [← qBipartiteConsDefect_of_measurements ψ
              (ProjMeas.postprocess LA f).toMeasurement PB.toMeasurement]

private lemma qBipartiteMatchMass_roleRegisterProjMeas_eq_average
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB))
    (MA NA : ProjMeas Outcome ιA) (MB NB : ProjMeas Outcome ιB) :
    qBipartiteMatchMass (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas
        (roleRegisterProjMeas NA NB).toSubMeas =
      (qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas +
        qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas) / 2 := by
  unfold qBipartiteMatchMass
  calc
    ∑ a : Outcome,
        ev (roleRegisterSymmState ψ)
          (opTensor ((roleRegisterProjMeas MA MB).outcome a)
            ((roleRegisterProjMeas NA NB).outcome a))
      = ∑ a : Outcome,
          ((1 / 2 : Error) * ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
            (1 / 2 : Error) * ev ψ (opTensor (NA.outcome a) (MB.outcome a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            exact ev_roleRegisterSymmState_roleRegisterProjMeas_outcome ψ MA NA MB NB a
    _ = (1 / 2 : Error) *
          ∑ a : Outcome, ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
        (1 / 2 : Error) *
          ∑ a : Outcome, ev ψ (opTensor (NA.outcome a) (MB.outcome a)) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ =
        (∑ a : Outcome, ev ψ (opTensor (MA.outcome a) (NB.outcome a)) +
          ∑ a : Outcome, ev ψ (opTensor (NA.outcome a) (MB.outcome a))) / 2 := by
          ring

private lemma qBipartiteConsDefect_roleRegisterProjMeas_eq_average
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (MA NA : ProjMeas Outcome ιA) (MB NB : ProjMeas Outcome ιB) :
    qBipartiteConsDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas
        (roleRegisterProjMeas NA NB).toSubMeas =
      (qBipartiteConsDefect ψ MA.toSubMeas NB.toSubMeas +
        qBipartiteConsDefect ψ NA.toSubMeas MB.toSubMeas) / 2 := by
  calc
    qBipartiteConsDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas
        (roleRegisterProjMeas NA NB).toSubMeas
      = ev (roleRegisterSymmState ψ)
          (1 : MIPStarRE.Quantum.Op
            (RoleRegisterLocal ιA ιB × RoleRegisterLocal ιA ιB)) -
          qBipartiteMatchMass (roleRegisterSymmState ψ)
            (roleRegisterProjMeas MA MB).toSubMeas
            (roleRegisterProjMeas NA NB).toSubMeas := by
            exact qBipartiteConsDefect_of_measurements (roleRegisterSymmState ψ)
              (roleRegisterProjMeas MA MB).toMeasurement
              (roleRegisterProjMeas NA NB).toMeasurement
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
          qBipartiteMatchMass (roleRegisterSymmState ψ)
            (roleRegisterProjMeas MA MB).toSubMeas
            (roleRegisterProjMeas NA NB).toSubMeas := by
            rw [ev_one_of_isNormalized (roleRegisterSymmState ψ)
              (roleRegisterSymmState_isNormalized ψ hψ), ev_one_of_isNormalized ψ hψ]
    _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
          ((qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas +
            qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas) / 2) := by
            rw [qBipartiteMatchMass_roleRegisterProjMeas_eq_average]
    _ = ((ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
            qBipartiteMatchMass ψ MA.toSubMeas NB.toSubMeas) +
          (ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
            qBipartiteMatchMass ψ NA.toSubMeas MB.toSubMeas)) / 2 := by
            ring
    _ = (qBipartiteConsDefect ψ MA.toSubMeas NB.toSubMeas +
          qBipartiteConsDefect ψ NA.toSubMeas MB.toSubMeas) / 2 := by
            rw [← qBipartiteConsDefect_of_measurements ψ MA.toMeasurement NB.toMeasurement]
            rw [← qBipartiteConsDefect_of_measurements ψ NA.toMeasurement MB.toMeasurement]

private lemma qBipartiteSSCDefect_roleRegisterProjMeas_eq_cons
    {Outcome ιA ιB : Type*}
    [Inhabited Outcome] [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (ψ : QuantumState (ιA × ιB)) (hψ : ψ.IsNormalized)
    (MA : ProjMeas Outcome ιA) (MB : ProjMeas Outcome ιB) :
    qBipartiteSSCDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas =
      qBipartiteConsDefect ψ MA.toSubMeas MB.toSubMeas := by
  calc
    qBipartiteSSCDefect (roleRegisterSymmState ψ)
        (roleRegisterProjMeas MA MB).toSubMeas
      = qBipartiteConsDefect (roleRegisterSymmState ψ)
          (roleRegisterProjMeas MA MB).toSubMeas
          (roleRegisterProjMeas MA MB).toSubMeas := by
          simp [qBipartiteSSCDefect, qBipartiteConsDefect, qBipartiteMatchMass,
            (roleRegisterProjMeas MA MB).total_eq_one, leftTensor, opTensor]
    _ = (qBipartiteConsDefect ψ MA.toSubMeas MB.toSubMeas +
          qBipartiteConsDefect ψ MA.toSubMeas MB.toSubMeas) / 2 := by
          rw [qBipartiteConsDefect_roleRegisterProjMeas_eq_average ψ hψ MA MA MB MB]
    _ = qBipartiteConsDefect ψ MA.toSubMeas MB.toSubMeas := by
          ring

/-- The point self-consistency branch of the heterogeneous role-register
symmetrization is exactly the original cross-prover point-agreement branch. -/
theorem roleRegisterSymmStrategy_selfConsistency_eq_pointAgreement
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB) :
    (strategy.roleRegisterSymmStrategy).selfConsistencyFailureProbability =
      strategy.pointAgreementFailureProbability := by
  haveI : Nonempty ιA := strategy.isNormalized.nonempty.map Prod.fst
  haveI : Nonempty ιB := strategy.isNormalized.nonempty.map Prod.snd
  unfold SymStrat.selfConsistencyFailureProbability ProjStrat.pointAgreementFailureProbability
  unfold bipartiteSSCError bipartiteConsError
  refine Finset.sum_congr rfl ?_
  intro u _
  exact congrArg (fun t => (uniformDistribution (Point params)).weight u * t)
    (qBipartiteSSCDefect_roleRegisterProjMeas_eq_cons strategy.state strategy.isNormalized
      (strategy.pointMeasurementA u) (strategy.pointMeasurementB u))

private lemma axisParallel_roleRegister_sample_eq_average
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (strategy : ProjStrat params ιA ιB) (s : AxisParallelTestSample params) :
    qBipartiteConsDefect (strategy.roleRegisterSymmStrategy.state)
        (axisParallelPointAnswerFamily strategy.roleRegisterSymmStrategy s)
        (axisParallelLineAnswerFamily strategy.roleRegisterSymmStrategy s) =
      (qBipartiteConsDefect strategy.state
          (axisParallelPointAnswerFamilyA strategy s)
          (axisParallelLineAnswerFamilyB strategy s) +
        qBipartiteConsDefect strategy.state
          (axisParallelLineAnswerFamilyA strategy s)
          (axisParallelPointAnswerFamilyB strategy s)) / 2 := by
  let ℓ : AxisParallelLine params := { base := s.1, direction := s.2 }
  have h := qBipartiteConsDefect_roleRegister_point_postprocessedLine_eq_average
    strategy.state strategy.isNormalized
    (strategy.pointMeasurementA s.1) (strategy.pointMeasurementB s.1)
    (strategy.axisParallelMeasurementA ℓ) (strategy.axisParallelMeasurementB ℓ)
    (fun p : AxisLinePolynomial params => p zeroCoord)
  simpa [SymStrat.axisParallelFailureProbability, roleRegisterSymmStrategy,
    axisParallelPointAnswerFamily, axisParallelLineAnswerFamily,
    roleRegisterPointMeasurement, roleRegisterAxisParallelMeasurement,
    axisParallelPointAnswerFamilyA, axisParallelPointAnswerFamilyB,
    axisParallelLineAnswerFamilyA, axisParallelLineAnswerFamilyB, ℓ,
    ProjMeas.postprocess_toSubMeas, add_comm] using h

/-- The axis-parallel branch of the heterogeneous role-register symmetrization
is exactly the axis-parallel role average of the original two-space strategy. -/
theorem roleRegisterSymmStrategy_axisParallel_eq_roleAverage
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB) :
    (strategy.roleRegisterSymmStrategy).axisParallelFailureProbability =
      strategy.axisParallelRoleAverage := by
  haveI : Nonempty ιA := strategy.isNormalized.nonempty.map Prod.fst
  haveI : Nonempty ιB := strategy.isNormalized.nonempty.map Prod.snd
  let axParDist := uniformDistribution (AxisParallelTestSample params)
  let symmErr : AxisParallelTestSample params → Error := fun s =>
    qBipartiteConsDefect (strategy.roleRegisterSymmStrategy.state)
      (axisParallelPointAnswerFamily strategy.roleRegisterSymmStrategy s)
      (axisParallelLineAnswerFamily strategy.roleRegisterSymmStrategy s)
  let pointLeftLineRight : AxisParallelTestSample params → Error := fun s =>
    qBipartiteConsDefect strategy.state
      (axisParallelPointAnswerFamilyA strategy s)
      (axisParallelLineAnswerFamilyB strategy s)
  let lineLeftPointRight : AxisParallelTestSample params → Error := fun s =>
    qBipartiteConsDefect strategy.state
      (axisParallelLineAnswerFamilyA strategy s)
      (axisParallelPointAnswerFamilyB strategy s)
  have hcongr :
      avgOver axParDist symmErr =
        avgOver axParDist (fun s => (pointLeftLineRight s + lineLeftPointRight s) / 2) := by
    apply avgOver_congr
    intro s
    exact axisParallel_roleRegister_sample_eq_average strategy s
  calc
    (strategy.roleRegisterSymmStrategy).axisParallelFailureProbability
      = avgOver axParDist symmErr := by
          rfl
    _ = avgOver axParDist (fun s => (pointLeftLineRight s + lineLeftPointRight s) / 2) :=
          hcongr
    _ = (avgOver axParDist pointLeftLineRight +
          avgOver axParDist lineLeftPointRight) / 2 := by
          rw [show (fun s => (pointLeftLineRight s + lineLeftPointRight s) / 2) =
              fun s => (1 / 2 : Error) * (pointLeftLineRight s + lineLeftPointRight s) by
            funext s
            ring]
          rw [avgOver_const_mul, avgOver_add]
          ring
    _ = strategy.axisParallelRoleAverage := by
          unfold ProjStrat.axisParallelRoleAverage
          unfold ProjStrat.axisParallelPointLeftLineRightFailureProbability
          unfold ProjStrat.axisParallelLineLeftPointRightFailureProbability
          change (avgOver axParDist pointLeftLineRight +
              avgOver axParDist lineLeftPointRight) / 2 =
            (avgOver axParDist lineLeftPointRight +
              avgOver axParDist pointLeftLineRight) / 2
          ring

private lemma diagonal_roleRegister_sample_eq_average
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA] [Nonempty ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB] [Nonempty ιB]
    (strategy : ProjStrat params ιA ιB)
    (j : Fin params.m) (s : RestrictedDiagonalSample params j) :
    qBipartiteConsDefect (strategy.roleRegisterSymmStrategy.state)
        (diagonalPointAnswerFamily strategy.roleRegisterSymmStrategy j s)
        (diagonalLineAnswerFamily strategy.roleRegisterSymmStrategy j s) =
      (qBipartiteConsDefect strategy.state
          (diagonalPointAnswerFamilyA strategy j s)
          (diagonalLineAnswerFamilyB strategy j s) +
        qBipartiteConsDefect strategy.state
          (diagonalLineAnswerFamilyA strategy j s)
          (diagonalPointAnswerFamilyB strategy j s)) / 2 := by
  let v := extendRestrictedDirection j s.2
  let ℓ : DiagonalLine params := { base := s.1, direction := v }
  have h := qBipartiteConsDefect_roleRegister_point_postprocessedLine_eq_average
    strategy.state strategy.isNormalized
    (strategy.pointMeasurementA s.1) (strategy.pointMeasurementB s.1)
    (strategy.diagonalMeasurementA ℓ) (strategy.diagonalMeasurementB ℓ)
    (fun p : DiagonalLinePolynomial params => p zeroCoord)
  simpa [roleRegisterSymmStrategy, diagonalPointAnswerFamily, diagonalLineAnswerFamily,
    roleRegisterPointMeasurement, roleRegisterDiagonalMeasurement,
    diagonalPointAnswerFamilyA, diagonalPointAnswerFamilyB,
    diagonalLineAnswerFamilyA, diagonalLineAnswerFamilyB, v, ℓ,
    ProjMeas.postprocess_toSubMeas, add_comm] using h

/-- The diagonal branch of the heterogeneous role-register symmetrization is
exactly the diagonal role average of the original two-space strategy. -/
theorem roleRegisterSymmStrategy_diagonal_eq_roleAverage
    {params : Parameters} [FieldModel params.q]
    {ιA : Type*} [Fintype ιA] [DecidableEq ιA]
    {ιB : Type*} [Fintype ιB] [DecidableEq ιB]
    (strategy : ProjStrat params ιA ιB) :
    (strategy.roleRegisterSymmStrategy).diagonalFailureProbability =
      strategy.diagonalRoleAverage := by
  haveI : Nonempty ιA := strategy.isNormalized.nonempty.map Prod.fst
  haveI : Nonempty ιB := strategy.isNormalized.nonempty.map Prod.snd
  let symmErr := fun j : Fin params.m => fun s : RestrictedDiagonalSample params j =>
    qBipartiteConsDefect (strategy.roleRegisterSymmStrategy.state)
      (diagonalPointAnswerFamily strategy.roleRegisterSymmStrategy j s)
      (diagonalLineAnswerFamily strategy.roleRegisterSymmStrategy j s)
  let pointLeftLineRight := fun j : Fin params.m => fun s : RestrictedDiagonalSample params j =>
    qBipartiteConsDefect strategy.state
      (diagonalPointAnswerFamilyA strategy j s)
      (diagonalLineAnswerFamilyB strategy j s)
  let lineLeftPointRight := fun j : Fin params.m => fun s : RestrictedDiagonalSample params j =>
    qBipartiteConsDefect strategy.state
      (diagonalLineAnswerFamilyA strategy j s)
      (diagonalPointAnswerFamilyB strategy j s)
  calc
    (strategy.roleRegisterSymmStrategy).diagonalFailureProbability
      = (1 / (params.m : Error)) *
          ∑ j : Fin params.m,
            avgOver (uniformDistribution (RestrictedDiagonalSample params j)) (symmErr j) := by
          rfl
    _ = (1 / (params.m : Error)) *
          ∑ j : Fin params.m,
            avgOver (uniformDistribution (RestrictedDiagonalSample params j))
              (fun s => (pointLeftLineRight j s + lineLeftPointRight j s) / 2) := by
          refine congrArg (fun t => (1 / (params.m : Error)) * t) ?_
          refine Finset.sum_congr rfl ?_
          intro j _
          apply avgOver_congr
          intro s
          exact diagonal_roleRegister_sample_eq_average strategy j s
    _ = (1 / (params.m : Error)) *
          ∑ j : Fin params.m,
            (avgOver (uniformDistribution (RestrictedDiagonalSample params j))
                (pointLeftLineRight j) +
              avgOver (uniformDistribution (RestrictedDiagonalSample params j))
                (lineLeftPointRight j)) / 2 := by
          refine congrArg (fun t => (1 / (params.m : Error)) * t) ?_
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [show (fun s => (pointLeftLineRight j s + lineLeftPointRight j s) / 2) =
              fun s => (1 / 2 : Error) * (pointLeftLineRight j s + lineLeftPointRight j s) by
            funext s
            ring]
          rw [avgOver_const_mul, avgOver_add]
          ring
    _ = strategy.diagonalRoleAverage := by
          unfold ProjStrat.diagonalRoleAverage
          unfold ProjStrat.diagonalPointLeftLineRightFailureProbability
          unfold ProjStrat.diagonalLineLeftPointRightFailureProbability
          change (1 / (params.m : Error)) *
              ∑ j : Fin params.m,
                (avgOver (uniformDistribution (RestrictedDiagonalSample params j))
                    (pointLeftLineRight j) +
                  avgOver (uniformDistribution (RestrictedDiagonalSample params j))
                    (lineLeftPointRight j)) / 2 =
            ((1 / (params.m : Error)) *
                ∑ j : Fin params.m,
                  avgOver (uniformDistribution (RestrictedDiagonalSample params j))
                    (lineLeftPointRight j) +
              (1 / (params.m : Error)) *
                ∑ j : Fin params.m,
                  avgOver (uniformDistribution (RestrictedDiagonalSample params j))
                    (pointLeftLineRight j)) / 2
          calc
            (1 / (params.m : Error)) *
                ∑ j : Fin params.m,
                  (avgOver (uniformDistribution (RestrictedDiagonalSample params j))
                      (pointLeftLineRight j) +
                    avgOver (uniformDistribution (RestrictedDiagonalSample params j))
                      (lineLeftPointRight j)) / 2
              = (1 / (params.m : Error)) *
                  ((∑ j : Fin params.m,
                      avgOver (uniformDistribution (RestrictedDiagonalSample params j))
                        (pointLeftLineRight j) +
                    ∑ j : Fin params.m,
                      avgOver (uniformDistribution (RestrictedDiagonalSample params j))
                        (lineLeftPointRight j)) / 2) := by
                  congr 1
                  rw [show
                    ∑ j : Fin params.m,
                      (avgOver (uniformDistribution (RestrictedDiagonalSample params j))
                          (pointLeftLineRight j) +
                        avgOver (uniformDistribution (RestrictedDiagonalSample params j))
                          (lineLeftPointRight j)) / 2 =
                    (∑ j : Fin params.m,
                      (avgOver (uniformDistribution (RestrictedDiagonalSample params j))
                          (pointLeftLineRight j) +
                        avgOver (uniformDistribution (RestrictedDiagonalSample params j))
                          (lineLeftPointRight j))) / 2 by
                    simp [div_eq_mul_inv, Finset.sum_mul]]
                  rw [← Finset.sum_add_distrib]
            _ = ((1 / (params.m : Error)) *
                    ∑ j : Fin params.m,
                      avgOver (uniformDistribution (RestrictedDiagonalSample params j))
                        (lineLeftPointRight j) +
                  (1 / (params.m : Error)) *
                    ∑ j : Fin params.m,
                      avgOver (uniformDistribution (RestrictedDiagonalSample params j))
                        (pointLeftLineRight j)) / 2 := by
                  ring


end ProjStrat

end MIPStarRE.LDT
