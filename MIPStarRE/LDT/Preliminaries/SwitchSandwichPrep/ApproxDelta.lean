import MIPStarRE.LDT.Preliminaries.SwitchSandwichPrep.InnerProduct

/-!
# Switch-sandwich preparation: `approx_δ` overlap gaps

Pointwise overlap-gap estimates used to bound the switch-sandwich approximation
error under `approx_δ` families.

## References

- arXiv:2009.12982, Section 7 (switch-sandwich preliminaries, `prop:switch-sandwich`).
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

lemma question_overlap_gap_left
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B : SubMeas Outcome ι) :
    |(∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)) -
        ∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)| ≤
      Real.sqrt (qSDD ψ A B) := by
  let diagA : Error := ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
  have hdiagA_le_one : diagA ≤ 1 := by
    simpa [diagA] using subMeas_diagMass_le_one ψ hψ A
  have haux :
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a)| ≤
        Real.sqrt (qSDD ψ A B) * Real.sqrt diagA := by
    calc
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a)|
        ≤ ∑ a : Outcome, |ev ψ ((A.outcome a - B.outcome a) * A.outcome a)| := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Outcome,
            Real.sqrt (ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))) *
              Real.sqrt (ev ψ (A.outcome a * A.outcome a)) := by
            refine Finset.sum_le_sum ?_
            intro a _
            have hherm : (A.outcome a - B.outcome a)ᴴ = A.outcome a - B.outcome a := by
              simp [SubMeas.outcome_hermitian]
            simpa [hherm, SubMeas.outcome_hermitian] using
              ev_abs_mul_le_sqrt ψ (A.outcome a - B.outcome a) (A.outcome a)
      _ ≤ Real.sqrt
            (∑ a : Outcome,
              ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))) *
          Real.sqrt diagA := by
            simpa [diagA] using
              Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
                (f := fun a =>
                  ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a)))
                (g := fun a => ev ψ (A.outcome a * A.outcome a))
                (fun a => ev_adjoint_self_nonneg ψ _)
                (fun a => by
                  simpa [SubMeas.outcome_hermitian] using
                    ev_adjoint_self_nonneg ψ (A.outcome a))
      _ = Real.sqrt (qSDD ψ A B) * Real.sqrt diagA := by
            simp [qSDD, qSDDCore, diagA]
  have hsqrtA : Real.sqrt diagA ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiagA_le_one
  have haux' :
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a)| ≤
        Real.sqrt (qSDD ψ A B) := by
    calc
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a)|
        ≤ Real.sqrt (qSDD ψ A B) * Real.sqrt diagA := haux
      _ ≤ Real.sqrt (qSDD ψ A B) * 1 := by
            exact mul_le_mul_of_nonneg_left hsqrtA (Real.sqrt_nonneg _)
      _ = Real.sqrt (qSDD ψ A B) := by ring
  convert haux' using 1
  refine congrArg abs ?_
  calc
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a) -
        ∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)
      = ∑ a : Outcome,
          (ev ψ (A.outcome a * A.outcome a) -
            ev ψ (A.outcome a * B.outcome a)) := by
              rw [← Finset.sum_sub_distrib]
    _ = ∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * A.outcome a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          have hcomm :
              ev ψ (B.outcome a * A.outcome a) = ev ψ (A.outcome a * B.outcome a) := by
            exact ev_mul_comm_of_psd ψ _ _ (B.outcome_pos a) (A.outcome_pos a)
          calc
            ev ψ (A.outcome a * A.outcome a) - ev ψ (A.outcome a * B.outcome a)
              = ev ψ (A.outcome a * A.outcome a) - ev ψ (B.outcome a * A.outcome a) := by
                  rw [hcomm]
            _ = ev ψ (A.outcome a * A.outcome a - B.outcome a * A.outcome a) := by
                  rw [(ev_sub ψ (A.outcome a * A.outcome a) (B.outcome a * A.outcome a)).symm]
            _ = ev ψ ((A.outcome a - B.outcome a) * A.outcome a) := by
                  simp [sub_mul]

lemma question_overlap_gap_right
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B : SubMeas Outcome ι) :
    |(∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)) -
        ∑ a : Outcome, ev ψ (B.outcome a * B.outcome a)| ≤
      Real.sqrt (qSDD ψ A B) := by
  let diagB : Error := ∑ a : Outcome, ev ψ (B.outcome a * B.outcome a)
  have hdiagB_le_one : diagB ≤ 1 := by
    simpa [diagB] using subMeas_diagMass_le_one ψ hψ B
  have haux :
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a)| ≤
        Real.sqrt (qSDD ψ A B) * Real.sqrt diagB := by
    calc
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a)|
        ≤ ∑ a : Outcome, |ev ψ ((A.outcome a - B.outcome a) * B.outcome a)| := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a : Outcome,
            Real.sqrt (ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))) *
              Real.sqrt (ev ψ (B.outcome a * B.outcome a)) := by
            refine Finset.sum_le_sum ?_
            intro a _
            have hherm : (A.outcome a - B.outcome a)ᴴ = A.outcome a - B.outcome a := by
              simp [SubMeas.outcome_hermitian]
            simpa [hherm, SubMeas.outcome_hermitian] using
              ev_abs_mul_le_sqrt ψ (A.outcome a - B.outcome a) (B.outcome a)
      _ ≤ Real.sqrt
            (∑ a : Outcome,
              ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a))) *
          Real.sqrt diagB := by
            simpa [diagB] using
              Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
                (f := fun a =>
                  ev ψ ((A.outcome a - B.outcome a)ᴴ * (A.outcome a - B.outcome a)))
                (g := fun a => ev ψ (B.outcome a * B.outcome a))
                (fun a => ev_adjoint_self_nonneg ψ _)
                (fun a => by
                  simpa [SubMeas.outcome_hermitian] using
                    ev_adjoint_self_nonneg ψ (B.outcome a))
      _ = Real.sqrt (qSDD ψ A B) * Real.sqrt diagB := by
            simp [qSDD, qSDDCore, diagB]
  have hsqrtB : Real.sqrt diagB ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiagB_le_one
  have haux' :
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a)| ≤
        Real.sqrt (qSDD ψ A B) := by
    calc
      |∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a)|
        ≤ Real.sqrt (qSDD ψ A B) * Real.sqrt diagB := haux
      _ ≤ Real.sqrt (qSDD ψ A B) * 1 := by
            exact mul_le_mul_of_nonneg_left hsqrtB (Real.sqrt_nonneg _)
      _ = Real.sqrt (qSDD ψ A B) := by ring
  convert haux' using 1
  refine congrArg abs ?_
  calc
    ∑ a : Outcome, ev ψ (A.outcome a * B.outcome a) -
        ∑ a : Outcome, ev ψ (B.outcome a * B.outcome a)
      = ∑ a : Outcome,
          (ev ψ (A.outcome a * B.outcome a) -
            ev ψ (B.outcome a * B.outcome a)) := by
              rw [← Finset.sum_sub_distrib]
    _ = ∑ a : Outcome, ev ψ ((A.outcome a - B.outcome a) * B.outcome a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          have hcomm :
              ev ψ (A.outcome a * B.outcome a) = ev ψ (B.outcome a * A.outcome a) := by
            exact ev_mul_comm_of_psd ψ _ _ (A.outcome_pos a) (B.outcome_pos a)
          calc
            ev ψ (A.outcome a * B.outcome a) - ev ψ (B.outcome a * B.outcome a)
              = ev ψ (A.outcome a * B.outcome a - B.outcome a * B.outcome a) := by
                  rw [(ev_sub ψ (A.outcome a * B.outcome a) (B.outcome a * B.outcome a)).symm]
            _ = ev ψ ((A.outcome a - B.outcome a) * B.outcome a) := by
                  simp [sub_mul]

/-- `prop:easy-approx-from-approx-delta`. -/
theorem easyApproxFromApproxDelta_twoFamily {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : IdxSubMeas Question Outcome ι) (δ : Error) :
    SDDRel ψ 𝒟 A B δ →
      |avgOver 𝒟 (fun q => ∑ a : Outcome, ev ψ ((A q).outcome a * (A q).outcome a)) -
          avgOver 𝒟 (fun q => ∑ a : Outcome, ev ψ ((A q).outcome a * (B q).outcome a))|
          ≤ Real.sqrt δ ∧
      |avgOver 𝒟 (fun q => ∑ a : Outcome, ev ψ ((A q).outcome a * (B q).outcome a)) -
          avgOver 𝒟 (fun q => ∑ a : Outcome, ev ψ ((B q).outcome a * (B q).outcome a))|
          ≤ Real.sqrt δ := by
  intro ⟨hδ⟩
  let diagA : Question → Error :=
    fun q => ∑ a : Outcome, ev ψ ((A q).outcome a * (A q).outcome a)
  let diagB : Question → Error :=
    fun q => ∑ a : Outcome, ev ψ ((B q).outcome a * (B q).outcome a)
  let overlap : Question → Error :=
    fun q => ∑ a : Outcome, ev ψ ((A q).outcome a * (B q).outcome a)
  let sdd : Question → Error := fun q => qSDD ψ (A q) (B q)
  have hleft_pointwise : ∀ q, |diagA q - overlap q| ≤ Real.sqrt (sdd q) := by
    intro q
    simpa [diagA, overlap, sdd] using
      question_overlap_gap_left ψ hψ (A q) (B q)
  have hright_pointwise : ∀ q, |overlap q - diagB q| ≤ Real.sqrt (sdd q) := by
    intro q
    simpa [diagB, overlap, sdd] using
      question_overlap_gap_right ψ hψ (A q) (B q)
  constructor
  · calc
      |avgOver 𝒟 diagA - avgOver 𝒟 overlap|
        = |avgOver 𝒟 (fun q => diagA q - overlap q)| := by
            simp [avgOver, Finset.sum_sub_distrib, mul_sub]
      _ ≤ Real.sqrt (avgOver 𝒟 sdd) := by
            exact
              avgOver_abs_le_sqrt_of_pointwise 𝒟
                (fun q => diagA q - overlap q)
                sdd
                hleft_pointwise
                (fun q => qSDD_nonneg ψ (A q) (B q))
                h𝒟
      _ ≤ Real.sqrt δ := by
            exact Real.sqrt_le_sqrt hδ
  · calc
      |avgOver 𝒟 overlap - avgOver 𝒟 diagB|
        = |avgOver 𝒟 (fun q => overlap q - diagB q)| := by
            simp [avgOver, Finset.sum_sub_distrib, mul_sub]
      _ ≤ Real.sqrt (avgOver 𝒟 sdd) := by
            exact
              avgOver_abs_le_sqrt_of_pointwise 𝒟
                (fun q => overlap q - diagB q)
                sdd
                hright_pointwise
                (fun q => qSDD_nonneg ψ (A q) (B q))
                h𝒟
      _ ≤ Real.sqrt δ := by
            exact Real.sqrt_le_sqrt hδ

end MIPStarRE.LDT.Preliminaries
