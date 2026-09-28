import MIPStarRE.LDT.MakingMeasurementsProjective.NaimarkFull

/-!
# Simultaneous dilation of a submeasurement family

The one-measurement Naimark construction uses the same auxiliary outcome
space for every question. Applying it pointwise therefore gives one
ambient space for an entire family and preserves every original effect
under compression to the distinguished auxiliary basis vector.

## References

- `blueprint/src/low_degree_simplified.tex`,
  `lem:simultaneous-dilation-compression`.
- `references/ldt-paper/orthonormalization.tex`, `thm:naimark`.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped MatrixOrder

universe u v

/-- A family of submeasurements has projective dilations on one common
auxiliary space, with exact compression for every outcome. -/
theorem simultaneous_submeasurement_dilation
    {Question : Type*} {Outcome : Type v} {ι : Type u}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι]
    (H : IdxSubMeas Question Outcome ι) :
    ∃ P : IdxProjSubMeas Question Outcome (ι × Option Outcome),
      ∀ (x : Question) (g : Outcome) (i j : ι),
        ((P x).toSubMeas.outcome g) (i, none) (j, none) =
          ((H x).outcome g) i j := by
  classical
  let data : Question → OneMeasNaimarkData Outcome ι :=
    questionwiseOneMeasNaimarkData H
  let P : IdxProjSubMeas Question Outcome (ι × Option Outcome) :=
    fun x => (data x).toProjSubMeas
  refine ⟨P, ?_⟩
  intro x g i j
  have hsource := questionwiseOneMeasNaimarkData_source_effect H x
  have hcompression := (data x).compression_none_none g i j
  simpa [P, data, OneMeasNaimarkData.toProjSubMeas,
    OneMeasNaimarkData.toProjSubMeasOption,
    restrictSomeProjSubMeas, hsource] using hcompression

/-- The common-ancilla projective family from the questionwise Naimark
construction. -/
noncomputable def simultaneousDilationFamily
    {Question : Type*} {Outcome : Type v} {ι : Type u}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι]
    (H : IdxSubMeas Question Outcome ι) :
    IdxProjSubMeas Question Outcome (ι × Option Outcome) :=
  fun x => (questionwiseOneMeasNaimarkData H x).toProjSubMeas

/-- Each dilated outcome compresses to its source effect. -/
theorem simultaneousDilationFamily_outcome_compression
    {Question : Type*} {Outcome : Type v} {ι : Type u}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι]
    (H : IdxSubMeas Question Outcome ι)
    (x : Question) (g : Outcome) (i j : ι) :
    ((simultaneousDilationFamily H x).toSubMeas.outcome g)
        (i, none) (j, none) = ((H x).outcome g) i j := by
  have h := (questionwiseOneMeasNaimarkData H x).compression_none_none g i j
  simpa [simultaneousDilationFamily,
    OneMeasNaimarkData.toProjSubMeas,
    OneMeasNaimarkData.toProjSubMeasOption,
    restrictSomeProjSubMeas,
    questionwiseOneMeasNaimarkData_source_effect H x] using h

/-- The total operator of every dilated submeasurement compresses to
the total operator of the original submeasurement. -/
theorem simultaneousDilationFamily_total_compression
    {Question : Type*} {Outcome : Type v} {ι : Type u}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι]
    (H : IdxSubMeas Question Outcome ι)
    (x : Question) (i j : ι) :
    (simultaneousDilationFamily H x).toSubMeas.total (i, none) (j, none) =
      (H x).total i j := by
  classical
  calc
    (simultaneousDilationFamily H x).toSubMeas.total (i, none) (j, none) =
        ∑ g, ((simultaneousDilationFamily H x).toSubMeas.outcome g)
          (i, none) (j, none) := by
      simpa only [Matrix.sum_apply] using congrArg
        (fun M : MIPStarRE.Quantum.Op (ι × Option Outcome) => M (i, none) (j, none))
        (simultaneousDilationFamily H x).toSubMeas.sum_eq_total.symm
    _ = ∑ g, ((H x).outcome g) i j := by
      apply Finset.sum_congr rfl
      intro g _
      exact simultaneousDilationFamily_outcome_compression H x g i j
    _ = (H x).total i j := by
      simpa only [Matrix.sum_apply] using congrArg
        (fun M : MIPStarRE.Quantum.Op ι => M i j) (H x).sum_eq_total

/-- The original finite register, packaged for the Naimark state extension. -/
def simultaneousDilationBaseSpace (ι : Type u)
    [Fintype ι] [DecidableEq ι] [Nonempty ι] : FiniteHilbertSpace.{u} :=
  { carrier := ι, instFintype := inferInstance,
    instDecidableEq := inferInstance, instNonempty := inferInstance }

/-- The bipartite state obtained by attaching the distinguished
auxiliary basis state to both registers. -/
noncomputable def simultaneousDilationState
    {Outcome : Type v} {ι : Type u}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) :
    QuantumState ((ι × Option Outcome) × (ι × Option Outcome)) :=
  let HA : FiniteHilbertSpace.{u} := simultaneousDilationBaseSpace ι
  naimarkProductExtensionState HA HA
    (oneNaimarkAuxHilbertSpace Outcome)
    (oneNaimarkAuxHilbertSpace Outcome)
    ψ (QuantumState.tensor
      (oneNaimarkAuxState Outcome) (oneNaimarkAuxState Outcome))

/-- Simultaneous dilation preserves every two-sided correlation of
the family, including those used for strong self-consistency. -/
theorem simultaneousDilationFamily_correlation
    {Question : Type*} {Outcome : Type v} {ι : Type u}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : IdxSubMeas Question Outcome ι)
    (ψ : QuantumState (ι × ι))
    (x y : Question) (g h : Outcome) :
    ev ψ (opTensor ((H x).outcome g) ((H y).outcome h)) =
      ev (simultaneousDilationState (Outcome := Outcome) ψ)
        (opTensor
          ((simultaneousDilationFamily H x).toSubMeas.outcome g)
          ((simultaneousDilationFamily H y).toSubMeas.outcome h)) := by
  let HA : FiniteHilbertSpace.{u} := simultaneousDilationBaseSpace ι
  let leftData := questionwiseOneMeasNaimarkData H x
  let rightData := questionwiseOneMeasNaimarkData H y
  have hleft := questionwiseOneMeasNaimarkData_source_effect H x
  have hright := questionwiseOneMeasNaimarkData_source_effect H y
  have hcorr := OneMeasNaimarkData.twoSidedCorrelationPreservation
    HA HA ψ leftData rightData g h
  convert hcorr using 1 <;>
    simp [simultaneousDilationState, simultaneousDilationFamily,
      HA, leftData, rightData, hleft, hright] <;> rfl

/-- The enlarged state remains normalized. -/
theorem simultaneousDilationState_isNormalized
    {Outcome : Type v} {ι : Type u}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized) :
    (simultaneousDilationState (Outcome := Outcome) ψ).IsNormalized := by
  let HA : FiniteHilbertSpace.{u} := simultaneousDilationBaseSpace ι
  have haux : (QuantumState.tensor
      (oneNaimarkAuxState Outcome) (oneNaimarkAuxState Outcome)).IsNormalized :=
    QuantumState.tensor_isNormalized
      (oneNaimarkAuxState_isNormalized Outcome)
      (oneNaimarkAuxState_isNormalized Outcome)
  exact naimarkProductExtensionState_isNormalized HA HA
    (oneNaimarkAuxHilbertSpace Outcome)
    (oneNaimarkAuxHilbertSpace Outcome) hψ haux

/-- The product-extension trace only sees the distinguished auxiliary
compression block on each local register. -/
theorem productExtension_correlation_of_compression
    {Outcome : Type v}
    [Fintype Outcome] [DecidableEq Outcome]
    (HA : FiniteHilbertSpace.{u})
    (ψ : QuantumState (HA.carrier × HA.carrier))
    (A B : MIPStarRE.Quantum.Op HA.carrier)
    (X Y : MIPStarRE.Quantum.Op (HA.carrier × Option Outcome))
    (hX : ∀ i j : HA.carrier, X (i, none) (j, none) = A i j)
    (hY : ∀ i j : HA.carrier, Y (i, none) (j, none) = B i j) :
    ev ψ (opTensor A B) =
      ev (naimarkProductExtensionState HA HA
        (oneNaimarkAuxHilbertSpace Outcome)
        (oneNaimarkAuxHilbertSpace Outcome) ψ
        (QuantumState.tensor
          (oneNaimarkAuxState Outcome) (oneNaimarkAuxState Outcome)))
        (opTensor X Y) := by
  let c : ℂ := Fintype.card (Option Outcome)
  let S : ℂ :=
    ∑ x : HA.carrier, ∑ x₁ : HA.carrier,
      ∑ x₂ : HA.carrier, ∑ x₃ : HA.carrier,
      A x₂ x * B x₃ x₁ * ψ.density (x, x₁) (x₂, x₃)
  unfold ev
  congr 1
  unfold MIPStarRE.Quantum.normalizedTrace
  simp [naimarkProductExtensionState,
    naimarkProductExtensionDensity, QuantumState.tensor,
    oneNaimarkAuxState, oneNaimarkAuxPureState,
    PureState.density, pureDensity, PureState.basis,
    Matrix.mul_apply, Matrix.trace, opTensor, Matrix.kronecker,
    Matrix.vecMulVec]
  simp [Fintype.sum_prod_type, mul_assoc, mul_left_comm, mul_comm]
  field_simp
  change S * c ^ (2 : ℕ) =
    ∑ x : HA.carrier, ∑ x₁ : HA.carrier,
      ∑ x₂ : HA.carrier, ∑ x₃ : HA.carrier,
      c ^ (2 : ℕ) * X (x₂, none) (x, none) *
        Y (x₃, none) (x₁, none) * ψ.density (x, x₁) (x₂, x₃)
  rw [show
      (∑ x : HA.carrier, ∑ x₁ : HA.carrier,
        ∑ x₂ : HA.carrier, ∑ x₃ : HA.carrier,
        c ^ (2 : ℕ) * X (x₂, none) (x, none) *
          Y (x₃, none) (x₁, none) * ψ.density (x, x₁) (x₂, x₃)) =
        c ^ (2 : ℕ) * S by
      calc
        (∑ x : HA.carrier, ∑ x₁ : HA.carrier,
          ∑ x₂ : HA.carrier, ∑ x₃ : HA.carrier,
          c ^ (2 : ℕ) * X (x₂, none) (x, none) *
            Y (x₃, none) (x₁, none) * ψ.density (x, x₁) (x₂, x₃)) =
          ∑ x : HA.carrier, ∑ x₁ : HA.carrier,
            ∑ x₂ : HA.carrier, ∑ x₃ : HA.carrier,
            c ^ (2 : ℕ) * (A x₂ x * B x₃ x₁ * ψ.density (x, x₁) (x₂, x₃)) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          refine Finset.sum_congr rfl ?_
          intro x₁ _
          refine Finset.sum_congr rfl ?_
          intro x₂ _
          refine Finset.sum_congr rfl ?_
          intro x₃ _
          rw [hX x₂ x, hY x₃ x₁]
          ring
        _ = c ^ (2 : ℕ) * S := by
          simp [S, mul_assoc, Finset.mul_sum]]
  ring_nf

/-- Mixed correlations with an unchanged original operator are
preserved by simultaneous dilation. -/
theorem simultaneousDilationFamily_original_left_correlation
    {Question : Type*} {Outcome : Type v} {ι : Type u}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : IdxSubMeas Question Outcome ι)
    (ψ : QuantumState (ι × ι))
    (R : MIPStarRE.Quantum.Op ι)
    (y : Question) (g : Outcome) :
    ev ψ (opTensor R ((H y).outcome g)) =
      ev (simultaneousDilationState (Outcome := Outcome) ψ)
        (opTensor
          (opTensor R (1 : MIPStarRE.Quantum.Op (Option Outcome)))
          ((simultaneousDilationFamily H y).toSubMeas.outcome g)) := by
  let HA : FiniteHilbertSpace.{u} := simultaneousDilationBaseSpace ι
  let P := (simultaneousDilationFamily H y).toSubMeas.outcome g
  have hX : ∀ i j : ι,
      (opTensor R (1 : MIPStarRE.Quantum.Op (Option Outcome)))
        (i, none) (j, none) = R i j := by
    intro i j
    simp [opTensor]
  have hY : ∀ i j : ι, P (i, none) (j, none) = ((H y).outcome g) i j := by
    intro i j
    have h := (questionwiseOneMeasNaimarkData H y).compression_none_none g i j
    simpa [P, simultaneousDilationFamily,
      OneMeasNaimarkData.toProjSubMeas,
      OneMeasNaimarkData.toProjSubMeasOption,
      restrictSomeProjSubMeas,
      questionwiseOneMeasNaimarkData_source_effect H y] using h
  have h := productExtension_correlation_of_compression
    (Outcome := Outcome) HA ψ R ((H y).outcome g)
    (opTensor R (1 : MIPStarRE.Quantum.Op (Option Outcome))) P hX hY
  convert h using 1 <;>
    simp [simultaneousDilationState, HA, P] <;> rfl

/-- The corresponding mixed correlation with the original operator on
the right register. -/
theorem simultaneousDilationFamily_original_right_correlation
    {Question : Type*} {Outcome : Type v} {ι : Type u}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (H : IdxSubMeas Question Outcome ι)
    (ψ : QuantumState (ι × ι))
    (R : MIPStarRE.Quantum.Op ι)
    (x : Question) (g : Outcome) :
    ev ψ (opTensor ((H x).outcome g) R) =
      ev (simultaneousDilationState (Outcome := Outcome) ψ)
        (opTensor
          ((simultaneousDilationFamily H x).toSubMeas.outcome g)
          (opTensor R (1 : MIPStarRE.Quantum.Op (Option Outcome)))) := by
  let HA : FiniteHilbertSpace.{u} := simultaneousDilationBaseSpace ι
  let P := (simultaneousDilationFamily H x).toSubMeas.outcome g
  have hX : ∀ i j : ι, P (i, none) (j, none) = ((H x).outcome g) i j := by
    intro i j
    have h := (questionwiseOneMeasNaimarkData H x).compression_none_none g i j
    simpa [P, simultaneousDilationFamily,
      OneMeasNaimarkData.toProjSubMeas,
      OneMeasNaimarkData.toProjSubMeasOption,
      restrictSomeProjSubMeas,
      questionwiseOneMeasNaimarkData_source_effect H x] using h
  have hY : ∀ i j : ι,
      (opTensor R (1 : MIPStarRE.Quantum.Op (Option Outcome)))
        (i, none) (j, none) = R i j := by
    intro i j
    simp [opTensor]
  have h := productExtension_correlation_of_compression
    (Outcome := Outcome) HA ψ ((H x).outcome g) R P
    (opTensor R (1 : MIPStarRE.Quantum.Op (Option Outcome))) hX hY
  convert h using 1 <;>
    simp [simultaneousDilationState, HA, P] <;> rfl

end MIPStarRE.LDT.SelfImprovement
