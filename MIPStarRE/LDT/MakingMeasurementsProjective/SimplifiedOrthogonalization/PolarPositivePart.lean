import MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization.SelectedProjectors

/-!
# Positive part of the selected polar matrix

The selected effects sum to a positive contraction `S`.  Its positive square
root is the operator `|X|` in the simplified orthogonalization proof.

## References

- `blueprint/src/chapter/low_degree_simplified.tex`, proof of
  `lem:state-dependent-orthogonalization`, the identity `|X| = S^(1/2)`.
- `references/ldt-paper/orthonormalization.tex`, Section 5.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization

open MIPStarRE.LDT

/-- The total selected effect `S = Σₐ Qₐ Mₐ`. -/
noncomputable def selectedEffectSum {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (L : Finset (Outcome × ι)) :
    MIPStarRE.Quantum.Op ι :=
  ∑ a, selectedProjector M L a * M.outcome a

/-- The positive square root of the selected effect sum. -/
noncomputable def selectedPolarPositivePart {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (L : Finset (Outcome × ι)) :
    MIPStarRE.Quantum.Op ι :=
  CFC.sqrt (selectedEffectSum M L)

/-- The polar positive part is a positive contraction with square `S`. -/
theorem selectedPolarPositivePart_properties {Outcome ι : Type*}
    [Fintype Outcome] [DecidableEq Outcome] [Fintype ι] [DecidableEq ι]
    (M : Measurement Outcome ι) (L : Finset (Outcome × ι)) :
    0 ≤ selectedPolarPositivePart M L ∧
      selectedPolarPositivePart M L ≤ 1 ∧
      selectedPolarPositivePart M L * selectedPolarPositivePart M L =
        selectedEffectSum M L := by
  have hS := selectedEffectSum_nonneg_le_one M L
  change 0 ≤ CFC.sqrt (selectedEffectSum M L) ∧
    CFC.sqrt (selectedEffectSum M L) ≤ 1 ∧
    CFC.sqrt (selectedEffectSum M L) * CFC.sqrt (selectedEffectSum M L) =
      selectedEffectSum M L
  refine ⟨CFC.sqrt_nonneg _, ?_, CFC.sqrt_mul_sqrt_self _ hS.1⟩
  let S := selectedEffectSum M L
  have hS_herm : S.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp hS.1).isHermitian
  have hS_sa : IsSelfAdjoint S := hS_herm.isSelfAdjoint
  have hS_le : S ≤ 1 := hS.2
  have hSle : cfc (id : ℝ → ℝ) S ≤ 1 := by
    simpa [cfc_id ℝ S (ha := hS_sa)] using hS_le
  have hspec :=
    (cfc_le_one_iff (f := (id : ℝ → ℝ)) (a := S) (ha := hS_sa)).mp hSle
  have hCfc : CFC.sqrt S = cfc Real.sqrt S := by
    rw [CFC.sqrt_eq_real_sqrt S (ha := hS.1),
      cfcₙ_eq_cfc (hf0 := by simp)]
  change CFC.sqrt S ≤ 1
  rw [hCfc]
  apply (cfc_le_one_iff (f := Real.sqrt) (a := S) (ha := hS_sa)).mpr
  intro x hx
  exact (Real.sqrt_le_one).mpr (hspec x hx)

end MIPStarRE.LDT.MakingMeasurementsProjective.SimplifiedOrthogonalization
