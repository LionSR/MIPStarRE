import MIPStarRE.LDT.Pasting.Simplified.WordEnergy

/-!
# Algebraic energy identity for measurement words

For any finite family of operators with both word normalizations, the sum of
squared mirror differences is the sum of the two identity operators minus the
forward and adjoint tensor correlations. This algebraic form precedes the
random-question averaging in the simplified pasting argument.

## References

- `blueprint/src/low_degree_simplified.tex`, equation `eq:random-word-energy`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The difference between a word on the left register and its adjoint on
the right register. -/
noncomputable def wordMirrorDifference (W : MIPStarRE.Quantum.Op ι) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  leftTensor (ι₂ := ι) W - rightTensor (ι₁ := ι) Wᴴ

private theorem wordMirrorDifference_adjoint_square
    (W : MIPStarRE.Quantum.Op ι) :
    (wordMirrorDifference W)ᴴ * wordMirrorDifference W =
      leftTensor (ι₂ := ι) (Wᴴ * W) +
        rightTensor (ι₁ := ι) (W * Wᴴ) -
          (opTensor W W + opTensor Wᴴ Wᴴ) := by
  let L := leftTensor (ι₂ := ι) W
  let R := rightTensor (ι₁ := ι) Wᴴ
  have hLstar : Lᴴ = leftTensor (ι₂ := ι) Wᴴ := leftTensor_conjTranspose W
  have hRstar : Rᴴ = rightTensor (ι₁ := ι) W := by simp [R]
  have hLL : Lᴴ * L = leftTensor (ι₂ := ι) (Wᴴ * W) := by
    rw [hLstar]
    exact leftTensor_mul_leftTensor Wᴴ W
  have hRR : Rᴴ * R = rightTensor (ι₁ := ι) (W * Wᴴ) := by
    rw [hRstar]
    exact rightTensor_mul_rightTensor W Wᴴ
  have hLR : Lᴴ * R = opTensor Wᴴ Wᴴ := by
    rw [hLstar]
    exact leftTensor_mul_rightTensor_eq_opTensor Wᴴ Wᴴ
  have hRL : Rᴴ * L = opTensor W W := by
    rw [hRstar]
    exact rightTensor_mul_leftTensor_eq_opTensor W W
  calc
    (wordMirrorDifference W)ᴴ * wordMirrorDifference W =
        Lᴴ * L + Rᴴ * R - (Lᴴ * R + Rᴴ * L) := by
          simp only [wordMirrorDifference, Matrix.conjTranspose_sub]
          noncomm_ring
    _ = leftTensor (ι₂ := ι) (Wᴴ * W) +
          rightTensor (ι₁ := ι) (W * Wᴴ) -
          (opTensor W W + opTensor Wᴴ Wᴴ) := by
            rw [hLL, hRR, hLR, hRL]
            abel

/-- Word normalization converts the mirror-energy sum into the two tensor
correlation sums. -/
theorem wordMirrorEnergy_eq_tensor_correlations
    {Word : Type*} [Fintype Word]
    (W : Word → MIPStarRE.Quantum.Op ι)
    (hleft : (∑ w : Word, (W w)ᴴ * W w) = 1)
    (hright : (∑ w : Word, W w * (W w)ᴴ) = 1) :
    (∑ w : Word, (wordMirrorDifference (W w))ᴴ * wordMirrorDifference (W w)) =
      (1 + 1 : MIPStarRE.Quantum.Op (ι × ι)) -
        ((∑ w : Word, opTensor (W w) (W w)) +
          (∑ w : Word, opTensor (W w)ᴴ (W w)ᴴ)) := by
  simp_rw [wordMirrorDifference_adjoint_square]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [leftTensor_finset_sum, rightTensor_finset_sum, hleft, hright]
  simp [leftTensor_one]

/-- Replacing every word by its adjoint leaves the summed mirror energy
unchanged when both word normalizations hold. -/
theorem wordMirrorEnergy_adjoint_eq
    {Word : Type*} [Fintype Word]
    (W : Word → MIPStarRE.Quantum.Op ι)
    (hleft : (∑ w : Word, (W w)ᴴ * W w) = 1)
    (hright : (∑ w : Word, W w * (W w)ᴴ) = 1) :
    (∑ w : Word,
      (wordMirrorDifference (W w)ᴴ)ᴴ * wordMirrorDifference (W w)ᴴ) =
      ∑ w : Word,
        (wordMirrorDifference (W w))ᴴ * wordMirrorDifference (W w) := by
  have hleft' : (∑ w : Word, ((W w)ᴴ)ᴴ * (W w)ᴴ) = 1 := by
    simpa using hright
  have hright' : (∑ w : Word, (W w)ᴴ * ((W w)ᴴ)ᴴ) = 1 := by
    simpa using hleft
  rw [wordMirrorEnergy_eq_tensor_correlations
    (fun w => (W w)ᴴ) hleft' hright',
    wordMirrorEnergy_eq_tensor_correlations W hleft hright]
  simp only [Matrix.conjTranspose_conjTranspose]
  congr 1
  ac_rfl

end MIPStarRE.LDT.Pasting
