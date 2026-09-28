import MIPStarRE.LDT.Pasting.Simplified.RandomWordEnergy
import MIPStarRE.LDT.Commutativity.Main.Results

/-!
# Fine-slice energy for the simplified commutation estimate

The one-step matching contraction bounds the energy of an uncompleted
slice outcome.  These operator estimates are the starting point for the
random-word commutation argument.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of
  `lem:commute-g-half-sandwich`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The squared mirror differences of a completed slice dominate the
gap of its matching-outcome contraction. -/
theorem one_sub_matchingOutcomeAt_le_mirror_energy
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    1 - matchingOutcomeAt params family x ≤
      ∑ a : GHatOutcome params,
        (leftTensor (ι₂ := ι) ((gHatIdxMeas params family x).outcome a) -
          rightTensor (ι₁ := ι) ((gHatIdxMeas params family x).outcome a)) *
        (leftTensor (ι₂ := ι) ((gHatIdxMeas params family x).outcome a) -
          rightTensor (ι₁ := ι) ((gHatIdxMeas params family x).outcome a)) := by
  rw [matchingOutcomeAt_mirror_energy]
  have hgap : 0 ≤ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
      matchingOutcomeAt params family x :=
    sub_nonneg.mpr (matchingOutcomeAt_le_one params family x)
  apply sub_nonneg.mp
  convert hgap using 1; abel

/-- The diagonal tensor sum of the uncompleted slice outcomes is bounded
by the tensor square of their total projector. -/
theorem fineSlice_diagonal_le_totalTensor
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    (∑ g : Polynomial params,
      opTensor ((family.meas x).outcome g) ((family.meas x).outcome g)) ≤
      opTensor (family.meas x).total (family.meas x).total := by
  let P := (family.meas x).toSubMeas
  calc
    (∑ g : Polynomial params, opTensor (P.outcome g) (P.outcome g)) ≤
        ∑ g : Polynomial params, opTensor (P.outcome g) P.total := by
          exact Finset.sum_le_sum fun g _ =>
            opTensor_mono_right (P.outcome_pos g) (P.outcome_le_total g)
    _ = opTensor P.total P.total := by
      rw [← opTensor_sum_left_finset, P.sum_eq_total]

/-- The positive energy operator obtained by inserting the gap of the
random matching contraction between a fine-slice projector. -/
noncomputable def fineSliceEnergy
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  ∑ g : Polynomial params,
    let G := (family.meas x).outcome g
    leftTensor (ι₂ := ι) G *
      (1 - matchingOutcomeAverage params family) *
        leftTensor (ι₂ := ι) G

/-- The fine-slice energy is positive. -/
theorem fineSliceEnergy_nonneg
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    0 ≤ fineSliceEnergy params family x := by
  unfold fineSliceEnergy
  apply Finset.sum_nonneg
  intro g _
  let G := (family.meas x).outcome g
  have hG : Gᴴ = G := (family.meas x).toSubMeas.outcome_hermitian g
  have hgap : 0 ≤ (1 : MIPStarRE.Quantum.Op (ι × ι)) -
      matchingOutcomeAverage params family :=
    sub_nonneg.mpr (matchingOutcomeAverage_le_one params family)
  simpa [G, leftTensor_conjTranspose, hG, Matrix.star_eq_conjTranspose] using
    (star_left_conjugate_nonneg hgap (leftTensor (ι₂ := ι) G))

/-- The fine-slice energy is bounded by the identity operator. -/
theorem fineSliceEnergy_le_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    fineSliceEnergy params family x ≤ 1 := by
  let P := (family.meas x).toSubMeas
  have hterm (g : Polynomial params) :
      leftTensor (ι₂ := ι) (P.outcome g) *
          (1 - matchingOutcomeAverage params family) *
            leftTensor (ι₂ := ι) (P.outcome g) ≤
        leftTensor (ι₂ := ι) (P.outcome g) := by
    let G := leftTensor (ι₂ := ι) (P.outcome g)
    have hGstar : Gᴴ = G := by
      simp [G, leftTensor_conjTranspose, P.outcome_hermitian g]
    have hGsq : G * G = G := by
      rw [show G * G = leftTensor (ι₂ := ι) (P.outcome g * P.outcome g) from
        leftTensor_mul_leftTensor _ _]
      exact congrArg (leftTensor (ι₂ := ι)) ((family.meas x).proj g)
    have hgap : (1 : MIPStarRE.Quantum.Op (ι × ι)) -
        matchingOutcomeAverage params family ≤ 1 :=
      sub_le_self _ (matchingOutcomeAverage_nonneg params family)
    simpa [G, hGsq] using IsSelfAdjoint.conjugate_le_conjugate hgap hGstar
  calc
    fineSliceEnergy params family x ≤
        ∑ g : Polynomial params, leftTensor (ι₂ := ι) (P.outcome g) := by
          unfold fineSliceEnergy
          exact Finset.sum_le_sum fun g _ => hterm g
    _ = leftTensor (ι₂ := ι) P.total := by rw [leftTensor_finset_sum, P.sum_eq_total]
    _ ≤ 1 := leftTensor_le_one (ι₂ := ι) P.total_le_one

/-- The operator whose state expectation is the fine-slice energy `β` in
the simplified proof. -/
noncomputable def meanFineSliceEnergy
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  averageOperatorOverDistribution (uniformDistribution (Fq params))
    (fineSliceEnergy params family)

/-- The averaged fine-slice energy is a positive contraction. -/
theorem meanFineSliceEnergy_nonneg
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    0 ≤ meanFineSliceEnergy params family := by
  exact averageOperatorOverDistribution_nonneg _ _
    (fineSliceEnergy_nonneg params family)

/-- The averaged fine-slice energy is at most the identity. -/
theorem meanFineSliceEnergy_le_one
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    meanFineSliceEnergy params family ≤ 1 := by
  exact averageOperatorOverDistribution_uniform_le_one _
    (fineSliceEnergy_le_one params family)

/-- Inserting a fine-slice outcome into the one-step mirror energy gives
exactly twice its matching-contraction energy. -/
theorem fineSliceEnergy_eq_half_mirror
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    (∑ g : Polynomial params,
      let G := (family.meas x).outcome g
      leftTensor (ι₂ := ι) G * matchingMirrorEnergyAverage params family *
        leftTensor (ι₂ := ι) G) =
      fineSliceEnergy params family x + fineSliceEnergy params family x := by
  rw [matchingMirrorEnergyAverage_eq]
  unfold fineSliceEnergy
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro g _
  dsimp
  noncomm_ring

/-- A first-register commutator with a word is the commutator with the
word's mirror difference. -/
theorem leftTensor_commutator_eq_wordMirrorDifference_commutator
    (G W : MIPStarRE.Quantum.Op ι) :
    leftTensor (ι₂ := ι) (G * W - W * G) =
      leftTensor (ι₂ := ι) G * wordMirrorDifference W -
        wordMirrorDifference W * leftTensor (ι₂ := ι) G := by
  let LG := leftTensor (ι₂ := ι) G
  let LW := leftTensor (ι₂ := ι) W
  let RW := rightTensor (ι₁ := ι) Wᴴ
  have hcross : LG * RW = RW * LG := by
    rw [show LG * RW = opTensor G Wᴴ from leftTensor_mul_rightTensor_eq_opTensor G Wᴴ,
      show RW * LG = opTensor G Wᴴ from rightTensor_mul_leftTensor_eq_opTensor G Wᴴ]
  calc
    leftTensor (ι₂ := ι) (G * W - W * G) = LG * LW - LW * LG := by
      rw [← leftTensor_sub, leftTensor_mul_leftTensor, leftTensor_mul_leftTensor]
    _ = LG * wordMirrorDifference W - wordMirrorDifference W * LG := by
      change LG * LW - LW * LG = LG * (LW - RW) - (LW - RW) * LG
      rw [mul_sub, sub_mul, hcross]
      abel

/-- The mirror defect of a completed slice after a fine-slice projector
splits into fine commutation and the original mirror defect. -/
theorem mirror_difference_mul_fineSlice_eq
    (G H : MIPStarRE.Quantum.Op ι) :
    (leftTensor (ι₂ := ι) H - rightTensor (ι₁ := ι) H) *
        leftTensor (ι₂ := ι) G =
      leftTensor (ι₂ := ι) (H * G - G * H) +
        leftTensor (ι₂ := ι) G *
          (leftTensor (ι₂ := ι) H - rightTensor (ι₁ := ι) H) := by
  let LG := leftTensor (ι₂ := ι) G
  let LH := leftTensor (ι₂ := ι) H
  let RH := rightTensor (ι₁ := ι) H
  have hcross : RH * LG = LG * RH := by
    rw [show RH * LG = opTensor G H from rightTensor_mul_leftTensor_eq_opTensor G H,
      show LG * RH = opTensor G H from leftTensor_mul_rightTensor_eq_opTensor G H]
  have hcomm : leftTensor (ι₂ := ι) (H * G - G * H) = LH * LG - LG * LH := by
    rw [← leftTensor_sub, leftTensor_mul_leftTensor, leftTensor_mul_leftTensor]
  rw [hcomm]
  change (LH - RH) * LG = (LH * LG - LG * LH) + LG * (LH - RH)
  rw [sub_mul, mul_sub, hcross]
  abel

/-- For a normalized state, the fine-slice energy lies in `[0,1]`. -/
theorem ev_meanFineSliceEnergy_bounds
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (ψ : QuantumState (ι × ι)) (hψ : ψ.IsNormalized) :
    0 ≤ ev ψ (meanFineSliceEnergy params family) ∧
      ev ψ (meanFineSliceEnergy params family) ≤ 1 := by
  constructor
  · simpa only [ev_zero] using
      (ev_mono ψ 0 _ (meanFineSliceEnergy_nonneg params family))
  · calc
      ev ψ (meanFineSliceEnergy params family) ≤ ev ψ 1 :=
        ev_mono ψ _ _ (meanFineSliceEnergy_le_one params family)
      _ = 1 := ev_one_of_isNormalized ψ hψ

end MIPStarRE.LDT.Pasting
