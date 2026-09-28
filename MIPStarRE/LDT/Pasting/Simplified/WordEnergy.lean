import MIPStarRE.LDT.Pasting.Simplified.WordNorm

/-!
# One-step mirror energy for completed slices

The matching-outcome contraction records exactly the squared mirror defect
of the completed projective slice measurement. This is the one-step case of
the random-word energy identity in the simplified pasting proof.

## References

- `blueprint/src/low_degree_simplified.tex`, `lem:pasting-completion` and
  equation `eq:random-word-energy`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem mirror_difference_square_of_proj
    (P : MIPStarRE.Quantum.Op ι) (hP : P * P = P) :
    (leftTensor (ι₂ := ι) P - rightTensor (ι₁ := ι) P) *
        (leftTensor (ι₂ := ι) P - rightTensor (ι₁ := ι) P) =
      leftTensor (ι₂ := ι) P + rightTensor (ι₁ := ι) P -
        (opTensor P P + opTensor P P) := by
  let L := leftTensor (ι₂ := ι) P
  let R := rightTensor (ι₁ := ι) P
  have hLL : L * L = L := by rw [show L * L = leftTensor (ι₂ := ι) (P * P) from
    leftTensor_mul_leftTensor P P, hP]
  have hRR : R * R = R := by rw [show R * R = rightTensor (ι₁ := ι) (P * P) from
    rightTensor_mul_rightTensor P P, hP]
  have hLR : L * R = opTensor P P := leftTensor_mul_rightTensor_eq_opTensor P P
  have hRL : R * L = opTensor P P := rightTensor_mul_leftTensor_eq_opTensor P P
  calc
    (L - R) * (L - R) = L * L + R * R - (L * R + R * L) := by
      noncomm_ring
    _ = L + R - (opTensor P P + opTensor P P) := by
      rw [hLL, hRR, hLR, hRL]

/-- The sum of squared completed-slice mirror differences is twice the
failure of the matching-outcome operator. -/
theorem matchingOutcomeAt_mirror_energy
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    (∑ a : GHatOutcome params,
      (leftTensor (ι₂ := ι) ((gHatIdxMeas params family x).outcome a) -
          rightTensor (ι₁ := ι) ((gHatIdxMeas params family x).outcome a)) *
        (leftTensor (ι₂ := ι) ((gHatIdxMeas params family x).outcome a) -
          rightTensor (ι₁ := ι) ((gHatIdxMeas params family x).outcome a))) =
      (1 + 1 : MIPStarRE.Quantum.Op (ι × ι)) -
        (matchingOutcomeAt params family x + matchingOutcomeAt params family x) := by
  let P := (gHatIdxMeas params family x).toSubMeas
  have hterm (a : GHatOutcome params) :
      (leftTensor (ι₂ := ι) (P.outcome a) - rightTensor (ι₁ := ι) (P.outcome a)) *
          (leftTensor (ι₂ := ι) (P.outcome a) - rightTensor (ι₁ := ι) (P.outcome a)) =
        leftTensor (ι₂ := ι) (P.outcome a) + rightTensor (ι₁ := ι) (P.outcome a) -
          (opTensor (P.outcome a) (P.outcome a) +
            opTensor (P.outcome a) (P.outcome a)) :=
    mirror_difference_square_of_proj _
      (gHatIdxMeas_proj params family x a)
  simp_rw [show ∀ a : GHatOutcome params,
    (gHatIdxMeas params family x).outcome a = P.outcome a from fun _ => rfl]
  simp_rw [hterm]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hPtotal : (∑ a : GHatOutcome params, P.outcome a) = 1 := by
    rw [P.sum_eq_total]
    simp [P, gHatIdxMeas, completeSubMeas]
  rw [leftTensor_finset_sum, rightTensor_finset_sum, hPtotal]
  simp [leftTensor_one, matchingOutcomeAt, P]

/-- The averaged one-step squared mirror operator for completed slices. -/
noncomputable def matchingMirrorEnergyAverage
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) : MIPStarRE.Quantum.Op (ι × ι) :=
  averageOperatorOverDistribution (uniformDistribution (Fq params))
    (fun x => ∑ a : GHatOutcome params,
      (leftTensor (ι₂ := ι) ((gHatIdxMeas params family x).outcome a) -
          rightTensor (ι₁ := ι) ((gHatIdxMeas params family x).outcome a)) *
        (leftTensor (ι₂ := ι) ((gHatIdxMeas params family x).outcome a) -
          rightTensor (ι₁ := ι) ((gHatIdxMeas params family x).outcome a)))

/-- The averaged one-step energy is `2(I - K)`. -/
theorem matchingMirrorEnergyAverage_eq
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    matchingMirrorEnergyAverage params family =
      (1 + 1 : MIPStarRE.Quantum.Op (ι × ι)) -
        (matchingOutcomeAverage params family + matchingOutcomeAverage params family) := by
  unfold matchingMirrorEnergyAverage
  rw [averageOperatorOverDistribution_congr _ _ _
    (matchingOutcomeAt_mirror_energy params family)]
  simp only [averageOperatorOverDistribution, smul_sub, smul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hconst := averageOperatorOverDistribution_const_of_isProbability
    (uniformDistribution (Fq params)) (uniformDistribution_isProbability (Fq params))
    (1 : MIPStarRE.Quantum.Op (ι × ι))
  simp only [averageOperatorOverDistribution] at hconst
  rw [hconst]
  rfl

end MIPStarRE.LDT.Pasting
