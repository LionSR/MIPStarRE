import MIPStarRE.LDT.Pasting.Simplified.FineEnergyBase

/-!
# Fine mirror energy before completion

The commutation estimate uses the original slice outcomes.  The sum of their
mirror energies already dominates the gap of the matching-outcome
contraction, so the failure outcome need not be inserted in this step.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of
  `lem:commute-g-half-sandwich`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Split the completed matching-outcome contraction into its original
slice outcomes and the failure projector. -/
theorem matchingOutcomeAt_eq_fine_and_failure
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    matchingOutcomeAt params family x =
      (∑ g : Polynomial params,
        opTensor ((family.meas x).outcome g) ((family.meas x).outcome g)) +
        opTensor (1 - (family.meas x).total) (1 - (family.meas x).total) := by
  simp [matchingOutcomeAt, gHatIdxMeas, completeSubMeas,
    Fintype.sum_option, add_comm]

/-- The squared mirror difference summed over the original slice
outcomes. -/
noncomputable def fineMirrorEnergyAt
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  ∑ g : Polynomial params,
    (leftTensor (ι₂ := ι) ((family.meas x).outcome g) -
      rightTensor (ι₁ := ι) ((family.meas x).outcome g)) *
    (leftTensor (ι₂ := ι) ((family.meas x).outcome g) -
      rightTensor (ι₁ := ι) ((family.meas x).outcome g))

/-- Expanding the fine mirror squares leaves a diagonal tensor sum. -/
theorem fineMirrorEnergyAt_eq
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    fineMirrorEnergyAt params family x =
      leftTensor (ι₂ := ι) (family.meas x).total +
        rightTensor (ι₁ := ι) (family.meas x).total -
          ((∑ g : Polynomial params,
              opTensor ((family.meas x).outcome g) ((family.meas x).outcome g)) +
            (∑ g : Polynomial params,
              opTensor ((family.meas x).outcome g) ((family.meas x).outcome g))) := by
  let P := (family.meas x).toSubMeas
  have hterm (g : Polynomial params) :
      (leftTensor (ι₂ := ι) (P.outcome g) -
          rightTensor (ι₁ := ι) (P.outcome g)) *
        (leftTensor (ι₂ := ι) (P.outcome g) -
          rightTensor (ι₁ := ι) (P.outcome g)) =
        leftTensor (ι₂ := ι) (P.outcome g) +
          rightTensor (ι₁ := ι) (P.outcome g) -
            (opTensor (P.outcome g) (P.outcome g) +
              opTensor (P.outcome g) (P.outcome g)) := by
    let L := leftTensor (ι₂ := ι) (P.outcome g)
    let R := rightTensor (ι₁ := ι) (P.outcome g)
    have hL : L * L = L := by
      rw [show L * L = leftTensor (ι₂ := ι) (P.outcome g * P.outcome g) from
        leftTensor_mul_leftTensor _ _]
      exact congrArg (leftTensor (ι₂ := ι)) ((family.meas x).proj g)
    have hR : R * R = R := by
      rw [show R * R = rightTensor (ι₁ := ι) (P.outcome g * P.outcome g) from
        rightTensor_mul_rightTensor _ _]
      exact congrArg (rightTensor (ι₁ := ι)) ((family.meas x).proj g)
    have hLR : L * R = opTensor (P.outcome g) (P.outcome g) :=
      leftTensor_mul_rightTensor_eq_opTensor _ _
    have hRL : R * L = opTensor (P.outcome g) (P.outcome g) :=
      rightTensor_mul_leftTensor_eq_opTensor _ _
    change (L - R) * (L - R) = L + R -
      (opTensor (P.outcome g) (P.outcome g) +
        opTensor (P.outcome g) (P.outcome g))
    calc
      (L - R) * (L - R) = L * L + R * R - (L * R + R * L) := by
        noncomm_ring
      _ = L + R - (opTensor (P.outcome g) (P.outcome g) +
          opTensor (P.outcome g) (P.outcome g)) := by
            rw [hL, hR, hLR, hRL]
  unfold fineMirrorEnergyAt
  simp_rw [show ∀ g : Polynomial params,
    (family.meas x).outcome g = P.outcome g from fun _ => rfl]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [leftTensor_finset_sum, rightTensor_finset_sum, P.sum_eq_total]

/-- The failure projector tensor square is determined by the total slice
projector and its two tensor placements. -/
theorem failure_tensor_square_eq
    (T : MIPStarRE.Quantum.Op ι) :
    opTensor (1 - T) (1 - T) =
      (1 : MIPStarRE.Quantum.Op (ι × ι)) -
        leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T +
          opTensor T T := by
  calc
    opTensor (1 - T) (1 - T) =
        leftTensor (ι₂ := ι) (1 - T) * rightTensor (ι₁ := ι) (1 - T) :=
          (leftTensor_mul_rightTensor_eq_opTensor _ _).symm
    _ = (1 - leftTensor (ι₂ := ι) T) *
          (1 - rightTensor (ι₁ := ι) T) := by
            rw [← leftTensor_sub, ← rightTensor_sub, leftTensor_one, rightTensor_one]
    _ = 1 - leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T +
          leftTensor (ι₂ := ι) T * rightTensor (ι₁ := ι) T := by
            noncomm_ring
    _ = 1 - leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T +
          opTensor T T := by rw [leftTensor_mul_rightTensor_eq_opTensor]

/-- The original slice mirror energy dominates the gap of the completed
matching-outcome contraction. This is the operator inequality used for `β`.
It avoids a factor from the failure outcome in the fine commutation step. -/
theorem one_sub_matchingOutcomeAt_le_fineMirrorEnergy
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    1 - matchingOutcomeAt params family x ≤
      fineMirrorEnergyAt params family x := by
  let T := (family.meas x).total
  let diag := ∑ g : Polynomial params,
    opTensor ((family.meas x).outcome g) ((family.meas x).outcome g)
  have hdiag : diag ≤ opTensor T T :=
    fineSlice_diagonal_le_totalTensor params family x
  have hmatching : matchingOutcomeAt params family x =
      diag + (1 - leftTensor (ι₂ := ι) T - rightTensor (ι₁ := ι) T +
        opTensor T T) := by
    rw [matchingOutcomeAt_eq_fine_and_failure, failure_tensor_square_eq]
  have hmirror : fineMirrorEnergyAt params family x =
      leftTensor (ι₂ := ι) T + rightTensor (ι₁ := ι) T -
        (diag + diag) := fineMirrorEnergyAt_eq params family x
  apply sub_nonneg.mp
  rw [hmatching, hmirror]
  have hgap : 0 ≤ opTensor T T - diag := sub_nonneg.mpr hdiag
  convert hgap using 1; abel

end MIPStarRE.LDT.Pasting
