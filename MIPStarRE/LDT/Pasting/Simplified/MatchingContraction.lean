import MIPStarRE.LDT.Pasting.Simplified.ContractionPowers
import MIPStarRE.LDT.Pasting.Defs.Families
import MIPStarRE.LDT.Basic.TensorPlacement

/-!
# Matching-outcome contraction

The simplified pasting proof averages the diagonal outcome projector of the
completed slice measurement. This operator is a positive contraction, so its
powers obey the linear bound from `ContractionPowers`.

## References

- `blueprint/src/low_degree_simplified.tex`, Section
  `A positive contraction for random measurement words`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The diagonal matching-outcome operator for a completed slice measurement. -/
noncomputable def matchingOutcomeAt (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    MIPStarRE.Quantum.Op (ι × ι) :=
  let P := (gHatIdxMeas params family x).toSubMeas
  ∑ a : GHatOutcome params, opTensor (P.outcome a) (P.outcome a)

/-- The matching-outcome operator averaged over a uniform slice question. -/
noncomputable def matchingOutcomeAverage (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) : MIPStarRE.Quantum.Op (ι × ι) :=
  averageOperatorOverDistribution (uniformDistribution (Fq params))
    (matchingOutcomeAt params family)

theorem matchingOutcomeAt_nonneg (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    0 ≤ matchingOutcomeAt params family x := by
  unfold matchingOutcomeAt
  exact Finset.sum_nonneg fun a _ =>
    opTensor_nonneg ((gHatIdxMeas params family x).toSubMeas.outcome_pos a)
      ((gHatIdxMeas params family x).toSubMeas.outcome_pos a)

theorem matchingOutcomeAt_le_one (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) :
    matchingOutcomeAt params family x ≤ 1 := by
  let P := (gHatIdxMeas params family x).toSubMeas
  simpa [matchingOutcomeAt, P] using
    (SubMeas.opTensor_sum_filter_le_one P P (fun _ : GHatOutcome params => True))

/-- The average matching-outcome operator is a positive contraction. -/
theorem matchingOutcomeAverage_nonneg (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    0 ≤ matchingOutcomeAverage params family := by
  unfold matchingOutcomeAverage
  exact averageOperatorOverDistribution_nonneg _ _
    (matchingOutcomeAt_nonneg params family)

theorem matchingOutcomeAverage_le_one (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) :
    matchingOutcomeAverage params family ≤ 1 := by
  unfold matchingOutcomeAverage
  exact averageOperatorOverDistribution_uniform_le_one _
    (matchingOutcomeAt_le_one params family)

/-- Operator power bound for the average matching-outcome contraction. -/
theorem matchingOutcomeAverage_power_bound (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (n : ℕ) :
    1 - matchingOutcomeAverage params family ^ n ≤
      n • (1 - matchingOutcomeAverage params family) :=
  one_sub_contraction_pow_le _
    (matchingOutcomeAverage_nonneg params family)
    (matchingOutcomeAverage_le_one params family) n

end MIPStarRE.LDT.Pasting
