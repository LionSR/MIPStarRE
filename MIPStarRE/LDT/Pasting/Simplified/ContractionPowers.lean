import MIPStarRE.LDT.Pasting.Defs.Tuples

/-!
# Powers of a positive contraction

The average matching-outcome operator in the simplified pasting proof is a
positive contraction. Its powers satisfy `I - Kⁿ ≤ n(I - K)`, which is the
operator estimate used for random measurement words.

## References

- `blueprint/src/low_degree_simplified.tex`, equation `eq:random-word-energy`.
- `references/ldt-paper/ld-pasting.tex`, Section 12.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every power of a positive contraction is again below the identity. -/
theorem one_sub_contraction_pow_nonneg
    (K : MIPStarRE.Quantum.Op ι) (hK : 0 ≤ K) (hKle : K ≤ 1)
    (n : ℕ) : 0 ≤ 1 - K ^ n := by
  have hIK : 0 ≤ (1 : MIPStarRE.Quantum.Op ι) - K := sub_nonneg.mpr hKle
  have hcomm : Commute K (1 - K) :=
    (Commute.one_right K).sub_right (Commute.refl K)
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow : 0 ≤ K ^ n :=
        (Matrix.PosSemidef.pow (Matrix.nonneg_iff_posSemidef.mp hK) n).nonneg
      have hprod : 0 ≤ K ^ n * (1 - K) :=
        Commute.mul_nonneg hpow hIK (hcomm.pow_left n)
      have hid : 1 - K ^ (n + 1) = (1 - K ^ n) + K ^ n * (1 - K) := by
        rw [pow_succ]
        noncomm_ring
      rw [hid]
      exact add_nonneg ih hprod

/-- The elementary spectral inequality used to bound random-word energy. -/
theorem one_sub_contraction_pow_le
    (K : MIPStarRE.Quantum.Op ι) (hK : 0 ≤ K) (hKle : K ≤ 1)
    (n : ℕ) : 1 - K ^ n ≤ n • (1 - K) := by
  have hIK : 0 ≤ (1 : MIPStarRE.Quantum.Op ι) - K := sub_nonneg.mpr hKle
  have hcomm : Commute K (1 - K) :=
    (Commute.one_right K).sub_right (Commute.refl K)
  induction n with
  | zero => simp
  | succ n ih =>
      have hpow_le : K ^ n ≤ 1 :=
        sub_nonneg.mp (one_sub_contraction_pow_nonneg K hK hKle n)
      have hcommPow : Commute (K ^ n) (1 - K) := hcomm.pow_left n
      have hcommSub : Commute (1 - K ^ n) (1 - K) :=
        (Commute.one_left (1 - K)).sub_left hcommPow
      have hprod_nonneg : 0 ≤ (1 - K ^ n) * (1 - K) :=
        Commute.mul_nonneg (sub_nonneg.mpr hpow_le) hIK hcommSub
      have hprod_le : K ^ n * (1 - K) ≤ 1 - K := by
        apply sub_nonneg.mp
        convert hprod_nonneg using 1
        noncomm_ring
      have hid : 1 - K ^ (n + 1) = (1 - K ^ n) + K ^ n * (1 - K) := by
        rw [pow_succ]
        noncomm_ring
      calc
        1 - K ^ (n + 1) = (1 - K ^ n) + K ^ n * (1 - K) := hid
        _ ≤ n • (1 - K) + (1 - K) := add_le_add ih hprod_le
        _ = (n + 1) • (1 - K) := by simp [add_smul]

end MIPStarRE.LDT.Pasting
