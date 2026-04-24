import MIPStarRE.LDT.Pasting.Bernoulli.TruncatedSums

/-!
# Scalar Bernoulli polynomial helpers for pasting

Purely scalar inequalities used by the matrix Chernoff wrapper.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators

/-- Scalar Bernoulli tail polynomial
`F(p) = ∑_{r=degree+1}^k C(k,r) p^r (1-p)^{k-r}` from
`lem:chernoff-bernoulli-matrix`. -/
noncomputable def scalarBernoulliTail (k degree : ℕ) (p : Error) : Error :=
  ∑ r ∈ Finset.Icc (degree + 1) k,
    (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))

/-- The affine lower envelope used in the matrix Chernoff reduction. -/
noncomputable def bernoulliTailLowerAffine (theta c : Error) (p : Error) : Error :=
  (1 - c) - ((1 / (1 - theta)) * (1 - p))

/-- The scalar Bernoulli tail polynomial is nonnegative on `[0,1]`. -/
private lemma scalarBernoulliTail_nonneg
    (k degree : ℕ) {p : Error} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ scalarBernoulliTail k degree p := by
  unfold scalarBernoulliTail
  refine Finset.sum_nonneg ?_
  intro r hr
  apply mul_nonneg
  · exact_mod_cast Nat.zero_le (Nat.choose k r)
  · apply mul_nonneg
    · exact pow_nonneg hp0 _
    · exact pow_nonneg (sub_nonneg.mpr hp1) _

/-- The paper's size condition `k ≥ 2d/θ` implies `d/k ≤ θ/2`. -/
private lemma degree_div_le_theta_half
    (theta : Error) (k degree : ℕ)
    (hθ0 : 0 < theta) (hk : (2 * (degree : Error)) / theta ≤ (k : Error)) :
    (degree : Error) / (k : Error) ≤ theta / 2 := by
  by_cases hk0 : k = 0
  · subst hk0
    have hdeg : degree = 0 := by
      by_contra hdeg
      have hdegpos : 0 < (degree : Error) := by
        exact_mod_cast Nat.pos_iff_ne_zero.mpr hdeg
      have hfracpos : 0 < (2 * (degree : Error)) / theta := by
        positivity
      linarith
    subst hdeg
    have hnonneg : 0 ≤ theta / 2 := by
      positivity
    simpa using hnonneg
  · have hkpos : 0 < (k : Error) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr hk0
    have hk' := hk
    field_simp [hθ0.ne', hkpos.ne'] at hk'
    have h2 : (2 * (degree : Error)) / (k : Error) ≤ theta := by
      rw [div_le_iff₀ hkpos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hk'
    have h2' : 2 * ((degree : Error) / (k : Error)) ≤ theta := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h2
    linarith

/-- Pointwise lower bound on `[0,1]` combining the scalar Chernoff estimate with
`k ≥ 2d/θ`.

The scalar Chernoff input remains an explicit hypothesis rather than a proof
hole, following the repository proof-integrity policy. -/
theorem bernoulliTailLowerAffine_le_scalarBernoulliTail
    (theta : Error) (k degree : ℕ)
    (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hk : (2 * (degree : Error)) / theta ≤ (k : Error))
    (hScalarTail :
      ∀ {q : Error}, (degree : Error) / (k : Error) ≤ q → q ≤ 1 →
        1 - Real.exp (-(2 * ((q - (degree : Error) / (k : Error)) ^ (2 : ℕ)) * (k : Error))) ≤
          scalarBernoulliTail k degree q)
    {p : Error} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bernoulliTailLowerAffine theta
      (Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2)) p ≤
        scalarBernoulliTail k degree p := by
  by_cases hpθ : p < theta
  · have htail_nonneg : 0 ≤ scalarBernoulliTail k degree p :=
      scalarBernoulliTail_nonneg k degree hp0 hp1
    have hθden : 0 < 1 - theta := sub_pos.mpr hθ1
    have hfrac_ge_one : 1 ≤ (1 - p) / (1 - theta) := by
      rw [one_le_div₀ hθden]
      linarith
    have hbase : 1 - (1 - p) / (1 - theta) ≤ 0 := by
      linarith
    have hexp_nonneg : 0 ≤ Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2) := by
      positivity
    have hLower :
        bernoulliTailLowerAffine theta
            (Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2)) p ≤ 0 := by
      unfold bernoulliTailLowerAffine
      have hrew : (1 / (1 - theta)) * (1 - p) = (1 - p) / (1 - theta) := by
        ring
      rw [hrew]
      linarith
    exact hLower.trans htail_nonneg
  · have hpθ' : theta ≤ p := le_of_not_gt hpθ
    have hdk_half : (degree : Error) / (k : Error) ≤ theta / 2 :=
      degree_div_le_theta_half theta k degree hθ0 hk
    have hdk_le_p : (degree : Error) / (k : Error) ≤ p := by
      linarith
    have hScalar := hScalarTail hdk_le_p hp1
    have hk_nonneg : 0 ≤ (k : Error) := by positivity
    have hpd_half : theta / 2 ≤ p - (degree : Error) / (k : Error) := by
      linarith
    have hsq : theta ^ (2 : ℕ) / 4 ≤ (p - (degree : Error) / (k : Error)) ^ (2 : ℕ) := by
      nlinarith [hpd_half, hθ0.le,
        sq_nonneg (p - (degree : Error) / (k : Error) - theta / 2)]
    have hExpCompare :
        Real.exp (-(2 * ((p - (degree : Error) / (k : Error)) ^ (2 : ℕ)) * (k : Error))) ≤
          Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hsq, hk_nonneg]
    have hConst :
        1 - Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2) ≤
          1 - Real.exp (-(2 * ((p - (degree : Error) / (k : Error)) ^ (2 : ℕ)) *
            (k : Error))) := by
      linarith
    have hθden : 0 < 1 - theta := sub_pos.mpr hθ1
    have hθinv_nonneg : 0 ≤ 1 / (1 - theta) := one_div_nonneg.mpr hθden.le
    have hp_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp1
    have hterm_nonneg : 0 ≤ (1 / (1 - theta)) * (1 - p) :=
      mul_nonneg hθinv_nonneg hp_nonneg
    have hLowerConst :
        bernoulliTailLowerAffine theta
            (Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2)) p ≤
          1 - Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2) := by
      unfold bernoulliTailLowerAffine
      linarith
    exact hLowerConst.trans (hConst.trans hScalar)

end MIPStarRE.LDT.Pasting
