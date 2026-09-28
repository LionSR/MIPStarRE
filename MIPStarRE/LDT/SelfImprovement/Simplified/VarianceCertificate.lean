import MIPStarRE.LDT.SelfImprovement.Simplified.SDPCertificate

/-!
# Variance certificate for the filtered measurement

The filtered outcome is the average of `Pᵤ T Pᵤ`.  Centering the point
operators at their average identifies its difference from `A T A` with
an average of positive sandwiches.  This is the operator calculation
`H - Z² ≥ 0` in the simplified self-improvement proof.

## References

- `blueprint/src/low_degree_simplified.tex`, proof of
  `lem:self-improvement-helper`, equation `eq:self-improvement-certificate-contraction`.
- `references/ldt-paper/self_improvement.tex`, `lem:sdp`.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.GlobalVariance
open scoped BigOperators MatrixOrder Matrix ComplexOrder

private theorem average_operator_sub {α ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (f g : α → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution 𝒟 (fun u => f u - g u) =
      averageOperatorOverDistribution 𝒟 f -
        averageOperatorOverDistribution 𝒟 g := by
  simp only [averageOperatorOverDistribution, smul_sub, Finset.sum_sub_distrib]

private theorem average_operator_add {α ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (f g : α → MIPStarRE.Quantum.Op ι) :
    averageOperatorOverDistribution 𝒟 (fun u => f u + g u) =
      averageOperatorOverDistribution 𝒟 f +
        averageOperatorOverDistribution 𝒟 g := by
  simp only [averageOperatorOverDistribution, smul_add, Finset.sum_add_distrib]

/-- The variance identity behind the simplified SDP certificate. -/
theorem average_sandwich_center_eq {α ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability)
    (P : α → MIPStarRE.Quantum.Op ι) (T : MIPStarRE.Quantum.Op ι) :
    let A := averageOperatorOverDistribution 𝒟 P
    averageOperatorOverDistribution 𝒟 (fun u => (P u - A) * T * (P u - A)) =
      averageOperatorOverDistribution 𝒟 (fun u => P u * T * P u) - A * T * A := by
  dsimp
  let A := averageOperatorOverDistribution 𝒟 P
  have hright :
      averageOperatorOverDistribution 𝒟 (fun u => P u * T * A) = A * T * A := by
    simpa [A, mul_assoc] using
      (averageOperatorOverDistribution_mul_left_right 𝒟
        (1 : MIPStarRE.Quantum.Op ι) (T * A) P)
  have hleft :
      averageOperatorOverDistribution 𝒟 (fun u => A * T * P u) = A * T * A := by
    simpa [A, mul_assoc] using
      (averageOperatorOverDistribution_mul_left_right 𝒟
        (A * T) (1 : MIPStarRE.Quantum.Op ι) P)
  have hconst :
      averageOperatorOverDistribution 𝒟 (fun _ => A * T * A) = A * T * A :=
    averageOperatorOverDistribution_const_of_isProbability 𝒟 h𝒟 _
  have hpoint (u : α) :
      (P u - A) * T * (P u - A) =
        ((P u * T * P u - P u * T * A) - A * T * P u) + A * T * A := by
    noncomm_ring
  rw [averageOperatorOverDistribution_congr 𝒟 _ _ hpoint]
  simp only [average_operator_add, average_operator_sub]
  rw [hright, hleft, hconst]
  noncomm_ring

/-- The filtered sandwich dominates the sandwich of the averaged point
operator. This is the operator-valued variance inequality used to bound
the SDP dual witness by the filtered measurement. -/
theorem average_sandwich_center_le {α ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (𝒟 : Distribution α) (h𝒟 : 𝒟.IsProbability)
    (P : α → MIPStarRE.Quantum.Op ι) (T : MIPStarRE.Quantum.Op ι)
    (hP : ∀ u, 0 ≤ P u) (hT : 0 ≤ T) :
    let A := averageOperatorOverDistribution 𝒟 P
    A * T * A ≤ averageOperatorOverDistribution 𝒟 (fun u => P u * T * P u) := by
  dsimp
  let A := averageOperatorOverDistribution 𝒟 P
  have hA : 0 ≤ A := averageOperatorOverDistribution_nonneg 𝒟 P hP
  have hAherm : Aᴴ = A :=
    (Matrix.nonneg_iff_posSemidef.mp hA).isHermitian.eq
  have hcenter : 0 ≤ averageOperatorOverDistribution 𝒟
      (fun u => (P u - A) * T * (P u - A)) := by
    apply averageOperatorOverDistribution_nonneg
    intro u
    have hPherm : (P u)ᴴ = P u :=
      (Matrix.nonneg_iff_posSemidef.mp (hP u)).isHermitian.eq
    have hdiff : (P u - A)ᴴ = P u - A := by
      rw [Matrix.conjTranspose_sub, hPherm, hAherm]
    have h : 0 ≤ (P u - A)ᴴ * T * (P u - A) := by
      simpa only [Matrix.star_eq_conjTranspose] using
        star_left_conjugate_nonneg hT (P u - A)
    rwa [hdiff] at h
  rw [average_sandwich_center_eq 𝒟 h𝒟 P T] at hcenter
  exact sub_nonneg.mp hcenter

/-- The optimal SDP dual witness satisfies `Z² ≤ H`, where `H` is the
total effect of the simplified filtered submeasurement. -/
theorem sdp_dual_square_le_filtered_total
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hpair : SdpOptimalPairWithSlackness params strategy T Z) :
    Z * Z ≤ (averagedSandwichedPolynomialSubMeas params strategy T).total := by
  classical
  rw [sdp_dual_square_eq_sandwiched_average params strategy T Z hpair]
  change
    (∑ g : Polynomial params,
      averagedPointOperator params strategy g * T.outcome g *
        averagedPointOperator params strategy g) ≤
      ∑ g : Polynomial params,
        averageOperatorOverDistribution (uniformDistribution (Point params))
          (fun u => sandwichedPolynomialOutcomeOperatorAt params strategy T u g)
  apply Finset.sum_le_sum
  intro g _
  let P : Point params → MIPStarRE.Quantum.Op ι :=
    pointConditionedOutcomeOperatorAtPolynomial params strategy g
  have hP (u : Point params) : 0 ≤ P u :=
    (strategy.pointMeasurement u).toSubMeas.outcome_pos (g u)
  have h := average_sandwich_center_le
    (uniformDistribution (Point params))
    (uniformDistribution_isProbability (Point params)) P (T.outcome g) hP
    (T.outcome_pos g)
  simpa only [P, averagedPointOperator, sandwichedPolynomialOutcomeOperatorAt]
    using h

/-- A positive operator whose square is below the identity is a contraction.
The proof uses positivity of `(I - Z)²` and avoids spectral calculus. -/
theorem positive_le_one_of_square_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Z : MIPStarRE.Quantum.Op ι) (hZ : 0 ≤ Z) (hsq : Z * Z ≤ 1) : Z ≤ 1 := by
  have hZherm : Zᴴ = Z :=
    (Matrix.nonneg_iff_posSemidef.mp hZ).isHermitian.eq
  have hminus_herm : ((1 : MIPStarRE.Quantum.Op ι) - Z)ᴴ = 1 - Z := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hZherm]
  have hminus : 0 ≤ ((1 : MIPStarRE.Quantum.Op ι) - Z) * (1 - Z) := by
    have h : 0 ≤ ((1 : MIPStarRE.Quantum.Op ι) - Z)ᴴ * (1 - Z) := by
      simpa only [Matrix.star_eq_conjTranspose, mul_one, one_mul] using
        star_left_conjugate_nonneg
          (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ι))
          ((1 : MIPStarRE.Quantum.Op ι) - Z)
    rwa [hminus_herm] at h
  have hdouble : Z + Z ≤ (1 : MIPStarRE.Quantum.Op ι) + 1 := by
    calc
      Z + Z ≤ 1 + Z * Z := by
        apply sub_nonneg.mp
        convert hminus using 1
        noncomm_ring
      _ ≤ 1 + 1 := by simpa [add_comm] using add_le_add_right hsq 1
  have htwo : (2 : ℝ) • Z ≤ (2 : ℝ) • (1 : MIPStarRE.Quantum.Op ι) := by
    simpa only [two_smul] using hdouble
  exact (smul_le_smul_iff_of_pos_left (by norm_num : (0 : ℝ) < 2)).mp htwo

/-- The dual witness in the simplified SDP construction is a positive
contraction, and its square is dominated by the filtered submeasurement. -/
theorem sdp_filtered_certificate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hpair : SdpOptimalPairWithSlackness params strategy T Z) :
    0 ≤ Z ∧ Z ≤ 1 ∧
      Z * Z ≤ (averagedSandwichedPolynomialSubMeas params strategy T).total ∧
      (averagedSandwichedPolynomialSubMeas params strategy T).total ≤ 1 := by
  have hsq := sdp_dual_square_le_filtered_total params strategy T Z hpair
  have htotal := (averagedSandwichedPolynomialSubMeas params strategy T).total_le_one
  exact ⟨hpair.dual_positive,
    positive_le_one_of_square_le_one Z hpair.dual_positive (hsq.trans htotal),
    hsq, htotal⟩

/-- The existing slackness-carrying helper construction supplies the
filtered-measurement certificate of the simplified proof. -/
theorem helper_filtered_certificate_of_slackness
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : Measurement (Polynomial params) ι)
    (H : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι) (eps delta : Error)
    (hhelper : SelfImprovementHelperConclusionWithSlackness
      params strategy T H Z eps delta) :
    0 ≤ Z ∧ Z ≤ 1 ∧ Z * Z ≤ H.total ∧ H.total ≤ 1 := by
  let hpair : SdpOptimalPairWithSlackness params strategy T.toSubMeas Z :=
    { toSdpOptimalPair := hhelper.toHelperConclusion.sdpWitness
      complementarySlackness := hhelper.complementarySlackness }
  rw [hhelper.toHelperConclusion.averagedConstruction]
  exact sdp_filtered_certificate params strategy T.toSubMeas Z hpair

/-- The certificate also gives the affine lower bound for the filtered
total effect used in the strong self-consistency argument. -/
theorem filtered_total_ge_two_dual_sub_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (T : SubMeas (Polynomial params) ι)
    (Z : MIPStarRE.Quantum.Op ι)
    (hpair : SdpOptimalPairWithSlackness params strategy T Z) :
    Z + Z - 1 ≤ (averagedSandwichedPolynomialSubMeas params strategy T).total := by
  have hZherm : Zᴴ = Z :=
    (Matrix.nonneg_iff_posSemidef.mp hpair.dual_positive).isHermitian.eq
  have hminus_herm : ((1 : MIPStarRE.Quantum.Op ι) - Z)ᴴ = 1 - Z := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hZherm]
  have hminus : 0 ≤ ((1 : MIPStarRE.Quantum.Op ι) - Z) * (1 - Z) := by
    have h : 0 ≤ ((1 : MIPStarRE.Quantum.Op ι) - Z)ᴴ * (1 - Z) := by
      simpa only [Matrix.star_eq_conjTranspose, mul_one, one_mul] using
        star_left_conjugate_nonneg
          (Matrix.PosSemidef.one.nonneg : 0 ≤ (1 : MIPStarRE.Quantum.Op ι))
          ((1 : MIPStarRE.Quantum.Op ι) - Z)
    rwa [hminus_herm] at h
  have hlow : Z + Z - 1 ≤ Z * Z := by
    apply sub_nonneg.mp
    convert hminus using 1
    noncomm_ring
  exact hlow.trans (sdp_dual_square_le_filtered_total params strategy T Z hpair)

end MIPStarRE.LDT.SelfImprovement
