import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import MIPStarRE.LDT.Pasting.Bernoulli.TruncatedSums

/-!
# Section 12 pasting: Bernoulli recurrence bridge

Recurrence-weight wrappers, the `fromHToG` bridge, and the Chernoff wrapper.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Bundle the four proved facts about the averaged total operator `G` used by
`fromHToGRecurrenceWeight` into a single `truncatedTypeSumRecurrence` call. -/
private lemma fromHToGRecurrenceWeight_recurrence
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    (truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail)ᴴ =
        truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail ∧
      0 ≤ truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail ∧
      truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail ≤ 1 ∧
      truncatedTypeSums family.averagedSubMeas.total params.d (prefixLen + 1) τtail =
        truncatedTypeSums family.averagedSubMeas.total params.d prefixLen
            (prependTypeBit true τtail) * family.averagedSubMeas.total +
          truncatedTypeSums family.averagedSubMeas.total params.d prefixLen
            (prependTypeBit false τtail) * (1 - family.averagedSubMeas.total) :=
  truncatedTypeSumRecurrence family.averagedSubMeas.total
    family.averagedSubMeas.total_nonneg family.averagedSubMeas.total_le_one
    params.d prefixLen τtail

/-- `fromHToGRecurrenceWeight` is Hermitian (source-style API). -/
theorem fromHToGRecurrenceWeight_isHermitian
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    (fromHToGRecurrenceWeight params family prefixLen τtail)ᴴ =
      fromHToGRecurrenceWeight params family prefixLen τtail :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).1

/-- `fromHToGRecurrenceWeight` is positive semidefinite (source-style API). -/
theorem fromHToGRecurrenceWeight_nonneg
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    0 ≤ fromHToGRecurrenceWeight params family prefixLen τtail :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).2.1

/-- `fromHToGRecurrenceWeight` is bounded above by the identity. -/
theorem fromHToGRecurrenceWeight_le_one
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    fromHToGRecurrenceWeight params family prefixLen τtail ≤ 1 :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).2.2.1

/-- One-step recurrence for `fromHToGRecurrenceWeight`: adding a new prefix bit
splits the weight into the `τ_ℓ = 1` and `τ_ℓ = 0` branches, each multiplied by
the appropriate Bernoulli factor `G` or `I - G`. -/
theorem fromHToGRecurrenceWeight_succ
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    fromHToGRecurrenceWeight params family (prefixLen + 1) τtail =
      fromHToGRecurrenceWeight params family prefixLen (prependTypeBit true τtail) *
          family.averagedSubMeas.total +
        fromHToGRecurrenceWeight params family prefixLen (prependTypeBit false τtail) *
          (1 - family.averagedSubMeas.total) :=
  (fromHToGRecurrenceWeight_recurrence params family prefixLen τtail).2.2.2

/-- `lem:from-H-to-G`.

The proof of the paper's Bernoulli-recurrence lemma uses exactly the two named
upstream ingredients cited in the blueprint: `cor:G-hat-facts` for the
`\sqrt{2ζ}` moves of `\widehat G` across the tensor factors, and
`lem:commute-g-half-sandwich` for every suffix length appearing in the two
`\sqrt{ν₄}` commutation moves.  The conclusion package records the displayed
scalar expectation inequalities from the paper, rather than a stronger `≈_δ`
statement between the already-averaged recurrence families. -/
lemma fromHToG
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta)
    (hhalf : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params ψbi family gamma zeta j)
    (k : ℕ) :
    FromHToGStatement params strategy ψbi family gamma zeta k := by
  constructor
  · intro ℓ hℓ τ
    /- Inductive step `ℓ` of the Bernoulli-tail recurrence
    (`ld-pasting.tex` / blueprint lines 961–1210).  With the statement now
    phrased at the scalar-expectation level and the suffix averages built over
    the paper's independent uniform distribution, the remaining work is to
    formalize the three scalar bridge lemmas corresponding to the proof's
    move-right / commute / move-right sequence:
    1. two `easyApproxFromApproxDelta` / `closenessOfIP` applications driven by
       `hfacts.completedSelfConsistency`, each contributing `√(2ζ)`;
    2. two `closenessOfIP` applications driven by the suffix-length witness
       `hhalf (k - ℓ)`, together contributing `2√ν₄`;
    3. the exact algebraic rewrite from the final `S_{τ_{≥ℓ}} G_{g_ℓ}^{x_ℓ}`
       expression to the next suffix weight via `fromHToGRecurrenceWeight_succ`.
    -/
    sorry
  · /- Aggregate the `k` scalar recurrence steps to show the uniform all-outcomes
    expansion equals the Bernoulli polynomial up to `ν₈`.  After the per-step
    scalar bridge above is formalized, the remaining endpoint work is:
    1. identify stage `0` with `fromHToGAllOutcomesMass`;
    2. identify stage `k` with `fromHToGBernoulliTailMass` using the
       `truncatedTypeSums` polynomial;
    3. telescope over `ℓ = 0, …, k - 1` and sum the per-step errors, then use
       the displayed bound `k * fromHToGRecurrenceError ≤ fromHToGError`.
    -/
    sorry

/-- Scalar Bernoulli tail polynomial
`F(p) = ∑_{r=degree+1}^k C(k,r) p^r (1-p)^{k-r}` from
`lem:chernoff-bernoulli-matrix`. -/
noncomputable def scalarBernoulliTail (k degree : ℕ) (p : Error) : Error :=
  ∑ r ∈ Finset.Icc (degree + 1) k,
    (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))

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

/-- Scalar Chernoff bound for the Bernoulli tail polynomial.

This is the single remaining live blocker in issue #597. The matrix theorem
below now reduces completely to this scalar inequality via continuous
functional calculus; once this theorem is discharged from Hoeffding/Chernoff
for sums of iid Bernoullis, no further operator work is needed in the matrix
layer. -/
theorem scalarBernoulliTail_lower_bound
    (k degree : ℕ) {p : Error}
    (hpd : (degree : Error) / (k : Error) ≤ p) (hp1 : p ≤ 1) :
    1 - Real.exp (-(2 * ((p - (degree : Error) / (k : Error)) ^ (2 : ℕ)) * (k : Error))) ≤
      scalarBernoulliTail k degree p := by
  /- The operator-to-scalar reduction in `chernoffBernoulliMatrix` is complete.
  What remains is the purely scalar lower-tail Chernoff estimate for the
  binomial polynomial above, e.g. via Hoeffding's inequality on a sum of iid
  Bernoulli variables or an equivalent PMF-level argument. -/
  sorry

/-- Real scalars act on `Op ι` as scalar multiples of the identity. -/
private lemma algebraMap_real_op_eq_smul_one (r : Error) :
    (algebraMap Error (MIPStarRE.Quantum.Op ι) r) =
      (r • (1 : MIPStarRE.Quantum.Op ι)) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.algebraMap_matrix_apply]
  · simp [Matrix.algebraMap_matrix_apply, hij]

/-- `ev` is linear for real scalar multiplication as written in this file. -/
private lemma ev_real_scale
    (ψ : QuantumState ι) (c : Error) (A : MIPStarRE.Quantum.Op ι) :
    ev ψ (c • A) = c * ev ψ A := by
  simpa using ev_scale ψ c A

/-- The scalar Bernoulli tail polynomial lifted through continuous functional
calculus is exactly the matrix Bernoulli tail operator. -/
private lemma cfc_scalarBernoulliTail_eq_bernoulliTailOperator
    (A : MIPStarRE.Quantum.Op ι) (hA : IsSelfAdjoint A) (k degree : ℕ) :
    cfc (scalarBernoulliTail k degree) A = bernoulliTailOperator k degree A := by
  let s := Finset.Icc (degree + 1) k
  calc
    cfc (scalarBernoulliTail k degree) A
      = cfc (∑ r ∈ s, fun p => (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))) A := by
          unfold scalarBernoulliTail
          congr 1
          funext p
          simp [s]
    _ = ∑ r ∈ s, cfc (fun p => (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r))) A := by
          simpa [s] using
            (cfc_sum (f := fun r p => (Nat.choose k r : Error) * (p ^ r * (1 - p) ^ (k - r)))
              (a := A) (s := s))
    _ = ∑ r ∈ s, (Nat.choose k r : ℂ) • (A ^ r * (1 - A) ^ (k - r)) := by
          refine Finset.sum_congr rfl ?_
          intro r hr
          rw [cfc_const_mul (a := A) (r := (Nat.choose k r : Error))
                (f := fun p => p ^ r * (1 - p) ^ (k - r))]
          rw [cfc_mul (a := A) (f := fun p => p ^ r) (g := fun p => (1 - p) ^ (k - r))]
          rw [cfc_pow (a := A) (f := fun p => p) (n := r) (ha := hA)]
          rw [cfc_pow (a := A) (f := fun p => 1 - p) (n := k - r) (ha := hA)]
          rw [cfc_sub (a := A) (f := fun _ => 1) (g := fun p => p)]
          rw [cfc_const (a := A) (r := (1 : Error)), algebraMap_real_op_eq_smul_one]
          rw [cfc_id' (R := Error) (a := A) (ha := hA)]
          ext i j
          simp
    _ = bernoulliTailOperator k degree A := by
          simp [bernoulliTailOperator, s]

/-- The affine lower envelope used in the matrix Chernoff reduction. -/
private noncomputable def bernoulliTailLowerAffine (theta c : Error) (p : Error) : Error :=
  (1 - c) - ((1 / (1 - theta)) * (1 - p))

/-- Continuous functional calculus sends the affine lower envelope to the
expected affine operator expression. -/
private lemma cfc_bernoulliTailLowerAffine_eq
    (A : MIPStarRE.Quantum.Op ι) (hA : IsSelfAdjoint A) (theta c : Error) :
    cfc (bernoulliTailLowerAffine theta c) A =
      ((1 - c : Error) • (1 : MIPStarRE.Quantum.Op ι)) -
        ((1 / (1 - theta) : Error) • (1 - A)) := by
  unfold bernoulliTailLowerAffine
  rw [cfc_sub (a := A) (f := fun _ => 1 - c)
    (g := fun p => (1 / (1 - theta)) * (1 - p))]
  rw [cfc_const (a := A) (r := (1 - c : Error)), algebraMap_real_op_eq_smul_one]
  rw [cfc_const_mul (a := A) (r := (1 / (1 - theta) : Error)) (f := fun p => 1 - p)]
  rw [cfc_sub (a := A) (f := fun _ => 1) (g := fun p => p)]
  rw [cfc_const (a := A) (r := (1 : Error)), algebraMap_real_op_eq_smul_one]
  rw [cfc_id' (R := Error) (a := A) (ha := hA)]
  simp

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
`k ≥ 2d/θ`. -/
private lemma bernoulliTailLowerAffine_le_scalarBernoulliTail
    (theta : Error) (k degree : ℕ)
    (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hk : (2 * (degree : Error)) / theta ≤ (k : Error))
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
    have hScalar := scalarBernoulliTail_lower_bound k degree hdk_le_p hp1
    have hk_nonneg : 0 ≤ (k : Error) := by
      positivity
    have hpd_half : theta / 2 ≤ p - (degree : Error) / (k : Error) := by
      linarith
    have hsq : theta ^ (2 : ℕ) / 4 ≤ (p - (degree : Error) / (k : Error)) ^ (2 : ℕ) := by
      nlinarith
    have hExpCompare :
        Real.exp (-(2 * ((p - (degree : Error) / (k : Error)) ^ (2 : ℕ)) * (k : Error))) ≤
          Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hConst :
        1 - Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2) ≤
          1 - Real.exp (-(2 * ((p - (degree : Error) / (k : Error)) ^ (2 : ℕ)) *
            (k : Error))) := by
      linarith
    have hterm_nonneg : 0 ≤ (1 / (1 - theta)) * (1 - p) := by
      have hθden : 0 < 1 - theta := sub_pos.mpr hθ1
      have hθinv_nonneg : 0 ≤ 1 / (1 - theta) := one_div_nonneg.mpr hθden.le
      have hp_nonneg : 0 ≤ 1 - p := sub_nonneg.mpr hp1
      exact mul_nonneg hθinv_nonneg hp_nonneg
    have hLowerConst :
        bernoulliTailLowerAffine theta
            (Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2)) p ≤
          1 - Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2) := by
      unfold bernoulliTailLowerAffine
      linarith
    exact hLowerConst.trans (hConst.trans hScalar)

/-- `lem:chernoff-bernoulli-matrix`.

The operator-level reduction is now fully internal: continuous functional
calculus compares the Bernoulli-tail polynomial `F(X)` against an affine lower
envelope, so the only remaining issue-#597 debt is the isolated scalar theorem
`scalarBernoulliTail_lower_bound`. -/
lemma chernoffBernoulliMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι)
    (hnorm : ψ.IsNormalized)
    (theta : Error) (k degree : ℕ) (X : MIPStarRE.Quantum.Op ι) (kappa : Error)
    (hθ0 : 0 < theta) (hθ1 : theta < 1)
    (hk : (2 * (degree : Error)) / theta ≤ (k : Error))
    (hXpsd : 0 ≤ X)
    (hXleOne : X ≤ 1)
    (hcomplete : CompletenessAtLeast ψ
      ({ outcome := fun _ => X
         total := X
         outcome_pos := by
           intro _
           exact hXpsd
         sum_eq_total := by
           simp
         total_le_one := by
           exact hXleOne } : SubMeas Unit ι)
      (1 - kappa)) :
    ChernoffBernoulliMatrixStatement ψ theta k degree X kappa hXpsd hXleOne := by
  let expTerm : Error := Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2)
  have htail := bernoulliTailOperator_le_one k degree X hXpsd hXleOne
  have hXsa : IsSelfAdjoint X :=
    (Matrix.nonneg_iff_posSemidef.mp hXpsd).isHermitian
  have hPointwise : ∀ x ∈ spectrum Error X,
      bernoulliTailLowerAffine theta expTerm x ≤ scalarBernoulliTail k degree x := by
    intro x hx
    have hx0 : 0 ≤ x := spectrum_nonneg_of_nonneg hXpsd hx
    have hx1 : x ≤ 1 := (CFC.le_one_iff (R := Error) X (ha := hXsa)).1 hXleOne x hx
    exact bernoulliTailLowerAffine_le_scalarBernoulliTail theta k degree hθ0 hθ1 hk hx0 hx1
  have hContLower : ContinuousOn (bernoulliTailLowerAffine theta expTerm) (spectrum Error X) := by
    unfold bernoulliTailLowerAffine
    fun_prop
  have hContTail : ContinuousOn (scalarBernoulliTail k degree) (spectrum Error X) := by
    unfold scalarBernoulliTail
    fun_prop
  have hCfcLe : cfc (bernoulliTailLowerAffine theta expTerm) X ≤ bernoulliTailOperator k degree X := by
    calc
      cfc (bernoulliTailLowerAffine theta expTerm) X ≤ cfc (scalarBernoulliTail k degree) X := by
        exact (cfc_le_iff (f := bernoulliTailLowerAffine theta expTerm)
          (g := scalarBernoulliTail k degree) (a := X) (hf := hContLower)
          (hg := hContTail) (ha := hXsa)).2 hPointwise
      _ = bernoulliTailOperator k degree X :=
        cfc_scalarBernoulliTail_eq_bernoulliTailOperator X hXsa k degree
  have hEvLe :
      ev ψ (cfc (bernoulliTailLowerAffine theta expTerm) X) ≤
        ev ψ (bernoulliTailOperator k degree X) :=
    ev_mono ψ _ _ hCfcLe
  have hEvOneSub : 1 - ev ψ X ≤ kappa := by
    have hmass : 1 - kappa ≤ ev ψ X := hcomplete.lowerBound
    linarith
  have hEvLower :
      1 - kappa / (1 - theta) - expTerm ≤
        ev ψ (cfc (bernoulliTailLowerAffine theta expTerm) X) := by
    have hθden : 0 < 1 - theta := sub_pos.mpr hθ1
    have hfrac : (1 / (1 - theta)) * (1 - ev ψ X) ≤ kappa / (1 - theta) := by
      have hdiv : (1 - ev ψ X) / (1 - theta) ≤ kappa / (1 - theta) :=
        div_le_div_of_nonneg_right hEvOneSub hθden.le
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
    rw [cfc_bernoulliTailLowerAffine_eq X hXsa theta expTerm]
    rw [ev_sub, ev_real_scale, ev_real_scale, ev_sub, ev_one_of_isNormalized ψ hnorm]
    linarith
  refine { tail_le_one := htail, matrixTailBound := ⟨?_⟩ }
  show _ ≥ _
  unfold subMeasMass
  exact le_trans hEvLower hEvLe

end MIPStarRE.LDT.Pasting
