import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import MIPStarRE.LDT.Pasting.Statements
import MIPStarRE.LDT.Pasting.Bernoulli.Scalar
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

/-- Telescoping for a scalar chain indexed by natural numbers.

This is the purely real-analysis part of the last step in `lem:from-H-to-G`:
if each adjacent stage changes by at most `e`, then the first and last stages are
within `k * e`.  The lemma is independent of the operator-valued Bernoulli
recurrence, so it can be reused once the remaining stage bridge is supplied. -/
private lemma abs_telescope_nat (f : ℕ → Error) (e : Error) :
    ∀ k : ℕ,
      (∀ ℓ : ℕ, ℓ < k → |f ℓ - f (ℓ + 1)| ≤ e) →
        |f 0 - f k| ≤ (k : Error) * e
  | 0, _ => by simp
  | k + 1, hstep => by
      have hprev : |f 0 - f k| ≤ (k : Error) * e :=
        abs_telescope_nat f e k
          (fun ℓ hℓ => hstep ℓ (Nat.lt_trans hℓ (Nat.lt_succ_self k)))
      have hlast : |f k - f (k + 1)| ≤ e := hstep k (Nat.lt_succ_self k)
      have htri :
          |f 0 - f (k + 1)| ≤ |f 0 - f k| + |f k - f (k + 1)| :=
        abs_sub_le (f 0) (f k) (f (k + 1))
      calc
        |f 0 - f (k + 1)| ≤ |f 0 - f k| + |f k - f (k + 1)| := htri
        _ ≤ (k : Error) * e + e := add_le_add hprev hlast
        _ = ((k + 1 : ℕ) : Error) * e := by
              push_cast
              ring

/-- The adjacent-stage recurrence fields imply the scalar first-to-last
`telescope` bound for the `fromHToG` stage masses. -/
private lemma fromHToGStageMass_telescope
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ)
    (hstep : ∀ ℓ : ℕ, ℓ < k →
      |fromHToGStageMass params ψbi family k ℓ -
          fromHToGStageMass params ψbi family k (ℓ + 1)| ≤
        fromHToGRecurrenceError params gamma zeta k) :
    |fromHToGStageMass params ψbi family k 0 -
        fromHToGStageMass params ψbi family k k| ≤
      (k : Error) * fromHToGRecurrenceError params gamma zeta k :=
  abs_telescope_nat
    (fun ℓ => fromHToGStageMass params ψbi family k ℓ)
    (fromHToGRecurrenceError params gamma zeta k) k hstep

/-- Reduce the final scalar `fromHToG` conclusion to the three paper-local
bridge facts: identify the Lean stage `0`, identify the Lean stage `k`, and
absorb the telescoped adjacent-stage loss into the displayed error term. -/
private lemma fromHToG_bernoulliPolynomialRewrite_of_stageEndpoints
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ)
    (hstep : ∀ ℓ : ℕ, ℓ < k →
      |fromHToGStageMass params ψbi family k ℓ -
          fromHToGStageMass params ψbi family k (ℓ + 1)| ≤
        fromHToGRecurrenceError params gamma zeta k)
    (hstage0 :
      fromHToGStageMass params ψbi family k 0 =
        fromHToGAllOutcomesMass params strategy ψbi family k)
    (hstagek :
      fromHToGStageMass params ψbi family k k =
        fromHToGBernoulliTailMass params ψbi family k)
    (herror :
      (k : Error) * fromHToGRecurrenceError params gamma zeta k ≤
        fromHToGError params gamma zeta k) :
    |fromHToGAllOutcomesMass params strategy ψbi family k -
        fromHToGBernoulliTailMass params ψbi family k| ≤
      fromHToGError params gamma zeta k := by
  have htelescope :=
    fromHToGStageMass_telescope params ψbi family gamma zeta k hstep
  have hmass :
      |fromHToGAllOutcomesMass params strategy ψbi family k -
          fromHToGBernoulliTailMass params ψbi family k| ≤
        (k : Error) * fromHToGRecurrenceError params gamma zeta k := by
    simpa [hstage0, hstagek] using htelescope
  exact le_trans hmass herror

/-- The residual, paper-specific stage facts still needed for `fromHToG`.

This deliberately does not duplicate the public theorem: the telescope from these
facts to `FromHToGStatement.bernoulliPolynomialRewrite` is already proved by
`fromHToG_bernoulliPolynomialRewrite_of_stageEndpoints`.  What remains here is
the operator/scalar bridge from `cor:G-hat-facts` and
`lem:commute-g-half-sandwich`, the endpoint identifications of stages `0` and
`k`, and the final displayed arithmetic comparison of error terms. -/
private structure FromHToGResidualStageFacts
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ) : Prop where
  recurrenceStep :
    ∀ ℓ : ℕ, ℓ < k →
      |fromHToGStageMass params ψbi family k ℓ -
          fromHToGStageMass params ψbi family k (ℓ + 1)| ≤
        fromHToGRecurrenceError params gamma zeta k
  stageZero_eq :
    fromHToGStageMass params ψbi family k 0 =
      fromHToGAllOutcomesMass params strategy ψbi family k
  stageK_eq :
    fromHToGStageMass params ψbi family k k =
      fromHToGBernoulliTailMass params ψbi family k
  recurrenceError_le :
    (k : Error) * fromHToGRecurrenceError params gamma zeta k ≤
      fromHToGError params gamma zeta k

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
  have hresidual :
      FromHToGResidualStageFacts params strategy ψbi family gamma zeta k := by
    /- Remaining work from #707, now narrowed to the paper-specific stage facts.

       Paper / blueprint anchor:
       * `references/ldt-paper/ld-pasting.tex`, proof of `lem:from-H-to-G`
         (roughly lines 1379–1664 in the current source);
       * `blueprint/src/chapter/ch09_pasting.tex`, proof of `lem:from-H-to-G`
         (roughly lines 979–1233 in the current source).

       What remains to formalize after this file's telescope reduction:
       1. prove each adjacent-stage recurrence step by the paper's
          move-right / commute / move-right chain, using two
          `easyApproxFromApproxDelta` / `closenessOfIP` moves from
          `hfacts.completedSelfConsistency`, then two suffix-commutation moves from
          `hhalf (k - ℓ)`, and finally the exact branch split via
          `fromHToGRecurrenceWeight_succ`;
       2. identify Lean stage `0` with `fromHToGAllOutcomesMass`;
       3. identify Lean stage `k` with `fromHToGBernoulliTailMass` through the
          `truncatedTypeSums` polynomial;
       4. discharge the displayed arithmetic comparison
          `k * fromHToGRecurrenceError ≤ fromHToGError`.

       The generic telescoping step from these facts to
       `bernoulliPolynomialRewrite` is now proved above in
       `fromHToG_bernoulliPolynomialRewrite_of_stageEndpoints`.
    -/
    -- Keep the two paper inputs visible at the residual proof site: future work
    -- should use them for the self-consistency and suffix-commutation moves above.
    have _ := hfacts.completedSelfConsistency
    have _ := hhalf
    sorry
  refine ⟨hresidual.recurrenceStep, ?_⟩
  exact fromHToG_bernoulliPolynomialRewrite_of_stageEndpoints
    params strategy ψbi family gamma zeta k
    hresidual.recurrenceStep hresidual.stageZero_eq hresidual.stageK_eq
    hresidual.recurrenceError_le

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
          rw [cfc_const (a := A) (r := (1 : Error)), Algebra.algebraMap_eq_smul_one]
          rw [cfc_id' (R := Error) (a := A) (ha := hA)]
          ext i j
          simp
    _ = bernoulliTailOperator k degree A := by
          simp [bernoulliTailOperator, s]

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
  rw [cfc_const (a := A) (r := (1 - c : Error)), Algebra.algebraMap_eq_smul_one]
  rw [cfc_const_mul (a := A) (r := (1 / (1 - theta) : Error)) (f := fun p => 1 - p)]
  rw [cfc_sub (a := A) (f := fun _ => 1) (g := fun p => p)]
  rw [cfc_const (a := A) (r := (1 : Error)), Algebra.algebraMap_eq_smul_one]
  rw [cfc_id' (R := Error) (a := A) (ha := hA)]
  simp

/-- `lem:chernoff-bernoulli-matrix`.

The operator-level reduction is now fully internal: continuous functional
calculus compares the Bernoulli-tail polynomial `F(X)` against an affine lower
envelope, and the scalar Hoeffding estimate is proved locally in
`Bernoulli/Scalar.lean`. -/
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
    exact bernoulliTailLowerAffine_le_scalarBernoulliTail theta k degree hθ0 hθ1 hk
      hx0 hx1
  have hContLower : ContinuousOn (bernoulliTailLowerAffine theta expTerm) (spectrum Error X) := by
    unfold bernoulliTailLowerAffine
    fun_prop
  have hContTail : ContinuousOn (scalarBernoulliTail k degree) (spectrum Error X) := by
    unfold scalarBernoulliTail
    fun_prop
  have hCfcLe :
      cfc (bernoulliTailLowerAffine theta expTerm) X ≤
        bernoulliTailOperator k degree X := by
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
    have hscale1 :
        ev ψ ((1 - expTerm : Error) • (1 : MIPStarRE.Quantum.Op ι)) =
          (1 - expTerm) * ev ψ (1 : MIPStarRE.Quantum.Op ι) := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      simpa using (ev_scale ψ (1 - expTerm) (1 : MIPStarRE.Quantum.Op ι))
    have hscale2 :
        ev ψ ((1 / (1 - theta) : Error) • (1 - X)) =
          (1 / (1 - theta)) * ev ψ (1 - X) := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      simpa using (ev_scale ψ (1 / (1 - theta)) (1 - X))
    rw [cfc_bernoulliTailLowerAffine_eq X hXsa theta expTerm, ev_sub, hscale1, hscale2,
      ev_sub, ev_one_of_isNormalized ψ hnorm]
    linarith
  refine { tail_le_one := htail, matrixTailBound := ⟨?_⟩ }
  show _ ≥ _
  unfold subMeasMass
  exact le_trans hEvLower hEvLe

end MIPStarRE.LDT.Pasting
