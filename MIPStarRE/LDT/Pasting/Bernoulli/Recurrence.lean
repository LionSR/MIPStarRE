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
  /- Remaining work from #673, stated at the single live proof gap.

     Paper / blueprint anchor:
     * `references/ldt-paper/ld-pasting.tex`, proof of `lem:from-H-to-G`
       (roughly lines 1379–1664 in the current source);
     * `blueprint/src/chapter/ch09_pasting.tex`, proof of `lem:from-H-to-G`
       (roughly lines 979–1233 in the current source).

     What remains to formalize:
     1. prove each adjacent-stage recurrence step by the paper's
        move-right / commute / move-right chain, using two
        `easyApproxFromApproxDelta` / `closenessOfIP` moves from
        `hfacts.completedSelfConsistency`, then two suffix-commutation moves from
        `hhalf (k - ℓ)`, and finally the exact branch split via
        `fromHToGRecurrenceWeight_succ`;
     2. identify Lean stage `0` with `fromHToGAllOutcomesMass`;
     3. identify Lean stage `k` with `fromHToGBernoulliTailMass` through the
        `truncatedTypeSums` polynomial;
     4. telescope the `k` adjacent-stage errors and discharge the displayed
        arithmetic bound `k * fromHToGRecurrenceError ≤ fromHToGError`.
  -/
  sorry

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
