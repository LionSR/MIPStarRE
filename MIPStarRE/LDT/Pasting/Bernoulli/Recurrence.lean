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

/-- `lem:chernoff-bernoulli-matrix`.

The core scalar inequality `ev ψ (F(X)) ≥ 1 - κ/(1-θ) - exp(-θ²k/2)` (paper
`ld-pasting.tex` lines 1670–1797) is taken as the explicit hypothesis
`hMatrixChernoff` rather than derived internally: its proof requires matrix
Chernoff infrastructure (additive Chernoff for sums of iid Bernoullis and
`Matrix.IsHermitian.spectral_theorem` composed with `ev`/`normalizedTrace`
expansion) that is not yet available in Mathlib. Once that infrastructure
lands, `hMatrixChernoff` can be discharged and removed from the signature. -/
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
      (1 - kappa))
    (hMatrixChernoff :
      1 - kappa / (1 - theta) - Real.exp (-((theta ^ (2 : ℕ)) * (k : Error)) / 2) ≤
        ev ψ (bernoulliTailOperator k degree X)) :
    ChernoffBernoulliMatrixStatement ψ theta k degree X kappa hXpsd hXleOne := by
  have htail := bernoulliTailOperator_le_one k degree X hXpsd hXleOne
  refine { tail_le_one := htail, matrixTailBound := ⟨?_⟩ }
  show _ ≥ _
  unfold subMeasMass
  exact hMatrixChernoff

end MIPStarRE.LDT.Pasting
