import MIPStarRE.LDT.Pasting.Bernoulli.TruncatedSums

set_option linter.style.setOption false
set_option linter.unusedVariables false

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

The bipartite state in the goal `FromHToGStatement` and in the recurrence
hypothesis `hhalf` is taken to be `strategy.state` directly, matching the
paper's identification of `\ket{\psi_{\mathrm{bi}}}` with the symmetric
strategy's bipartite state (both are typed `QuantumState (ι × ι)` since
`SymStrat.state` is itself bipartite — see
`MIPStarRE/LDT/Test/Strategy.lean:75`). This keeps the Lean signature in
lockstep with the blueprint statement (`blueprint/src/chapter/ch09_pasting.tex:887–903`)
and lets `hself`/`hcons`/`hbound`, which are phrased over `strategy.state`,
be reused without an equality bridge. -/
lemma fromHToG
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hhalf : CommuteGHalfSandwichStatement params strategy.state family gamma zeta k) :
    FromHToGStatement params strategy strategy.state family gamma zeta k := by
  constructor -- FromHToGStatement
  · -- recurrenceStep: per-step Bernoulli-tail commutation
    intro ℓ hℓ τ
    constructor -- SDDOpRel
    /- Inductive step ℓ of the Bernoulli-tail recurrence (ld-pasting.tex
    lines 1346–1666). Three commutation sub-steps per induction step:
    (a) move rightmost Ĝ^{x_ℓ} to 2nd tensor factor (√(2ζ)),
    (b) commute leftmost Ĝ past remaining factors (√ν₄),
    (c) move leftmost to 2nd tensor factor (√(2ζ)).
    Per-step error: 2√(2ζ) + 2√ν₄ = fromHToGRecurrenceError. -/
    /- Remaining obstruction after the issue #395 refactor:
    `fromHToGRecurrenceLeftFamily` / `fromHToGRecurrenceRightFamily` now carry
    the correct suffix-stage operators
    `E_{x_{≥ℓ}} ∑_{g_{≥ℓ} ∈ Outcomes_{τ_{≥ℓ}}} Ĥ^{x_{≥ℓ}}_{g_{≥ℓ}} ⊗ S_{τ_{≥ℓ}}`
    and `E_{x_{>ℓ}} ∑_{g_{>ℓ} ∈ Outcomes_{τ_{>ℓ}}} Ĥ^{x_{>ℓ}}_{g_{>ℓ}} ⊗ S_{τ_{>ℓ}}`,
    with `RightFamily ℓ = LeftFamily (ℓ + 1)` by `rfl`. What is still missing is
    the bridge from these averaged/type-restricted suffix families to the
    existing commutation infrastructure: the proof needs (1) a suffix-length
    specialization of `hhalf` (or a strengthened hypothesis `∀ j ≤ k, ... j`),
    and (2) helper lemmas unpacking one stage into the paper's three substeps
    move-right / commute / move-right so that `cor:G-hat-facts` supplies the two
    `√(2ζ)` terms and `hhalf` supplies the `√ν₄` term via `sddOpRel_mono` /
    `sddOpRel_trans`. -/
    sorry
  · -- bernoulliPolynomialRewrite: aggregate k recurrence steps
    constructor -- SDDRel
    /- Aggregate the `k` recurrence steps to show all-outcomes expansion
    `≈ F(G)`. The family refactor now gives the required telescoping identity
    `RightFamily ℓ = LeftFamily (ℓ + 1)`, but two endpoint bridges are still
    missing: stage `0` must be identified with `allOutcomesExpansionFamily`, and
    stage `k` with `bernoulliTailFromFamily` via the `truncatedTypeSums`
    polynomial. After those endpoint lemmas are formalized, `sddOpRel_chain`
    plus summation over the full types `τ : GHatType k` should close this field
    with total error `k * fromHToGRecurrenceError ≤ fromHToGError`. -/
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
