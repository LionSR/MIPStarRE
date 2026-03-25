import MIPStarRE.LDT.Preliminaries.Defs

/-!
# Section 4 — Measurement calculus propositions

Main propositions and supporting lemmas from Section 4 of the low
individual degree paper (`references/ldt-paper/preliminaries.tex`).

## Main results

* `simeqForMeasurements` — consistency ↔ agreement probability
* `simeqToApprox` — consistency → state-dependent distance (factor 2δ)
* `simeqDataProcessing` — post-processing preserves consistency

## Supporting lemmas (from the blueprint)

* `triangleInequalityForVectorsSquared` — ‖ψ₁+⋯+ψₖ‖² ≤ k(‖ψ₁‖²+⋯+‖ψₖ‖²)
* `triangleInequalityForApproxDelta` — triangle inequality for ≈_δ
* `closenessOfInnerProducts` — closeness of inner products under ≈_γ
* `triangleSub` — transferring consistency through state-dependent distance
* `simeqTriangleInequality` — triangle inequality for ≃_δ
-/

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-! ### Infrastructure lemmas for the main proofs -/

/-- State-dependent distance is bounded by twice the consistency error
for measurements.

Proof sketch: expand `‖(Aₐ ⊗ I − I ⊗ Bₐ)|ψ⟩‖²` using linearity of
expectation values. For measurements (`∑ Aₐ = I`), the total mass
is 1, so the squared distance decomposes as
`2(1 − diagonal overlap) ≤ 2 × off-diagonal mass`.

Requires: operator algebra infrastructure connecting the scaffold-level
`expectationValue` to the matrix-level PSD/measurement properties.
See `inconsistency_add_diagOverlap_eq_one` in `Quantum/Measurement.lean`
for the matrix-level counterpart. -/
theorem stateDependentDistanceError_le_two_mul_consistencyError
    {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedMeasurement Question Outcome) :
    stateDependentDistanceError ψ 𝒟
      (IndexedMeasurement.toIndexedSubMeasurement A)
      (IndexedMeasurement.toIndexedSubMeasurement B) ≤
    2 * consistencyError ψ 𝒟
      (IndexedMeasurement.toIndexedSubMeasurement A)
      (IndexedMeasurement.toIndexedSubMeasurement B) := by
  sorry

/-- Postprocessing does not increase consistency error.

Proof sketch: merging outcome classes via `f` can only decrease the
off-diagonal mass. A pair `(a, a')` with `a ≠ a'` but `f a = f a'`
moves from the off-diagonal sum to the diagonal overlap, strictly
reducing the defect. The total overlap is preserved because
`postprocess` does not change `totalOperator`.

Requires: positivity of cross-terms `⟨ψ| Aₐ Bₐ' |ψ⟩ ≥ 0` for
PSD operators and PSD states, which is not yet encoded at the
scaffold level. -/
theorem consistencyError_postprocess_le
    {Question α β : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question α) (f : α → β) :
    consistencyError ψ 𝒟
      (postprocessIndexedSubMeasurement A f)
      (postprocessIndexedSubMeasurement B f) ≤
    consistencyError ψ 𝒟 A B := by
  sorry

/-! ### Main theorems (Section 4 propositions) -/

/-- `prop:simeq-for-measurements`.

Consistency ↔ agreement probability for measurements. The
off-diagonal mass is at most δ if and only if the diagonal
overlap (agreement probability) is at least 1 − δ. This is
an immediate consequence of the definitions: `agreementProbability`
is defined as `1 − consistencyError`. -/
theorem simeqForMeasurements {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedMeasurement Question Outcome) (δ : Error) :
    consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement A)
        (IndexedMeasurement.toIndexedSubMeasurement B) δ ↔
      ConsistencyAsAgreement ψ 𝒟 A B δ := by
  unfold consistency
  constructor
  · intro ⟨h⟩
    exact ⟨by unfold agreementProbability; linarith⟩
  · intro ⟨h⟩
    exact ⟨by unfold agreementProbability at h; linarith⟩

/-- `prop:simeq-to-approx`.

Consistency implies state-dependent distance for measurements,
with a factor of 2. Uses
`stateDependentDistanceError_le_two_mul_consistencyError` as the
key bridge lemma. -/
theorem simeqToApprox {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedMeasurement Question Outcome) (δ : Error) :
    consistency ψ 𝒟 (IndexedMeasurement.toIndexedSubMeasurement A)
        (IndexedMeasurement.toIndexedSubMeasurement B) δ →
      bipartiteStateDependentDistance ψ 𝒟
        (IndexedMeasurement.toIndexedSubMeasurement A)
        (IndexedMeasurement.toIndexedSubMeasurement B)
        (2 * δ) := by
  unfold consistency bipartiteStateDependentDistance
  intro ⟨h⟩
  exact ⟨by linarith
    [stateDependentDistanceError_le_two_mul_consistencyError ψ 𝒟 A B]⟩

/-- `prop:simeq-data-processing`.

Post-processing preserves consistency: if `A ≃_δ B` and `f` is
a map on the answer set, then `A_f ≃_δ B_f`. Uses
`consistencyError_postprocess_le` as the key monotonicity lemma. -/
theorem simeqDataProcessing {Question α β : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question α) (δ : Error) (f : α → β) :
    consistency ψ 𝒟 A B δ →
      consistency ψ 𝒟
        (postprocessIndexedSubMeasurement A f)
        (postprocessIndexedSubMeasurement B f) δ := by
  unfold consistency
  intro ⟨h⟩
  exact ⟨le_trans (consistencyError_postprocess_le ψ 𝒟 A B f) h⟩

/-- `prop:cons-sub-meas`. -/
theorem consSubMeas {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome)
    (B : IndexedMeasurement Question Outcome) (γ : Error) :
    consistency ψ 𝒟 A (IndexedMeasurement.toIndexedSubMeasurement B) γ →
      ConsSubMeasStatement ψ 𝒟 A B γ := by
  sorry

/-- `prop:switch-sandwich`. -/
theorem switchSandwich {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedProjectiveSubMeasurement Question Outcome)
    (B : Operator) (_hB : OperatorBetweenZeroAndOne B) (δ : Error) :
    bipartiteStateDependentDistance ψ 𝒟
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement A)
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement A) δ →
      SwitchSandwichStatement ψ 𝒟 A B δ := by
  sorry

/-- `prop:completeness-transfer-projective-P`. -/
theorem completenessTransferProjectiveP {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome)
    (P : IndexedProjectiveSubMeasurement Question Outcome) (ε : Error) :
    stateDependentDistance ψ 𝒟 A
        (IndexedProjectiveSubMeasurement.toIndexedSubMeasurement P) ε →
      CompletenessTransferProjectivePStatement ψ 𝒟 A P ε := by
  sorry

/-- `prop:two-notions-of-self-consistency`. -/
theorem twoNotionsOfSelfConsistency {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A : IndexedSubMeasurement Question Outcome) (δ : Error) :
    strongSelfConsistency ψ 𝒟 A δ →
      bipartiteStateDependentDistance ψ 𝒟 A A (2 * δ) := by
  sorry

/-- `prop:completing-to-measurement`. -/
theorem completingToMeasurement {Outcome : Type*}
    (ψ : QuantumState)
    (A : Measurement Outcome) (B : SubMeasurement Outcome)
    (a0 : Outcome) (δ ζ : Error) :
    strongSelfConsistency ψ (uniformDistribution Unit)
        (constantSubMeasurementFamily A.toSubMeasurement) ζ →
      stateDependentDistance ψ (uniformDistribution Unit)
        (constantSubMeasurementFamily A.toSubMeasurement)
        (constantSubMeasurementFamily B) δ →
      ∃ C : Measurement Outcome,
        CompletingToMeasurementStatement ψ A B C a0 δ ζ := by
  sorry

/-! ### Supporting lemmas from the blueprint (Section 4 preliminaries)

These lemmas appear in `blueprint/src/chapter/ch03_preliminaries.tex` and
provide the combinatorial and analytic backbone for the measurement
calculus. They are stated at the scaffold level; full proofs require
the operator algebra bridge to the matrix layer in `Quantum/`. -/

/-- `prop:triangle-inequality-for-vectors-squared`.

For nonnegative reals, `(x₁ + ⋯ + xₖ)² ≤ k · (x₁² + ⋯ + xₖ²)`.
This is the scalar backbone of the vector norm triangle inequality
`‖ψ₁ + ⋯ + ψₖ‖² ≤ k · (‖ψ₁‖² + ⋯ + ‖ψₖ‖²)`.

Proof: by Cauchy–Schwarz, `(∑ 1·xᵢ)² ≤ (∑ 1²)(∑ xᵢ²) = k · ∑ xᵢ²`. -/
theorem triangleInequalityForVectorsSquared {k : ℕ}
    (xs : Fin k → ℝ) (hx : ∀ i, 0 ≤ xs i) :
    (∑ i, xs i) ^ 2 ≤ ↑k * ∑ i, xs i ^ 2 := by
  sorry

/-- `prop:triangle-inequality-for-approx_delta`.

If `A ≈_{δ₁} B` and `B ≈_{δ₂} C`, then `A ≈_{2·(δ₁+δ₂)} C`.

More generally, for a chain `Aᵢ ≈_{δᵢ} Aᵢ₊₁` of length `k`,
`A₁ ≈_{k·(δ₁+⋯+δₖ)} Aₖ₊₁`.

Proof: expand `(A₁ − Aₖ₊₁)|ψ⟩` as a telescoping sum and apply
`triangleInequalityForVectorsSquared`. -/
theorem triangleInequalityForApproxDelta
    {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B C : IndexedSubMeasurement Question Outcome)
    (δ₁ δ₂ : Error) :
    stateDependentDistance ψ 𝒟 A B δ₁ →
    stateDependentDistance ψ 𝒟 B C δ₂ →
    stateDependentDistance ψ 𝒟 A C (2 * (δ₁ + δ₂)) := by
  sorry

/-- `prop:closeness-of-ip`.

If `A ≈_γ B` and `{Cₐ,ᵦ}` satisfies
`∑ₐ (∑ᵦ Cₐ,ᵦ)(∑ᵦ Cₐ,ᵦ)† ≤ I` for every `x`, then the averaged
inner products `𝔼ₓ ∑ₐ,ᵦ ⟨ψ|Cₐ,ᵦ Aₐ|ψ⟩` and
`𝔼ₓ ∑ₐ,ᵦ ⟨ψ|Cₐ,ᵦ Bₐ|ψ⟩` differ by at most `√γ`.

Proof: Cauchy–Schwarz applied to the difference, using the
normalization hypothesis on the `Cₐ,ᵦ`.

Note: the full statement requires tensor product and multi-indexed
operator families not yet available at the scaffold level. The type
signature below captures the conclusion; the normalization hypothesis
on `C` is a placeholder pending the tensor product API. -/
theorem closenessOfInnerProducts {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedSubMeasurement Question Outcome) (γ : Error)
    (hAB : stateDependentDistance ψ 𝒟 A B γ)
    (hγ : 0 ≤ γ)
    (evA evB : Error)
    (_hNormC : True) -- placeholder for C normalization
    (_hEvDiff : True) :  -- placeholder for ev computation
    |evA - evB| ≤ Real.sqrt γ := by
  sorry

/-- `prop:triangle-sub`.

Transferring consistency through state-dependent distance:
if `A ≃_δ C` and `A ≈_ε B` (where `A`, `B` are measurements),
then `B ≃_{δ + √ε} C`.

Proof: rewrite the inconsistency of `B` with `C` as total mass
minus diagonal overlap. The total mass is unchanged because `A`
and `B` are measurements, and the diagonal overlap changes by at
most `√ε` by Cauchy–Schwarz. -/
theorem triangleSub {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B : IndexedMeasurement Question Outcome)
    (C : IndexedSubMeasurement Question Outcome) (δ ε : Error) :
    consistency ψ 𝒟
      (IndexedMeasurement.toIndexedSubMeasurement A) C δ →
    stateDependentDistance ψ 𝒟
      (IndexedMeasurement.toIndexedSubMeasurement A)
      (IndexedMeasurement.toIndexedSubMeasurement B) ε →
    consistency ψ 𝒟
      (IndexedMeasurement.toIndexedSubMeasurement B) C
      (δ + Real.sqrt ε) := by
  sorry

/-- `prop:simeq-triangle-inequality`.

If `A ≃_ε B`, `C ≃_δ B`, and `C ≃_γ D` (all measurements), then
`A ≃_{ε + 2√(δ+γ)} D`.

Proof: convert the two consistencies involving `C` to state-dependent
distance via `simeqToApprox`, compose them by
`triangleInequalityForApproxDelta`, and transfer the result back
to consistency via `triangleSub`. -/
theorem simeqTriangleInequality {Question Outcome : Type*}
    (ψ : QuantumState) (𝒟 : Distribution Question)
    (A B C D : IndexedMeasurement Question Outcome)
    (ε δ γ : Error) :
    consistency ψ 𝒟
      (IndexedMeasurement.toIndexedSubMeasurement A)
      (IndexedMeasurement.toIndexedSubMeasurement B) ε →
    consistency ψ 𝒟
      (IndexedMeasurement.toIndexedSubMeasurement C)
      (IndexedMeasurement.toIndexedSubMeasurement B) δ →
    consistency ψ 𝒟
      (IndexedMeasurement.toIndexedSubMeasurement C)
      (IndexedMeasurement.toIndexedSubMeasurement D) γ →
    consistency ψ 𝒟
      (IndexedMeasurement.toIndexedSubMeasurement A)
      (IndexedMeasurement.toIndexedSubMeasurement D)
      (ε + 2 * Real.sqrt (δ + γ)) := by
  sorry

end MIPStarRE.LDT.Preliminaries
