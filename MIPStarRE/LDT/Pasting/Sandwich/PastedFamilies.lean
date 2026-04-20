import MIPStarRE.LDT.Pasting.Sandwich.GHatSandwich

/-!
# Section 12 — Sandwich constructions: pasted families

Pasted interpolation families, recurrence weights, and final operator families.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Source-style recurrence weight `S_{τtail}` from `lem:from-H-to-G`.

The parameter `prefixLen` is the number of type bits already converted into the
Bernoulli polynomial.  This is exactly `truncatedTypeSums` specialized to the
averaged complete operator `G = E_x ∑_g G^x_g`. -/
noncomputable def fromHToGRecurrenceWeight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (prefixLen : ℕ) {tailLen : ℕ}
    (τtail : GHatType tailLen) : MIPStarRE.Quantum.Op ι :=
  truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail

/-- The suffix-specialized recurrence weight used by the `fromHToG` families.

Semantics/indexing fix: the previous grouped Bernoulli encoding
`∑_r C(ℓ-1, r) G^r (I-G)^(ℓ-1-r)` interpreted `ℓ` as the paper's 1-indexed
prefix length, whereas the callers (`FromHToGStatement.recurrenceStep` uses
`∀ ℓ < k`) and the rest of `Pasting/` treat `ℓ` as 0-indexed — the off-by-one
produced a binomial of degree `ℓ - 1` instead of the paper's
`\binom{\ell}{r}` (see `references/ldt-paper/ld-pasting.tex` eq. (S-def)).
The new definition uses `truncatedTypeSums` at `prefixLen = ℓ`, which sums
over `GHatType ℓ` and matches both the 0-indexed convention and the proved
recurrence in `truncatedTypeSumRecurrence`.  The index `ℓ` is zero-based:
the suffix is `τ_{≥ℓ}` and the prefix has length `ℓ`. -/
noncomputable def suffixBernoulliWeightOperator (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) (τ : GHatType k) : MIPStarRE.Quantum.Op ι :=
  fromHToGRecurrenceWeight params family ℓ (gHatTypeSuffix ℓ τ)

/-- Definitional bridge from the suffix API to the proved truncated-sum API.

Not tagged `@[simp]`: eager unfolding would eliminate every mention of the
named `suffixBernoulliWeightOperator` abstraction and leak the
`gHatTypeSuffix` wrapper into downstream goals.  Call sites that need the
expansion should use `unfold` or `show` explicitly. -/
lemma suffixBernoulliWeightOperator_eq_truncatedTypeSums
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) (τ : GHatType k) :
    suffixBernoulliWeightOperator params family k ℓ τ =
      truncatedTypeSums family.averagedSubMeas.total params.d ℓ (gHatTypeSuffix ℓ τ) := by
  rfl

/-- The interpolated operator `H^{x_1,\dots,x_k}_h` restricted to tuples that are
globally consistent with a single polynomial.

The paper's definition (`references/ldt-paper/ld-pasting.tex` lines 474–495) sums
only tuples `(g_1,…,g_k)` in `Global_τ(x)` — those consistent with a single
polynomial `h` — and then interpolates.  The `|τ| ≥ d+1` eligibility filter is
applied by `interpolationEligibleSandwichFamily`; this definition additionally
restricts to globally consistent tuples via `IsGloballyConsistent`. -/
noncomputable def pastedInterpolationFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (Polynomial params.next) ι :=
  fun xs =>
    postprocess
      (restrictSubMeas
        (interpolationEligibleSandwichFamily params family k xs)
        (IsGloballyConsistent params xs))
      (interpolateCompletedSlices params k xs)

/-- The averaged sandwiched family restricted to outcome tuples of type `τ`
with `|τ| ≥ d+1`, as in `lem:over-all-outcomes`. -/
noncomputable def averagedEligibleSandwichSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    SubMeas (GHatTupleOutcome params k) ι :=
  averageIdxSubMeas
    (distinctTupleDistribution params k)
    (interpolationEligibleSandwichFamily params family k)
    (distinctTupleDistribution_weight_sum_le_one params k)

/-- The specific pasted submeasurement constructed from the sandwich/interpolation scheme. -/
noncomputable def constructedPastedSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) : SubMeas (Polynomial params.next) ι :=
  averageIdxSubMeas
    (distinctTupleDistribution params k)
    (pastedInterpolationFamily params family k)
    (distinctTupleDistribution_weight_sum_le_one params k)

/-- The distinguished fallback polynomial `h₀` that receives the completion mass. -/
noncomputable def pastedFallbackOutcome (params : Parameters) [FieldModel params.q] :
    Polynomial params.next :=
  fallbackInterpolatedPolynomial params

/-- The specific pasted measurement obtained by completing the constructed pasted submeasurement.

The paper adds all missing mass `I - H_total` to a single distinguished polynomial
outcome `h₀` (the fallback interpolant).  So the outcome operator for `h₀` becomes
`H_{h₀} + (I - H_total)` while all other outcomes keep their original operators, and
the total is genuinely the identity `I`. -/
noncomputable def constructedPastedMeasurement (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) : Measurement (Polynomial params.next) ι :=
  Preliminaries.completeAtOutcome
    (constructedPastedSubMeas params family k)
    (pastedFallbackOutcome params)

/-- Placeholder family for the vertical axis-parallel line measurement `B^u_f`. -/
noncomputable def verticalLineMeasurementFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxSubMeas (VerticalLineQuestion params) (AxisLinePolynomial params.next) ι :=
  fun u =>
    let ℓ : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := lastCoord params }
    (strategy.axisParallelMeasurement ℓ).toSubMeas

/-- Explicit value extracted from the `i`-th completed slice outcome at the test point. -/
noncomputable def ldSandwichLineOnePointLeftFamily (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
  fun q =>
    postprocess (gHatSandwichFamily params family k q.2) (fun gs =>
      if h : i < k then
        Option.map (fun g => g q.1) (gs ⟨i, h⟩)
      else
        none)

/-- Explicit value extracted from the vertical line measurement `B^u` at the slice height `x_i`. -/
noncomputable def ldSandwichLineOnePointRightFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (_family : IdxPolyFamily params ι)
    (k i : ℕ) : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
  fun q =>
    postprocess (verticalLineMeasurementFamily params strategy q.1) (fun f =>
      if h : i < k then
        some (f (q.2 ⟨i, h⟩))
      else
        none)

/-- Restrict a global polynomial-valued submeasurement to the vertical line through `u`. -/
noncomputable def hRestrictionToVerticalLine (params : Parameters) [FieldModel params.q]
    (H : SubMeas (Polynomial params.next) ι) :
    IdxSubMeas (VerticalLineQuestion params) (AxisLinePolynomial params.next) ι :=
  fun u =>
    let verticalLine : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := ⟨params.m, Nat.lt_succ_self params.m⟩ }
    postprocess H (fun h => Polynomial.restrictToAxisParallelLine params.next h verticalLine)

/-- Collapse a submeasurement to its `Unit`-valued total operator. -/
noncomputable def pastedMeasurementTotal
    {α : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (H : SubMeas α ι) : IdxSubMeas Unit Unit ι :=
  constSubMeasFamily (postprocess H (fun _ => ()))

/-- The total operator of the specifically constructed pasted submeasurement. -/
noncomputable def constructedPastedMeasurementTotal (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas Unit Unit ι :=
  pastedMeasurementTotal (constructedPastedSubMeas params family k)

/-- The expansion over all outcome types `τ`, written as the
total mass of the averaged sandwich family restricted to `|τ| ≥ d+1`. -/
noncomputable def allOutcomesExpansionFamily (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas Unit Unit ι :=
  pastedMeasurementTotal (averagedEligibleSandwichSubMeas params family k)

/-- The Bernoulli-tail polynomial in the averaged complete operator `G = E_x \sum_g G^x_g`. -/
noncomputable def bernoulliTailFromFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas Unit Unit ι :=
  constSubMeasFamily <|
    let Y := bernoulliTailOperator k params.d ((IdxPolyFamily.averagedSubMeas family).total)
    { outcome := fun _ => Y
      total := Y
      outcome_pos := by
        intro _
        let G := (IdxPolyFamily.averagedSubMeas family).total
        have hG : 0 ≤ G := (IdxPolyFamily.averagedSubMeas family).total_nonneg
        have hGle : G ≤ 1 := (IdxPolyFamily.averagedSubMeas family).total_le_one
        simpa [G] using bernoulliTailOperator_nonneg k params.d G hG hGle
      sum_eq_total := by
        simp
      total_le_one := by
        let G := (IdxPolyFamily.averagedSubMeas family).total
        have hG : 0 ≤ G := (IdxPolyFamily.averagedSubMeas family).total_nonneg
        have hGle : G ≤ 1 := (IdxPolyFamily.averagedSubMeas family).total_le_one
        simpa [Y, G] using bernoulliTailOperator_le_one k params.d G hG hGle }

/-- The suffix-indexed `\widehat H` family from the `fromHToG` recurrence.

For a fixed full type `τ ∈ {0,1}^k` and a prefix length `prefixLen`, this is the
paper's average `\E_{x_{≥ prefixLen}} \sum_{g_{≥ prefixLen} ∈ O_{τ_{≥ prefixLen}}}
\widehat H^{x_{≥ prefixLen}}_{g_{≥ prefixLen}}`, represented as a submeasurement on
the remaining completed-slice tuples. -/
noncomputable def fromHToGRecurrenceSuffixHSubMeas (params : Parameters)
    [FieldModel params.q] (family : IdxPolyFamily params ι) (k prefixLen : ℕ)
    (τ : GHatType k) :
    SubMeas (GHatTupleOutcome params (k - prefixLen)) ι :=
  averageIdxSubMeas
    (distinctTupleDistribution params (k - prefixLen))
    (fun xs =>
      open Classical in
        restrictSubMeas
          (gHatSandwichFamily params family (k - prefixLen) xs)
          (outcomesByType (gHatTypeSuffix prefixLen τ)))
    (distinctTupleDistribution_weight_sum_le_one params (k - prefixLen))

/-- Core recurrence family for `lem:from-H-to-G` at a fixed prefix length.

This packages the paper-faithful product
`\E_{x_{≥ prefixLen}} \sum_{g_{≥ prefixLen} ∈ O_{τ_{≥ prefixLen}}}
\widehat H^{x_{≥ prefixLen}}_{g_{≥ prefixLen}} \ot S_{τ_{≥ prefixLen}}`
as a `Unit`-indexed raw operator family, keeping the theorem surface unchanged
while exposing the correct suffix-level `\widehat H` data underneath. -/
noncomputable def fromHToGRecurrenceSuffixFamily (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k prefixLen : ℕ)
    (τ : GHatType k) :
    IdxOpFamily Unit Unit ι :=
  fun _ =>
    let hSuffix := fromHToGRecurrenceSuffixHSubMeas params family k prefixLen τ
    let weight := suffixBernoulliWeightOperator params family k prefixLen τ
    { outcome := fun _ => hSuffix.total * weight
      total := hSuffix.total * weight }

/-- One recurrence-step left-hand family from the proof of `lem:from-H-to-G`,
parameterised by the suffix type `τ ∈ {0,1}^k`.

For each step `ℓ`, the paper (`references/ldt-paper/ld-pasting.tex` lines 1380–1425)
forms the product `Ĥ^{x_{≥ℓ}}_{g_{≥ℓ}} ⊗ S_{τ_{≥ℓ}}` where `S_{τ_{≥ℓ}}` is the
Bernoulli weight operator depending on the suffix type `τ`. -/
noncomputable def fromHToGRecurrenceLeftFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ)
    (τ : GHatType k) :
    IdxOpFamily Unit Unit ι :=
  fromHToGRecurrenceSuffixFamily params strategy family k ℓ τ

/-- One recurrence-step right-hand family from the proof of `lem:from-H-to-G`,
parameterised by the suffix type `τ ∈ {0,1}^k`.

Mirror of `fromHToGRecurrenceLeftFamily` on the Bernoulli-tail side.
See `references/ldt-paper/ld-pasting.tex` lines 1380–1425. -/
noncomputable def fromHToGRecurrenceRightFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ)
    (τ : GHatType k) :
    IdxOpFamily Unit Unit ι :=
  fromHToGRecurrenceSuffixFamily params strategy family k (ℓ + 1) τ

end MIPStarRE.LDT.Pasting
