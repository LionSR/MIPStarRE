import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncation
import MIPStarRE.LDT.MakingMeasurementsProjective.Statements

/-!
# Section 9 — Spectral Truncation for Orthonormalization

This file records the useful spectral-truncation conversion needed when the
Section 9 helper output is later fed into the orthonormalization theorem.  The
paper input is the family `\widehat H` produced in
`references/ldt-paper/self_improvement.tex`; the spectral-truncation step is the
one isolated in `references/ldt-paper/orthonormalization.tex`:

* the **spectral-truncation** step (`lem:projective-non-measurement`) on the
  option-completed, left-lifted helper measurement.

This module deliberately does not expose a bundled `OrthonormalizationInput` or
a locality-preserving repair hypothesis.  The paper-facing self-improvement
theorem keeps the remaining orthonormalization construction as the tracked proof
gap in `selfImprovement`, rather than replacing it by an extra theorem
hypothesis.

## What this file provides

* `OrthonormalizationSpectralObligation` — the spectral slice of
  the Section 9 helper-output construction, isolated.
* `orthonormalizationSpectralObligation_of_roundingWitnesses` — narrows the
  spectral slice down to an obligation for `RoundingToProjectorsWitness`es for the
  option-completed left-lifted helper measurement, using the conversion
  introduced by `#1042`.
* `orthonormalizationSpectralObligation_of_projectiveNonMeasurement` — narrows
  the same slice to the named QXP-layer statement
  `projectiveNonMeasurement`, i.e. the Lean form of
  `lem:projective-non-measurement`.

## References

* `references/ldt-paper/orthonormalization.tex` line 414
  (`lem:projective-non-measurement`) for the spectral-truncation obligation.
* `references/ldt-paper/orthonormalization.tex` line 67
  (`thm:orthonormalization`) for the overall theorem this obligation feeds.
* `references/ldt-paper/self_improvement.tex` lines 679–697
  (helper output `\widehat{H}` is fed to `thm:orthonormalization`).
* The current source-facing self-improvement tracker #1515: the remaining
  orthonormalization construction is kept as a proof gap on the paper-facing
  theorem, with only the spectral-truncation conversion recorded here.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Spectral-truncation obligation -/

-- This obligation is `Type`-valued because spectral truncation carries
-- rounded-family data.

/-- Obligation for the **spectral-truncation** slice of
the Section 9 orthonormalization construction.

Paper origin: the projective-output passage in
`references/ldt-paper/self_improvement.tex:10-13`, using the
orthonormalization theorem from
`references/ldt-paper/orthonormalization.tex:273-282`.

For every helper sub-measurement `Hhat` satisfying the helper-stage bipartite
strong-self-consistency hypothesis (`BipartiteSSCRel ... ζ_helper`), this
yields the `SpectralTruncationInput` for the *option-completed* left-lifted
measurement `optionCompletion Hhat`, at error
`consistencyToAlmostProjectiveError (2 * ζ_helper)`.

This isolates only the spectral-truncation part of the construction; the
remaining locality-preserving repair is left inside the tracked proof gap for
the paper-facing theorem. -/
abbrev OrthonormalizationSpectralObligation
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (eps delta : Error) :=
  ∀ {Hhat : SubMeas (Polynomial params) ι},
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Hhat)
      (selfImprovementHelperError params eps delta) →
    SpectralTruncationInput strategy.state
      (leftLiftedMeasurement (ιB := ι) (optionCompletion Hhat))
      (consistencyToAlmostProjectiveError
        (2 * selfImprovementHelperError params eps delta))

/-! ### Spectral slice from per-`Hhat` rounding witnesses -/

/-- Build the spectral slice of the Section 9 orthonormalization construction from
an obligation for `RoundingToProjectorsWitness`es on the option-completed
left-lifted helper measurement.

This is the SelfImprovement-level analogue of `#1042`: it lifts the existing
field-for-field conversion `spectralTruncationStatement_of_witness` to the
quantification used by `OrthonormalizationSpectralObligation`.  The honest
mathematical content — actually building `R` — remains the caller's
responsibility, exactly as in `#1042`. -/
noncomputable def orthonormalizationSpectralObligation_of_roundingWitnesses
    {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι} {eps delta : Error}
    (hround : ∀ {Hhat : SubMeas (Polynomial params) ι},
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta) →
      Σ' R : OpFamily (Option (Polynomial params)) (ι × ι),
        RoundingToProjectorsWitness strategy.state
          (leftLiftedMeasurement (ιB := ι) (optionCompletion Hhat))
          (consistencyToAlmostProjectiveError
            (2 * selfImprovementHelperError params eps delta)) R) :
    OrthonormalizationSpectralObligation params strategy eps delta :=
  fun {Hhat} hssc =>
    let ⟨R, hR⟩ := hround hssc
    fun _hψ _halmostProj =>
      spectralTruncationStatement_of_witness strategy.state
        (leftLiftedMeasurement (ιB := ι) (optionCompletion Hhat))
        (consistencyToAlmostProjectiveError
          (2 * selfImprovementHelperError params eps delta))
        R hR

/-- Build the spectral slice of the Section 9 orthonormalization construction from
the named QXP-layer `projectiveNonMeasurement` statement.

Compared with `orthonormalizationSpectralObligation_of_roundingWitnesses`, this
version exposes the remaining constructive obligation at the paper-facing
statement `lem:projective-non-measurement` instead of asking callers to provide
the dependent pair of rounded-family data directly. -/
noncomputable def orthonormalizationSpectralObligation_of_projectiveNonMeasurement
    {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι} {eps delta : Error}
    (hprojective : ∀ {Hhat : SubMeas (Polynomial params) ι},
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta) →
      projectiveNonMeasurement strategy.state
        (leftLiftedMeasurement (ιB := ι) (optionCompletion Hhat))
        (consistencyToAlmostProjectiveError
          (2 * selfImprovementHelperError params eps delta))) :
    OrthonormalizationSpectralObligation params strategy eps delta :=
  fun {Hhat} hssc =>
    spectralTruncationInput_of_projectiveNonMeasurement strategy.state
      (leftLiftedMeasurement (ιB := ι) (optionCompletion Hhat))
      (consistencyToAlmostProjectiveError
        (2 * selfImprovementHelperError params eps delta))
      (hprojective hssc)

/-- Build the spectral slice of the Section 9 orthonormalization construction
directly from the constructive spectral-truncation theorem.

This construction records all three scalar branches needed for the paper-facing
statement `lem:projective-non-measurement`: the exact endpoint `ζ = 0`, the
nontrivial proof for `0 < ζ ≤ 1/4`, and the trivial large-error branch used in
the surrounding orthonormalization argument.  Callers therefore supply only the
source almost-projective defect through `SpectralTruncationInput`; the case
split is handled internally. -/
noncomputable def orthonormalizationSpectralObligation_of_sourceAlmostProjective
    {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι} {eps delta : Error} :
    OrthonormalizationSpectralObligation params strategy eps delta :=
  fun {Hhat} _hssc =>
    spectralTruncationInput_of_sourceAlmostProjective strategy.state
      (leftLiftedMeasurement (ιB := ι) (optionCompletion Hhat))
      (consistencyToAlmostProjectiveError
        (2 * selfImprovementHelperError params eps delta))

end MIPStarRE.LDT.SelfImprovement
