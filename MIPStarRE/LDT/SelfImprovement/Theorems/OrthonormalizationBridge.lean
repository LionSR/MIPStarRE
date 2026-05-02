import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncation

/-!
# Section 9 — `OrthonormalizationInput` producer bridge

This file provides a *narrowed* constructor for the
`SelfImprovement.OrthonormalizationInput` requirement of the reduced
self-improvement theorem (`Theorems/Results.lean`), splitting it into the two
paper-faithful pieces from `references/ldt-paper/orthonormalization.tex`:

* the **spectral-truncation** step (`lem:projective-non-measurement`) on the
  option-completed, left-lifted helper measurement, and
* the **locality-preserving repair** step on the option-completed helper
  measurement.

The split mirrors `MakingMeasurementsProjective.OrthonormalizationInput`, which
is itself the structure left after `orthonormalizationMainLemma_local` was
proved internally.  At present the spectral and repair pieces are still the
opaque external inputs called out by the `#931` blocker; this bridge does *not*
discharge them, but it lets a downstream caller close `OrthonormalizationInput`
by independently supplying the two pieces.

In addition, `orthonormalizationSpectralProducer_of_roundingWitnesses` plumbs
the existing spectral-truncation conversion landed by `#1042`
(`spectralTruncationStatement_of_witness`) all the way to the SelfImprovement
producer.  Together with a separate locality-preserving repair producer, this
gives a path to closing `SelfImprovement.OrthonormalizationInput` from the
honest QXP-layer rounding witnesses without restating the full input as an
extra assumption.

## What this file provides

* `OrthonormalizationSpectralProducer` — the spectral slice of
  `SelfImprovement.OrthonormalizationInput`, isolated.
* `OrthonormalizationRepairProducer` — the locality-preserving repair slice.
* `orthonormalizationInput_of_producers` — combines the two slices into the
  full `SelfImprovement.OrthonormalizationInput`.
* `orthonormalizationSpectralProducer_of_roundingWitnesses` — narrows the
  spectral slice down to a producer of `RoundingToProjectorsWitness`es for the
  option-completed left-lifted helper measurement, using the conversion
  introduced by `#1042`.

## References

* `references/ldt-paper/orthonormalization.tex` line 414
  (`lem:projective-non-measurement`) for the spectral-truncation producer.
* `references/ldt-paper/orthonormalization.tex` lines 270–310 and line 547
  (`lem:projective-low-rank-sum`) for the option-completion reduction and
  rounded sub-measurement repair.
* `references/ldt-paper/orthonormalization.tex` line 67
  (`thm:orthonormalization`) for the overall theorem this bridge feeds.
* `references/ldt-paper/self_improvement.tex` lines 679–697
  (helper output `\widehat{H}` is fed to `thm:orthonormalization`).
* Issue `#931`, comment by `claude` (2026-05-02): the orthonormalization
  producer reduces to the two constructive Section 5 witnesses on
  `optionCompletion Hhat`.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Spectral and repair slice producers -/

-- The spectral producer is `Type`-valued because spectral truncation carries
-- rounded-family data, while the repair producer is proposition-valued.

/-- Producer of the **spectral-truncation** slice of
`SelfImprovement.OrthonormalizationInput`.

For every helper sub-measurement `Hhat` satisfying the helper-stage bipartite
strong-self-consistency hypothesis (`BipartiteSSCRel ... ζ_helper`), this
yields the `SpectralTruncationInput` for the *option-completed* left-lifted
measurement `optionCompletion Hhat`, at error
`consistencyToAlmostProjectiveError (2 * ζ_helper)`.

This isolates the `spectral` field of
`MakingMeasurementsProjective.OrthonormalizationInput`. -/
abbrev OrthonormalizationSpectralProducer
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

/-- Producer of the **locality-preserving repair** slice of
`SelfImprovement.OrthonormalizationInput`.

For every helper sub-measurement `Hhat` satisfying the helper-stage bipartite
strong-self-consistency hypothesis, this yields the
`LeftLiftedProjectivizationRepairInput` for `optionCompletion Hhat` at error
`consistencyToAlmostProjectiveError (2 * ζ_helper)`. -/
abbrev OrthonormalizationRepairProducer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (eps delta : Error) : Prop :=
  ∀ {Hhat : SubMeas (Polynomial params) ι},
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Hhat)
      (selfImprovementHelperError params eps delta) →
    LeftLiftedProjectivizationRepairInput strategy.state
      (optionCompletion Hhat)
      (consistencyToAlmostProjectiveError
        (2 * selfImprovementHelperError params eps delta))

/-! ### Combining slice producers -/

/-- Combine the spectral and repair slice producers into a full
`SelfImprovement.OrthonormalizationInput`.

This is the narrowed bridge advertised by issue `#931`: it converts two
independent paper-faithful slice producers into the bundled input that the
reduced self-improvement theorem expects.  No mathematical content is added or
discharged here; the bridge is structural. -/
def orthonormalizationInput_of_producers
    {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι} {eps delta : Error}
    (hspectral : OrthonormalizationSpectralProducer params strategy eps delta)
    (hrepair : OrthonormalizationRepairProducer params strategy eps delta) :
    OrthonormalizationInput params strategy eps delta :=
  fun {_Hhat} hssc =>
    { spectral := hspectral hssc
      repair := hrepair hssc }

/-! ### Spectral slice from per-`Hhat` rounding witnesses -/

/-- Build the spectral slice of `SelfImprovement.OrthonormalizationInput` from
a producer of `RoundingToProjectorsWitness`es on the option-completed
left-lifted helper measurement.

This is the SelfImprovement-level analogue of `#1042`: it lifts the existing
field-for-field conversion `spectralTruncationStatement_of_witness` to the
quantification used by `OrthonormalizationSpectralProducer`.  The honest
mathematical content — actually building `R` — remains the caller's
responsibility, exactly as in `#1042`.  Combined with
`orthonormalizationInput_of_producers` and a separate repair producer, this
turns a `RoundingToProjectorsWitness` producer into the full
`SelfImprovement.OrthonormalizationInput`. -/
noncomputable def orthonormalizationSpectralProducer_of_roundingWitnesses
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
    OrthonormalizationSpectralProducer params strategy eps delta :=
  fun {Hhat} hssc =>
    let ⟨R, hR⟩ := hround hssc
    fun _hψ _halmostProj =>
      spectralTruncationStatement_of_witness strategy.state
        (leftLiftedMeasurement (ιB := ι) (optionCompletion Hhat))
        (consistencyToAlmostProjectiveError
          (2 * selfImprovementHelperError params eps delta))
        R hR

end MIPStarRE.LDT.SelfImprovement
