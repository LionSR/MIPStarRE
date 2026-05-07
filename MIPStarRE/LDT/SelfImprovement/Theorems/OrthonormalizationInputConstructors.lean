import MIPStarRE.LDT.SelfImprovement.Theorems.OrthonormalizationBridge

/-!
# Section 9 — Orthonormalization input constructors

This file contains the final constructor forms built from the spectral and
repair producers in `OrthonormalizationBridge.lean`.

## References

- `references/ldt-paper/orthonormalization.tex`
- `references/ldt-paper/self_improvement.tex`
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Build `SelfImprovement.OrthonormalizationInput` from the constructive
spectral-truncation theorem and a QXP-layer repair producer.

The spectral slice is supplied by
`orthonormalizationSpectralProducer_of_sourceAlmostProjective`; the remaining
caller obligation is therefore only the locality-preserving QXP repair
producer. -/
noncomputable def orthonormalizationInput_of_sourceAlmostProjectiveAndQXPLayerRepair
    {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι} {eps delta : Error}
    (hqxp : OrthonormalizationQXPLayerRepairProducer params strategy eps delta) :
    OrthonormalizationInput params strategy eps delta :=
  orthonormalizationInput_of_producers
    orthonormalizationSpectralProducer_of_sourceAlmostProjective
    (orthonormalizationRepairProducer_of_qxpLayer hqxp)

/-- Build the residual-domination orthonormalization input from the constructive
spectral-truncation theorem and a residual-dominating QXP repair producer.

This is the monotone-total analogue of
`orthonormalizationInput_of_sourceAlmostProjectiveAndQXPLayerRepair`: after the
spectral slice has been discharged by the source almost-projective theorem, the
only remaining orthonormalization input is the QXP repair together with
domination of the fresh residual outcome. -/
noncomputable def
    orthonormalizationResidualDominationInput_of_sourceAlmostProjectiveAndQXPLayerRepair
    {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι} {eps delta : Error}
    (hqxp :
      OrthonormalizationQXPLayerRepairProducerWithResidualDomination
        params strategy eps delta) :
    OrthonormalizationResidualDominationInput params strategy eps delta :=
  orthonormalizationResidualDominationInput_of_producers
    orthonormalizationSpectralProducer_of_sourceAlmostProjective
    hqxp

/-- Build the residual-domination orthonormalization input from an ordinary QXP
repair producer and a separate residual-domination proof for the same canonical
QXP layer.

This is useful when the `P`-versus-`Q` approximation and the fresh-outcome
operator inequality are established by different parts of the construction. -/
noncomputable def
    orthonormalizationResidualDominationInput_of_sourceQXPRepairAndResidualDomination
    {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι} {eps delta : Error}
    (hqxp : OrthonormalizationQXPLayerRepairProducer params strategy eps delta)
    (hdom : ∀ {Hhat : SubMeas (Polynomial params) ι}
      (hssc : BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
      (hSpectral : SpectralTruncationStatement strategy.state
        (leftLiftedMeasurement (ιB := ι) (optionCompletion Hhat))
        (consistencyToAlmostProjectiveError
          (2 * selfImprovementHelperError params eps delta))),
        QXPLayerResidualDomination (hqxp hssc hSpectral).data Hhat) :
    OrthonormalizationResidualDominationInput params strategy eps delta :=
  orthonormalizationResidualDominationInput_of_sourceAlmostProjectiveAndQXPLayerRepair
    (residualDominatingRepairProducer_of_qxpLayer_and_residualDomination hqxp hdom)

/-- Build `SelfImprovement.OrthonormalizationInput` from the two constructive
Section 5 witness producers exposed by the current formalization:

* per-helper rounding witnesses, which supply the spectral-truncation slice;
* per-helper QXP-layer repair witnesses, whose canonical projective family is
  a left lift of a local `ProjSubMeas`.

The remaining mathematical content is exactly the construction of those two
witness producers; this theorem only composes the already-formalized
conversions. -/
noncomputable def orthonormalizationInput_of_roundingAndQXPLayerRepair
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
            (2 * selfImprovementHelperError params eps delta)) R)
    (hqxp : OrthonormalizationQXPLayerRepairProducer params strategy eps delta) :
    OrthonormalizationInput params strategy eps delta :=
  orthonormalizationInput_of_producers
    (orthonormalizationSpectralProducer_of_roundingWitnesses hround)
    (orthonormalizationRepairProducer_of_qxpLayer hqxp)

/-- Build the strengthened residual-domination orthonormalization input from
the same spectral rounding witnesses as the ordinary constructor, together
with a QXP-layer repair producer that also proves domination of the completed
residual outcome. -/
noncomputable def
    orthonormalizationResidualDominationInput_of_roundingAndQXPLayerRepair
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
            (2 * selfImprovementHelperError params eps delta)) R)
    (hqxp :
      OrthonormalizationQXPLayerRepairProducerWithResidualDomination
        params strategy eps delta) :
    OrthonormalizationResidualDominationInput params strategy eps delta :=
  orthonormalizationResidualDominationInput_of_producers
    (orthonormalizationSpectralProducer_of_roundingWitnesses hround)
    hqxp

/-- Build the strengthened residual-domination orthonormalization input from
ordinary QXP repair witnesses together with a separate proof that each
canonical QXP repair dominates the completed residual outcome.

This constructor is useful when the `P`-versus-`Q` approximation and the
residual outcome inequality are proved by different arguments. -/
noncomputable def
    orthonormalizationResidualDominationInput_of_roundingAndQXPLayerRepairAndResidualDomination
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
            (2 * selfImprovementHelperError params eps delta)) R)
    (hqxp : OrthonormalizationQXPLayerRepairProducer params strategy eps delta)
    (hdom : ∀ {Hhat : SubMeas (Polynomial params) ι}
      (hssc : BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily Hhat)
        (selfImprovementHelperError params eps delta))
      (hSpectral : SpectralTruncationStatement strategy.state
        (leftLiftedMeasurement (ιB := ι) (optionCompletion Hhat))
        (consistencyToAlmostProjectiveError
          (2 * selfImprovementHelperError params eps delta))),
        QXPLayerResidualDomination (hqxp hssc hSpectral).data Hhat) :
    OrthonormalizationResidualDominationInput params strategy eps delta :=
  orthonormalizationResidualDominationInput_of_roundingAndQXPLayerRepair
    hround
    (residualDominatingRepairProducer_of_qxpLayer_and_residualDomination hqxp hdom)

end MIPStarRE.LDT.SelfImprovement
