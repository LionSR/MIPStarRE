import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncation
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities
import MIPStarRE.LDT.Preliminaries.DistanceBounds

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
* `LeftLiftedQXPLayerRepairWitness` — a stronger QXP-layer repair witness
  whose rounded family is canonically `ProjSubMeas.liftLeft P`.
* `LeftLiftedQXPLayerRepairWitnessWithResidualDomination` — the same witness,
  specialized to the option-completed helper measurement and carrying the
  residual-domination invariant needed for the monotone-total route.
* `leftLiftedQXPLayerRepairWitness_of_lifted_qxp_sddOpRel` — converts a
  lifted raw QXP approximation into that locality-preserving witness.
* `leftLiftedQXPLayerRepairWitness_of_local_qxp_sddOpRel` — transports a local
  QXP approximation through a left marginal identity before applying the lifted
  witness constructor.
* `leftLiftedProjectivizationRepairInput_of_lifted_qxp_sddOpRel` — composes
  the same approximation with the existing repair-input bridge.
* `orthonormalizationInput_of_producers` — combines the two slices into the
  full `SelfImprovement.OrthonormalizationInput`.
* `orthonormalizationResidualDominationInput_of_producers` — the corresponding
  strengthened input for the residual-domination orthonormalization wrapper.
* `orthonormalizationSpectralProducer_of_roundingWitnesses` — narrows the
  spectral slice down to a producer of `RoundingToProjectorsWitness`es for the
  option-completed left-lifted helper measurement, using the conversion
  introduced by `#1042`.
* `orthonormalizationSpectralProducer_of_projectiveNonMeasurement` — narrows
  the same slice to the named QXP-layer statement
  `projectiveNonMeasurement`, i.e. the Lean form of
  `lem:projective-non-measurement`.
* `orthonormalizationInput_of_roundingAndQXPLayerRepair` — combines the
  rounding-witness spectral route with the QXP-layer local repair route.

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

/-! ### QXP-layer locality-preserving repair witnesses -/

/-- A stronger repair witness for a left-lifted measurement, carried by a
paper-style Q/X/XHat/P layer.

The data field records the local QXP layer.  The rounded family is not an
arbitrary projective family on the bipartite space: it is the left lift of
`qxpProjSubMeas data` for some local QXP layer, whose outcomes are the paper
operators `P_a = XHat† T_a XHat`. -/
structure LeftLiftedQXPLayerRepairWitness {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι)) (A : Measurement Outcome ι) (ζ : Error) where
  /-- The local Q/X/XHat/P layer from which the repaired family is extracted. -/
  data : QXPLayerData Outcome ι
  /-- The rounded-projective closeness bound for the canonical local QXP
  projectivization after lifting it to the left tensor factor. -/
  closeness :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (leftLiftedMeasurement (ιB := ι) A).toSubMeas)
      (constSubMeasFamily
        (ProjSubMeas.liftLeft (qxpProjSubMeas data)).toSubMeas)
      (roundingToProjectiveError ζ)

/-- A QXP-layer repair witness for an option-completed helper submeasurement,
strengthened by domination of the fresh residual outcome.

The underlying repaired family is still the canonical local family
`qxpProjSubMeas data`.  The additional field is the construction-level
inequality isolated in issue `#1300`: after completing `A` by the residual
operator `I - A.total`, the QXP repair assigns at least that operator to the
fresh `none` outcome.  This is precisely the hypothesis needed by
`orthonormalization_with_total_le_of_residual_domination`. -/
structure LeftLiftedQXPLayerRepairWitnessWithResidualDomination {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι)) (A : SubMeas Outcome ι) (ζ : Error) where
  /-- The local Q/X/XHat/P layer for the option-completed outcome type. -/
  data : QXPLayerData (Option Outcome) ι
  /-- The rounded-projective closeness bound for the canonical local QXP
  repair of the option-completed helper measurement. -/
  closeness :
    SDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily (leftLiftedMeasurement (ιB := ι) (optionCompletion A)).toSubMeas)
      (constSubMeasFamily
        (ProjSubMeas.liftLeft (qxpProjSubMeas data)).toSubMeas)
      (roundingToProjectiveError ζ)
  /-- The repaired fresh residual outcome dominates the original completion
  residual. -/
  residual_domination :
    (optionCompletion A).outcome none ≤ (qxpProjSubMeas data).outcome none

namespace LeftLiftedQXPLayerRepairWitnessWithResidualDomination

/-- The residual-domination field gives the operator total comparison for the
restricted repaired family selected by the QXP layer. -/
theorem restrictSome_total_le {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ι × ι)} {A : SubMeas Outcome ι} {ζ : Error}
    (W : LeftLiftedQXPLayerRepairWitnessWithResidualDomination ψ A ζ) :
    (restrictSomeProjSubMeas (qxpProjSubMeas W.data)).toSubMeas.total ≤ A.total :=
  restrictSomeProjSubMeas_total_le_of_optionCompletion_residual_le
    A (qxpProjSubMeas W.data) W.residual_domination

/-- The residual-domination field gives the right-register expectation
comparison for the restricted repaired family selected by the QXP layer. -/
theorem restrictSome_rightTensor_total_ev_le {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ι × ι)} {A : SubMeas Outcome ι} {ζ : Error}
    (W : LeftLiftedQXPLayerRepairWitnessWithResidualDomination ψ A ζ) :
    ev ψ (rightTensor (ι₁ := ι)
        (restrictSomeProjSubMeas (qxpProjSubMeas W.data)).toSubMeas.total) ≤
      ev ψ (rightTensor (ι₁ := ι) A.total) :=
  restrictSomeProjSubMeas_rightTensor_total_ev_le_of_optionCompletion_residual_le
    (ψ := ψ) A (qxpProjSubMeas W.data) W.residual_domination

/-- Adjoin a residual-domination invariant to an ordinary QXP repair witness
for the option-completed measurement. -/
def ofRepairWitness {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ι × ι)} {A : SubMeas Outcome ι} {ζ : Error}
    (W : LeftLiftedQXPLayerRepairWitness ψ (optionCompletion A) ζ)
    (hdom : QXPLayerResidualDomination W.data A) :
    LeftLiftedQXPLayerRepairWitnessWithResidualDomination ψ A ζ where
  data := W.data
  closeness := W.closeness
  residual_domination := hdom.residual_le

end LeftLiftedQXPLayerRepairWitnessWithResidualDomination

/-- Build the left-lifted QXP repair witness from a lifted raw QXP
approximation.

The hypothesis is the local QXP approximation after placing both raw operator
families on the left tensor factor.  Together with the pointwise identification
of the source measurement `A` with the `Q`-layer outcomes, this yields exactly
the `LeftLiftedQXPLayerRepairWitness`: the repaired projective family is the
left lift of the canonical local `qxpProjSubMeas data`, not an arbitrary
bipartite projective family. -/
noncomputable def leftLiftedQXPLayerRepairWitness_of_lifted_qxp_sddOpRel
    {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ι × ι)} {A : Measurement Outcome ι} {ζ : Error}
    (data : QXPLayerData Outcome ι)
    (hA :
      ∀ a : Outcome, data.qLayer.q.outcome a = A.outcome a)
    (hclose :
      SDDOpRel ψ (uniformDistribution Unit)
        (constOpFamily
          (OpFamily.leftPlacedOpFamily (ιB := ι) data.qLayer.q))
        (constOpFamily
          (OpFamily.leftPlacedOpFamily (ιB := ι) (PFamily data)))
        (roundingToProjectiveError ζ)) :
    LeftLiftedQXPLayerRepairWitness ψ A ζ := by
  refine
    { data := data
      closeness := ?_ }
  refine ⟨?_⟩
  have herror :
      sddError ψ (uniformDistribution Unit)
          (constSubMeasFamily (leftLiftedMeasurement (ιB := ι) A).toSubMeas)
          (constSubMeasFamily
            (ProjSubMeas.liftLeft (qxpProjSubMeas data)).toSubMeas) =
        sddErrorOp ψ (uniformDistribution Unit)
          (constOpFamily
            (OpFamily.leftPlacedOpFamily (ιB := ι) data.qLayer.q))
          (constOpFamily
            (OpFamily.leftPlacedOpFamily (ιB := ι) (PFamily data))) := by
    unfold sddError sddErrorOp
    refine avgOver_congr (uniformDistribution Unit) _ _ ?_
    intro u
    unfold qSDD qSDDOp qSDDCore
    refine Finset.sum_congr rfl ?_
    intro a _
    have hTa : (Ta data.qLayer a)ᴴ = Ta data.qLayer a := by
      simpa [Ta] using ProjMeas.outcome_hermitian data.qLayer.t a
    simp [constSubMeasFamily, constOpFamily, leftLiftedMeasurement,
      leftPlacedSubMeas, ProjSubMeas.liftLeft, SubMeas.liftLeft,
      OpFamily.leftPlacedOpFamily, PFamily, pFamilyFromXHat, Pa, hA, hTa,
      Matrix.mul_assoc]
  rw [herror]
  exact hclose.squaredDistanceBound

/-- Build the left-lifted QXP repair witness from a local QXP approximation and
a left-marginal expectation identity.

The local approximation is measured in a state `φ` on the original Hilbert
space.  If `φ` has the same expectations as the left tensor placements in the
bipartite state `ψ`, then the local `Q`-versus-`P` estimate transports to the
left tensor factor and hence gives the locality-preserving witness required by
the orthonormalization bridge. -/
noncomputable def leftLiftedQXPLayerRepairWitness_of_local_qxp_sddOpRel
    {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ι × ι)} {φ : QuantumState ι}
    {A : Measurement Outcome ι} {ζ : Error}
    (data : QXPLayerData Outcome ι)
    (hA :
      ∀ a : Outcome, data.qLayer.q.outcome a = A.outcome a)
    (hev : ∀ X : MIPStarRE.Quantum.Op ι,
      ev ψ (leftTensor (ι₂ := ι) X) = ev φ X)
    (hclose :
      SDDOpRel φ (uniformDistribution Unit)
        (constOpFamily data.qLayer.q)
        (constOpFamily (PFamily data))
        (roundingToProjectiveError ζ)) :
    LeftLiftedQXPLayerRepairWitness ψ A ζ :=
  leftLiftedQXPLayerRepairWitness_of_lifted_qxp_sddOpRel data hA
    (MIPStarRE.LDT.Preliminaries.sddOpRel_leftPlaced_of_ev_eq ψ φ
      (uniformDistribution Unit)
      (constOpFamily data.qLayer.q) (constOpFamily (PFamily data))
      (roundingToProjectiveError ζ) hev hclose)

/-- Build a residual-dominating QXP repair witness from a lifted raw QXP
approximation and the residual-domination invariant for the canonical local
projective family. -/
noncomputable def
    leftLiftedQXPLayerRepairWitnessWithResidualDomination_of_lifted_qxp_sddOpRel
    {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ι × ι)} {A : SubMeas Outcome ι} {ζ : Error}
    (data : QXPLayerData (Option Outcome) ι)
    (hA :
      ∀ oa : Option Outcome, data.qLayer.q.outcome oa = (optionCompletion A).outcome oa)
    (hclose :
      SDDOpRel ψ (uniformDistribution Unit)
        (constOpFamily
          (OpFamily.leftPlacedOpFamily (ιB := ι) data.qLayer.q))
        (constOpFamily
          (OpFamily.leftPlacedOpFamily (ιB := ι) (PFamily data)))
        (roundingToProjectiveError ζ))
    (hdom : QXPLayerResidualDomination data A) :
    LeftLiftedQXPLayerRepairWitnessWithResidualDomination ψ A ζ :=
  LeftLiftedQXPLayerRepairWitnessWithResidualDomination.ofRepairWitness
    (leftLiftedQXPLayerRepairWitness_of_lifted_qxp_sddOpRel data hA hclose)
    hdom

/-- Build a residual-dominating QXP repair witness from a local raw QXP
approximation, a left-marginal expectation identity, and the
residual-domination invariant for the canonical local projective family. -/
noncomputable def
    leftLiftedQXPLayerRepairWitnessWithResidualDomination_of_local_qxp_sddOpRel
    {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ι × ι)} {φ : QuantumState ι}
    {A : SubMeas Outcome ι} {ζ : Error}
    (data : QXPLayerData (Option Outcome) ι)
    (hA :
      ∀ oa : Option Outcome, data.qLayer.q.outcome oa = (optionCompletion A).outcome oa)
    (hev : ∀ X : MIPStarRE.Quantum.Op ι,
      ev ψ (leftTensor (ι₂ := ι) X) = ev φ X)
    (hclose :
      SDDOpRel φ (uniformDistribution Unit)
        (constOpFamily data.qLayer.q)
        (constOpFamily (PFamily data))
        (roundingToProjectiveError ζ))
    (hdom : QXPLayerResidualDomination data A) :
    LeftLiftedQXPLayerRepairWitnessWithResidualDomination ψ A ζ :=
  leftLiftedQXPLayerRepairWitnessWithResidualDomination_of_lifted_qxp_sddOpRel
    data hA
    (MIPStarRE.LDT.Preliminaries.sddOpRel_leftPlaced_of_ev_eq ψ φ
      (uniformDistribution Unit)
      (constOpFamily data.qLayer.q) (constOpFamily (PFamily data))
      (roundingToProjectiveError ζ) hev hclose)
    hdom

/-- A QXP-layer witness producer implies the existing left-lifted repair input.

This is the locality-preserving bridge needed by the orthonormalization slice:
once the QXP construction supplies its canonical local projective
submeasurement and the lifted closeness estimate, the existential in
`LeftLiftedProjectivizationRepairInput` is discharged by choosing exactly that
local submeasurement. -/
noncomputable def leftLiftedProjectivizationRepairInput_of_qxpLayer
    {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ι × ι)} {A : Measurement Outcome ι} {ζ : Error}
    (hwitness :
      SpectralTruncationStatement ψ (leftLiftedMeasurement (ιB := ι) A) ζ →
        LeftLiftedQXPLayerRepairWitness ψ A ζ) :
    LeftLiftedProjectivizationRepairInput ψ A ζ :=
  fun hSpectral =>
    let W := hwitness hSpectral
    ⟨qxpProjSubMeas W.data, ⟨W.closeness⟩⟩

/-- A residual-domination QXP-layer witness producer implies the strengthened
left-lifted repair input used by the monotone-total orthonormalization wrapper.

This is the residual analogue of
`leftLiftedProjectivizationRepairInput_of_qxpLayer`: it chooses the same
canonical projective family `qxpProjSubMeas data`, and also returns the
domination of the fresh `none` outcome. -/
noncomputable def
    leftLiftedProjectivizationRepairInputWithResidualDomination_of_qxpLayer
    {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ι × ι)} {A : SubMeas Outcome ι} {ζ : Error}
    (hwitness :
      SpectralTruncationStatement ψ
          (leftLiftedMeasurement (ιB := ι) (optionCompletion A)) ζ →
        LeftLiftedQXPLayerRepairWitnessWithResidualDomination ψ A ζ) :
    SpectralTruncationStatement ψ
        (leftLiftedMeasurement (ιB := ι) (optionCompletion A)) ζ →
      ∃ P : ProjSubMeas (Option Outcome) ι,
        RoundedProjMeasStatement ψ
          (leftLiftedMeasurement (ιB := ι) (optionCompletion A))
          (ProjSubMeas.liftLeft P) (roundingToProjectiveError ζ) ∧
        (optionCompletion A).outcome none ≤ P.outcome none :=
  fun hSpectral =>
    let W := hwitness hSpectral
    ⟨qxpProjSubMeas W.data, ⟨W.closeness⟩, W.residual_domination⟩

/-- Build the left-lifted projectivization repair input directly from a lifted
raw QXP approximation.

This is the repair-input form of
`leftLiftedQXPLayerRepairWitness_of_lifted_qxp_sddOpRel`.  It composes that
QXP witness with `leftLiftedProjectivizationRepairInput_of_qxpLayer`, so the
chosen repaired family remains the canonical local family
`qxpProjSubMeas data` after left tensor placement. -/
noncomputable def leftLiftedProjectivizationRepairInput_of_lifted_qxp_sddOpRel
    {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    {ψ : QuantumState (ι × ι)} {A : Measurement Outcome ι} {ζ : Error}
    (data : QXPLayerData Outcome ι)
    (hA :
      ∀ a : Outcome, data.qLayer.q.outcome a = A.outcome a)
    (hclose :
      SDDOpRel ψ (uniformDistribution Unit)
        (constOpFamily
          (OpFamily.leftPlacedOpFamily (ιB := ι) data.qLayer.q))
        (constOpFamily
          (OpFamily.leftPlacedOpFamily (ιB := ι) (PFamily data)))
        (roundingToProjectiveError ζ)) :
    LeftLiftedProjectivizationRepairInput ψ A ζ :=
  leftLiftedProjectivizationRepairInput_of_qxpLayer
    (fun _ => leftLiftedQXPLayerRepairWitness_of_lifted_qxp_sddOpRel data hA hclose)

/-- SelfImprovement-level producer of QXP-layer repair witnesses for each
helper submeasurement. -/
abbrev OrthonormalizationQXPLayerRepairProducer
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (eps delta : Error) :=
  ∀ {Hhat : SubMeas (Polynomial params) ι},
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Hhat)
      (selfImprovementHelperError params eps delta) →
    SpectralTruncationStatement strategy.state
      (leftLiftedMeasurement (ιB := ι) (optionCompletion Hhat))
      (consistencyToAlmostProjectiveError
        (2 * selfImprovementHelperError params eps delta)) →
    LeftLiftedQXPLayerRepairWitness strategy.state (optionCompletion Hhat)
      (consistencyToAlmostProjectiveError
        (2 * selfImprovementHelperError params eps delta))

/-- SelfImprovement-level producer of residual-dominating QXP-layer repair
witnesses for each helper submeasurement.

Compared with `OrthonormalizationQXPLayerRepairProducer`, this is the
construction-level strengthening needed for the monotone-total point-consistency
route: the option-completed QXP repair must dominate the original residual
outcome. -/
abbrev OrthonormalizationQXPLayerRepairProducerWithResidualDomination
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (eps delta : Error) :=
  ∀ {Hhat : SubMeas (Polynomial params) ι},
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Hhat)
      (selfImprovementHelperError params eps delta) →
    SpectralTruncationStatement strategy.state
      (leftLiftedMeasurement (ιB := ι) (optionCompletion Hhat))
      (consistencyToAlmostProjectiveError
        (2 * selfImprovementHelperError params eps delta)) →
    LeftLiftedQXPLayerRepairWitnessWithResidualDomination strategy.state Hhat
      (consistencyToAlmostProjectiveError
        (2 * selfImprovementHelperError params eps delta))

/-- Upgrade an ordinary QXP-layer repair producer to a residual-dominating one
when the residual-domination invariant is supplied separately for the canonical
QXP layer it constructs.

This separates the two mathematical obligations: the QXP repair producer gives
the `P`-versus-`Q` approximation, while `hdom` records the additional
operator-order fact at the fresh residual outcome. -/
noncomputable def residualDominatingRepairProducer_of_qxpLayer_and_residualDomination
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
    OrthonormalizationQXPLayerRepairProducerWithResidualDomination
      params strategy eps delta :=
  fun hssc hSpectral =>
    LeftLiftedQXPLayerRepairWitnessWithResidualDomination.ofRepairWitness
      (hqxp hssc hSpectral) (hdom hssc hSpectral)

/-- Convert the QXP-layer locality witness producer into the repair slice of
`SelfImprovement.OrthonormalizationInput`. -/
noncomputable def orthonormalizationRepairProducer_of_qxpLayer
    {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι} {eps delta : Error}
    (hqxp : OrthonormalizationQXPLayerRepairProducer params strategy eps delta) :
    OrthonormalizationRepairProducer params strategy eps delta :=
  fun hssc =>
    leftLiftedProjectivizationRepairInput_of_qxpLayer (hqxp hssc)

/-- SelfImprovement-level strengthened orthonormalization input carrying the
residual-domination invariant. -/
abbrev OrthonormalizationResidualDominationInput
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι) (eps delta : Error) :=
  ∀ {Hhat : SubMeas (Polynomial params) ι},
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily Hhat)
      (selfImprovementHelperError params eps delta) →
    MIPStarRE.LDT.MakingMeasurementsProjective.OrthonormalizationInputWithResidualDomination
      strategy.state Hhat (selfImprovementHelperError params eps delta)

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

/-- Forget the residual domination conclusion from one strengthened
orthonormalization repair input. -/
noncomputable def repairInput_of_repairInputWithResidualDomination
    {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι} {eps delta : Error}
    {Hhat : SubMeas (Polynomial params) ι}
    (H :
      MIPStarRE.LDT.MakingMeasurementsProjective.OrthonormalizationInputWithResidualDomination
        strategy.state Hhat (selfImprovementHelperError params eps delta)) :
    LeftLiftedProjectivizationRepairInput strategy.state (optionCompletion Hhat)
      (consistencyToAlmostProjectiveError
        (2 * selfImprovementHelperError params eps delta)) :=
  fun hSpectral =>
    let ⟨P, hRounded, _hResidual⟩ := H.repair hSpectral
    ⟨P, hRounded⟩

/-- Forget the residual-domination field of the strengthened input, yielding
the ordinary orthonormalization input required by the reduced self-improvement
theorem. -/
noncomputable def orthonormalizationInput_of_residualDominationInput
    {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι} {eps delta : Error}
    (hinput :
      OrthonormalizationResidualDominationInput params strategy eps delta) :
    OrthonormalizationInput params strategy eps delta :=
  fun {_Hhat} hssc =>
    let H := hinput hssc
    { spectral := H.spectral
      repair := repairInput_of_repairInputWithResidualDomination H }

/-- Combine the spectral slice and the residual-dominating QXP repair slice into
the strengthened orthonormalization input used by the monotone-total route. -/
noncomputable def orthonormalizationResidualDominationInput_of_producers
    {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι} {eps delta : Error}
    (hspectral : OrthonormalizationSpectralProducer params strategy eps delta)
    (hrepair :
      OrthonormalizationQXPLayerRepairProducerWithResidualDomination
        params strategy eps delta) :
    OrthonormalizationResidualDominationInput params strategy eps delta :=
  fun {_Hhat} hssc =>
    { spectral := hspectral hssc
      repair :=
        leftLiftedProjectivizationRepairInputWithResidualDomination_of_qxpLayer
          (hrepair hssc) }

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

/-- Build the spectral slice of `SelfImprovement.OrthonormalizationInput` from
the named QXP-layer `projectiveNonMeasurement` statement.

Compared with `orthonormalizationSpectralProducer_of_roundingWitnesses`, this
version exposes the remaining constructive obligation at the paper-facing
statement `lem:projective-non-measurement` instead of asking callers to provide
the dependent pair of rounded-family data directly. -/
noncomputable def orthonormalizationSpectralProducer_of_projectiveNonMeasurement
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
    OrthonormalizationSpectralProducer params strategy eps delta :=
  fun {Hhat} hssc =>
    spectralTruncationInput_of_projectiveNonMeasurement strategy.state
      (leftLiftedMeasurement (ιB := ι) (optionCompletion Hhat))
      (consistencyToAlmostProjectiveError
        (2 * selfImprovementHelperError params eps delta))
      (hprojective hssc)

/-- Build the spectral slice of `SelfImprovement.OrthonormalizationInput`
directly from the constructive spectral-truncation theorem.

This route now packages all three scalar branches needed for the paper-facing
statement `lem:projective-non-measurement`: the exact endpoint `ζ = 0`, the
nontrivial proof for `0 < ζ ≤ 1/4`, and the trivial large-error branch used in
the surrounding orthonormalization argument.  Callers therefore supply only the
source almost-projective defect through `SpectralTruncationInput`; the case
split is handled internally. -/
noncomputable def orthonormalizationSpectralProducer_of_sourceAlmostProjective
    {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι} {eps delta : Error} :
    OrthonormalizationSpectralProducer params strategy eps delta :=
  fun {Hhat} _hssc =>
    spectralTruncationInput_of_sourceAlmostProjective strategy.state
      (leftLiftedMeasurement (ιB := ι) (optionCompletion Hhat))
      (consistencyToAlmostProjectiveError
        (2 * selfImprovementHelperError params eps delta))

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
Section 5 witness producers exposed by the current bridge:

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
the same spectral rounding witnesses as the ordinary bridge, together with a
QXP-layer repair producer that also proves domination of the completed residual
outcome. -/
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
