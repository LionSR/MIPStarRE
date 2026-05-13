import MIPStarRE.LDT.SelfImprovement.Theorems.Statements
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization.RestrictSome
import MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncation
import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayerIdentities
import MIPStarRE.LDT.Preliminaries.DistanceBounds

/-!
# Section 9 — `OrthonormalizationInput` obligations

This file records legacy internal constructors for
`SelfImprovement.OrthonormalizationInput`, splitting that construction input
into the two paper-faithful pieces from
`references/ldt-paper/orthonormalization.tex`:

* the **spectral-truncation** step (`lem:projective-non-measurement`) on the
  option-completed, left-lifted helper measurement, and
* the **locality-preserving repair** step on the option-completed helper
  measurement.

The split mirrors `MakingMeasurementsProjective.OrthonormalizationInput`, which
is an internal proof-obligation structure for the Section 5 construction.
At present the spectral and repair pieces are still the open Section 5 inputs
tracked by #1515 and #1458; this file does *not* discharge them. It only narrows
the missing proof obligations to the two constructive Section 5 witnesses.
Paper-facing theorems should use the source statement with a tracked `sorry`
until these witnesses are actually proved from the source hypotheses.

In addition, `orthonormalizationSpectralObligation_of_roundingWitnesses`
composes the spectral-truncation conversion established in `#1042`
(`spectralTruncationStatement_of_witness`) with the SelfImprovement obligation.
Together with a separate locality-preserving repair obligation, this gives a
path from the honest QXP-layer rounding witnesses to
`SelfImprovement.OrthonormalizationInput`, without restating the full input as an
extra assumption of a paper-facing theorem.

## What this file provides

* `OrthonormalizationSpectralObligation` — the spectral slice of
  `SelfImprovement.OrthonormalizationInput`, isolated.
* `OrthonormalizationRepairObligation` — the locality-preserving repair slice.
* `LeftLiftedQXPLayerRepairWitness` — a stronger QXP-layer repair witness
  whose rounded family is canonically `ProjSubMeas.liftLeft P`.
* `leftLiftedQXPLayerRepairWitness_of_lifted_qxp_sddOpRel` — converts a lifted
  QXP approximation into that locality-preserving witness.
* `leftLiftedQXPLayerRepairWitness_of_local_qxp_sddOpRel` — transports a local
  QXP approximation through a left marginal identity before applying the lifted
  witness constructor.
* `leftLiftedProjectivizationRepairInput_of_lifted_qxp_sddOpRel` — composes
  the same approximation with the existing repair-input conversion.
* `orthonormalizationInput_of_obligations` — combines the two slices into the
  full `SelfImprovement.OrthonormalizationInput`.
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
* `references/ldt-paper/orthonormalization.tex` lines 270–310 and line 547
  (`lem:projective-low-rank-sum`) for the option-completion reduction and
  rounded sub-measurement repair.
* `references/ldt-paper/orthonormalization.tex` line 67
  (`thm:orthonormalization`) for the overall theorem this obligation feeds.
* `references/ldt-paper/self_improvement.tex` lines 679–697
  (helper output `\widehat{H}` is fed to `thm:orthonormalization`).
* The current source-facing self-improvement tracker #1515: the
  orthonormalization obligation reduces to the two constructive Section 5
  witnesses on `optionCompletion Hhat`.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Spectral and repair slice obligations -/

-- The spectral obligation is `Type`-valued because spectral truncation carries
-- rounded-family data, while the repair obligation is proposition-valued.

/-- Obligation for the **spectral-truncation** slice of
`SelfImprovement.OrthonormalizationInput`.

Paper origin: the projective-output passage in
`references/ldt-paper/self_improvement.tex:10-13`, using the
orthonormalization theorem from
`references/ldt-paper/orthonormalization.tex:273-282`.

For every helper sub-measurement `Hhat` satisfying the helper-stage bipartite
strong-self-consistency hypothesis (`BipartiteSSCRel ... ζ_helper`), this
yields the `SpectralTruncationInput` for the *option-completed* left-lifted
measurement `optionCompletion Hhat`, at error
`consistencyToAlmostProjectiveError (2 * ζ_helper)`.

This isolates the `spectral` field of
`MakingMeasurementsProjective.OrthonormalizationInput`. -/
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

/-- Obligation for the **locality-preserving repair** slice of
`SelfImprovement.OrthonormalizationInput`.

Paper origin: the projective-output passage in
`references/ldt-paper/self_improvement.tex:10-13`, using the
orthonormalization theorem from
`references/ldt-paper/orthonormalization.tex:273-282`.

For every helper sub-measurement `Hhat` satisfying the helper-stage bipartite
strong-self-consistency hypothesis, this yields the
`LeftLiftedProjectivizationRepairInput` for `optionCompletion Hhat` at error
`consistencyToAlmostProjectiveError (2 * ζ_helper)`. -/
abbrev OrthonormalizationRepairObligation
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

/-- Paper origin: `references/ldt-paper/orthonormalization.tex:273-282`
(`\label{sec:orthogonalization}`, `\label{lem:orthonormalization-main-lemma}`)
and `references/ldt-paper/self_improvement.tex:628-671`
(`\label{sec:self-improvement-projective}`, `\label{thm:self-improvement}`).

A stronger repair witness for a left-lifted measurement, carried by a
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

/-- Build the left-lifted QXP repair witness from a lifted QXP approximation.

The hypothesis is the local QXP approximation after placing both operator
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

/-- A QXP-layer witness obligation implies the existing left-lifted repair input.

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

/-- Build the left-lifted projectivization repair input directly from a lifted
QXP approximation.

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

/-- SelfImprovement-level obligation for QXP-layer repair witnesses for each
helper submeasurement.

Paper origin: the same orthonormalization step in
`references/ldt-paper/self_improvement.tex:10-13`, via the QXP-layer repair
route for `references/ldt-paper/orthonormalization.tex:273-282`. -/
abbrev OrthonormalizationQXPLayerRepairObligation
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

/-- Convert the QXP-layer locality witness obligation into the repair slice of
`SelfImprovement.OrthonormalizationInput`. -/
noncomputable def orthonormalizationRepairObligation_of_qxpLayer
    {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι} {eps delta : Error}
    (hqxp : OrthonormalizationQXPLayerRepairObligation params strategy eps delta) :
    OrthonormalizationRepairObligation params strategy eps delta :=
  fun hssc =>
    leftLiftedProjectivizationRepairInput_of_qxpLayer (hqxp hssc)

/-! ### Combining slice obligations -/

/-- Combine the spectral and repair slice obligations into a full
`SelfImprovement.OrthonormalizationInput`.

This is the narrowed conditional interface used by the #1515 repair route: it
converts two independent paper-faithful slice obligations into the bundled input
that the reduced self-improvement theorem expects.  No mathematical content is
added or discharged here; the interface is structural. -/
def orthonormalizationInput_of_obligations
    {params : Parameters} [FieldModel params.q]
    {strategy : SymStrat params ι} {eps delta : Error}
    (hspectral : OrthonormalizationSpectralObligation params strategy eps delta)
    (hrepair : OrthonormalizationRepairObligation params strategy eps delta) :
    OrthonormalizationInput params strategy eps delta :=
  fun {_Hhat} hssc =>
    { spectral := hspectral hssc
      repair := hrepair hssc }

/-! ### Spectral slice from per-`Hhat` rounding witnesses -/

/-- Build the spectral slice of `SelfImprovement.OrthonormalizationInput` from
an obligation for `RoundingToProjectorsWitness`es on the option-completed
left-lifted helper measurement.

This is the SelfImprovement-level analogue of `#1042`: it lifts the existing
field-for-field conversion `spectralTruncationStatement_of_witness` to the
quantification used by `OrthonormalizationSpectralObligation`.  The honest
mathematical content — actually building `R` — remains the caller's
responsibility, exactly as in `#1042`.  Combined with
`orthonormalizationInput_of_obligations` and a separate repair obligation, this
turns a `RoundingToProjectorsWitness` obligation into the full
`SelfImprovement.OrthonormalizationInput`. -/
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

/-- Build the spectral slice of `SelfImprovement.OrthonormalizationInput` from
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

/-- Build the spectral slice of `SelfImprovement.OrthonormalizationInput`
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
