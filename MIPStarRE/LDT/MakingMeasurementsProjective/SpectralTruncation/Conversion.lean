import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
import MIPStarRE.LDT.MakingMeasurementsProjective.QXPLayer.RankReduction
import MIPStarRE.LDT.MakingMeasurementsProjective.SpectralTruncation.ProjectiveNonMeasurement

/-!
# Spectral truncation statement conversions

This file contains the structural conversions from the paper witness
`projectiveNonMeasurement` and the rounded-projector witness used by the QXP
rank-reduction layer to the `SpectralTruncationStatement` interface used by
orthonormalization.

The conversions are field-for-field copies.  The constructive spectral
truncation theorem, which produces such a rounded projective family from the
paper's almost-projective hypothesis, is proved in the sibling proof-layer
module `SpectralTruncation.ProjectiveNonMeasurement`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

universe uOutcome uι

/-! ### Spectral truncation statement conversion

Convert a `RoundingToProjectorsWitness` to a `SpectralTruncationStatement`.
The two types are field-for-field identical after `SpectralTruncationStatement.closeness`
was weakened to `2√ζ`. -/

/-- Convert a `RoundingToProjectorsWitness` to a `SpectralTruncationStatement`.

This is a structural field-for-field copy: both types carry the same data
(rounded family, projectivity, `2√ζ` closeness, total bound `1 + 2√ζ`).

The mathematical content of `lem:projective-non-measurement` — constructing
the rounded family — is the caller's responsibility when building a
`RoundingToProjectorsWitness`. -/
noncomputable def spectralTruncationStatement_of_witness {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (R : OpFamily Outcome ι)
    (hwitness : RoundingToProjectorsWitness ψ A ζ R) :
    SpectralTruncationStatement ψ A ζ :=
  ⟨R, hwitness.projective, hwitness.closeness, hwitness.sum_eq_total,
    hwitness.total_le⟩

namespace SpectralTruncationStatement

/-- Paper origin: `references/ldt-paper/orthonormalization.tex:414-531`
(`\label{lem:projective-non-measurement}`; rounding-to-projectors lemma
with `2√ζ` closeness and `(1+2√ζ)·I` total bound).

Convert a spectral-truncation statement back to the rounded-projector
witness consumed by the QXP rank-reduction layer.

The conversion is structural.  It does not recover the source almost-projective
estimate, because that estimate is not a field of `SpectralTruncationStatement`;
rank-reduction constructors which need it therefore keep it as a separate
hypothesis. -/
noncomputable def toRoundingToProjectorsWitness {Outcome : Type uOutcome}
    [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState ι} {A : Measurement Outcome ι} {ζ : Error}
    (h : SpectralTruncationStatement ψ A ζ) :
    RoundingToProjectorsWitness ψ A ζ h.roundedFamily where
  projective := h.projective
  closeness := h.closeness
  sum_eq_total := h.sum_eq_total
  total_le := h.total_le

end SpectralTruncationStatement

/-! ### Rank-reduction from spectral truncation -/

/-- Feed a spectral-truncation statement into the QXP rank-reduction layer.

The statement `SpectralTruncationStatement` remembers the rounded projectors
and their distance from the source measurement.  The rank-reduction witness also
records the source almost-projectivity estimate, so that estimate remains an
explicit hypothesis here.  This is the precise interface needed when the
orthonormalization spectral input is followed by the paper's
`Q -> X -> Xhat -> P` repair layer. -/
lemma projectiveLowRankSum_of_spectralTruncationStatement
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_le : ζ ≤ 1 / 4)
    (hSpectral : SpectralTruncationStatement ψ A ζ)
    (hsource :
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data :=
  projectiveLowRankSum_of_roundingWitness ψ A ζ hψ hζ hζ_le hSpectral.roundedFamily
    hSpectral.toRoundingToProjectorsWitness hsource

/-- **Rank reduction** (`\label{lem:projective-low-rank-sum}`).

Paper origin: `references/ldt-paper/orthonormalization.tex:540-658`.

The paper first applies `\label{lem:projective-non-measurement}` to obtain the
rounded projective family `R_a`, and then performs the rank-reduction argument.
This theorem keeps that source-facing boundary: the rounded family is produced
internally from the source almost-projectivity estimate and is then passed to
the internal constructor `projectiveLowRankSum_of_roundingWitness`. -/
lemma projectiveLowRankSum {Outcome : Type uOutcome}
    {ι : Type uι} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (hψ : ψ.IsNormalized)
    (hζ : 0 ≤ ζ) (hζ_le : ζ ≤ 1 / 4)
    (source_almost_projective :
      ∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data := by
  classical
  obtain ⟨q, hrounded⟩ :=
    projectiveNonMeasurement_of_sourceAlmostProjective_two_mul_full
      ψ A ζ hψ source_almost_projective
  exact projectiveLowRankSum_of_roundingWitness ψ A ζ hψ hζ hζ_le q hrounded
    source_almost_projective

/-- Build a `SpectralTruncationStatement` from the named
`lem:projective-non-measurement` witness.

The paper's spectral truncation step is represented in the QXP layer by
`projectiveNonMeasurement`, which is a proposition asserting the existence of a
rounded projective family with the same bounds as `SpectralTruncationStatement`.
This conversion uses choice to extract the rounded family and then applies
`spectralTruncationStatement_of_witness`. -/
noncomputable def spectralTruncationStatement_of_projectiveNonMeasurement
    {Outcome : Type uOutcome} [Fintype Outcome] [DecidableEq Outcome]
    {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι) (ζ : Error)
    (hprojective : projectiveNonMeasurement ψ A ζ) :
    SpectralTruncationStatement ψ A ζ :=
  let R : OpFamily Outcome ι := Classical.choose hprojective
  let hR : RoundingToProjectorsWitness ψ A ζ R :=
    Classical.choose_spec hprojective
  spectralTruncationStatement_of_witness ψ A ζ R hR

end MIPStarRE.LDT.MakingMeasurementsProjective
