import MIPStarRE.LDT.MakingMeasurementsProjective.Statements

/-!
# Section 5 — Producer for the locality-preserving repair stage

This file records one analytic obligation from Section 5 of the paper that
is not yet proved in Lean: the locality-preserving repair stage of the
orthogonalization argument.

## Scope

The upstream **spectral-truncation stage** is already proved by
`spectralTruncationInput_of_sourceAlmostProjective` in
`MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean`,
which is fully wired through
`projectiveNonMeasurement_of_sourceAlmostProjective_full`. Consumers that
need a producer for `SpectralTruncationInput` should call the existing one
directly.

The remaining obligation recorded here:

- **`leftLiftedProjectivizationRepairProducer`** — paper origin
  `references/ldt-paper/orthonormalization.tex` lines 534–740 (the late
  repair stage of the orthogonalization-lemma proof, which produces a genuine
  projective sub-measurement from a rounded family while preserving the
  left-lifted product form `P_a ⊗ I`).

Once this proof is complete, the hypothesis
`LeftLiftedProjectivizationRepairInput` required by the orthonormalization
main lemma can be discharged by calling this declaration directly.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

/-- Producer for `LeftLiftedProjectivizationRepairInput`.

Paper origin: `references/ldt-paper/orthonormalization.tex` lines 534–740 (the
late repair stage of the orthogonalization-lemma proof).

The paper's proof transports the rounded family produced by
`lem:projective-non-measurement` (already formalized — see
`spectralTruncationInput_of_sourceAlmostProjective`) through the `Q/X/X̂/P`
algebra (formalized as `QXPLayerData` and the rectangular polar decomposition
for the sigma-range embedding, PR #1237 / closed #1117 / closed #1228) to a
genuine projective sub-measurement `P = {P_a}` with closeness
`A_a ⊗ I ≈_{roundingToProjectiveError ζ} P_a ⊗ I`. The locality-preserving
form (output `P_a ⊗ I` rather than an arbitrary lifted family) is the
specialization required by `orthonormalizationMainLemma` and thereby by
`mainFormal`'s base-case bridge.

The companion `leftLiftedProjectivizationRepairInputDischarge` provides
`LeftLiftedProjectivizationRepairInput` in the form required by
`orthonormalizationMainLemma`. -/
theorem leftLiftedProjectivizationRepairProducer
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι)) (A : Measurement Outcome ι) (ζ : Error)
    (_hSpectral :
      SpectralTruncationStatement ψ (leftLiftedMeasurement (ιB := ι) A) ζ) :
    ∃ P : ProjSubMeas Outcome ι,
      RoundedProjMeasStatement ψ (leftLiftedMeasurement (ιB := ι) A)
        (ProjSubMeas.liftLeft P) (roundingToProjectiveError ζ) := by
  sorry

/-- Provides `LeftLiftedProjectivizationRepairInput` in the form required by
`orthonormalizationMainLemma`, derived from
`leftLiftedProjectivizationRepairProducer`. -/
def leftLiftedProjectivizationRepairInputDischarge
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι)) (A : Measurement Outcome ι) (ζ : Error) :
    LeftLiftedProjectivizationRepairInput ψ A ζ :=
  fun hSpectral => leftLiftedProjectivizationRepairProducer ψ A ζ hSpectral

end MIPStarRE.LDT.MakingMeasurementsProjective
