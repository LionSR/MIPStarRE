import MIPStarRE.LDT.MakingMeasurementsProjective.Statements

/-!
# Section 5 — Locality-preserving projectivization repair

This file records one analytic obligation from Section 5 of the paper that
is not yet proved in Lean: the locality-preserving repair stage of the
orthogonalization argument.

## Scope

The **spectral-truncation stage** (the first part of the proof of rounding
to projectors) is already proved by
`spectralTruncationInput_of_sourceAlmostProjective` in
`MakingMeasurementsProjective/SpectralTruncation/ProjectiveNonMeasurement.lean`,
which is fully proved via
`projectiveNonMeasurement_of_sourceAlmostProjective_full`. Proofs that
require `SpectralTruncationInput` should call that declaration directly.

The remaining obligation recorded here:

- **`leftLiftedProjectivizationRepairProducer`** — paper origin
  `references/ldt-paper/orthonormalization.tex` lines 534–860 (rank
  reduction and the `Q`/`√Q` completeness setup) and 862–1194 (the
  `X`/`X̂`/`P` algebra producing the lifted projective sub-measurement,
  including the final triangle-inequality assembly), i.e. the late repair
  stage of the orthogonalization-lemma proof, which produces a genuine
  projective sub-measurement from a rounded family while preserving the
  left-lifted product form `P_a ⊗ I`.

Once this proof is complete, the hypothesis
`LeftLiftedProjectivizationRepairInput` required by the orthonormalization
main lemma can be discharged by calling this declaration directly.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

/-- Given a normalized state `ψ`, a measurement `A`, and the
spectral-truncation output on the left-lifted family `A_a ⊗ I`, produces a
projective sub-measurement `P = {P_a}` on the underlying space such that
the lifted family `{P_a ⊗ I}` satisfies
`A_a ⊗ I ≈_{roundingToProjectiveError ζ} P_a ⊗ I` (paper bound `84 ζ^{1/4}`).
The locality-preserving form (output `P_a ⊗ I` rather than an arbitrary
lifted family) is the specialization required by `orthonormalizationMainLemma`.

Paper origin: `references/ldt-paper/orthonormalization.tex` lines 534–860
(rank reduction `lem:projective-low-rank-sum` and the `Q`-side setup:
`lem:Q-completeness`, `lem:sqrt-Q-completeness`, `lem:q-almost-projective`,
`lem:xa-t`, `lem:qa-restated`) and 862–1194 (the `X`/`X̂`/`P` algebra
proper: `lem:X-squared`, `lem:X-hat-squared`, `lem:X-times-X-hat`,
`lem:squared-difference`, `lem:P-projectivity`, `lem:P-Q-approx`, plus the
final triangle-inequality assembly producing the `84 ζ^{1/4}` bound captured
by `roundingToProjectiveError ζ`). Together these constitute the late
repair stage of the orthogonalization-lemma proof.

The paper's proof transports the rounded family produced by
`lem:projective-non-measurement` (already formalized — see
`spectralTruncationInput_of_sourceAlmostProjective`) through the `Q/X/X̂/P`
algebra (formalized as `QXPLayerData` and the rectangular polar decomposition
for the sigma-range embedding) to a genuine projective sub-measurement
`P = {P_a}` with closeness
`A_a ⊗ I ≈_{roundingToProjectiveError ζ} P_a ⊗ I`. The locality-preserving
form (output `P_a ⊗ I` rather than an arbitrary lifted family) is the
specialization required by `orthonormalizationMainLemma` and thereby by
`mainFormal`'s base-case bridge.
-/
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
end MIPStarRE.LDT.MakingMeasurementsProjective
