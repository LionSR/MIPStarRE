# Scouting report for `MIPStarRE/LDT/MakingMeasurementsProjective/Theorems.lean`

Date: 2026-04-02

Repository/toolchain inspected:

- `lean-toolchain` is `leanprover/lean4:v4.28.0`.
- Lean file read carefully: `MIPStarRE/LDT/MakingMeasurementsProjective/Theorems.lean`
- Supporting local statement/definition files read carefully:
  - `MIPStarRE/LDT/MakingMeasurementsProjective/Statements.lean`
  - `MIPStarRE/LDT/MakingMeasurementsProjective/Defs.lean`
  - `MIPStarRE/Quantum/FiniteMatrix.lean`
  - `MIPStarRE/LDT/Basic/SubMeasurement.lean`
- Paper source read carefully:
  - `references/ldt-paper/orthonormalization.tex`
- Mathlib API checked directly in the local checkout under `.lake/packages/mathlib/Mathlib`.

## Executive summary

Short answer to the key question:

- Yes, this local Mathlib for Lean `v4.28.0` does have the key Hermitian-matrix spectral infrastructure.
- `Matrix.PosSemidef.sqrt` exists, but it is now a deprecated shim over `CFC.sqrt`.
- `Matrix.IsHermitian.spectral_theorem` exists.
- `Matrix.IsHermitian.cfc` exists, and is the more modern API for matrix functional calculus.
- The exact symbol `Matrix.innerMulLe_norm_mul_iff` does **not** exist.
- I found no ready-made matrix `Schur` decomposition API, no ready-made matrix `SVD` API, and no ready-made matrix `polar decomposition` API.

My main conclusion:

- `oneMeasNaimark` is no longer blocked by the mere absence of matrix square roots or a spectral theorem API. The real work is tensor/index bookkeeping plus proving the compression identity cleanly.
- The early orthonormalization stages are plausible with existing Mathlib.
- The late orthonormalization stage in the paper depends on an explicit SVD-style construction that does **not** appear to have a corresponding off-the-shelf Mathlib API.
- There is also a repo-level statement mismatch: the current `adjustTruncatedProjections` target error and the requirement that the output be a genuine `ProjSubMeas` do not line up cleanly with the paper's proof decomposition.

## Exact API reconnaissance

Direct Lean checks succeeded:

```lean
#check Matrix.PosSemidef.sqrt
#check Matrix.IsHermitian.spectral_theorem
#check Matrix.IsHermitian.cfc
#check CFC.sqrt
```

Observed types:

- `Matrix.PosSemidef.sqrt : (hA : A.PosSemidef) -> Matrix n n 𝕜`
- `Matrix.IsHermitian.spectral_theorem : A = conjStarAlgAut ... (diagonal (RCLike.ofReal ∘ hA.eigenvalues))`
- `Matrix.IsHermitian.cfc : (hA : A.IsHermitian) -> (f : ℝ → ℝ) -> Matrix n n 𝕜`
- `CFC.sqrt : a -> a`

Relevant Mathlib files and what they provide:

- `Mathlib/Analysis/Matrix/Spectrum.lean`
  - `Matrix.IsHermitian.eigenvalues`
  - `Matrix.IsHermitian.eigenvectorBasis`
  - `Matrix.IsHermitian.eigenvectorUnitary`
  - `Matrix.IsHermitian.spectral_theorem`
- `Mathlib/Analysis/Matrix/HermitianFunctionalCalculus.lean`
  - `Matrix.IsHermitian.cfc`
  - matrix-level continuous functional calculus built from the Hermitian spectral theorem
- `Mathlib/Analysis/Matrix/Order.lean`
  - deprecated `Matrix.PosSemidef.sqrt`
  - `CFC.sqrt_nonneg`
  - `CFC.sq_sqrt`
  - `CFC.sqrt_mul_sqrt_self`
  - `Matrix.PosSemidef.dotProduct_mulVec_zero_iff`
- `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean`
  - order lemmas for `sqrt` in star-ordered rings

Negative search results:

- `rg -n "innerMulLe_norm_mul_iff" .lake/packages/mathlib/Mathlib` returned nothing.
- Searches for `svd`, `SVD`, `polar decomposition`, `polarDecomposition`, and matrix `Schur` diagonalization APIs returned no relevant matrix factorization API.
- There is a `SchurComplement` API, but that is about block matrices, not Schur unitary triangularization.

Useful generic inequality replacements that do exist:

- `norm_inner_le_norm`
- `nnnorm_inner_le_nnnorm`
- `re_inner_le_norm`

So the exact symbol named in the prompt is absent, but generic Cauchy-Schwarz infrastructure is available.

## Repo-specific observations that matter

The local Lean statements are not a perfect one-for-one transliteration of the paper proof.

Important examples:

- `OneMeasNaimarkLemma` in `Statements.lean` is stated as existence of `OneMeasNaimarkData`, but `OneMeasNaimarkData` itself includes the substantive field
  `expectation_preservation`.
- `SpectralTruncationStatement` only asks for a `Nonempty (MatrixSpectralTruncationMeasurementWitness ...)`, so the local theorem is a packaging statement rather than a fully abstract theorem about `SDDRel`.
- `Quantum.SpectralTruncation` in `MIPStarRE/Quantum/FiniteMatrix.lean` already packages the desired output of truncating one Hermitian operator to one projector:
  Hermitian source, projective target, and the τ-distance bound.
- `ProjSubMeas` in `MIPStarRE/LDT/Basic/SubMeasurement.lean` still requires the submeasurement total to satisfy `total ≤ 1`.

The biggest mismatch I found:

- `roundingToProjectiveError` is defined as `12 * ζ^(1/2)` in `Defs.lean`.
- But the paper's late-stage SVD construction only gets from `Q` to a genuine projective submeasurement `P` with error `30 * ζ^(1/4)`, not `12 * ζ^(1/2)`.
- The intermediate family `Q = {Q_a}` from rank reduction is **not** a `ProjSubMeas` in the repo sense, because the paper only proves `Q := ∑_a Q_a ≤ (1 + 2√ζ) I`, not `Q ≤ I`.

So the current `adjustTruncatedProjections` target seems stronger than what the paper actually proves in that stage.

## Per-`sorry` scouting

I list the 8 `sorry` sites in file order.

### 1. `oneMeasNaimark`

Lean site:

- `Theorems.lean:67-71`

Lean statement:

- For a submeasurement `M : Quantum.Submeasurement α d`, prove `OneMeasNaimarkLemma α d M`.
- The intended construction is described in the docstring at `Theorems.lean:39-66`.
- The packaged data to produce is `OneMeasNaimarkData` from `Defs.lean:157-183`.

Paper correspondence:

- This corresponds to the unlabeled helper lemma `lem:naimark-helper` at `orthonormalization.tex:121-159`.

Paper proof summary:

- Choose basis vectors `|a⟩` and `|⊥⟩` in the auxiliary space.
- Build a unitary/isometry using `sqrt(A_a)` and `sqrt(I - A)`.
- Define `\widehat A_a = U† (I ⊗ |a⟩⟨a|) U`.
- Prove compression:
  `(I ⊗ ⟨aux|) \widehat A_a (I ⊗ |aux⟩) = A_a`.

Mathlib infrastructure needed:

- PSD square roots for each `A_a`.
- PSD square root for `I - ∑ A_a`.
- Hermitian/projective facts for conjugates of diagonal projectors.
- Kronecker/tensor algebra and basis projector calculations.

Assessment:

- The square-root API exists. This is no longer blocked on `Matrix.PosSemidef.sqrt` being absent.
- The modern route should probably use `CFC.sqrt` and `CFC.sqrt_mul_sqrt_self`, with `Matrix.PosSemidef.sqrt` only if one wants the old name.
- The real work is:
  - proving `I - total(M)` is PSD,
  - building the lifted operator cleanly on `d × Option α`,
  - proving the projection and sum bounds,
  - proving the normalized-trace compression identity.

Bottom line:

- Feasible with current Mathlib.
- Hard part is matrix/tensor bookkeeping, not missing spectral theory.

### 2. `naimark`

Lean site:

- `Theorems.lean:94-106`

Lean statement:

- Produce `data : NaimarkData ...` and prove `NaimarkStatement ψ A B data`.
- `NaimarkData` lives at `Defs.lean:248-263`.
- `NaimarkStatement` lives at `Statements.lean:43-94`.

Paper correspondence:

- `thm:naimark` at `orthonormalization.tex:36-63`.
- Proof at `orthonormalization.tex:161-187`.

Paper proof summary:

- Apply the helper lemma independently to each Alice question and each Bob question.
- Tensor all auxiliary states together.
- Extend each per-question dilated measurement by identity on all other auxiliary registers.
- Conclude exact preservation of joint outcome probabilities.

Mathlib infrastructure needed:

- Mostly dependent on `oneMeasNaimark`.
- Product-index and tensor bookkeeping.
- Showing measurements on disjoint auxiliary coordinates commute.

Assessment:

- This theorem is conceptually downstream of `oneMeasNaimark`.
- Once the one-measurement dilation exists with exact expectation preservation, the rest is mostly indexed bookkeeping.
- The exponential-size auxiliary index `QuestionA → Option OutcomeA` and `QuestionB → Option OutcomeB` may make proofs unpleasant, but not mathematically blocked.

Bottom line:

- Not blocked by Mathlib spectral APIs.
- Blocked in practice by the implementation burden of the previous theorem plus tensor bookkeeping.

### 3. `orthonormalization`

Lean site:

- `Theorems.lean:112-123`

Lean statement:

- From strong self-consistency of a submeasurement `A`, produce `P : ProjSubMeas` with `SDDRel ... (orthonormalizationError ζ)`.
- `orthonormalizationError ζ = 100 * ζ^(1/4)` in `Defs.lean:292-295`.

Paper correspondence:

- `thm:orthonormalization` at `orthonormalization.tex:67-77`.
- Reduction proof at `orthonormalization.tex:304-370`.

Paper proof summary:

- Complete the submeasurement by adding a `⊥` outcome.
- Show the completed measurement is `2ζ`-self-consistent.
- Invoke the measurement-version lemma.
- Restrict back to the original outcomes.
- Use `84 * 2^(1/4) ≤ 100`.

Mathlib infrastructure needed:

- No spectral theorem needed directly here.
- Mostly algebra on expectations and nonnegativity.
- Dependency on `orthonormalizationMainLemma`.

Assessment:

- This part is relatively straightforward once the measurement-version lemma exists.
- No new matrix square-root or spectral-theorem burden here.

Bottom line:

- Mathematically easy relative to the main lemma.
- Mostly a wrapper around the measurement case.

### 4. `orthonormalizationMainLemma`

Lean site:

- `Theorems.lean:128-139`

Lean statement:

- From `ConsRel ... A B ζ`, produce `P : ProjSubMeas` and `RoundedProjMeasStatement ψ A P (84 * ζ^(1/4))`.

Paper correspondence:

- `lem:orthonormalization-main-lemma` at `orthonormalization.tex:282-293`.
- Full proof at `orthonormalization.tex:374-1194`.

Paper proof summary:

- Use consistency with `B` only once, via Cauchy-Schwarz, to derive
  `∑_a ⟨ψ|(A_a - A_a^2) ⊗ I|ψ⟩ ≤ 2ζ`.
- Spectrally truncate each `A_a` to a projector `R_a`.
- Post-process to `Q_a` by rank reduction.
- Prove completeness of `Q` and of `sqrt(Q)`.
- Define matrices `X_a`, `X`, use an SVD `X = U Σ V†`, and build `P` from `\hat X = U I V†`.
- Show `P` is a projective submeasurement and close to `Q`, hence to `A`.

Mathlib infrastructure needed:

- Generic Cauchy-Schwarz in an inner product space.
- Spectral theorem / functional calculus for Hermitian matrices.
- Matrix square roots of PSD matrices.
- Matrix order on Hermitian/PSD matrices.
- A usable SVD or equivalent polar-decomposition argument.

Assessment:

- The first half of this proof is plausible with existing Mathlib.
- The second half is where I expect real friction:
  - I found no ready-made matrix SVD API.
  - I found no ready-made polar decomposition API.
  - I found no ready-made Schur unitary decomposition API that would substitute.
- This means the late part of the paper proof would likely need to be reworked, or one must formalize the needed factorization from scratch.

Bottom line:

- This is the genuinely hard `sorry`.
- Spectral theorem and square roots exist.
- Missing factorization infrastructure for the `X = U Σ V†` part is the main blocker.

### 5. `consistencyToAlmostProjective`

Lean site:

- `Theorems.lean:143-152`

Lean statement:

- From `ConsRel ... A B ζ`, produce `AlmostProjMeasStatement ψ A (2ζ)`.
- `AlmostProjMeasStatement` is in `Statements.lean:98-111`.

Paper correspondence:

- This is the opening of the proof of `lem:orthonormalization-main-lemma`, specifically `orthonormalization.tex:385-407`.
- There is no separate labeled paper lemma for this exact step.

Paper proof summary:

- From `A_a ⊗ I \simeq_ζ I ⊗ B_a`, deduce `∑_a ⟨ψ|A_a ⊗ B_a|ψ⟩ ≥ 1 - ζ`.
- Apply Cauchy-Schwarz:
  `∑_a ⟨ψ|(A_a ⊗ I)(I ⊗ B_a)|ψ⟩ ≤ sqrt(∑_a ⟨ψ|A_a^2 ⊗ I|ψ⟩)`.
- Rearrange to get the almost-idempotence defect bound.

Mathlib infrastructure needed:

- Generic inner product Cauchy-Schwarz.
- Basic positivity for measurement operators and the fact that `A` and `B` are measurements.

Assessment:

- The exact symbol `Matrix.innerMulLe_norm_mul_iff` is absent, but that does not look fatal.
- Existing generic lemmas `norm_inner_le_norm`, `nnnorm_inner_le_nnnorm`, and `re_inner_le_norm` should be enough after the expectations are expressed in a genuine Hilbert-space inner product.
- No spectral theorem needed here.

Bottom line:

- Very plausible with current Mathlib.
- This is not where the infrastructure risk lies.

### 6. `spectralTruncateAlmostProjective`

Lean site:

- `Theorems.lean:155-161`

Lean statement:

- From `AlmostProjMeasStatement ψ A ζ`, produce `SpectralTruncationStatement ψ A ζ`.
- `SpectralTruncationStatement` is only a witness-existence package in `Statements.lean:115-120`.
- The witness type is `MatrixSpectralTruncationMeasurementWitness` from `Defs.lean:366-375`.

Paper correspondence:

- This corresponds primarily to the labeled lemma `lem:projective-non-measurement` at `orthonormalization.tex:414-531`.

Paper proof summary:

- Diagonalize each Hermitian effect `A_a`.
- Threshold eigenvalues with `trunc_δ`.
- Get a projector `R_a`.
- Prove the τ-distance bound using the scalar inequality
  `(x - trunc_δ(x))^2 ≤ (1/δ)(x - x^2)`.

Mathlib infrastructure needed:

- Hermitian diagonalization.
- Functional calculus or explicit spectral decomposition.
- Ability to define and reason about a thresholded spectral projector.

Assessment:

- `Matrix.IsHermitian.spectral_theorem` and `Matrix.IsHermitian.cfc` are present.
- `CFC.sqrt` is present, but note that the threshold function `trunc_δ` is discontinuous, so continuous functional calculus alone does not directly build `R_a`.
- The paper's proof is actually closer to "explicit eigenbasis + diagonal truncation" than to pure CFC.
- Since `Quantum.SpectralTruncation` is already a lightweight witness structure (`FiniteMatrix.lean:116-120`), one possible approach is:
  - use the spectral theorem to write each `A_a` as `U diag(λ) U†`,
  - define `R_a := U diag(trunc_δ(λ)) U†`,
  - prove the packaged witness.

Bottom line:

- Feasible with current Mathlib spectral infrastructure.
- The missing piece is not square root; it is an ergonomic spectral-projection/truncation construction.

### 7. `adjustTruncatedProjections`

Lean site:

- `Theorems.lean:165-173`

Lean statement:

- From `SpectralTruncationStatement ψ A ζ`, produce a genuine `ProjSubMeas` with error
  `roundingToProjectiveError ζ = 12 * ζ^(1/2)`.
- Relevant defs:
  - `roundingToProjectiveError` at `Defs.lean:313-315`
  - `RoundedProjMeasStatement` at `Statements.lean:123-133`

Paper correspondence:

- This does **not** match a single labeled paper lemma cleanly.
- The natural paper candidates are:
  - rank reduction `lem:projective-low-rank-sum` at `orthonormalization.tex:540-659`
  - plus the later `Q -> P` SVD argument at `orthonormalization.tex:665-1194`

Paper proof summary relevant here:

- From truncated projectors `R_a`, derive lower-rank projectors `Q_a` with
  `A_a ⊗ I \approx_{12√ζ} Q_a ⊗ I`.
- But `Q := ∑_a Q_a` only satisfies `Q ≤ (1 + 2√ζ) I`.
- To get an actual projective submeasurement `P`, the paper then performs the long SVD construction and loses another `30 ζ^(1/4)`.

Assessment:

- This is the strongest mismatch in the file.
- The paper's `Q_a` are not obviously a `ProjSubMeas` in the repo's sense because `ProjSubMeas` still requires `total ≤ 1`.
- The paper's final `P_a` are a genuine projective submeasurement, but only after the SVD construction, and with error `30 ζ^(1/4)` relative to `Q`, not `12√ζ`.
- Therefore the current Lean statement seems stronger than the paper stage it is supposed to represent.

Bottom line:

- As written, I do not think the paper proof directly proves this Lean statement.
- Either the statement should be weakened/reindexed, or the intended decomposition should be changed.

### 8. `roundAlmostProjMeas`

Lean site:

- `Theorems.lean:177-185`

Lean statement:

- Compose the previous two stages to round an almost-projective measurement to a projective submeasurement.

Paper correspondence:

- This is a local composition lemma, not a named paper theorem.
- It is meant to compress the spectral truncation plus adjustment stages of the proof of `lem:orthonormalization-main-lemma`.

Assessment:

- If `spectralTruncateAlmostProjective` and `adjustTruncatedProjections` lined up with the paper, this lemma would be routine.
- Because `adjustTruncatedProjections` currently appears misaligned with the paper, this composition lemma inherits that mismatch.

Bottom line:

- Easy if the previous statement is fixed.
- Currently downstream of the same statement-design issue.

## Which `sorry`s really need square root / spectral theorem / SVD?

Needs matrix square root directly:

- `oneMeasNaimark`
- the late `sqrt(Q)` part inside `orthonormalizationMainLemma`

Needs Hermitian spectral theorem directly:

- `oneMeasNaimark` if implemented via spectral square roots
- `spectralTruncateAlmostProjective`
- the `sqrt(Q)` and diagonalization parts of `orthonormalizationMainLemma`

Needs Cauchy-Schwarz but not spectral theory:

- `consistencyToAlmostProjective`
- the top-level `orthonormalization` reduction

Needs SVD/polar-decomposition-like infrastructure:

- only the late part of `orthonormalizationMainLemma`
- practically also `adjustTruncatedProjections` if the current statement is kept

## Recommended implementation path

If the goal is to fill these `sorry`s with the least infrastructure pain, I would do this order:

1. Prove `consistencyToAlmostProjective`.
2. Revisit the statement of `adjustTruncatedProjections` before proving anything downstream.
3. Prove `spectralTruncateAlmostProjective` using explicit Hermitian diagonalization, not a search for an SVD API.
4. Prove `oneMeasNaimark` using `CFC.sqrt` or the deprecated `Matrix.PosSemidef.sqrt` name plus explicit tensor algebra.
5. Prove `naimark`.
6. Only then decide whether to formalize the paper's SVD construction, or to replace it with a different argument better aligned with available Mathlib.

## Final verdict

The answer to the user's headline question is:

- Mathlib `v4.28.0` in this repo **does** have the matrix square-root and Hermitian spectral-theorem APIs needed for the Naimark helper lemma and for spectral truncation.
- The real gap is **not** square roots or the Hermitian spectral theorem.
- The real gap is the late orthonormalization factorization machinery:
  there is no obvious off-the-shelf matrix SVD / polar decomposition / Schur-unitary-decomposition API to support the paper's `X = U Σ V†` construction.
- Independently of Mathlib, the current Lean decomposition around `adjustTruncatedProjections` appears misaligned with the paper and should be sanity-checked before implementation starts.
