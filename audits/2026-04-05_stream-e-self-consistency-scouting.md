---
title: "Stream E self-consistency API scouting"
date: 2026-04-05
author: AI research assistant
purpose: >
  Mathlib and local API scouting for self-consistency extension propositions.
status: snapshot
track: paper2009ldt
kind: scouting-report
---

# Stream E Scouting: Self-Consistency Extensions

## Scope

This note scouts existing Mathlib and `MIPStarRE` infrastructure for the five SSC-extension propositions:

1. `prop:other-two-notions-of-self-consistency`
2. `prop:two-notions-of-self-consistency-after-evaluation`
3. `prop:completeness-transfer-self-consistent-A`
4. `prop:self-consistency-implies-data-processing`
5. `prop:cool-prop`

I use "local SSC" for the square-based defect
`qSSCDefect ψ A = max 0 (ev ψ A.total - Σ_a ev ψ (A_a^2))`
and "bipartite SSC" for the overlap-based defect
`qBipartiteSSCDefect ψ A = max 0 (ev ψ (A ⊗ I).total - Σ_a ev ψ (A_a ⊗ A_a))`.

## A. Mathlib Search

### 1. Kronecker / PSD

Useful Mathlib items:

- `.lake/packages/mathlib/Mathlib/Analysis/Matrix/Order.lean:270`
  `Matrix.PosSemidef.kronecker`
  Signature:
  `x.PosSemidef -> y.PosSemidef -> (Matrix.kroneckerMap (fun x y => x * y) x y).PosSemidef`
- `.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Kronecker.lean:364`
  `Matrix.mul_kronecker_mul`
- `.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Kronecker.lean:394`
  `Matrix.conjTranspose_kronecker`
- `.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Kronecker.lean:398`
  `Matrix.conjTranspose_kronecker'`

This is already enough for the repo's `leftTensor`, `rightTensor`, `opTensor` layer, and the local code is already using `Matrix.PosSemidef.kronecker` repeatedly.

### 2. Swap / permutation on tensor products

The most relevant Mathlib items I found are:

- `.lake/packages/mathlib/Mathlib/LinearAlgebra/TensorProduct/Matrix.lean:56`
  `TensorProduct.toMatrix_comm`
  This identifies `TensorProduct.comm` with a swap permutation matrix.
- `.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Kronecker.lean:146`
  `Matrix.kroneckerMap_reindex`
- `.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Kronecker.lean:153`
  `Matrix.kroneckerMap_reindex_left`
- `.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Kronecker.lean:159`
  `Matrix.kroneckerMap_reindex_right`
- `.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/Kronecker.lean:398`
  `Matrix.conjTranspose_kronecker'`
  gives a `Prod.swap`-based reindexing formula.

Takeaway: Mathlib has the raw swap/reindex machinery, but the repo is not currently using a ready-made "swap conjugates `A ⊗ I` to `I ⊗ A`" lemma. The repo instead packages symmetry through `PermInvState.swap_ev`.

### 3. Fiberwise sums for postprocessing

Useful Mathlib items:

- `.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean`
  `Finset.sum_fiberwise`
  Signature:
  `Finset.sum_fiberwise (s : Finset ι) (g : ι -> κ) (f : ι -> M) :
    ∑ j, ∑ i ∈ s with g i = j, f i = ∑ i ∈ s, f i`
- same file:
  `Finset.sum_fiberwise_of_maps_to`
- same file:
  `Finset.sum_fiberwise_eq_sum_filter`

This is exactly the infrastructure needed for `postprocess`.

## B. Existing Repo Infrastructure

### 1. Core definitions and relations

File: `MIPStarRE/LDT/Test/Defs.lean`

- `qSSCDefect` at line 83
  `qSSCDefect ψ A := max 0 (ev ψ A.total - ∑ a, ev ψ (A.outcome a * A.outcome a))`
- `sscError` at line 112
  `sscError ψ 𝒟 A := avgOver 𝒟 (fun q => qSSCDefect ψ (A q))`
- `qBipartiteSSCDefect` at line 178
  `qBipartiteSSCDefect ψ A := max 0 (ev ψ (leftTensor A.total) - ∑ a, ev ψ (opTensor (A_a) (A_a)))`
- `ConsRel` at line 146
  wrapper around `consError ψ 𝒟 A B ≤ δ`
- `SDDRel` at line 153
  wrapper around `sddError ψ 𝒟 A B ≤ δ`
- `SSCRel` at line 167
  wrapper around `sscError ψ 𝒟 A ≤ δ`
- `BipartiteSSCRel` at line 197
  wrapper around `bipartiteSSCError ψ 𝒟 A ≤ δ`
- `postprocess_total` at line 316
  `(postprocess A f).total = A.total`

### 2. `PermInvState` API

File: `MIPStarRE/LDT/Test/Strategy.lean:32`

- `structure PermInvState (ψ : QuantumState (ι × ι)) : Prop where`
  `swap_ev : ∀ M, ev ψ (leftTensor M) = ev ψ (rightTensor M)`

What `swap_ev` gives:

- It is an expectation-level symmetry, not an operator equality.
- It is exactly what the existing SSC bridge proofs use to replace
  `ev ψ (rightTensor (A_a * A_a))` by `ev ψ (leftTensor (A_a * A_a))`.
- It is sufficient for turning left/right expansion formulas into `2 * (...)` expressions.
- There is no richer API on `PermInvState` in the repo right now.

### 3. Postprocessing and lifts

File: `MIPStarRE/LDT/Basic/SubMeasurement.lean`

- `postprocess` at line 216
  `outcome b := ∑ a ∈ univ.filter (fun a => f a = b), A.outcome a`
- `SubMeas.liftLeft` at line 362
  `A_a` becomes `A_a ⊗ I`
- `SubMeas.liftRight` at line 382
  `A_a` becomes `I ⊗ A_a`
- `IdxSubMeas.liftLeft` / `IdxSubMeas.liftRight` at lines 375 and 395
- `leftPlacedSubMeas` / `rightPlacedSubMeas` at lines 422 and 438
- `leftTensor_finset_sum` / `rightTensor_finset_sum` at lines 264 and 277

There is also raw-family postprocessing in `MIPStarRE/LDT/Basic/OpFamily.lean:79`, which may matter later for commutativity-side `SDDOpRel` bridges.

### 4. Tensor / expectation helpers

File: `MIPStarRE/LDT/Basic/Operator.lean`

- `opTensor`, `leftTensor`, `rightTensor` at lines 45, 51, 56
- `leftTensor_mul_rightTensor_eq_opTensor` at line 61
- `opTensor_nonneg` at line 70
- `opTensor_le_leftTensor` at line 78
- `opTensor_mono_left` at line 87
- `ev_nonneg_of_psd` at line 271
- `ev_mul_comm_of_psd` at line 322
- `ev_abs_mul_le_sqrt` at line 385

These are the core reusable ingredients for the SSC gap estimates.

### 5. Sandwich families

File: `MIPStarRE/LDT/Preliminaries/Defs.lean`

- `BipartiteSDDRel` at line 19
- `diagonalSandwichFamily` at line 54
  outcome `a ↦ (A_a ⊗ I) * (I ⊗ B_a)`
- `totalSandwichFamily` at line 133
  outcome `a ↦ (A.total ⊗ I) * (I ⊗ B_a)`
- `CompTransferStmt` at line 230
- `completeAtOutcome` at line 243

### 6. Already-proved preliminaries that matter here

File: `MIPStarRE/LDT/Preliminaries/Theorems.lean`

- `simeqDataProcessing` at line 313
  public opposite-side postprocessing theorem, but for `IdxMeas`, not general `IdxSubMeas`
- `stateDependentDistanceRel_triangle` at line 371
  private triangle inequality:
  `SDDRel A B δ1 -> SDDRel B C δ2 -> SDDRel A C (2 * (δ1 + δ2))`
- `consSubMeas` at line 717
- `subMeas_diagMass_le_mass` at line 815
- `projSubMeas_diagMass_eq_mass` at line 845
- `question_overlap_gap_left` at line 1008
- `question_overlap_gap_right` at line 1086
- `switchSandwich` at line 2275
- `completenessTransferProjectiveP` at line 2436
- `qSDD_liftLeft_liftRight_le_two_qBipartiteSSCDefect` at line 2521
- `twoNotionsOfSelfConsistency` at line 2731
- `bipartiteSSC_implies_localSSC_liftLeft` at line 2838
- `completion_self_distance` at line 2781
- `completingToMeasurement` at line 3200

## C. Proposition-by-Proposition Strategy

### 1. `prop:other-two-notions-of-self-consistency`

Status:

- If your hypothesis is the overlap-based bipartite SSC notion, this is already essentially formalized by
  `Preliminaries.twoNotionsOfSelfConsistency`.
- If your hypothesis is the square-based local `SSCRel`, then the exact bridge is not present.

Existing proof path:

- `qSDD_liftLeft_liftRight_le_two_qBipartiteSSCDefect`
  proves the pointwise estimate.
- `twoNotionsOfSelfConsistency`
  averages it to `SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftRight A) (2 * δ)`.

Important nuance:

- The existing theorem gives error `2 * δ`, not `δ`.
- The current proof genuinely uses `PermInvState.swap_ev`.

Difficulty:

- Low if a rephrasing of the existing theorem is acceptable.
- Medium if you need local square-based SSC as the hypothesis.

### 2. `prop:two-notions-of-self-consistency-after-evaluation`

What already exists:

- The pointwise postprocessing monotonicity needed for bipartite overlap defects is already proved privately:
  `qConsDefect_leftRight_postprocess_le` in `Preliminaries/Theorems.lean:267`.
- `simeqDataProcessing` is public, but specialized to full measurements.

Likely proof strategy:

1. Add a short public wrapper:
   postprocessing preserves `BipartiteSSCRel` for `IdxSubMeas`.
   This is just the private `qConsDefect_leftRight_postprocess_le` averaged.
2. Apply that wrapper to `A` and `f`.
3. Reuse `twoNotionsOfSelfConsistency` on the postprocessed family.

So proposition 2 looks structurally short once the right public wrapper exists.

Difficulty:

- Low-to-medium.
- The main work is API exposure, not mathematics.

### 3. `prop:completeness-transfer-self-consistent-A`

This one is not already present as a public theorem, but the proof ingredients are all there.

Best route:

1. Unpack SSC of `A` to get
   `diagA := Σ_a ev ψ (A_a^2) >= mass(A) - δ`.
   If the hypothesis is bipartite SSC, use `bipartiteSSC_implies_localSSC_liftLeft` first.
2. Let
   `overlap := Σ_a ev ψ (A_a * B_a)`,
   `diagB := Σ_a ev ψ (B_a^2)`.
3. Use
   `question_overlap_gap_left` to show `diagA - overlap <= sqrt ε`.
4. Use
   `question_overlap_gap_right` to show `overlap - diagB <= sqrt ε`.
5. Use
   `subMeas_diagMass_le_mass`
   to get `diagB <= mass(B)`.
6. Chain:
   `mass(B) >= diagB >= overlap - sqrt ε >= diagA - 2 sqrt ε >= mass(A) - δ - 2 sqrt ε`.

Important caveat:

- The existing overlap-gap lemmas require a normalized state hypothesis `ψ.IsNormalized`.

Difficulty:

- Medium.
- The proof should be fairly short once the exact hypothesis is chosen.

### 4. `prop:self-consistency-implies-data-processing`

This is the genuinely hard one.

The existing code strongly suggests the intended ingredients are:

- `twoNotionsOfSelfConsistency`
- a public bipartite-SSC postprocess wrapper for submeasurements
- `consSubMeas`
- `switchSandwich`
- `completenessTransferProjectiveP`
- `completingToMeasurement`
- `stateDependentDistanceRel_triangle`

Why I think this is the right cluster:

- `consSubMeas` and the sandwich families are precisely the bridge from opposite-side consistency to same-side approximations involving `A_a ⊗ B_a` and `A.total ⊗ B_a`.
- `switchSandwich` is the projective-specific Cauchy-Schwarz/sandwich transport theorem.
- `completenessTransferProjectiveP` and `completingToMeasurement` are the repo's existing ways of controlling missing mass and converting submeasurements into honest measurements with quantitative error.

Most plausible proof shape:

1. Derive approximate self-consistency / opposite-side consistency for the relevant projective object `P`.
2. Postprocess on opposite sides, where the monotonicity theorem is true.
3. Compare the postprocessed same-side left-lift families through sandwich families.
4. Use triangle bookkeeping to collapse to the target `8δ + 8√ε` bound.

What still looks missing:

- A public postprocess theorem for bipartite SSC on `IdxSubMeas`.
- Possibly one or two rewriting lemmas turning the exact postprocessed target into the already-defined sandwich/normalization families cleanly.
- Depending on the exact formal statement, you may also need a public version of the private triangle lemma.

Difficulty:

- High.
- This is the proposition most likely to need small bridge lemmas even though the big ingredients are already in place.

### 5. `prop:cool-prop`

This is basically already contained in the repo.

If the intended hypothesis is bipartite SSC:

- `bipartiteSSC_implies_localSSC_liftLeft`
  gives `SSCRel ψ 𝒟 (IdxSubMeas.liftLeft A) ζ`.
- Specializing to a constant family over `Unit` rewrites exactly to
  `Σ_a ev ψ (leftTensor (A_a * A_a)) >= ev ψ (leftTensor A.total) - ζ`.
- Since `leftTensor` is multiplicative (`leftTensor_mul_leftTensor`), this is the desired
  `Σ_a <ψ|A_a^2 ⊗ I|ψ> >= Σ_a <ψ|A_a ⊗ I|ψ> - ζ`.

If the intended hypothesis is already local SSC on `A.liftLeft`, then the statement is nearly just `qSSCDefect` unfolded.

Difficulty:

- Very low.
- This should be a short public corollary.

## D. Dependencies / Suggested Order

Suggested order if these are to become public theorems:

1. Re-expose proposition 1 from `twoNotionsOfSelfConsistency` if the bipartite hypothesis is acceptable.
2. Add a public `BipartiteSSCRel` postprocess lemma for `IdxSubMeas`.
3. Deduce proposition 2 from step 2 plus proposition 1.
4. Publish proposition 5 as a corollary of `bipartiteSSC_implies_localSSC_liftLeft`.
5. Prove proposition 3 from proposition 5 plus the overlap-gap lemmas.
6. Attack proposition 4 last, using the already-proved sandwich/completion theorems.

Independence notes:

- Proposition 5 is almost independent and should be the easiest new public statement.
- Proposition 3 does not need proposition 2.
- Proposition 4 is the one that really depends on the rest of the graph.

## E. Bottom Line

- Proposition 1: already present up to hypothesis packaging and a factor-of-2 convention.
- Proposition 2: mathematically almost done; needs a small public wrapper for submeasurement postprocessing.
- Proposition 3: should be straightforward from existing overlap-gap lemmas.
- Proposition 4: hardest item; likely mostly theorem-chaining plus 1-3 missing bridge lemmas.
- Proposition 5: essentially already proved privately.
