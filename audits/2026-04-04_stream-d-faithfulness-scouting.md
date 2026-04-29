---
title: "Stream D faithfulness scouting"
date: 2026-04-04
purpose: >
  Faithfulness scouting for the triangle-inequality propositions in the preliminaries.
status: snapshot
track: paper2009ldt
kind: scouting-report
---

# Stream D Faithfulness: Triangle Inequalities

Date: 2026-04-04

This note compares the exact paper statements in `references/ldt-paper/preliminaries.tex` with the current Lean relation types.

## Executive Summary

- `prop:triangle-sub` is a mixed-side statement:
  `A, B` are measurements on the left register, `C` is a submeasurement on the right register.
  The first hypothesis is cross-side consistency (`≃`), but the second is same-side squared distance (`≈`) between `A ⊗ I` and `B ⊗ I`.
- Because of that, the faithful Lean shape for `prop:triangle-sub` is:
  `ConsRel` for the `≃` hypothesis and conclusion, plus plain `SDDRel` on left-lifted families for the `≈` hypothesis.
  `BipartiteSDDRel` is the wrong relation there.
- `prop:simeq-triangle-inequality` should be a theorem on four measurements with three `ConsRel` hypotheses and one `ConsRel` conclusion.
  Sidewise, `A, C` live on the left and `B, D` live on the right after tensor placement.
- `prop:triangle-inequality-for-approx_delta` is stated in the paper for arbitrary matrix families, so the most faithful Lean version is over `IdxOpFamily` / `SDDOpRel`.
  The current private `stateDependentDistanceRel_triangle` is the right two-step
  submeasurement specialization, but not the exact type used in the paper.
- `prop:triangle-inequality-for-vectors-squared` should stay a pure normed-space lemma.
  It should not be restated in terms of `ev` or operator norms.

## 1. `prop:triangle-sub`

Paper statement:

- `A = {A_a^x}` and `B = {B_a^x}` are measurements.
- `C = {C_a^x}` is a submeasurement.
- Hypotheses:
  `A_a^x ⊗ I ≃_δ I ⊗ C_a^x`
  and
  `A_a^x ⊗ I ≈_ε B_a^x ⊗ I`.
- Conclusion:
  `B_a^x ⊗ I ≃_{δ + sqrt ε} I ⊗ C_a^x`.

Faithfulness points:

- The `≈_ε` hypothesis is definitely same-side.
  It compares `A ⊗ I` and `B ⊗ I`, not `A ⊗ I` and `I ⊗ B`.
- The bipartite layout is:
  `A, B` on `H_A`,
  `C` on `H_B`.
- The paper does not require `H_A = H_B`.
  The current `leftTensor` / `rightTensor` operators support distinct dimensions, but the existing `SubMeas.liftLeft` / `liftRight` API is specialized to `(ι × ι)`.
  So the proposed signature is the most faithful version available inside the current codebase, not the fully dimension-polymorphic mathematical statement.
- The proof uses that both `A` and `B` are measurements when rewriting
  `∑_a A_a^x = I` and `∑_a B_a^x = I`.
  It only uses `C` as a submeasurement.

Best Lean formulation:

- Use `ConsRel` for the cross-side `≃` hypothesis and conclusion.
- Use plain `SDDRel` for the same-side `≈` hypothesis, with both families left-lifted into the ambient bipartite space.
- Do not use `BipartiteSDDRel` for the `≈` hypothesis:
  `BipartiteSDDRel ψ 𝒟 A B ε` means `A ⊗ I ≈_ε I ⊗ B`, which is not the paper hypothesis.

Most faithful signature in the current codebase:

```lean
theorem triangleSub
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : IdxMeas Question Outcome ι)
    (C : IdxSubMeas Question Outcome ι)
    (δ ε : Error) :
    ConsRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A))
      (IdxSubMeas.liftRight C) δ →
    SDDRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A))
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas B)) ε →
    ConsRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas B))
      (IdxSubMeas.liftRight C)
      (δ + Real.sqrt ε)
```

Why the extra `hψ` and `h𝒟` appear:

- The paper suppresses normalization and probability-mass assumptions.
- The local `QuantumState` type does not encode normalization.
- The local `Distribution` type does not encode that weights sum to `1`.
- The proof needs exactly those facts to bound the submeasurement diagonal mass by `1`, so the faithful Lean theorem should add them explicitly rather than weakening the relation types.

Constant check:

- The paper bound is exactly `δ + sqrt ε`.
- That matches the current proof style:
  difference of the diagonal overlaps is bounded by `sqrt ε`,
  then added to the original `δ`.

## 2. `prop:triangle-inequality-for-vectors-squared`

Paper statement:

- Pure linear algebra.
- Inputs are just vectors `|ψ_1⟩, ..., |ψ_k⟩`.
- No measurements, submeasurements, tensor placement, or state-dependent expectation values appear.

Best Lean formulation:

- Keep it as a pure normed-space fact.
- Do not restate it using `ev`.
- Do not specialize it to operators unless a later proof absolutely forces that.

Recommended signature:

```lean
theorem norm_sq_sum_le_card_mul_sum_norm_sq
    {α E : Type*}
    [DecidableEq α] [NormedAddCommGroup E]
    (s : Finset α) (v : α → E) :
    ‖∑ a in s, v a‖ ^ 2 ≤ (s.card : ℝ) * ∑ a in s, ‖v a‖ ^ 2
```

If a `Fintype`-indexed corollary is more convenient later, add it on top of this.

## 3. `prop:triangle-inequality-for-approx_delta`

Paper statement:

- The families are arbitrary matrices.
- This is not restricted to measurements or submeasurements.
- The proposition is ambient-space only:
  no bipartite structure is built into the statement itself.

Faithfulness point:

- The relation in the paper is best matched by the raw-family API:
  `OpFamily`, `IdxOpFamily`, `qSDDOp`, `SDDOpRel`.
- The existing private theorem
  `stateDependentDistanceRel_triangle`
  is mathematically the right binary inequality, but it is typed over `IdxSubMeas`, not raw families.

Most faithful Lean signature:

```lean
theorem stateDependentDistanceOpRel_triangle
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B C : IdxOpFamily Question Outcome ι)
    (δ₁ δ₂ : Error) :
    SDDOpRel ψ 𝒟 A B δ₁ →
    SDDOpRel ψ 𝒟 B C δ₂ →
    SDDOpRel ψ 𝒟 A C (2 * (δ₁ + δ₂))
```

Interpretation:

- This is the `k = 2` primitive.
- The exact paper statement with `A₁, ..., A_{k+1}` should then be an induction corollary over this binary theorem.
- For the `simeq` triangle proof, the current submeasurement theorem is already enough, because the instantiated families happen to be lifted measurements.

Constant check:

- Paper chain statement:
  `k * (δ₁ + ... + δ_k)`.
- Binary specialization:
  `2 * (δ₁ + δ₂)`.
- That matches the current private theorem exactly.

## 4. `prop:simeq-triangle-inequality`

Paper statement:

- All four families `A, B, C, D` are measurements.
- Side assignment in the hypotheses is:
  `A, C` on the left,
  `B, D` on the right.
- The three hypotheses are all cross-side `≃` statements:
  `A ⊗ I ≃_ε I ⊗ B`,
  `C ⊗ I ≃_δ I ⊗ B`,
  `C ⊗ I ≃_γ I ⊗ D`.

Best Lean formulation:

- Use `IdxMeas` for all four families.
- Use `ConsRel` throughout, with explicit left/right lifts.
- `ConsAgreement` is not the right surface API here:
  it hides the tensor-side placement, and `triangle-sub` needs the cross-side structure explicitly.

Most faithful signature in the current codebase:

```lean
theorem simeqTriangle
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B C D : IdxMeas Question Outcome ι)
    (ε δ γ : Error) :
    ConsRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) ε →
    ConsRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas C))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) δ →
    ConsRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas C))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D)) γ →
    ConsRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D))
      (ε + 2 * Real.sqrt (δ + γ))
```

How it should be proved:

- Convert the second and third `ConsRel` hypotheses with `simeqToApprox`.
- Unfold `BipartiteSDDRel` to obtain same-ambient `SDDRel` statements on
  `liftLeft C`, `liftRight B`, and `liftRight D`.
- Apply the binary `≈` triangle inequality to get
  `I ⊗ B ≈_{4δ + 4γ} I ⊗ D`.
- Feed that into `triangleSub` together with the first `ConsRel` hypothesis.

Constant check:

- `simeqToApprox` gives `2δ` and `2γ`.
- The binary `≈` triangle gives
  `2 * ((2δ) + (2γ)) = 4δ + 4γ`.
- `triangleSub` then gives
  `ε + sqrt (4δ + 4γ) = ε + 2 * sqrt (δ + γ)`.
- So the exact final paper constant is
  `ε + 2 * sqrt (δ + γ)`,
  not `ε + δ + γ`.

## 5. Relation map

- Paper `A ⊗ I ≃_δ I ⊗ C`
  maps to
  `ConsRel ψ 𝒟 (liftLeft A) (liftRight C) δ`.
- Paper `A ⊗ I ≈_ε B ⊗ I`
  maps to
  `SDDRel ψ 𝒟 (liftLeft A) (liftLeft B) ε`.
- Paper `A ⊗ I ≈_ε I ⊗ B`
  maps to
  `BipartiteSDDRel ψ 𝒟 A B ε`.

So for `prop:triangle-sub`, the correct answer is:

- yes, the `≈_ε` is same-side;
- no, `BipartiteSDDRel` is not the right hypothesis there;
- yes, the faithful Lean theorem should mix `ConsRel` and `SDDRel`.

## 6. Final Recommendation

- Keep `prop:triangle-inequality-for-vectors-squared` as a standalone pure norm lemma.
- Expose a raw-family public theorem for the binary `≈` triangle inequality on `SDDOpRel`.
- State `prop:triangle-sub` with:
  `A, B : IdxMeas`,
  `C : IdxSubMeas`,
  one `ConsRel` hypothesis,
  one same-side `SDDRel` hypothesis on left lifts,
  and a `ConsRel` conclusion.
- State `prop:simeq-triangle-inequality` with four `IdxMeas` families and three `ConsRel` hypotheses.
- Keep `ConsAgreement` out of these theorem signatures.
  It is equivalent for measurement/measurement consistency, but it hides the side placement that matters here.
