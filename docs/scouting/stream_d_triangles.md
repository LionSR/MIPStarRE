# Stream D Scouting: Triangle Inequalities

## Executive Summary

- `prop:triangle-inequality-for-vectors-squared` does **not** appear to exist in the current Mathlib snapshot under a ready-made name like `norm_sum_sq_le`, `sum_norm_sq_le`, or `sq_norm_sum_le`.
- Mathlib **does** already provide the exact lower-level ingredients needed to prove it in a short Lean proof:
  `norm_sum_le`, `sq_sum_le_card_mul_sum_sq`, `pow_sum_le_card_mul_sum_pow`, `norm_add_sq`, `norm_inner_le_norm`, and `re_inner_le_norm`.
- The local codebase already contains the key analytic infrastructure for `prop:triangle-sub`:
  a state-weighted Cauchy-Schwarz lemma, a weighted finite-sum Cauchy-Schwarz, diagonal-mass bounds for submeasurements, and two overlap-gap lemmas proved by exactly the paper's style of argument.
- `prop:simeq-triangle-inequality` should compose cleanly from:
  `simeqToApprox` + existing `≈` triangle + new `triangle-sub`,
  with constants matching the paper after simplification:
  `sqrt (4 * (δ + γ)) = 2 * sqrt (δ + γ)`.
- Dependency-wise:
  `prop:triangle-inequality-for-vectors-squared` is standalone.
  `prop:triangle-sub` does **not** need it in the current codebase, because the repo already uses `Real.sum_sqrt_mul_sqrt_le` directly.
  `prop:simeq-triangle-inequality` depends on `prop:triangle-sub` plus existing local lemmas.

## A. Mathlib Findings

### Core norm and inner-product lemmas

- `.lake/packages/mathlib/Mathlib/Analysis/Normed/Group/Basic.lean:772`

```lean
theorem norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (f : ι → E) :
    ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖
```

- `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean:401`

```lean
theorem norm_add_sq (x y : E) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * re ⟪x, y⟫ + ‖y‖ ^ 2
```

- `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean:454`

```lean
theorem norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖
```

- `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean:462`

```lean
theorem re_inner_le_norm (x y : E) : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖
```

- `.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Basic.lean:390`

```lean
theorem inner_self_eq_norm_sq (x : E) : re ⟪x, x⟫ = ‖x‖ ^ 2
```

There is no hit for `inner_mul_le_norm_mul_norm` in this snapshot; the usable current names are `norm_inner_le_norm` and `re_inner_le_norm`.

### Finite-sum squared inequalities

- `.lake/packages/mathlib/Mathlib/Algebra/Order/Chebyshev.lean:137`

```lean
theorem sq_sum_le_card_mul_sum_sq :
    (∑ i ∈ s, f i) ^ 2 ≤ #s * ∑ i ∈ s, f i ^ 2
```

- `.lake/packages/mathlib/Mathlib/Algebra/Order/Chebyshev.lean:120`

```lean
lemma pow_sum_le_card_mul_sum_pow (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∀ n, (∑ i ∈ s, f i) ^ (n + 1) ≤ (#s : α) ^ n * ∑ i ∈ s, f i ^ (n + 1)
```

- `.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:221`

```lean
lemma sum_mul_sq_le_sq_mul_sq (s : Finset ι) (f g : ι → R) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2
```

- `.lake/packages/mathlib/Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean:106`

```lean
lemma sum_sq_le_sq_sum_of_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) :
    ∑ i ∈ s, f i ^ 2 ≤ (∑ i ∈ s, f i) ^ 2
```

### Square-root Cauchy-Schwarz for sums

- `.lake/packages/mathlib/Mathlib/Data/Real/Sqrt.lean:489`

```lean
lemma Real.sum_sqrt_mul_sqrt_le (s : Finset ι) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    ∑ i ∈ s, √(f i) * √(g i) ≤ √(∑ i ∈ s, f i) * √(∑ i ∈ s, g i)
```

This is exactly the finite-sum Cauchy-Schwarz shape already used throughout the local repo.

### Bottom line for `prop:triangle-inequality-for-vectors-squared`

I did **not** find a theorem already packaged as

- `norm_sum_sq_le`
- `sum_norm_sq_le`
- `sq_norm_sum_le`
- `norm_sum_le_card_smul_sum_norm_sq`

in the current Mathlib checkout.

The intended proof can be built immediately from existing lemmas:

```lean
calc
  ‖∑ i ∈ s, ψ i‖ ^ 2 ≤ (∑ i ∈ s, ‖ψ i‖) ^ 2 := by
    gcongr
    exact norm_sum_le s ψ
  _ ≤ s.card * ∑ i ∈ s, ‖ψ i‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => ‖ψ i‖)
```

For a family indexed by a finite type with `k = Fintype.card α`, this becomes

```lean
‖∑ i, ψ i‖ ^ 2 ≤ k * ∑ i, ‖ψ i‖ ^ 2
```

So item 1 is a short wrapper theorem, not a missing deep fact.

## B. Existing Local Helpers

### Already in `MIPStarRE/LDT/Basic/Operator.lean`

- `MIPStarRE/LDT/Basic/Operator.lean:237`

```lean
theorem ev_diff_triangle
    (ψ : QuantumState ι) (X Y Z : MIPStarRE.Quantum.Op ι) :
    ev ψ ((X - Z)ᴴ * (X - Z)) ≤
    2 * (ev ψ ((X - Y)ᴴ * (X - Y)) + ev ψ ((Y - Z)ᴴ * (Y - Z)))
```

- `MIPStarRE/LDT/Basic/Operator.lean:332`

```lean
theorem ev_cauchy_schwarz
    (ψ : QuantumState ι) (A B : MIPStarRE.Quantum.Op ι) :
    (ev ψ (Aᴴ * B)) ^ 2 ≤ ev ψ (Aᴴ * A) * ev ψ (Bᴴ * B)
```

- `MIPStarRE/LDT/Basic/Operator.lean:385`

```lean
theorem ev_abs_mul_le_sqrt
    (ψ : QuantumState ι) (A B : MIPStarRE.Quantum.Op ι) :
    |ev ψ (A * B)| ≤
      Real.sqrt (ev ψ (A * Aᴴ)) * Real.sqrt (ev ψ (Bᴴ * B))
```

This is the main operator-level Cauchy-Schwarz helper used in the local proofs.

### Already in `MIPStarRE/LDT/Preliminaries/Theorems.lean`

- `MIPStarRE/LDT/Preliminaries/Theorems.lean:121`

```lean
theorem simeqToApprox
    ... :
    ConsRel ψ 𝒟 (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) δ →
    BipartiteSDDRel ψ 𝒟 (IdxMeas.toIdxSubMeas A) (IdxMeas.toIdxSubMeas B) (2 * δ)
```

- `MIPStarRE/LDT/Preliminaries/Theorems.lean:346`

```lean
private lemma questionSDD_triangle
    (ψ : QuantumState ι) (A B C : SubMeas Outcome ι) :
    qSDD ψ A C ≤ 2 * (qSDD ψ A B + qSDD ψ B C)
```

- `MIPStarRE/LDT/Preliminaries/Theorems.lean:371`

```lean
private lemma stateDependentDistanceRel_triangle
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B C : IdxSubMeas Question Outcome ι) (δ₁ δ₂ : Error) :
    SDDRel ψ 𝒟 A B δ₁ →
    SDDRel ψ 𝒟 B C δ₂ →
    SDDRel ψ 𝒟 A C (2 * (δ₁ + δ₂))
```

- `MIPStarRE/LDT/Preliminaries/Theorems.lean:739`

```lean
private lemma weightedFinsetCauchySchwarz
    (𝒟 : Distribution Question)
    (t x y : Question → Outcome → Error)
    ...
    :
    |avgOver 𝒟 (fun q => ∑ a, t q a)| ≤
      Real.sqrt (avgOver 𝒟 (fun q => ∑ a, x q a)) *
      Real.sqrt (avgOver 𝒟 (fun q => ∑ a, y q a))
```

- `MIPStarRE/LDT/Preliminaries/Theorems.lean:815`

```lean
lemma subMeas_diagMass_le_mass
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) :
    ∑ a, ev ψ (A.outcome a * A.outcome a) ≤ ev ψ A.total
```

- `MIPStarRE/LDT/Preliminaries/Theorems.lean:832`

```lean
lemma subMeas_diagMass_le_one
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized) (A : SubMeas Outcome ι) :
    ∑ a, ev ψ (A.outcome a * A.outcome a) ≤ 1
```

- `MIPStarRE/LDT/Preliminaries/Theorems.lean:973`

```lean
private lemma avgOver_abs_le_sqrt_of_pointwise
    (𝒟 : Distribution Question) (f g : Question → Error)
    (hf : ∀ q, |f q| ≤ Real.sqrt (g q))
    (hg : ∀ q, 0 ≤ g q)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    |avgOver 𝒟 f| ≤ Real.sqrt (avgOver 𝒟 g)
```

- `MIPStarRE/LDT/Preliminaries/Theorems.lean:1008`

```lean
private lemma question_overlap_gap_left
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized) (A B : SubMeas Outcome ι) :
    |(∑ a, ev ψ (A.outcome a * A.outcome a)) -
      ∑ a, ev ψ (A.outcome a * B.outcome a)| ≤
    Real.sqrt (qSDD ψ A B)
```

- `MIPStarRE/LDT/Preliminaries/Theorems.lean:1086`

```lean
private lemma question_overlap_gap_right
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized) (A B : SubMeas Outcome ι) :
    |(∑ a, ev ψ (A.outcome a * B.outcome a)) -
      ∑ a, ev ψ (B.outcome a * B.outcome a)| ≤
    Real.sqrt (qSDD ψ A B)
```

- `MIPStarRE/LDT/Preliminaries/Theorems.lean:1161`

```lean
private lemma sum_ev_mul_leftBounded_le_of_leftHermitian
    (ψ : QuantumState ι)
    (LB : MIPStarRE.Quantum.Op ι)
    (X Y : Outcome → MIPStarRE.Quantum.Op ι)
    ...
    :
    |∑ a, ev ψ (X a * (LB * Y a))| ≤
      Real.sqrt (∑ a, ev ψ (X a * X a)) *
      Real.sqrt (∑ a, ev ψ ((Y a)ᴴ * Y a))
```

This last lemma is the most reusable local ingredient for `prop:triangle-sub`.

### Important local template

- `MIPStarRE/LDT/Preliminaries/Theorems.lean:2296`
  `completenessTransfer_core`

This proof already performs the same high-level maneuver needed for `triangle-sub`:

- define pointwise overlap gaps;
- bound them by `sqrt (qSDD ...)`;
- average them;
- convert `avg sqrt(sdd)` into `sqrt(avg sdd)`.

So even though the exact theorem is different, the proof architecture is already present in the file.

## C. Proposition-by-Proposition Assessment

### 1. `prop:triangle-inequality-for-vectors-squared`

Status:
not present as a ready-made theorem name in current Mathlib.

Best proof route:

```lean
calc
  ‖∑ i ∈ s, ψ i‖ ^ 2 ≤ (∑ i ∈ s, ‖ψ i‖) ^ 2 := by
    gcongr
    exact norm_sum_le s ψ
  _ ≤ s.card * ∑ i ∈ s, ‖ψ i‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => ‖ψ i‖)
```

If you want the paper statement with a literal scalar `k`, the cleanest index type is probably `Fin k` or any finite type plus `k = Fintype.card α`.

### 2. `prop:triangle-sub`

Paper shape:

```text
If A⊗I ≃_δ I⊗C and A⊗I ≈_ε B⊗I, then B⊗I ≃_{δ + √ε} I⊗C.
```

Local shape that matches the codebase best:

```lean
ConsRel ψ 𝒟 (IdxSubMeas.liftLeft A.toSubMeas) (IdxSubMeas.liftRight C) δ
SDDRel  ψ 𝒟 (IdxSubMeas.liftLeft A.toSubMeas) (IdxSubMeas.liftLeft B.toSubMeas) ε
⊢
ConsRel ψ 𝒟 (IdxSubMeas.liftLeft B.toSubMeas) (IdxSubMeas.liftRight C) (δ + Real.sqrt ε)
```

Likely extra assumptions:

- `hψ : ψ.IsNormalized`
- `h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1`

The state normalization is needed for `subMeas_diagMass_le_one`.
The distribution-mass bound is needed for `avgOver_abs_le_sqrt_of_pointwise`.

Recommended proof strategy:

1. Work questionwise.
2. Let

```text
overlapAC q := ∑ a, ev ψ ((A_a ⊗ I) * (I ⊗ C_a))
overlapBC q := ∑ a, ev ψ ((B_a ⊗ I) * (I ⊗ C_a))
```

3. Since `A` and `B` are measurements, both left totals are `1`, so the `qConsDefect` total-overlap term is the same for `(A,C)` and `(B,C)`. The only thing that changes is the diagonal overlap sum.
4. Rewrite

```text
overlapAC q - overlapBC q
  = ∑ a, ev ψ (((A_a - B_a) ⊗ I) * (I ⊗ C_a)).
```

5. Apply `sum_ev_mul_leftBounded_le_of_leftHermitian` with:

- `LB := 1`
- `X a := leftTensor (A_a - B_a)`
- `Y a := rightTensor (C_a)`

The hypotheses are easy:

- `LBᴴ = LB` and `LB * LB ≤ 1` are trivial for `LB = 1`;
- `X a` is Hermitian because measurement outcomes are PSD, hence Hermitian;
- `Y a` is Hermitian because submeasurement outcomes are PSD.

6. The conclusion becomes

```text
|overlapAC q - overlapBC q|
  ≤ sqrt (qSDD ψ ((liftLeft A) q) ((liftLeft B) q))
    * sqrt (diagC q).
```

7. Bound `diagC q ≤ 1` by `subMeas_diagMass_le_one ψ hψ ((IdxSubMeas.liftRight C) q)` or the equivalent unsimplified form.
8. Conclude the pointwise inequality

```text
qConsDefect ψ ((liftLeft B) q) ((liftRight C) q)
  ≤ qConsDefect ψ ((liftLeft A) q) ((liftRight C) q)
    + sqrt (qSDD ψ ((liftLeft A) q) ((liftLeft B) q)).
```

9. Average over `𝒟`.
10. Use `avgOver_abs_le_sqrt_of_pointwise` to convert

```text
avgOver 𝒟 (fun q => sqrt (sdd q)) ≤ sqrt (avgOver 𝒟 sdd).
```

11. Finish with the hypotheses `hAC` and `hAB`.

Key point:
this theorem does **not** need the standalone vector inequality from item 1. The existing local finite-sum Cauchy-Schwarz machinery is already exactly what the proof wants.

### 3. `prop:simeq-triangle-inequality`

Paper shape:

```text
If A⊗I ≃_ε I⊗B, C⊗I ≃_δ I⊗B, C⊗I ≃_γ I⊗D,
then A⊗I ≃_{ε + 2√(δ + γ)} I⊗D.
```

Composition route:

1. Apply `simeqToApprox` to the second and third premises:

```text
C⊗I ≈_{2δ} I⊗B
C⊗I ≈_{2γ} I⊗D
```

2. Use the existing `≈` triangle (`stateDependentDistanceRel_triangle`) to get an `≈` relation between `I⊗B` and `I⊗D`.
   With the current local constants this gives error `4 * (δ + γ)`.

3. Apply the right-handed analogue of `triangle-sub` to combine

```text
A⊗I ≃_ε I⊗B
I⊗B ≈_{4(δ+γ)} I⊗D
```

and obtain

```text
A⊗I ≃_{ε + sqrt (4 * (δ + γ))} I⊗D
```

which simplifies to

```text
A⊗I ≃_{ε + 2 * Real.sqrt (δ + γ)} I⊗D.
```

### One subtlety to plan for

For this composition to be completely smooth, you will probably want one small auxiliary lemma that I did **not** find already packaged in the repo:

- symmetry of `qSDD` / `SDDRel`, or
- a mirrored "triangle-sub on the right" theorem.

Reason:
`simeqToApprox` naturally produces a left-vs-right `≈` relation, while the final composition is most naturally stated by perturbing the **right** family `I⊗B -> I⊗D`. The constants still line up perfectly, but one of those small API lemmas will make the final theorem much cleaner.

## D. Dependency Graph

- Item 1 is standalone pure linear algebra.
- Item 2 depends on existing local operator Cauchy-Schwarz and diagonal-mass lemmas, not on item 1.
- Item 3 depends on:
  `simeqToApprox`
  `stateDependentDistanceRel_triangle`
  the new `triangle-sub`
  and likely a tiny symmetry/mirror helper for `≈`.

## E. Recommended Minimal Implementation Order

1. Add the standalone finite-sum theorem for vectors squared as a small Mathlib-wrapper lemma.
2. Add a reusable pointwise overlap-perturbation lemma generalizing `question_overlap_gap_right` from `B` to an arbitrary submeasurement `C`.
3. Package that averaged version as `prop:triangle-sub`.
4. Add either `qSDD` symmetry or a right-handed `triangle-sub`.
5. Finish `prop:simeq-triangle-inequality` by composing existing results with the new theorem.
