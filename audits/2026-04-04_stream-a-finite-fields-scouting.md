---
title: "Stream A finite-fields scouting"
date: 2026-04-04
author: AI research assistant
purpose: >
  Mathlib scouting for finite fields, finite-field traces, additive characters, and Fourier orthogonality.
status: snapshot
track: paper2009ldt
kind: scouting-report
---

# Stream A Scouting: Finite Fields and Fourier Orthogonality

Date: 2026-04-04

## Executive Summary

Mathlib already has the core ingredients for the paper's preliminaries:

1. a genuine finite-field carrier `GaloisField p n`,
2. the finite-field trace `Algebra.trace (ZMod p) F`,
3. an explicit trace formula
   `algebraMap _ _ (Algebra.trace _ _ x) = ∑ i < [F : ZMod p], x ^ (p ^ i)`,
4. additive-character orthogonality lemmas strong enough to prove
   `𝔼_x ω^(tr (x * a)) = if a = 0 then 1 else 0`,
5. product/expectation lemmas that make the vector case straightforward.

The main gap is not Mathlib. It is the current local model:

- `MIPStarRE.LDT.Basic.Parameters` uses `Fq := Fin q` and `Scalar := ZMod q`.
- That is only semantically correct for prime `q`.
- For prime powers `q = p^t` with `t > 1`, the paper's `𝔽_q` should instead be modeled by
  `GaloisField p t` or the local wrapper `HonestFq`.

So the recommendation is:

- For paper-accurate finite-field formalization, use `GaloisField p t` plus a small local wrapper
  layer for trace and characters.
- Keep the existing `ZMod q`/`Fin q` infrastructure only for prime-field or coding-only parts.

## Existing Local Code

### Core parameter model

From `MIPStarRE/LDT/Basic/Parameters.lean`:

```lean
abbrev Fq (params : Parameters) := Fin params.q
abbrev Point (params : Parameters) := Fin params.m → Fq params
abbrev Scalar (params : Parameters) := ZMod params.q
abbrev PolynomialModel (params : Parameters) := MvPolynomial (Fin params.m) (Scalar params)
abbrev LinePolynomialModel (params : Parameters) := _root_.Polynomial (Scalar params)

structure PrimePowerFieldSpec (params : Parameters) where
  p : ℕ
  n : ℕ
  pPrime : Nat.Prime p
  nPos : 0 < n
  cardEq : params.q = p ^ n

noncomputable abbrev HonestFq (params : Parameters) (spec : PrimePowerFieldSpec params) :=
  letI : Fact spec.p.Prime := ⟨spec.pPrime⟩
  GaloisField spec.p spec.n

def decodeScalar {params : Parameters} (x : Fq params) : Scalar params := ...
def encodeScalar {params : Parameters} (x : Scalar params) : Fq params := ...
```

Takeaway:

- There is already a hook for genuine finite fields: `PrimePowerFieldSpec` and `HonestFq`.
- But the active polynomial and point infrastructure still runs over `Fin q` and `ZMod q`.
- I did not find a local finite-field trace definition.
- I did not find a local `decodeScalar`/`encodeScalar` bridge from coded points into `HonestFq`.

### Existing Fourier/character work in the repo

From `MIPStarRE/LDT/ExpansionHypercubeGraph/Defs.lean`:

```lean
noncomputable def dotProductZMod (params : Parameters) (u α : Point params) : ZMod params.q :=
  ∑ i : Fin params.m, ((u i).val : ZMod params.q) * ((α i).val : ZMod params.q)

lemma sum_stdAddChar_mul_fin (params : Parameters) (a : ZMod params.q) :
    ∑ x : Fq params, ZMod.stdAddChar (N := params.q) (((x.val : ZMod params.q) * a)) =
      if a = 0 then params.q else 0 := by
  ...

lemma fourierBasisState_update_sum (params : Parameters) (u α : Point params)
    (i : Fin params.m) :
    ∑ x : Fq params, fourierBasisState params α (Function.update u i x) =
      ((if α i = (0 : Fq params) then params.q else 0 : ℕ) : ℂ) *
        fourierBasisState params α u := by
  ...
```

Takeaway:

- There is already a scalar orthogonality lemma in the repo, but over `ZMod q`, not `𝔽_q`.
- There is also already a coordinate-wise summation lemma that is close in spirit to the vector
  factorization argument.
- This is useful if `q` is prime.
- It does not solve the prime-power finite-field case.

### Explicit local note about the prime-power gap

From `MIPStarRE/LDT/Pasting/Defs.lean`:

```lean
-- Note: honest Lagrange interpolation requires Field (ZMod q), which
-- holds only for prime q. For prime-power q, use GaloisField via
-- PrimePowerFieldSpec. For now, use Lagrange basis coefficient = 1
```

This matches the main finding of this scouting pass.

## Mathlib Declarations Found

### 1. Finite-field carrier and cardinality

File: `Mathlib/FieldTheory/Finite/GaloisField.lean`

```lean
def GaloisField := SplittingField (X ^ p ^ n - X : (ZMod p)[X])
```

```lean
theorem GaloisField.finrank {n} (h : n ≠ 0) :
    Module.finrank (ZMod p) (GaloisField p n) = n
```

```lean
theorem GaloisField.card (h : n ≠ 0) :
    Nat.card (GaloisField p n) = p ^ n
```

File: `Mathlib/FieldTheory/Finite/Basic.lean`

```lean
theorem FiniteField.card (p : ℕ) [CharP K p] :
    ∃ n : ℕ+, Nat.Prime p ∧ Fintype.card K = p ^ (n : ℕ)
```

```lean
theorem FiniteField.pow_card (a : K) : a ^ Fintype.card K = a
```

```lean
theorem FiniteField.pow_card_pow (n : ℕ) (a : K) :
    a ^ Fintype.card K ^ n = a
```

Usefulness:

- `GaloisField p n` is the right carrier for `𝔽_{p^n}`.
- `GaloisField.finrank` gives `[𝔽_q : 𝔽_p] = t`.
- `FiniteField.card` recovers the prime-power decomposition abstractly for any finite field.

### 2. Finite-field trace

File: `Mathlib/FieldTheory/Finite/Trace.lean`

```lean
theorem FiniteField.trace_to_zmod_nondegenerate (F : Type*) [Field F] [Finite F]
    [Algebra (ZMod (ringChar F)) F] {a : F} (ha : a ≠ 0) :
    ∃ b : F, Algebra.trace (ZMod (ringChar F)) F (a * b) ≠ 0
```

```lean
theorem FiniteField.algebraMap_trace_eq_sum_pow :
    algebraMap K L (Algebra.trace K L x) =
      ∑ i ∈ Finset.range (Module.finrank K L), x ^ (Nat.card K ^ i)
```

Usefulness:

- This is the exact API needed for the paper's finite-field trace.
- Specializing to `K = ZMod p`, `L = GaloisField p t` gives:
  `algebraMap _ _ (trace x) = ∑_{i < t} x^(p^i)`.
- This is the paper's formula after interpreting the `trace` value in the big field via
  `algebraMap`.

What is slightly missing:

- There is no ready-made named local theorem stating directly:
  `Algebra.trace (ZMod p) F x = ...` in `ZMod p`.
- The Mathlib theorem gives the formula after applying `algebraMap`.
- That is still fine, since `algebraMap (ZMod p) F` is injective for fields.

### 3. Additive-character core API

File: `Mathlib/Algebra/Group/AddChar.lean`

```lean
def doubleDualEmb : A →+ AddChar (AddChar A M) M
```

```lean
lemma sum_eq_ite (ψ : AddChar A R) [Decidable (ψ = 0)] :
    ∑ a, ψ a = if ψ = 0 then ↑(card A) else 0
```

File: `Mathlib/Analysis/Fourier/FiniteAbelian/Orthogonality.lean`

```lean
lemma AddChar.expect_eq_ite (ψ : AddChar G R) :
    𝔼 a, ψ a = if ψ = 0 then 1 else 0
```

Usefulness:

- These are the cleanest generic orthogonality statements.
- If you define the paper's character as an `AddChar`, the scalar and vector orthogonality
  statements become immediate once you know whether the character is trivial.

### 4. Primitive additive characters on finite fields

File: `Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean`

```lean
def AddChar.IsPrimitive (ψ : AddChar R R') : Prop := ∀ ⦃a : R⦄, a ≠ 0 → mulShift ψ a ≠ 1
```

```lean
theorem AddChar.IsPrimitive.of_ne_one {F : Type u} [Field F] {ψ : AddChar F R'} (hψ : ψ ≠ 1) :
    IsPrimitive ψ
```

```lean
theorem AddChar.sum_eq_zero_of_ne_one [IsDomain R'] {ψ : AddChar R R'} (hψ : ψ ≠ 1) :
    ∑ a, ψ a = 0
```

```lean
theorem AddChar.sum_mulShift {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar R R'} (b : R)
    (hψ : IsPrimitive ψ) :
    ∑ x : R, ψ (x * b) = if b = 0 then Fintype.card R else 0
```

```lean
noncomputable def AddChar.FiniteField.primitiveChar_to_Complex :
    AddChar F ℂ
```

```lean
lemma AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive :
    (primitiveChar_to_Complex F).IsPrimitive
```

Also important is how Mathlib builds the primitive finite-field character:

```lean
let ψ' := ψ.char.compAddMonoidHom (Algebra.trace (ZMod p) F).toAddMonoidHom
```

This appears inside the construction of `primitiveChar`.

Usefulness:

- `sum_mulShift` is already almost exactly `prop:fourier-fact-scalar`.
- The proof route is:
  define `ψ_F(x) := ω^(trace x)` as an additive character on `F`,
  show it is primitive,
  apply `sum_mulShift`.
- Mathlib's finite-field primitive character is already built through `Algebra.trace`.

What is slightly missing:

- There is no named theorem saying Mathlib's `primitiveChar_to_Complex` is judgmentally equal to
  the paper's explicit `ω^(tr[x])`.
- For statements corresponding to the paper, a small wrapper definition is recommended.

### 5. `ZMod` characters and roots of unity

File: `Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean`

```lean
noncomputable def ZMod.stdAddChar : AddChar (ZMod N) ℂ
```

```lean
lemma ZMod.stdAddChar_coe (j : ℤ) :
    stdAddChar (j : ZMod N) = exp (2 * π * I * j / N)
```

```lean
lemma ZMod.isPrimitive_stdAddChar (N : ℕ) [NeZero N] :
    (stdAddChar (N := N)).IsPrimitive
```

```lean
noncomputable def ZMod.rootsOfUnityAddChar (n : ℕ) [NeZero n] :
    AddChar (ZMod n) (rootsOfUnity n Circle)
```

Usefulness:

- For the paper's `ω = e^{2πi/p}`, the easiest concrete choice is to use
  `ZMod.stdAddChar (N := p)` on the prime field.
- Then define the finite-field character by composing with
  `(Algebra.trace (ZMod p) F).toAddMonoidHom`.

### 6. `ZMod` Fourier and duality API

File: `Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean`

```lean
def AddChar.zmod (x : ZMod n) : AddChar (ZMod n) Circle
```

```lean
def AddChar.zmodAddEquiv : ZMod n ≃+ AddChar (ZMod n) ℂ
```

Usefulness:

- Useful if you want to reason in terms of the dual group of `ZMod p`.
- Probably not the shortest route for Stream A, but good supporting API.

### 7. Product/vector factorization support

File: `Mathlib/Algebra/DirectSum/AddChar.lean`

```lean
def AddChar.directSum (ψ : ∀ i, AddChar (G i) R) : AddChar (⨁ i, G i) R
```

File: `Mathlib/Algebra/BigOperators/Expect.lean`

```lean
lemma Finset.expect_product (s : Finset ι) (t : Finset κ) (f : ι × κ → M) :
    𝔼 x ∈ s ×ˢ t, f x = 𝔼 i ∈ s, 𝔼 j ∈ t, f (i, j)
```

```lean
lemma Finset.expect_product' (s : Finset ι) (t : Finset κ) (f : ι → κ → M) :
    𝔼 i ∈ s ×ˢ t, f i.1 i.2 = 𝔼 i ∈ s, 𝔼 j ∈ t, f i j
```

Usefulness:

- These are enough for the vector case.
- For `F_q^m`, either:
  1. define one additive character on the full additive group and use `AddChar.expect_eq_ite`, or
  2. factor the expectation coordinate-by-coordinate using `expect_product`.

## What Is Missing / API Gaps

### In Mathlib

I did not find a single out-of-the-box declaration matching the exact paper statement verbatim:

```text
E_{x ∈ 𝔽_q} ω^(tr[x * a]) = if a = 0 then 1 else 0
```

But all pieces are present.

The only real glue still needed is:

1. a wrapper definition for the paper's additive character,
2. a lemma identifying it as primitive or nontrivial,
3. a normalization step turning sums into expectations.

### In the local codebase

The main issue is semantic, not theorem-search:

1. `Scalar params := ZMod params.q` is not `𝔽_q` unless `q` is prime.
2. `mulCoord` currently uses multiplication in `ZMod q`, not in `𝔽_{p^t}`.
3. local polynomials are over `ZMod q`, so prime-power finite-field results will not transport
   cleanly without a new carrier or a bridge layer.

## Recommended Approach

### Recommendation

Use Mathlib directly for the finite-field results, but introduce thin local wrappers.

Concretely:

1. Define a genuine field carrier for this stream:
   `F := HonestFq params spec` or directly `GaloisField p t`.
2. Define the finite-field trace by:
   `ffTrace : F → ZMod p := Algebra.trace (ZMod p) F`.
3. Define the paper's character by:
   `ffAddChar : AddChar F ℂ :=
      (ZMod.stdAddChar (N := p)).compAddMonoidHom ffTrace.toAddMonoidHom`
4. Prove or package:
   `∑ x : F, ffAddChar (x * a) = if a = 0 then Fintype.card F else 0`
   using `AddChar.sum_mulShift`.
5. Convert to expectation with `Fintype.expect_eq_sum_div_card`.
6. For vectors `Fin m → F`, either:
   - define `x ↦ ffAddChar (∑ i, x i * a i)` as one `AddChar`, then use generic orthogonality, or
   - factor the expectation with `Finset.expect_product`.

### Why this is the best route

- It matches the paper mathematically for all prime powers.
- It uses Mathlib's strongest existing theorems rather than reproving orthogonality from scratch.
- It keeps the exact formula `tr(x) = ∑ x^(p^i)` available through
  `FiniteField.algebraMap_trace_eq_sum_pow`.

### What not to do

Avoid formalizing Stream A purely in the current `ZMod q`/`Fin q` model if the goal is the paper's
`𝔽_q` for prime powers. That route is only faithful when `q` is prime.

## Key Types To Use

### Best choice for the finite field

Use:

```lean
GaloisField p t
```

or the existing local wrapper:

```lean
HonestFq params spec
```

### Best choice for additive characters

Use `AddChar`.

Why:

- orthogonality is already in `AddChar.sum_eq_ite`, `AddChar.expect_eq_ite`,
  `AddChar.sum_mulShift`,
- primitive-character support is already in
  `Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean`.

### Best choice for `ω`

Use:

```lean
ZMod.stdAddChar (N := p)
```

as the concrete complex character on the prime field `ZMod p`.

Then define the finite-field character by precomposing with the trace.

### When `ZMod q` is still fine

Use `ZMod q` only when the development is intentionally about the prime field or only about a
coded ambient type, not about the genuine finite field `𝔽_q` for prime powers.

## Bottom Line

Yes, Mathlib is sufficient for Stream A.

The right formalization path is:

- `GaloisField p t` for `𝔽_q`,
- `Algebra.trace (ZMod p) _` for the field trace,
- `ZMod.stdAddChar` composed with trace for `ω^(tr[·])`,
- `AddChar.sum_mulShift` for the scalar orthogonality lemma,
- `AddChar.expect_eq_ite` or `Finset.expect_product` for the vector lemma.

The main local work is a wrapper layer connecting the paper's notation to Mathlib's APIs and
separating the genuine finite-field carrier from the current `ZMod q` coding.
