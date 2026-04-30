---
title: "Stream C Cauchy-Schwarz scouting"
date: 2026-04-04
purpose: >
  Scouting note for Cauchy-Schwarz propositions and their local and Mathlib proof ingredients.
status: snapshot
track: paper2009ldt
kind: scouting-report
---

# Stream C Scouting: Core Cauchy-Schwarz Propositions

Date: 2026-04-04

This note scouts both Mathlib and the local `MIPStarRE` code for the three target propositions:

1. `prop:closeness-of-ip`
2. `prop:easy-approx-from-approx-delta`
3. `prop:cab-approx-delta`

The short version is:

- Mathlib has the matrix order / PSD / trace infrastructure you want.
- The local code already has the main state-weighted Cauchy-Schwarz lemma in exactly the right shape: `ev_cauchy_schwarz` and `ev_abs_mul_le_sqrt`.
- Proposition 2 is very close to current infrastructure.
- Proposition 1 needs one new generalized "test-family against an SDD difference" lemma.
- Proposition 3 needs one new contraction lemma for raw operator families (`qSDDOp` / `SDDOpRel`), because the output is usually not a submeasurement.

## 1. Mathlib hits

### 1.1 Generic Cauchy-Schwarz / inner-product facts

From `Mathlib/Analysis/InnerProductSpace/Basic.lean`:

```lean
theorem norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖
theorem re_inner_le_norm (x y : E) : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖
theorem abs_real_inner_le_norm (x y : F) : |⟪x, y⟫_ℝ| ≤ ‖x‖ * ‖y‖
```

These are generic Hilbert-space inequalities, but there is no obvious matrix-specialized theorem already phrased as a weighted trace inequality of the form
`|Re tr(ρ X* Y)| ≤ ...`.
The local `ev_cauchy_schwarz` is the better API for this project.

### 1.2 Matrix order / PSD API

From `Mathlib/Analysis/Matrix/Order.lean`:

```lean
lemma le_iff {A B : Matrix n n 𝕜} : A ≤ B ↔ (B - A).PosSemidef
lemma nonneg_iff_posSemidef {A : Matrix n n 𝕜} : 0 ≤ A ↔ A.PosSemidef
protected alias ⟨LE.le.posSemidef, PosSemidef.nonneg⟩ := nonneg_iff_posSemidef

theorem PosSemidef.kronecker {x : Matrix n n 𝕜} {y : Matrix m m 𝕜}
    (hx : x.PosSemidef) (hy : y.PosSemidef) : (x ⊗ₖ y).PosSemidef
```

These are the main order-translation lemmas. Local code already uses them heavily.

### 1.3 Sandwich / conjugation PSD lemmas

From `Mathlib/LinearAlgebra/Matrix/PosDef.lean`:

```lean
lemma conjTranspose_mul_mul_same {A : Matrix n n R} (hA : PosSemidef A) (B : Matrix n m R) :
    PosSemidef (Bᴴ * A * B)

lemma mul_mul_conjTranspose_same {A : Matrix n n R} (hA : PosSemidef A) (B : Matrix m n R) :
    PosSemidef (B * A * Bᴴ)

lemma trace_nonneg [AddLeftMono R] {A : Matrix n n R} (hA : A.PosSemidef) : 0 ≤ A.trace

theorem posSemidef_conjTranspose_mul_self [StarOrderedRing R] (A : Matrix m n R) :
    PosSemidef (Aᴴ * A)

theorem posSemidef_self_mul_conjTranspose [StarOrderedRing R] (A : Matrix m n R) :
    PosSemidef (A * Aᴴ)
```

These are exactly the PSD tools behind the local expectation-value positivity lemmas.

### 1.4 Trace identities

From `Mathlib/LinearAlgebra/Matrix/Trace.lean`:

```lean
theorem trace_add (A B : Matrix n n R) : trace (A + B) = trace A + trace B
theorem trace_smul [DistribSMul α R] (r : α) (A : Matrix n n R) :
    trace (r • A) = r • trace A
theorem trace_conjTranspose [StarAddMonoid R] (A : Matrix n n R) :
    trace Aᴴ = star (trace A)
theorem trace_one : trace (1 : Matrix n n R) = Fintype.card n
theorem trace_mul_comm [AddCommMonoid R] [CommMagma R] (A : Matrix m n R) (B : Matrix n m R) :
    trace (A * B) = trace (B * A)
```

These are enough for the local `normalizedTrace_*` and cyclic rewrites.

### 1.5 What I did not find in Mathlib

- No ready-to-use theorem already phrased as the state-weighted operator Cauchy-Schwarz inequality you want.
- No obvious off-the-shelf theorem for
  `|Re tr(ρ Σ_a X_a Y_a)|`
  with the exact square-sum bounds needed in Props 1 and 2.
- No obvious matrix-trace inequality that directly replaces the local `question_overlap_gap_*` pattern.

So for this stream, Mathlib is the PSD/order backend, while the local `ev_*` API is the proof-facing frontend.

## 2. Existing local helpers worth reusing

### 2.1 Core expectation-value API

From `MIPStarRE/LDT/Basic/Operator.lean`:

```lean
theorem ev_sub
    (ψ : QuantumState ι) (X Y : Op ι) :
    ev ψ (X - Y) = ev ψ X - ev ψ Y

theorem ev_sum
    [Fintype α] (ψ : QuantumState ι) (f : α → Op ι) :
    ev ψ (∑ a, f a) = ∑ a, ev ψ (f a)

theorem ev_adjoint_self_nonneg
    (ψ : QuantumState ι) (M : Op ι) :
    0 ≤ ev ψ (Mᴴ * M)

theorem ev_nonneg_of_psd
    (ψ : QuantumState ι) (X : Op ι) (hX : 0 ≤ X) :
    0 ≤ ev ψ X

theorem ev_mono
    (ψ : QuantumState ι) (X Y : Op ι) (h : X ≤ Y) :
    ev ψ X ≤ ev ψ Y

theorem ev_mul_comm_of_psd
    (ψ : QuantumState ι) (A B : Op ι)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ev ψ (A * B) = ev ψ (B * A)

theorem ev_cauchy_schwarz
    (ψ : QuantumState ι) (A B : Op ι) :
    (ev ψ (Aᴴ * B)) ^ 2 ≤ ev ψ (Aᴴ * A) * ev ψ (Bᴴ * B)

theorem ev_abs_mul_le_sqrt
    (ψ : QuantumState ι) (A B : Op ι) :
    |ev ψ (A * B)| ≤
      Real.sqrt (ev ψ (A * Aᴴ)) * Real.sqrt (ev ψ (Bᴴ * B))
```

This is the main toolkit for all three propositions.

Two especially important observations:

- `ev_abs_mul_le_sqrt` is already the exact "state-dependent Cauchy-Schwarz" inequality.
- `ev_mono` lets you pass from operator inequalities like `∑ D_a D_aᴴ ≤ 1` to scalar inequalities.

### 2.2 Matrix/operator order helpers

From `MIPStarRE/Quantum/FiniteMatrix.lean`:

```lean
theorem sandwich_nonneg {M P : Op d} (hP : 0 ≤ P) (hMH : Mᴴ = M) :
    0 ≤ M * P * M

theorem sandwich_mono {M P Q : Op d} (hMH : Mᴴ = M) (hPQ : P ≤ Q) :
    M * P * M ≤ M * Q * M

theorem sq_le_self {X : Op d} (hX : 0 ≤ X) (hXle : X ≤ 1) :
    X * X ≤ X
```

`sandwich_mono` is the key local lemma for Prop 3.

### 2.3 Submeasurement facts

From `MIPStarRE/LDT/Basic/SubMeasurement.lean`:

```lean
theorem SubMeas.outcome_hermitian (A : SubMeas α ι) (a : α) :
    (A.outcome a)ᴴ = A.outcome a

theorem Measurement.outcome_le_one (M : Measurement α ι) (a : α) :
    M.outcome a ≤ 1

theorem SubMeas.outcome_le_total (A : SubMeas α ι) (a : α) :
    A.outcome a ≤ A.total

theorem SubMeas.outcome_le_one (A : SubMeas α ι) (a : α) :
    A.outcome a ≤ 1

theorem SubMeas.total_nonneg (A : SubMeas α ι) :
    0 ≤ A.total

def SubMeas.liftLeft (A : SubMeas α ι) : SubMeas α (ι × ι)
def SubMeas.liftRight (A : SubMeas α ι) : SubMeas α (ι × ι)
```

For Props 1 and 2, `SubMeas.outcome_hermitian`, `SubMeas.outcome_le_one`, and `SubMeas.total_nonneg` are the relevant ones.

### 2.4 SDD / raw-family definitions

From `MIPStarRE/LDT/Test/Defs.lean`:

```lean
noncomputable def qMatchMass
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) : Error :=
  ∑ a, ev ψ (A.outcome a * B.outcome a)

noncomputable def qSDDCore
    (ψ : QuantumState ι)
    (A B : Outcome → Op ι) : Error :=
  ∑ a, ev ψ ((A a - B a)ᴴ * (A a - B a))

noncomputable def qSDD
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) : Error :=
  qSDDCore ψ A.outcome B.outcome

noncomputable def qSDDOp
    (ψ : QuantumState ι) (A B : OpFamily Outcome ι) : Error :=
  qSDDCore ψ A.outcome B.outcome

structure SDDRel ... where
  squaredDistanceBound : sddError ψ 𝒟 A B ≤ δ

structure SDDOpRel ... where
  squaredDistanceBound : sddErrorOp ψ 𝒟 A B ≤ δ

theorem qSDD_nonneg
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) :
    0 ≤ qSDD ψ A B
```

For Prop 3, `qSDDOp` and `SDDOpRel` are the right target API if the multiplied family is not itself a submeasurement.

### 2.5 Existing Cauchy-Schwarz packaging in `Preliminaries/Theorems`

From `MIPStarRE/LDT/Preliminaries/Theorems.lean`:

```lean
private lemma weightedFinsetCauchySchwarz
    (𝒟 : Distribution Question)
    (t x y : Question → Outcome → Error)
    (ht : ∀ q a, |t q a| ≤ Real.sqrt (x q a) * Real.sqrt (y q a))
    (hx : ∀ q a, 0 ≤ x q a)
    (hy : ∀ q a, 0 ≤ y q a) :
    |avgOver 𝒟 (fun q => ∑ a : Outcome, t q a)| ≤
      Real.sqrt (avgOver 𝒟 (fun q => ∑ a : Outcome, x q a)) *
        Real.sqrt (avgOver 𝒟 (fun q => ∑ a : Outcome, y q a))

lemma subMeas_diagMass_le_mass
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) :
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a) ≤ ev ψ A.total

lemma subMeas_diagMass_le_one
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized) (A : SubMeas Outcome ι) :
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a) ≤ 1

private lemma avgOver_abs_le_sqrt_of_pointwise
    (𝒟 : Distribution Question) (f g : Question → Error)
    (hf : ∀ q, |f q| ≤ Real.sqrt (g q))
    (hg : ∀ q, 0 ≤ g q)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    |avgOver 𝒟 f| ≤ Real.sqrt (avgOver 𝒟 g)

private lemma question_overlap_gap_left
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B : SubMeas Outcome ι) :
    |(∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)) -
        ∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)| ≤
      Real.sqrt (qSDD ψ A B)

private lemma question_overlap_gap_right
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B : SubMeas Outcome ι) :
    |(∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)) -
        ∑ a : Outcome, ev ψ (B.outcome a * B.outcome a)| ≤
      Real.sqrt (qSDD ψ A B)

private lemma sum_ev_mul_leftBounded_le_of_leftHermitian
    (ψ : QuantumState ι)
    (LB : Op ι)
    (X Y : Outcome → Op ι)
    (hLB_herm : LBᴴ = LB)
    (hLB_sq_le_one : LB * LB ≤ 1)
    (hXherm : ∀ a, (X a)ᴴ = X a)
    (hYherm : ∀ a, (Y a)ᴴ = Y a) :
    |∑ a : Outcome, ev ψ (X a * (LB * Y a))| ≤
      Real.sqrt (∑ a : Outcome, ev ψ (X a * X a)) *
        Real.sqrt (∑ a : Outcome, ev ψ ((Y a)ᴴ * Y a))
```

These are the strongest reusable local ingredients for Stream C.

## 3. Gap analysis

### 3.1 Proposition 2 is almost already covered

`prop:easy-approx-from-approx-delta` is very close to

```lean
sum_ev_mul_leftBounded_le_of_leftHermitian
```

with the specialization:

- `LB := 1`
- `X a := A.outcome a - B.outcome a`
- `Y a := C.outcome a`

Then:

- `hLB_herm` is trivial.
- `hLB_sq_le_one` is trivial.
- `hXherm` follows from `SubMeas.outcome_hermitian`.
- `hYherm` follows from `SubMeas.outcome_hermitian`.
- The second square-root factor is bounded by `1` using `subMeas_diagMass_le_one`.

So Prop 2 looks like a thin wrapper plus an averaging step.

### 3.2 Proposition 1 needs a new generalized local lemma

The existing overlap-gap lemmas hardcode the "test family" to be `A_a` or `B_a`.

What Prop 1 wants is the more general pattern:

```text
If ∑_a D_a D_a† ≤ I, then
|∑_a ev ψ (D_a * (A_a - B_a))| ≤ sqrt (qSDD ψ A B).
```

with `D_a := ∑_b C_{a,b}`.

The proof skeleton is exactly the same as `question_overlap_gap_left/right`, but the final control of the second factor changes:

- current overlap lemmas use `subMeas_diagMass_le_one` on `A` or `B`;
- Prop 1 needs `ev_sum + ev_mono + ev_one_of_isNormalized` applied to the operator inequality
  `∑_a D_a D_a† ≤ I`.

So the missing reusable lemma is something like:

```lean
private lemma question_testFamily_gap
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B : SubMeas Outcome ι)
    (D : Outcome → Op ι)
    (hD : ∑ a, D a * (D a)ᴴ ≤ 1) :
    |∑ a, ev ψ (D a * (A.outcome a - B.outcome a))| ≤
      Real.sqrt (qSDD ψ A B)
```

There should also be an adjoint/right-multiplied sibling with the matching square-sum assumption.

### 3.3 Proposition 3 needs a raw-family contraction lemma

`C_{a,b} A_a` and `C_{a,b} B_a` are generally not submeasurement outcomes, so the natural target is `qSDDOp` / `SDDOpRel`, not `qSDD` / `SDDRel`.

The missing lemma is something like:

```lean
private lemma qSDDOp_left_mul_contracts
    (ψ : QuantumState ι)
    (A B : SubMeas Outcome ι)
    (C : Outcome → Aux → Op ι)
    (hC : ∀ a, ∑ b, (C a b)ᴴ * C a b ≤ 1) :
    qSDDOp ψ
      { outcome := fun (ab : Outcome × Aux) => C ab.1 ab.2 * A.outcome ab.1, ... }
      { outcome := fun (ab : Outcome × Aux) => C ab.1 ab.2 * B.outcome ab.1, ... }
      ≤ qSDD ψ A B
```

The proof is straightforward but currently un-packaged.

### 3.4 Distribution normalization is a real API gap

`Distribution` only stores:

- finite support,
- nonnegative weights,
- vanishing outside support.

It does not store `∑ weight = 1`, or even `≤ 1`.

That matters because Props 1 and 2 are statements about `E_x`, and the local helper

```lean
avgOver_abs_le_sqrt_of_pointwise
```

requires the extra hypothesis

```lean
h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1
```

So unless you work only with `uniformDistribution ...`, you will need an explicit mass hypothesis for any averaged `≤ sqrt δ` statement.

## 4. Recommended proof strategy by proposition

### 4.1 `prop:closeness-of-ip`

Suggested local statement first:

```text
Fix one question x.
Let D_a := ∑_b C_{a,b}.
Assume ∑_a D_a D_a† ≤ I.
Then |∑_a ev ψ (D_a * (A_a - B_a))| ≤ sqrt (qSDD ψ A B).
```

Recommended proof:

1. Rewrite the target from `Σ_{a,b}` to `Σ_a` using linearity:
   `ev_sum`, `Matrix.sum_mul`, `Matrix.mul_sum`, `Finset.sum_sigma'` / product-sum rewrites.
2. Use
   `ev_abs_mul_le_sqrt ψ (D_a) (A_a - B_a)`
   or the right-oriented variant, depending on the proposition's exact multiplication order.
3. Sum with `Real.sum_sqrt_mul_sqrt_le`.
4. Identify the `qSDD` factor from
   `∑_a ev ψ ((A_a - B_a)ᴴ * (A_a - B_a))`.
5. Bound the test-family factor via:
   `ev_sum`, `ev_mono`, `hD`, `ev_one_of_isNormalized`.
6. Average over questions using `avgOver_abs_le_sqrt_of_pointwise` plus the distribution-mass hypothesis.
7. Use `Real.sqrt_le_sqrt` from the SDD assumption.

For the "forward vs adjoint" variants:

- if the summand is `ev ψ (D_a * (A_a - B_a))`, the natural bound is on `∑ D_a D_a†`;
- if the summand is `ev ψ ((A_a - B_a) * D_a)`, the natural bound is on `∑ D_a† D_a`.

So I would make that orientation explicit in the final theorem statements rather than trying to hide it.

### 4.2 `prop:easy-approx-from-approx-delta`

Recommended proof:

1. First prove the questionwise statement
   `|∑_a ev ψ ((A_a - B_a) * C_a)| ≤ sqrt (qSDD ψ A B)`.
2. Apply `sum_ev_mul_leftBounded_le_of_leftHermitian` with
   `LB := 1`, `X a := A_a - B_a`, `Y a := C_a`.
3. Bound the second factor by `1` using `subMeas_diagMass_le_one ψ hψ C`.
4. Average with `avgOver_abs_le_sqrt_of_pointwise`.
5. Finish with the SDD hypothesis and `Real.sqrt_le_sqrt`.

This is the cleanest of the three propositions and is the best first target to implement.

### 4.3 `prop:cab-approx-delta`

Recommended proof:

1. Work questionwise first.
2. Define the raw families on `(a,b)`:
   - `F (a,b) := C_{a,b} * A_a`
   - `G (a,b) := C_{a,b} * B_a`
3. Expand:

   ```text
   qSDDOp ψ F G
   = ∑_{a,b} ev ψ (((C_{a,b}(A_a-B_a))†) * (C_{a,b}(A_a-B_a)))
   = ∑_{a,b} ev ψ ((A_a-B_a) * (C_{a,b}† C_{a,b}) * (A_a-B_a))
   ```

   using `SubMeas.outcome_hermitian` for `A_a - B_a`.
4. Sum over `b` first and rewrite with `Matrix.sum_mul` / `Matrix.mul_sum`:

   ```text
   ∑_b (A_a-B_a) * (C_{a,b}† C_{a,b}) * (A_a-B_a)
   = (A_a-B_a) * (∑_b C_{a,b}† C_{a,b}) * (A_a-B_a)
   ```

5. Use `sandwich_mono` with middle bound
   `∑_b C_{a,b}† C_{a,b} ≤ 1`.
6. Apply `ev_mono`.
7. Sum over `a` to conclude `qSDDOp ψ F G ≤ qSDD ψ A B`.
8. Average over questions to get `SDDOpRel`.

Unless there is extra positivity/boundedness data on the multiplied family, I would not target `SDDRel` here; `SDDOpRel` is the natural codomain.

## 5. Does `question_overlap_gap_left/right` generalize to Prop 1?

Yes, in proof pattern; no, as a drop-in lemma.

The common skeleton is:

1. Rewrite the desired difference as a single sum against `(A_a - B_a)`.
2. Apply `Finset.abs_sum_le_sum_abs`.
3. Apply `ev_abs_mul_le_sqrt` pointwise.
4. Combine with `Real.sum_sqrt_mul_sqrt_le`.
5. Control the second square-root factor by a global `≤ 1` bound.

For `question_overlap_gap_left/right`, the second factor is

- `∑ ev(A_a^2)` or
- `∑ ev(B_a^2)`,

and the control comes from `subMeas_diagMass_le_one`.

For `prop:closeness-of-ip`, the second factor becomes

- `∑ ev(D_a D_a†)` or
- `∑ ev(D_a† D_a)`,

and the control comes from an external operator inequality

- `∑ D_a D_a† ≤ I` or
- `∑ D_a† D_a ≤ I`.

So the right abstraction is a generalized overlap-gap lemma with an arbitrary test family, not a special-case tweak of the current left/right overlap lemmas.

## 6. Recommended implementation order

1. Implement `prop:easy-approx-from-approx-delta`.
   This is the closest to existing infrastructure and should validate the API shape.

2. Implement a generalized local "test-family gap" lemma for Prop 1.
   Once that exists, the averaged proposition should be short.

3. Implement the raw-family contraction lemma for Prop 3.
   This is conceptually simple, but it needs a clean indexing choice and should probably target `SDDOpRel`.

## 7. Bottom line

What already exists is strong enough for the core Cauchy-Schwarz step:

- `ev_cauchy_schwarz`
- `ev_abs_mul_le_sqrt`
- `ev_mono`
- `sandwich_mono`
- `weightedFinsetCauchySchwarz`

What is still missing is mostly packaging:

- a generalized local Cauchy-Schwarz lemma for arbitrary test families with a square-sum bound;
- a raw-operator-family contraction lemma for left multiplication by `C_{a,b}`;
- an explicit distribution-mass hypothesis whenever a theorem really means an expectation.
