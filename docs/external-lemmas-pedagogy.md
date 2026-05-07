# External Lemmas — Pedagogy and Mathlib Mapping

A register of mathematical facts used in the Lean formalization whose proof
is **not** explained in the LDT paper sources (`references/ldt-paper/`).  For
each entry, we give the paper location, the Mathlib (or external) declaration
that supplies the fact, and a brief pedagogical explanation.

This document is intended for:

- **New contributors** who need to understand where a proof step "comes from"
  when the paper doesn't elaborate it,
- **Paper-gap auditors** checking whether a Mathlib-dependent step faithfully
  reproduces the paper's reasoning,
- **Upstreaming scouts** looking for candidates to contribute back to Mathlib
  (tracked in issue [#1250]).

## Table of Contents

1. [Cauchy–Schwarz inequalities for approximate measurements](#1-cauchyschwarz-for-approximate-measurements)
2. [Schwartz–Zippel lemma for multivariate polynomials](#2-schwartzzippel-for-multivariate-polynomials)
3. [Fourier orthogonality over finite fields](#3-fourier-orthogonality-over-finite-fields)
4. [Finite-field trace identity](#4-finite-field-trace-identity)
5. [Eigenvalue bounds and spectral theory](#5-eigenvalue-bounds-and-spectral-theory)
6. [Matrix order and positive semidefinite operators](#6-matrix-order-and-psd-operators)
7. [Continuous Functional Calculus (CFC)](#7-continuous-functional-calculus-for-matrices)
8. [Chebyshev sum inequality](#8-chebyshev-sum-inequality)
9. [External result statements (Polishchuk–Spielman, Raz–Safra)](#9-external-result-statements)

---

## 1. Cauchy–Schwarz for approximate measurements

**Paper reference**: Section 3 (Preliminaries), Propositions
`prop:easy-approx-from-approx-delta`, `prop:closeness-of-ip`,
`prop:cab-approx-delta`.

**Lean file**: `MIPStarRE/LDT/Preliminaries/CauchySchwarz.lean`

**What the paper assumes**: The Cauchy–Schwarz inequality for inner products
in a Hilbert space, plus standard manipulation of absolute values and sums.

**Mathlib source**: The proofs use only elementary real analysis
(`Real.sqrt`, `Real.sum_sqrt_mul_sqrt_le`, `Finset.abs_sum_le_sum_abs`)
plus project-local expectation lemmas (`ev_adjoint_self_nonneg`,
`ev_abs_mul_le_sqrt`).  No external "Cauchy–Schwarz theorem" import is
needed because the form used is a direct consequence of the
*sum-of-sqrt-products* inequality, which Mathlib provides in
`Analysis/Calculus/MeanInequalities`.

**Pedagogical note**: The key insight is that
`|∑ a, ψ(X_a Y_a)| ≤ (∑ a, ψ(X_a X_a†))^(1/2) · (∑ a, ψ(Y_a† Y_a))^(1/2)`
follows from the standard Cauchy–Schwarz inequality applied to the
inner product `⟨u, v⟩ = ∑ a, ψ(u_a v_a†)` on operators.  The proof in
`CauchySchwarz.lean` breaks this into three standard inequalities:
triangle inequality for sums, pointwise `|ψ(X_a Y_a)| ≤ sqrt(ψ(X_a X_a†)) *
sqrt(ψ(Y_a† Y_a))`, and the sum-of-sqrt-products inequality
`Real.sum_sqrt_mul_sqrt_le`.

**Upstream potential**: Low — this is a specialized application of
general inequalities to the project's `ev` / `QuantumState` types.
Not a candidate for Mathlib.

---

## 2. Schwartz–Zippel for multivariate polynomials

**Paper reference**: Section 3 (Preliminaries), Proposition
`prop:schwartz-zippel`.

**Lean file**: `MIPStarRE/LDT/Preliminaries/Polynomials.lean`

**What the paper assumes**: If `P` is a non-zero polynomial over `F_q` in
`m` variables with individual degree at most `d` in each variable, then
`Pr_{x ∈ F_q^m}[P(x) = 0] ≤ m·d / q`.

**Mathlib source**: `Mathlib.Algebra.MvPolynomial.SchwartzZippel`

The Mathlib lemma `MvPolynomial.schwartz_zippel_totalDegree` gives exactly this bound
for polynomials over any integral domain, with zero-probability measured
as a cardinality ratio over the full product space.  The project wraps it:

```lean
abbrev polyFunc (m : ℕ) (K : Type*) [CommSemiring K] (d : ℕ) :
    Submodule K (MvPolynomial (Fin m) K) :=
  MvPolynomial.restrictDegree (Fin m) K d
```

Then the Schwartz–Zippel bound follows from
`MvPolynomial.schwartz_zippel_totalDegree`.

**Pedagogical note**: Schwartz–Zippel is a standard result in theoretical
computer science.  The Mathlib proof follows the classical induction on
variables: factor `P` as a polynomial in `x_1` with coefficients in
`F_q[x_2, ..., x_m]`, apply the univariate bound (a degree-`d` polynomial
over a field has at most `d` roots) to the leading coefficient, and
union-bound over variables.

**Upstream potential**: None — Mathlib already has the lemma.

---

## 3. Fourier orthogonality over finite fields

**Paper reference**: Section 3 (Preliminaries), Propositions
`prop:fourier-fact-scalar` and `prop:fourier-fact-vector`.

**Lean file**: `MIPStarRE/LDT/Preliminaries/FiniteFields.lean`

**What the paper assumes**: For a finite field `F_q = GF(p^t)` with
additive character `ω = exp(2πi·tr(_) / p)`, we have
`E_{x ∈ F_q} ω(tr[x·a]) = 1` if `a = 0`, `0` otherwise.

**Mathlib source**:
- `Mathlib.NumberTheory.LegendreSymbol.AddCharacter` — additive characters
  over finite abelian groups
- `Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality` — orthogonality of
  additive characters over finite groups
- `Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar` — the primitive
  additive character `x ↦ exp(2πi·x/p)` on `ZMod p`

The key Mathlib lemma is `AddChar.expect_eq_ite` (or similar in the
`AddChar` API), which gives the expectation of a nontrivial additive
character over the whole group as zero.

**Pedagogical note**: An additive character of a finite abelian group `G`
is a homomorphism `χ : G → ℂ×` with `|χ(g)| = 1`.  Characters are
orthogonal:
`E_{g∈G} χ(g) · ψ(g)⁻¹ = 1` if `χ = ψ`, `0` otherwise.
For the paper's setting, `G = F_q` (additive group of the field) and
`χ_a(x) = ω(tr[a·x])`.  The orthogonality follows because the trace
form `(a, x) ↦ tr[a·x]` is a nondegenerate bilinear form, so
`a = 0` gives the trivial character (value always 1) and `a ≠ 0` gives
a nontrivial character (orthogonal to the trivial one).

**Upstream potential**: None — Mathlib already has the full theory.

---

## 4. Finite-field trace identity

**Paper reference**: Section 3 (Preliminaries), Definition
`def:finite-field-trace`.

**Lean file**: `MIPStarRE/LDT/Preliminaries/FiniteFields.lean`

**What the paper assumes**: The trace `tr : F_q → F_p` is
`tr(x) = ∑_{ℓ=0}^{t-1} x^{p^ℓ}` where `q = p^t`.

**Mathlib source**: `Algebra.trace` from field theory (`Algebra/Trace`).

The Mathlib lemma `FiniteField.algebraMap_trace_eq_sum_pow` confirms
that the algebraic trace over `ZMod p ⊆ F_q` agrees with the Frobenius
sum formula.

**Pedagogical note**: The trace of a finite field extension `F_q / F_p`
is the sum of the Galois conjugates:
`Tr_{F_q/F_p}(x) = x + x^p + x^{p^2} + ... + x^{p^(t-1)}`.
This is a linear map `F_q → F_p`.  Mathlib defines it via the general
`Algebra.trace` for finite extensions, and `FiniteField` provides the
explicit Frobenius-sum formula.

**Upstream potential**: None — Mathlib already has the lemma.

---

## 5. Eigenvalue bounds and spectral theory

**Paper reference**: Section 4 (Making measurements projective),
Lemmas `lem:projective-non-measurement` etc.

**Lean files**:
- `MIPStarRE/Quantum/FiniteMatrix.lean`
- `MIPStarRE/Quantum/FiniteHilbert.lean`
- `MIPStarRE/LDT/MakingMeasurementsProjective/`

**What the paper assumes**: Standard finite-dimensional spectral theory:
Hermitian matrices have real eigenvalues, PSD matrices have nonnegative
eigenvalues, `0 ≤ A ≤ 1` implies `A^2 ≤ A`, spectral truncation
(keeping only eigenvectors with eigenvalue ≥ ε), etc.

**Mathlib source**: `Mathlib.LinearAlgebra.Matrix.PosDef` for PSD
properties, `Mathlib.Analysis.InnerProductSpace.Spectrum` for spectral
theorems for finite-dimensional operators.  The project uses Mathlib's
`Matrix.PosSemidef` typeclass and associated lemmas:
- `PosSemidef.mul_mul_conjTranspose_same` — PSD is stable under
  `A ↦ B†·A·B`
- `sq_le_self` (project-local) — `0 ≤ X ≤ 1` ⇒ `X² ≤ X`

**Pedagogical note**: The finite-dimensional spectral theorem says every
Hermitian matrix `A` can be diagonalized by a unitary:
`A = U·Λ·U†` where `Λ` is a diagonal matrix of real eigenvalues.  For
PSD matrices, all eigenvalues are ≥ 0.  The inequality `X² ≤ X` when
`0 ≤ X ≤ 1` follows because `λ² ≤ λ` for each eigenvalue `λ ∈ [0,1]`.

**Upstream potential**: `sq_le_self` is a project-local lemma that uses
Mathlib's `PosSemidef` API but packages a specific proof for the `X ≤ 1`
case.  Slight upstream potential — it's a matrix analog of a standard
operator algebra fact, but the `0 ≤ X ≤ 1` proof is specialized to
finite-dimensional complex matrices.  Tracked at [#1250].

---

## 6. Matrix order and PSD operators

**Paper reference**: Throughout Sections 4–12.

**Lean files**:
- `MIPStarRE/Quantum/FiniteMatrix.lean` — `Op d`, `normalizedTrace`,
  `tauNormSq`, `IsProj`
- `MIPStarRE/LDT/Basic/SubMeasurement.lean` — `SubMeas`, `Measurement`,
  `ProjSubMeas`, `ProjMeas`, tensor-placement lemmas

**What the paper assumes**: Standard matrix algebra facts about
positively semidefinite operators, matrix multiplication, trace
properties, tensor products, etc.

**Mathlib source**: `Mathlib.LinearAlgebra.Matrix` provides the full
matrix algebra; `Matrix.le_iff` and `Matrix.nonneg_iff_posSemidef`
connect the order to PSD; `leftTensor`, `rightTensor`, and `opTensor`
provide the Kronecker product; `Matrix.trace` provides the trace.

Key Mathlib lemmas used but not reproved:

- `sandwich_nonneg` — PSD is preserved under `M·P·M` when `M` is Hermitian
  and `P` is PSD
- `sandwich_mono` — monotonicity under the same sandwich
- `leftTensor_nonneg` / `rightTensor_nonneg` — PSD lifts through tensor
  product with identity
- `leftTensor_le_one` / `rightTensor_le_one` — the identity bound lifts
- `opTensor_nonneg` — PSD is stable under Kronecker product

**Pedagogical note**: The matrix order `A ≤ B` is defined as
`B - A` is PSD.  The sandwich lemma `M·P·M ≥ 0` follows because
`(M·P·M) = M·(P)·M†` (since `M` is Hermitian) and PSD is stable under
congruence.  Tensor product with identity preserves both PSD and the
`≤ 1` bound because the eigenvalues of `A ⊗ I` are just the eigenvalues
of `A`.

**Upstream potential**: Most of these are standard Mathlib facts already.
The project-local `sandwich_nonneg` and `sandwich_mono` could be
upstreamed if Mathlib doesn't have the `Matrix`-flavored versions
(Mathlib's `PosSemidef` API may already cover them under different
names).

---

## 7. Continuous Functional Calculus for matrices

**Paper reference**: Section 4 (Making measurements projective), where
the `CFC.sqrt` of a PSD operator appears.

**Lean files**: `MIPStarRE/Quantum/FiniteMatrix.lean`,
`MIPStarRE/Quantum/FiniteHilbert.lean`

**What the paper assumes**: Applying a continuous function `f` to a
Hermitian matrix via spectral decomposition, specifically `√A` for
`A ≥ 0`.

**Mathlib source**: `Mathlib.Analysis.CstarAlgebra.ContinuousFunctionalCalculus`
provides the CFC.  For `Matrix ι ι ℂ`:

- `CFC.sqrt_nonneg` — `0 ≤ A` ⇒ `0 ≤ √A`
- `CFC.sqrt_one` — `√1 = 1`
- `CFC.sqrt_mul_sqrt_self` — needs explicit `0 ≤ A` hypothesis
- `cfc_nnreal_le_iff` — to prove `√A ≤ 1` when `A ≤ 1`, by comparing
  spectra via NNReal

**Pedagogical note**: The continuous functional calculus for a Hermitian
matrix `A = U·Λ·U†` applies `f` pointwise to eigenvalues:
`f(A) = U·f(Λ)·U†`.  For `f(x) = √x` on `[0,∞)`, this produces the PSD
square root.  Mathlib's `CFC` framework is fully general (for
C*-algebras), so for the finite-dimensional matrix case one uses
`cfc_nonneg_iff` and `cfc_nnreal_le_iff` to reduce to spectrum
comparisons.

**Known pitfall**: Direct `CFC.sqrt` on a term typed as
`MatrixOperator model.space` / `Quantum.Op model.space.carrier` can
hit a `NonUnitalContinuousFunctionalCalculus` typeclass heartbeat
timeout when `model.space` is a structure field.  The workaround
(document in project memory) is to define a helper over an explicit
carrier type and then instantiate with local `Fintype`/`DecidableEq`
instances.

**Upstream potential**: The CFC framework is already in Mathlib.  The
heartbeat timeout is a Mathlib performance issue, not a gap.

---

## 8. Chebyshev sum inequality

**Paper reference**: Used internally in `Preliminaries/Triangles.lean`.

**Lean file**: `MIPStarRE/LDT/Preliminaries/Triangles.lean`

**What the paper assumes**: Standard Chebyshev rearrangement / sum
inequality for monotone sequences.

**Mathlib source**: `Mathlib.Algebra.Order.Chebyshev`

The import is used for sum-rearrangement bounds that appear in the
triangle-inequality chain for measurement distance.

**Pedagogical note**: Chebyshev's sum inequality states that for two
similarly sorted sequences `(a_i)` and `(b_i)`,
`(1/n)·∑ a_i·b_i ≥ ((1/n)·∑ a_i)·((1/n)·∑ b_i)`.
The Mathlib lemma in `Algebra/Order/Chebyshev` provides this in
the `Finset` formulation.

**Upstream potential**: None — Mathlib has the lemma.

---

## 9. External result statements

Some lemmas in the Lean codebase take explicit `*Statement` hypotheses
that represent external mathematical results the project does not plan
to formalize.  These are **not** pedagogical gaps in the LDT paper —
they are citations to other papers:

### Polishchuk–Spielman classical test soundness

**Paper**: Polishchuk–Spielman, "Nearly linear-size holographic proofs"
(FOCS 1994 / 1997).

**Lean declaration**: `MIPStarRE.LDT.Test.PolishchukSpielmanClassicalSoundnessStatement`

This is a named `Prop` that says: "for a classical test with slack
parameter `κ`, the error bound `poly(m)·(poly(ε)+poly(d/q))` holds."
The project takes it as an unformalized hypothesis.  The paper's
Section 2 (Overview) uses it to bootstrap the soundness analysis.

**Pedagogical note**: Polishchuk–Spielman proves that the low-individual-degree
test accepts with high probability only strategies that are close to
passing.  It is a key building block in the paper's argument chain
but is treated as a black box.

### Raz–Safra classical test

**Paper**: Raz–Safra, "A sub-constant error-probability low-degree test,
and a sub-constant error-probability PCP characterization of NP" (STOC 1997).

**Lean declaration**: `MIPStarRE.LDT.Test.RazSafraSoundnessStatement`

Analogous to Polishchuk–Spielman but for the surface-vs-point test.

### Matrix Chernoff bound

**Lean declaration**: `chernoffBernoulliMatrix` (internal, in
`Pasting/Bernoulli/MatrixChernoff.lean`).

This is a matrix-version of the Chernoff concentration bound, used for
Bernoulli matrix sums.  The project now proves this internal statement locally
using CFC reduction plus a local scalar Hoeffding step; it is no longer kept as
an external `*Statement` hypothesis.  There remains a Mathlib gap for a general
matrix Chernoff inequality (beyond this project-specific formalization).

**Pedagogical note**: The classical Chernoff bound says that the sum of
independent Bernoulli random variables concentrates exponentially around
its mean.  The matrix version replaces the scalar absolute value with
the operator norm and uses the Golden–Thompson inequality instead of
Markov's inequality.  This is a genuine Mathlib gap; see [#1250] for
upstreaming tracking.

---

## How to contribute a pedagogical explanation

When you encounter a Mathlib lemma whose proof you needed to understand
to use in the project, add a section to this document:

1. **Paper reference**: Which line / proposition in the LDT paper uses
   this fact?
2. **Lean file**: Which project file imports and uses the Mathlib lemma?
3. **Mathlib source**: The exact `import` path and lemma name.
4. **Pedagogical note**: A few paragraphs explaining what the lemma says
   in mathematical language, how it connects to the paper's notation,
   and why the proof works.
5. **Upstream potential**: Whether this could/should be upstreamed to
   Mathlib (`low`, `medium`, `high`), with a brief rationale.

## See also

- `docs/paper-gaps/policy.tex` — paper-gap documentation conventions
- `docs/formalization-patterns.md` — formalization patterns
- Issue [#1250] — Mathlib upstreaming candidates tracker
- `docs/PROOF_INTEGRITY.md` — proof integrity rules
  (A5 castle-in-the-air = Mathlib-bypass; A6 external `*Statement` smuggles)

[#1250]: https://github.com/LionSR/MIPStarRE/issues/1250
