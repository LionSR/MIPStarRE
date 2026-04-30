---
title: "Stream B faithfulness scouting"
date: 2026-04-04
purpose: >
  Faithfulness scouting for Schwartz-Zippel and polynomial statements in the LDT preliminaries.
status: snapshot
track: paper2009ldt
kind: scouting-report
---

# Stream B Faithfulness Scouting: Schwartz–Zippel and Polynomial Statements

Date: 2026-04-04

## Executive recommendation

The formalization of the paper statement should use a genuine finite field `K`, not the
current `Scalar params := ZMod params.q`, and it should quantify over actual polynomials
`MvPolynomial (Fin m) K`, not functions `Point params → Fq params`.

Concretely:

- Model `polyfunc{m}{q}{d}` by `MvPolynomial.restrictDegree (Fin m) K d`.
- State Schwartz–Zippel for two distinct polynomials `g ≠ h` by applying Mathlib's
  `MvPolynomial.schwartz_zippel_totalDegree` to `g - h`.
- Derive the individual-degree corollary from a short local lemma
  `totalDegree p ≤ m * d` under `∀ i, degreeOf i p ≤ d`.
- Keep the main theorem abstract over `[Field K] [Fintype K]`.
- Only bridge to `Parameters` in a second layer:
  `Scalar params = ZMod params.q` when `q` is prime, or `HonestFq params spec` when
  `q = p^n`.

This is the most faithful match to the paper statements in
`references/ldt-paper/preliminaries.tex:89-123`.

## What the paper actually says

From `references/ldt-paper/preliminaries.tex:89-123`:

- `polyfunc{m}{q}{d}` is the set of polynomials in `F_q^m` with individual degree `d`.
- The remark immediately clarifies that "individual degree `d`" means "degree of each variable is
  at most `d`".
- The Schwartz–Zippel lemma is stated for two distinct polynomials `g, h` of total degree `d`.
- The corollary uses: individual degree `d` implies total degree `m d`, hence
  `Pr[g(x) = h(x)] ≤ m d / q`.

Two faithfulness points matter here:

1. `polyfunc{m}{q}{d}` is a set of polynomials, not a predicate on functions.
2. "Distinct" means polynomial inequality `g ≠ h`, not merely different functions.

## Existing local code

From `MIPStarRE/LDT/Basic/Parameters.lean:56-60`:

```lean
abbrev Fq (params : Parameters) := Fin params.q
abbrev Scalar (params : Parameters) := ZMod params.q
abbrev PolynomialModel (params : Parameters) := MvPolynomial (Fin params.m) (Scalar params)
```

So the current active polynomial model is over `ZMod q`, not over a general finite field of size
`q`.

From `MIPStarRE/LDT/Basic/Parameters.lean:70-82`, there is already an honest escape hatch:

```lean
structure PrimePowerFieldSpec (params : Parameters) where
  ...

noncomputable abbrev HonestFq (params : Parameters) (spec : PrimePowerFieldSpec params) :=
  GaloisField spec.p spec.n
```

From `MIPStarRE/LDT/Basic/Parameters.lean:205-210`:

```lean
def HasLowIndividualDegree (params : Parameters) (g : Point params → Fq params) : Prop :=
  ∃ p : PolynomialModel params,
    (∀ i, MvPolynomial.degreeOf i p ≤ params.d) ∧
      g = evalPolynomialModel params p
```

This is useful operationally, but it is not the paper's object: it is a predicate on functions
having some polynomial witness.

From `MIPStarRE/LDT/Basic/Parameters.lean:299-313`:

```lean
structure Polynomial (params : Parameters) where
  poly : PolynomialModel params
  lowIndividualDegree : ∀ i, MvPolynomial.degreeOf i poly ≤ params.d
```

This is much closer to the paper, because it is a bundled polynomial together with the degree
bound.

From `MIPStarRE/LDT/Basic/Parameters.lean:688-712`, the repo already proves
`Polynomial params` is equivalent to
`MvPolynomial.restrictDegree (Fin params.m) (Scalar params) params.d`.

## What Mathlib already gives

### Schwartz–Zippel

From `.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/SchwartzZippel.lean:192-203`:

```lean
lemma schwartz_zippel_totalDegree {n} {p : MvPolynomial (Fin n) R} (hp : p ≠ 0) (S : Finset R) :
    #{f ∈ piFinset fun _ ↦ S | eval f p = 0} / (#S ^ n : ℚ≥0) ≤ p.totalDegree / #S
```

This is already the one-polynomial version we need.

### `restrictDegree` really is individual degree

From `.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/Basic.lean:169-187`:

```lean
def restrictDegree (m : ℕ) : Submodule R (MvPolynomial σ R) :=
  restrictSupport R { n | ∀ i, n i ≤ m }

theorem mem_restrictDegree (p : MvPolynomial σ R) (n : ℕ) :
    p ∈ restrictDegree σ R n ↔ ∀ s ∈ p.support, ∀ i, s i ≤ n
```

So `restrictDegree` is exactly per-variable degree bounded by `d`, not total degree.

### Degree lemmas needed for the bridge

From `.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/CommRing.lean:106-108` and
`:193-198`:

```lean
theorem degreeOf_sub_le (i : σ) (p q : MvPolynomial σ R) :
    degreeOf i (p - q) ≤ max (degreeOf i p) (degreeOf i q)

theorem totalDegree_sub (a b : MvPolynomial σ R) :
    (a - b).totalDegree ≤ max a.totalDegree b.totalDegree
```

From `.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Degrees.lean:471-474`:

```lean
lemma degreeOf_le_totalDegree (f : MvPolynomial σ R) (i : σ) : f.degreeOf i ≤ f.totalDegree
```

Mathlib does not appear to have the exact packaged lemma
"if `∀ i, degreeOf i p ≤ d` then `totalDegree p ≤ m * d`",
but it is easy to prove locally from `totalDegree`, `degreeOf_le_iff`, and `Finsupp.sum_fintype`.

### Function-level injectivity under degree `< q`

From `.lake/packages/mathlib/Mathlib/FieldTheory/Finite/Polynomial.lean:154-157` and
`:219-223`:

```lean
def R [CommRing K] : Type u :=
  restrictDegree σ K (Fintype.card K - 1)

theorem eq_zero_of_eval_eq_zero [Finite σ] (p : MvPolynomial σ K)
    (h : ∀ v : σ → K, eval v p = 0)
    (hp : p ∈ restrictDegree σ K (Fintype.card K - 1)) : p = 0
```

This is useful later if we ever want to move from polynomial equality to function equality under
the usual "`degree < q` in each variable" hypothesis. It is not the right primary formulation for
the paper statement, because the paper starts with syntactic polynomial distinctness.

## Analysis by question

### 1. What should `polyfunc{m}{q}{d}` be?

Best answer: Option A, with Option B as a local wrapper.

Why:

- Option A, `MvPolynomial.restrictDegree (Fin m) K d`, is the canonical set-of-polynomials object,
  and Mathlib defines it exactly as "every variable has degree at most `d`".
- Option B, the existing `Polynomial params` structure, is also good as a bundled local API, but
  only after choosing the correct coefficient field.
- Option C, a bare predicate `∀ i, degreeOf i p ≤ d`, is logically equivalent data but not the
  right object-level representation of the paper's named set `polyfunc{m}{q}{d}`.

Important caveat:

- The current `Polynomial params` is built over `Scalar params := ZMod params.q`, so it is only
  paper-faithful when `q` is prime.
- For prime-power `q`, the faithful version would be the same structure but over
  `HonestFq params spec`.

So the most faithful formulation is:

```lean
abbrev PolyFunc (m d : ℕ) (K : Type*) [CommSemiring K] :=
  MvPolynomial.restrictDegree (Fin m) K d
```

and then, if desired, a bundled wrapper mirroring the existing `Polynomial params`.

### 2. What about the paper's field `F_q`?

The paper says `q` is a prime power and works over `F_q`, so the faithful coefficient type is a
finite field, not `ZMod q` in general.

Recommendations:

- Main theorem layer:

```lean
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
```

- If we want a literal `q` in the statement, add `hq : Fintype.card K = q`.
- For `Parameters`, use `HonestFq params spec` when `spec : PrimePowerFieldSpec params`.
- Only specialize to `Scalar params = ZMod params.q` when `params.q` is prime.

This matches the paper and also matches Mathlib's hypothesis
`[CommRing R] [IsDomain R]` in `SchwartzZippel.lean:62`.

### 3. How should "distinct" be represented?

As polynomial inequality:

```lean
g ≠ h
```

with `g h : MvPolynomial (Fin m) K`.

This is faithful to the paper's wording and is the right bridge to Mathlib:

```lean
have hsub : g - h ≠ 0 := sub_ne_zero.mpr hgh
```

Then the event

```lean
MvPolynomial.eval x g = MvPolynomial.eval x h
```

is rewritten as

```lean
MvPolynomial.eval x (g - h) = 0
```

using `MvPolynomial.eval_sub`.

Important clarification:

- Even over genuine finite fields, two distinct polynomials can agree on every point if the degree
  is large enough, for example `X^q - X` and `0` over `F_q`.
- That is not a problem for the paper's theorem, because the bound `d / q` can then be at least
  `1`.
- The real issue with `ZMod q` for non-prime `q` is stronger: the theorem itself can fail because
  `ZMod q` is not a domain. For example over `ZMod 4`, the nonzero polynomial `2 * X` has total
  degree `1` but vanishes on half the points, so the zero probability is `1/2`, which is larger
  than `1/4`.

So the main theorem should not be stated directly over the current `Scalar params` without extra
assumptions.

### 4. How should `Pr_{x in F_q^m}[g(x) = h(x)]` be represented?

Mathlib already uses the finite uniform count ratio in `ℚ≥0`, so the cleanest faithful core
definition is:

```lean
noncomputable def agreementProb
    (g h : MvPolynomial (Fin m) K) : ℚ≥0 :=
  #{x ∈ piFinset (fun _ : Fin m => (Finset.univ : Finset K))
      | MvPolynomial.eval x g = MvPolynomial.eval x h}
    / (Fintype.card K ^ m : ℚ≥0)
```

This exactly matches the paper's probability over the uniform distribution on `K^m`.

Then:

- keep the main theorem in `ℚ≥0`, because that is what Mathlib gives directly,
- add an `ℝ`-valued wrapper theorem later if the surrounding preliminaries prefer `ℝ`.

The coercion step is routine:

```lean
show ((agreementProb g h : ℚ≥0) : ℝ) ≤ (d : ℝ) / Fintype.card K
```

So the recommendation is:

- theorem layer: `ℚ≥0`,
- presentation layer: optional `ℝ` corollary.

### 5. Can we verify the degree bridge needed for the corollary?

Yes, but one helper lemma is still local rather than already packaged.

For `g - h`:

- `MvPolynomial.totalDegree_sub` exists.
- `MvPolynomial.degreeOf_sub_le` exists.

So if both `g` and `h` have total degree at most `d`, then

```lean
have hdeg_sub : (g - h).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_sub g h).trans (max_le hg hh)
```

For the individual-degree corollary:

- There is no ready-made theorem exactly saying
  `∀ i, degreeOf i p ≤ d -> totalDegree p ≤ m * d`.
- But it is straightforward to prove:

```lean
lemma totalDegree_le_card_mul_of_forall_degreeOf_le
    {σ : Type*} [Fintype σ] [DecidableEq σ] {p : MvPolynomial σ R} {d : ℕ}
    (hp : ∀ i, MvPolynomial.degreeOf i p ≤ d) :
    p.totalDegree ≤ Fintype.card σ * d := by
  rw [MvPolynomial.totalDegree]
  refine Finset.sup_le ?_
  intro s hs
  calc
    s.sum (fun _ e => e) = ∑ i : σ, s i := by rw [Finsupp.sum_fintype]
    _ ≤ ∑ i : σ, d := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact (MvPolynomial.degreeOf_le_iff.mp (hp i)) s hs
    _ = Fintype.card σ * d := by simp
```

For `σ = Fin m`, the RHS simplifies to `m * d`.

So the corollary route is completely viable.

### 6. Proposed Lean signatures

I recommend separating:

1. a core abstract theorem over finite fields,
2. a corollary for `restrictDegree`,
3. only afterwards a bridge theorem to `Parameters`.

#### Core total-degree theorem

```lean
noncomputable def agreementProb
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {m : ℕ} (g h : MvPolynomial (Fin m) K) : ℚ≥0 :=
  #{x ∈ piFinset (fun _ : Fin m => (Finset.univ : Finset K))
      | MvPolynomial.eval x g = MvPolynomial.eval x h}
    / (Fintype.card K ^ m : ℚ≥0)

theorem agreementProb_le_totalDegree_div_card
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {m d : ℕ} {g h : MvPolynomial (Fin m) K}
    (hgh : g ≠ h)
    (hg : g.totalDegree ≤ d)
    (hh : h.totalDegree ≤ d) :
    agreementProb g h ≤ d / Fintype.card K := by
  ...
```

This matches the paper's "two distinct polynomials of total degree `d`" better than a theorem
stated directly on one polynomial `p`.

#### Individual-degree corollary

```lean
theorem agreementProb_le_individualDegree_div_card
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {m d : ℕ} {g h : MvPolynomial (Fin m) K}
    (hgh : g ≠ h)
    (hg : g ∈ MvPolynomial.restrictDegree (Fin m) K d)
    (hh : h ∈ MvPolynomial.restrictDegree (Fin m) K d) :
    agreementProb g h ≤ (m * d) / Fintype.card K := by
  ...
```

This is the most faithful corollary to the paper's `g, h in polyfunc{m}{q}{d}`.

#### Optional bundled version

If we later introduce a bundled honest-field polynomial type:

```lean
structure HonestPolynomial (params : Parameters) (spec : PrimePowerFieldSpec params) where
  poly : MvPolynomial (Fin params.m) (HonestFq params spec)
  lowIndividualDegree : ∀ i, MvPolynomial.degreeOf i poly ≤ params.d
```

then the corollary can be restated with `g h : HonestPolynomial params spec`.

### 7. Should the theorem be abstract or stated directly over `Parameters`?

Recommendation: state it abstractly first, then bridge.

Reasons:

- The paper statement is field-theoretic; `Parameters` currently packages a coding model using
  `Fin q` and `ZMod q`.
- Mathlib's theorem already lives in the abstract field/domain world.
- A direct `Parameters` statement over the current `Scalar params := ZMod params.q` is only valid
  for prime `q`, not for general prime powers.
- The abstract theorem is reusable across both the prime-field and honest-prime-power layers.

Best architecture:

1. Core theorem over `K`.
2. Prime-field specialization with `[Fact params.q.Prime]` and `K := Scalar params`.
3. Honest finite-field specialization with `K := HonestFq params spec`.

The one thing I would avoid is making the first theorem about
`Point params → Fq params`, because that forces us into function semantics and the `Fin q` coding
before we have the right algebraic carrier.

## Final recommendation

For exact paper faithfulness:

- `polyfunc{m}{q}{d}` should be modeled primarily by
  `MvPolynomial.restrictDegree (Fin m) K d`.
- "distinct" should be `g ≠ h` as polynomials.
- The main theorem should be over `[Field K] [Fintype K]`.
- The probability should be represented as a finite uniform count ratio, naturally in `ℚ≥0`.
- The corollary should use a short local lemma converting individual degree bounds to
  `totalDegree ≤ m * d`.
- Integration with `Parameters` should be a bridge layer, not the foundational statement.

If we want the shortest path with the least refactor:

- prove the abstract theorem now,
- specialize to `ZMod q` only when `q` is prime,
- leave the honest prime-power specialization for the finite-field bridge layer built on
  `HonestFq params spec`.
