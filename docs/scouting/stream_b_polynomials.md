# Stream B Scouting: Schwartz-Zippel and Polynomial APIs

## Bottom line

Mathlib already contains a dedicated multivariate Schwartz-Zippel development:

- `.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/SchwartzZippel.lean`

So the core lemma does **not** need to be proved from scratch if we work over an actual finite field carrier. The main gap is instead between:

- Mathlib's theorems, which are stated for `MvPolynomial (Fin n) R` over an integral domain / field, and
- the current `MIPStarRE` model, which uses `Scalar params := ZMod params.q` and `Point params := Fin params.m → Fin params.q`.

That modeling choice is fine for prime `q`, but for general prime powers it is not the paper's `F_q`.

## A. Mathlib findings

### 1. `MvPolynomial` core API

From [Degrees.lean](/Users/siruilu/Local/agentFormalization/MIPStarRE/.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Degrees.lean):

```lean
/-- `degreeOf n p` gives the highest power of X_n that appears in `p` -/
def degreeOf (n : σ) (p : MvPolynomial σ R) : ℕ :=

lemma degreeOf_le_iff {n : σ} {f : MvPolynomial σ R} {d : ℕ} :
    degreeOf n f ≤ d ↔ ∀ m ∈ support f, m n ≤ d

theorem degreeOf_C (a : R) (x : σ) : degreeOf x (C a : MvPolynomial σ R) = 0

theorem degreeOf_X [DecidableEq σ] (i j : σ) [Nontrivial R] :
    degreeOf i (X j : MvPolynomial σ R) = if i = j then 1 else 0

theorem degreeOf_mul_le (i : σ) (f g : MvPolynomial σ R) :
    degreeOf i (f * g) ≤ degreeOf i f + degreeOf i g

theorem degreeOf_sum_le {ι : Type*} (i : σ) (s : Finset ι) (f : ι → MvPolynomial σ R) :
    degreeOf i (∑ j ∈ s, f j) ≤ s.sup fun j => degreeOf i (f j)

theorem degreeOf_prod_le {ι : Type*} (i : σ) (s : Finset ι) (f : ι → MvPolynomial σ R) :
    degreeOf i (∏ j ∈ s, f j) ≤ ∑ j ∈ s, (f j).degreeOf i

theorem degreeOf_pow_le (i : σ) (p : MvPolynomial σ R) (n : ℕ) :
    degreeOf i (p ^ n) ≤ n * degreeOf i p

theorem degreeOf_rename_of_injective {p : MvPolynomial σ R} {f : σ → τ} (h : Function.Injective f)
    (i : σ) : degreeOf (f i) (rename f p) = degreeOf i p

/-- `totalDegree p` gives the maximum |s| over the monomials X^s in `p` -/
def totalDegree (p : MvPolynomial σ R) : ℕ :=

lemma degreeOf_le_totalDegree (f : MvPolynomial σ R) (i : σ) : f.degreeOf i ≤ f.totalDegree
```

Also from [CommRing.lean](/Users/siruilu/Local/agentFormalization/MIPStarRE/.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/CommRing.lean):

```lean
theorem totalDegree_sub (a b : MvPolynomial σ R) :
    (a - b).totalDegree ≤ max a.totalDegree b.totalDegree
```

This is exactly the ingredient needed to pass from distinct `g, h` to a bound on `g - h`.

### 2. Subtypes for bounded degree

From [RingTheory/MvPolynomial/Basic.lean](/Users/siruilu/Local/agentFormalization/MIPStarRE/.lake/packages/mathlib/Mathlib/RingTheory/MvPolynomial/Basic.lean):

```lean
def restrictTotalDegree (m : ℕ) : Submodule R (MvPolynomial σ R)

def restrictDegree (m : ℕ) : Submodule R (MvPolynomial σ R)

theorem mem_restrictTotalDegree (p : MvPolynomial σ R) :
    p ∈ restrictTotalDegree σ R m ↔ p.totalDegree ≤ m

theorem mem_restrictDegree (p : MvPolynomial σ R) (n : ℕ) :
    p ∈ restrictDegree σ R n ↔ ∀ s ∈ p.support, ∀ i, (s : σ →₀ ℕ) i ≤ n

theorem mem_restrictDegree_iff_sup [DecidableEq σ] (p : MvPolynomial σ R) (n : ℕ) :
    p ∈ restrictDegree σ R n ↔ ∀ i, p.degrees.count i ≤ n
```

This is the closest built-in Mathlib object to a syntactic version of `polyfunc{m}{q}{d}`.

### 3. Evaluation API

From [Eval.lean](/Users/siruilu/Local/agentFormalization/MIPStarRE/.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/Eval.lean):

```lean
def eval₂ (p : MvPolynomial σ R) : S₁

def eval₂Hom (f : R →+* S₁) (g : σ → S₁) : MvPolynomial σ R →+* S₁

def eval (f : σ → R) : MvPolynomial σ R →+* R

theorem eval_eq' [Fintype σ] (X : σ → R) (f : MvPolynomial σ R) :
    eval X f = ∑ d ∈ f.support, f.coeff d * ∏ i, X i ^ d i

theorem eval_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) (g : σ → R) :
    eval g (∏ i ∈ s, f i) = ∏ i ∈ s, eval g (f i)
```

These are the APIs the local code is already using.

### 4. Univariate root bounds

From [Algebra/Polynomial/Roots.lean](/Users/siruilu/Local/agentFormalization/MIPStarRE/.lake/packages/mathlib/Mathlib/Algebra/Polynomial/Roots.lean):

```lean
theorem card_roots' (p : R[X]) : Multiset.card p.roots ≤ natDegree p

theorem card_roots_sub_C' {p : R[X]} {a : R} (hp0 : 0 < degree p) :
    Multiset.card (p - C a).roots ≤ natDegree p
```

This is the univariate base-case technology used inside the multivariate Schwartz-Zippel proof.

There is also a finite-field image bound in [FieldTheory/Finite/Basic.lean](/Users/siruilu/Local/agentFormalization/MIPStarRE/.lake/packages/mathlib/Mathlib/FieldTheory/Finite/Basic.lean):

```lean
theorem card_image_polynomial_eval [DecidableEq R] [Fintype R] {p : R[X]} (hp : 0 < p.degree) :
    Fintype.card R ≤ natDegree p * #(univ.image fun x => eval x p)
```

### 5. Schwartz-Zippel already exists

From [SchwartzZippel.lean](/Users/siruilu/Local/agentFormalization/MIPStarRE/.lake/packages/mathlib/Mathlib/Algebra/MvPolynomial/SchwartzZippel.lean):

```lean
lemma schwartz_zippel_sup_sum :
    ∀ {n} {p : MvPolynomial (Fin n) R} (hp : p ≠ 0) (S : Fin n → Finset R),
      #{x ∈ S ^^ n | eval x p = 0} / ∏ i, (#(S i) : ℚ≥0) ≤
        p.support.sup fun s ↦ ∑ i, (s i / #(S i) : ℚ≥0)

lemma schwartz_zippel_sum_degreeOf {n} {p : MvPolynomial (Fin n) R} (hp : p ≠ 0)
    (S : Fin n → Finset R) :
    #{x ∈ S ^^ n | eval x p = 0} / ∏ i, (#(S i) : ℚ≥0) ≤ ∑ i, (p.degreeOf i / #(S i) : ℚ≥0)

lemma schwartz_zippel_totalDegree {n} {p : MvPolynomial (Fin n) R} (hp : p ≠ 0) (S : Finset R) :
    #{f ∈ piFinset fun _ ↦ S | eval f p = 0} / (#S ^ n : ℚ≥0) ≤ p.totalDegree / #S
```

This is almost exactly what Stream B needs.

Important details:

- Variables are indexed by `Fin n`, which matches `Fin m`.
- Coefficients live in `R` with `[CommRing R] [IsDomain R] [DecidableEq R]`.
- The bound is expressed in `ℚ≥0`, not `ℚ` or `ℝ`.
- The theorem counts zeros of one polynomial, not equal-value points of two polynomials. That is easy to reduce using `p := g - h`.

### 6. Finite-field polynomial functions modulo pointwise equality

From [FieldTheory/Finite/Polynomial.lean](/Users/siruilu/Local/agentFormalization/MIPStarRE/.lake/packages/mathlib/Mathlib/FieldTheory/Finite/Polynomial.lean):

```lean
def R [CommRing K] : Type u :=
  restrictDegree σ K (Fintype.card K - 1)

noncomputable def evalᵢ [CommRing K] : R σ K →ₗ[K] (σ → K) → K

theorem eq_zero_of_eval_eq_zero [Finite σ] (p : MvPolynomial σ K) (h : ∀ v : σ → K, eval v p = 0)
    (hp : p ∈ restrictDegree σ K (Fintype.card K - 1)) : p = 0
```

This is very relevant to issue `#117`: Mathlib already has a canonical "polynomials modulo finite-field functional collapse" story for individual degree `< q`.

### 7. Other nearby finite-field solution counting

From [FieldTheory/ChevalleyWarning.lean](/Users/siruilu/Local/agentFormalization/MIPStarRE/.lake/packages/mathlib/Mathlib/FieldTheory/ChevalleyWarning.lean):

```lean
theorem MvPolynomial.sum_eval_eq_zero (f : MvPolynomial σ K)
    (h : f.totalDegree < (q - 1) * Fintype.card σ) : ∑ x, eval x f = 0

theorem char_dvd_card_solutions {f : MvPolynomial σ K} (h : f.totalDegree < Fintype.card σ) :
    p ∣ Fintype.card { x : σ → K // eval x f = 0 }
```

This is not Schwartz-Zippel, but it shows the zero-set counting machinery around `MvPolynomial.eval` is already developed in Mathlib.

## B. Existing `MIPStarRE` codebase findings

### 1. Current polynomial model in `LDT/Basic/Parameters.lean`

From [Parameters.lean](/Users/siruilu/Local/agentFormalization/MIPStarRE/MIPStarRE/LDT/Basic/Parameters.lean):

```lean
abbrev Fq (params : Parameters) := Fin params.q
abbrev Scalar (params : Parameters) := ZMod params.q
abbrev PolynomialModel (params : Parameters) := MvPolynomial (Fin params.m) (Scalar params)
abbrev LinePolynomialModel (params : Parameters) := _root_.Polynomial (Scalar params)
```

There is already a noncomputable "honest field" escape hatch:

```lean
structure PrimePowerFieldSpec (params : Parameters) where
  p : ℕ
  n : ℕ
  pPrime : Nat.Prime p
  nPos : 0 < n
  cardEq : params.q = p ^ n

noncomputable abbrev HonestFq (params : Parameters) (spec : PrimePowerFieldSpec params) :=
  letI : Fact spec.p.Prime := ⟨spec.pPrime⟩
  GaloisField spec.p spec.n
```

But the main polynomial API is still built over `ZMod q`.

### 2. Existing low-individual-degree notion

The repo already has the exact syntactic notion the paper wants:

```lean
def HasLowIndividualDegree (params : Parameters) (g : Point params → Fq params) : Prop :=
  ∃ p : PolynomialModel params,
    (∀ i, MvPolynomial.degreeOf i p ≤ params.d) ∧
      g = evalPolynomialModel params p

structure Polynomial (params : Parameters) where
  poly : PolynomialModel params
  lowIndividualDegree : ∀ i, MvPolynomial.degreeOf i poly ≤ params.d
```

So `polyfunc{m}{q}{d}` does not need a brand-new idea. It is already very close to:

- `HasLowIndividualDegree params g` if you want a property of functions, or
- `Polynomial params` if you want a concrete answer type with a stored witness.

### 3. Existing `md` corollary already appears in line restriction code

The repo already proves the diagonal-line degree blowup by `m`:

```lean
structure DiagonalLinePolynomial (params : Parameters) where
  poly : LinePolynomialModel params
  degreeBounded : poly.natDegree ≤ params.m * params.d

noncomputable def restrictToDiagonalLine (params : Parameters)
    (g : Polynomial params) (ℓ : DiagonalLine params) : DiagonalLinePolynomial params
```

Inside that proof, the repo directly sums individual degree bounds to get an `m * d` bound.

### 4. Existing `restrictDegree` bridge for finite enumeration

The repo also already identifies its bounded polynomial answers with Mathlib's `restrictDegree` subtype:

```lean
noncomputable instance (params : Parameters) : Fintype (Polynomial params) := by
  let e :
      Polynomial params ≃
        MvPolynomial.restrictDegree (Fin params.m) (Scalar params) params.d := ...
```

This is a good sign: the local representation is already aligned with the relevant Mathlib subtype.

### 5. Issue `#117`

GitHub issue `#117` is:

- title: "The difference between polynomials and mod q polynomials on finite domains"
- URL: <https://github.com/LionSR/MIPStarRE/issues/117>

Issue body summary:

- it questions whether `PolynomialModel` should really be "polynomials of mod q"
- it asks whether these should instead be polynomials on finite domains
- it notes confusion about why the finite-domain approach would need noncomputability

This is the right issue. The current code also contains a concrete TODO acknowledging the gap. From [Pasting/Defs.lean](/Users/siruilu/Local/agentFormalization/MIPStarRE/MIPStarRE/LDT/Pasting/Defs.lean):

```lean
-- Note: honest Lagrange interpolation requires Field (ZMod q), which
-- holds only for prime q. For prime-power q, use GaloisField via
-- PrimePowerFieldSpec. For now, use Lagrange basis coefficient = 1
```

## C. Assessment

### Does Schwartz-Zippel already exist in Mathlib?

Yes.

The key declaration is:

```lean
MvPolynomial.schwartz_zippel_totalDegree
```

and there is an even sharper individual-degree version:

```lean
MvPolynomial.schwartz_zippel_sum_degreeOf
```

So the theorem should be **composed from Mathlib**, not reproved from scratch.

### Gap between Mathlib and what the paper needs

#### 1. The main theorem exists, but over an actual field/domain

Mathlib's theorem is for `MvPolynomial (Fin n) R` with `[IsDomain R]`.

The repo currently uses:

- coefficients: `ZMod q`
- points: `Fin q`

For non-prime `q`, `ZMod q` is not a field and not an integral domain, so the theorem cannot be instantiated there.

#### 2. The paper's `F_q` is not the same as current `Scalar := ZMod q`

For prime powers, the paper means a finite field of size `q`.

The code already knows this via `HonestFq`, but most APIs do not use it yet.

#### 3. The theorem is for zeros of one polynomial, not `g(x) = h(x)`

This is a small gap:

- define `p := g - h`
- use `g ≠ h` to get `p ≠ 0`
- rewrite `g(x) = h(x)` as `p.eval x = 0`
- use `totalDegree_sub` to bound `p.totalDegree`

This part should be routine.

#### 4. The theorem's codomain is `ℚ≥0`

If the final statement in the repo wants `ℚ` or `ℝ` probabilities, there will be a small coercion / rewriting layer.

#### 5. `polyfunc{m}{q}{d}` could mean either syntax or extensional functions

There are two reasonable formalizations:

- syntactic: a subtype of bounded-degree polynomials
- extensional: a set/type of functions admitting such a polynomial representation

Mathlib's Schwartz-Zippel theorem is naturally about the syntactic polynomial.

The repo already supports both viewpoints:

- `Polynomial params` for syntax-with-witness
- `HasLowIndividualDegree params g` for functions

### Best route for the `md/q` corollary

There are two clean options:

1. Use `schwartz_zippel_totalDegree` plus a proof that total degree is at most `m * d`.
2. Use `schwartz_zippel_sum_degreeOf` directly and bound
   `∑ i, degreeOf i p / q ≤ m * d / q`.

Option 2 is likely cleaner in Lean because it avoids a separate total-degree lemma and matches the hypothesis "individual degree ≤ d" exactly.

## D. Recommended approach

### Recommendation

Use Mathlib's existing Schwartz-Zippel theorem and prove thin wrapper lemmas.

More concretely:

1. Formalize the theorem first over a genuine field:
   - variables: `Fin m`
   - coefficients: `K`
   - assumptions: `[Fintype K] [Field K]`
2. Define the paper-facing polynomial family as either:
   - `MvPolynomial.restrictDegree (Fin m) K d`, or
   - a local wrapper structure mirroring current `Polynomial params`, but over `K`
3. Prove the equality version by applying Schwartz-Zippel to `g - h`.
4. Prove the individual-degree corollary using `schwartz_zippel_sum_degreeOf`.

### What not to do

Do **not** spend time reproving Schwartz-Zippel from univariate root counting unless there is a strong reason to avoid Mathlib dependencies. The theorem is already there.

Do **not** build the theorem on top of `ZMod q` for arbitrary `q`. That will fight the wrong abstraction.

### How this fits the current repo

Short term, the least invasive path is:

- add a field-parametrized theorem layer, separate from current `Parameters`
- keep the current `Parameters`-based gameplay APIs unchanged for now
- bridge later once the repo decides how to represent the actual `F_q`

Long term, if the repo wants the paper's statements literally for arbitrary prime powers, it should migrate theorem-facing polynomial objects away from `ZMod q` and toward the existing `HonestFq` / `PrimePowerFieldSpec` story.

## E. Estimated difficulty

### 1. Wrapper theorem over an actual finite field

Estimated difficulty: **low to moderate**

Reasons:

- the main theorem already exists
- `Fin m` indexing already matches Mathlib's statement
- the `g - h` reduction is standard
- the only likely friction is coercions from counts/probabilities in `ℚ≥0`

### 2. Integrating it with the current `Parameters` API for arbitrary `q`

Estimated difficulty: **moderate to high**

Reasons:

- current coefficients are `ZMod q`
- prime-power finite fields are only present as an unused noncomputable side API
- several local definitions currently evaluate through `Fin q` plus `ZMod q`
- issue `#117` is fundamentally about this mismatch

### 3. If you only need prime `q`

Estimated difficulty: **moderate**

This is easier than the full prime-power case, because `ZMod q` is then a field and the existing code is much closer to Mathlib's assumptions.

## Final recommendation

For Stream B itself:

- `polyfunc{m}{q}{d}`: reuse the existing local notion, or define a field-parametrized subtype using `MvPolynomial.restrictDegree`
- Schwartz-Zippel: **use Mathlib's `MvPolynomial.schwartz_zippel_totalDegree` / `schwartz_zippel_sum_degreeOf`**
- corollary `Pr ≤ md/q`: derive it from `schwartz_zippel_sum_degreeOf`

For the repo architecture:

- treat issue `#117` as real technical debt
- avoid baking new theorem statements around `ZMod q` if the target really is `F_q` for prime powers
- prefer a theorem layer over genuine finite fields, then add bridges into the existing `Parameters` world as needed
