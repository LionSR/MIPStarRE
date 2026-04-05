# Faithfulness Scouting: Stream A — Finite Fields & Fourier

Date: 2026-04-04

## Scope

This note compares the exact paper statements in
`references/ldt-paper/preliminaries.tex:15-83` against the current Lean code in:

- `MIPStarRE/LDT/Basic/Parameters.lean`
- `MIPStarRE/LDT/ExpansionHypercubeGraph/Defs.lean`
- `MIPStarRE/LDT/Basic/Distribution.lean`

The goal is to decide the most faithful formalization for the paper's finite-field/Fourier
preliminaries, not merely the easiest local reuse.

## Paper Facts To Preserve

From `preliminaries.tex:18-25`:

- `F_q` is a genuine finite field of cardinality `q = p^t`, for any prime power.
- `ω = e^{2πi/p}` is the `p`-th root of unity, not the `q`-th root.
- The trace is `tr : F_q → F_p`, with
  `tr[x] = ∑_{ℓ=0}^{t-1} x^(p^ℓ)`.

From `preliminaries.tex:31-37`:

- scalar orthogonality is
  `E_{x ∈ F_q} ω^(tr[x * a]) = if a = 0 then 1 else 0`.

From `preliminaries.tex:66-82`:

- vector orthogonality is over `u, v : F_q^m`,
  with dot product `u · v = ∑ i, u_i * v_i` in `F_q`,
  and
  `E_{u ∈ F_q^m} ω^(tr[u · v]) = if v = 0 then 1 else 0`.

## What The Current Code Actually Models

### `Parameters.lean`

The active local carriers are:

```lean
abbrev Fq (params : Parameters) := Fin params.q
abbrev Point (params : Parameters) := Fin params.m → Fq params
abbrev Scalar (params : Parameters) := ZMod params.q
```

There is also a prime-power witness:

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

So the repo already knows the difference between:

- coded coordinates: `Fin q` / `ZMod q`
- honest field semantics: `GaloisField p n`

but almost all active definitions still use the coded side.

### `ExpansionHypercubeGraph/Defs.lean`

The current Fourier layer says:

```lean
`φ_α(u) = (1/√M) · ω^{⟨u, α⟩}` for `α ∈ F_q^m`,
where `ω = exp(2πi/q)` and `⟨u, α⟩ = ∑ᵢ uᵢ · αᵢ (mod q)`.
```

and implements:

```lean
noncomputable def addCharFq (params : Parameters) (a : Fq params) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (a.val : ℂ) / (params.q : ℂ))

noncomputable def dotProductZMod (params : Parameters) (u α : Point params) : ZMod params.q :=
  ∑ i : Fin params.m, ((u i).val : ZMod params.q) * ((α i).val : ZMod params.q)
```

with orthogonality lemma:

```lean
lemma sum_stdAddChar_mul_fin (params : Parameters) (a : ZMod params.q) :
    ∑ x : Fq params, ZMod.stdAddChar (N := params.q) (((x.val : ZMod params.q) * a)) =
      if a = 0 then params.q else 0
```

This is faithful only in the prime case `q = p`.

For `q = p^t` with `t > 1`, it is not the paper's object:

- `Fin q` is not a field.
- `ZMod q` is not a field.
- `ω` is currently a `q`-th root, but the paper uses a `p`-th root.
- the dot product is currently computed in `ZMod q`, not in `F_q`.
- there is no field trace `F_q → F_p` in the current Fourier definitions.

### `Distribution.lean`

The current expectation helper is:

```lean
def avgOver {α : Type*} (𝒟 : Distribution α) (f : α → Error) : Error := ...
```

where `Error := ℝ`.

So `avgOver (uniformDistribution F) ...` cannot directly state the paper's Fourier identities,
because those expectations are complex-valued.

## Question 1: How should the paper's `F_q` be represented?

Recommendation: Option A, concretely through the existing
`HonestFq params spec := GaloisField spec.p spec.n`.

Why not Option B:

- `ZMod q` is only a field when `q` is prime.
- the paper explicitly quantifies over every prime power `q = p^t`.
- restricting to `ZMod q` silently changes the theorem.

Why not pure Option C as the primary representation:

- an abstract `[Field F] [Finite F]` presentation is mathematically valid,
  but by itself it hides the exact prime-power data the paper names (`p`, `t`, `q`).
- the repo already has `PrimePowerFieldSpec`, so using `HonestFq` gives a faithful carrier
  and integrates with existing parameter infrastructure.

Best practical formulation:

- implement the paper-faithful statements over `HonestFq params spec`, or equivalently
  over `GaloisField spec.p spec.n`;
- only generalize later to an abstract finite field if that genuinely reduces proof burden.

## Question 2: How should the paper's trace be represented?

Recommendation: Option A as the main definition,
`Algebra.trace (ZMod p) F`, with Option B as a supporting theorem.

Reason:

- the paper's displayed formula is explicit, but Mathlib already identifies the finite-field trace
  abstractly and proves the Frobenius-sum formula.
- `Mathlib.FieldTheory.Finite.Trace` provides:

```lean
FiniteField.algebraMap_trace_eq_sum_pow
```

which says

```lean
algebraMap K L (Algebra.trace K L x) =
  ∑ i ∈ Finset.range (Module.finrank K L), x ^ (Nat.card K ^ i)
```

Specialized to `K = ZMod p` and `L = GaloisField p t`, this is exactly the paper's
`∑_{ℓ=0}^{t-1} x^(p^ℓ)` formula after mapping into `F_q`.

So the faithful pattern is:

- define the trace semantically as `Algebra.trace (ZMod p) F`;
- prove a local lemma showing it matches the paper's explicit sum formula.

That gives both:

- the right object for downstream algebraic reasoning,
- and the exact displayed paper formula for documentation/rewrites.

## Question 3: How should the paper's character `ω^(tr[x*a])` be represented?

Recommendation: Option A.

Use the standard additive character on `ZMod p`, then compose with the trace:

```lean
(ZMod.stdAddChar (N := p)).compAddMonoidHom
  (Algebra.trace (ZMod p) F).toAddMonoidHom
```

and then precompose with multiplication by `a`.

This is the faithful encoding of the paper's expression:

- `ZMod.stdAddChar (N := p)` supplies `ω = e^{2πi/p}`;
- `Algebra.trace (ZMod p) F` lands in `F_p = ZMod p`;
- composing them yields the additive character
  `x ↦ ω^(tr x)`;
- evaluating at `x * a` yields `x ↦ ω^(tr (x * a))`.

Why not Option B as the main interface:

- a raw `AddChar F ℂ` loses the paper's structure.
- the trace-to-prime-field factorization is exactly what the paper emphasizes.

So a good local definition is:

```lean
noncomputable def paperAddChar {p t : ℕ} [Fact p.Prime] (F := GaloisField p t) :
    AddChar F ℂ :=
  (ZMod.stdAddChar (N := p)).compAddMonoidHom
    (Algebra.trace (ZMod p) F).toAddMonoidHom
```

and then simply use the lambda `fun x => paperAddChar ... (x * a)` in theorem statements.

## Question 4: How should `E_{x ∈ F_q}` be represented?

Recommendation: statement-level Option A (`Finset.expect Finset.univ`), proof-level Option B.

Why not Option C:

- `avgOver (uniformDistribution F)` is specialized to `Error = ℝ`.
- the Fourier expressions are `ℂ`-valued.
- so the current distribution layer is not the right interface for these propositions.

Why Option A is best for statements:

- `Finset.expect` literally matches the paper's expectation notation.
- Mathlib already has
  `Fintype.expect_eq_sum_div_card`,
  so it rewrites to the normalized finite sum when needed.

Why Option B is still useful in proofs:

- the local orthogonality lemma we will likely prove first is naturally an unnormalized sum,
  mirroring `sum_stdAddChar_mul_fin`;
- the expectation statement then follows by dividing by `Fintype.card F = q`.

So the clean pattern is:

- theorem statements use `𝔼 x : F, ...`;
- proofs pass through `∑ x : F, ... = if ... then q else 0`.

## Question 5: How do `sum_stdAddChar_mul_fin` and `fourierBasisState` relate?

They are partially reusable as proof-pattern references, but not as faithful final statements.

### `sum_stdAddChar_mul_fin`

This is the prime-field special case of the paper's scalar proposition:

- when `F_q = ZMod p`, the trace is the identity,
- and `ω` is indeed the `p`-th root of unity,
- so
  `ω^(tr (x * a)) = ZMod.stdAddChar (x * a)`.

But as soon as `q = p^t` with `t > 1`, it is no longer the same theorem.

Conclusion:

- reuse the proof strategy;
- do not treat the current lemma as the faithful formalization of `prop:fourier-fact-scalar`.

### `fourierBasisState`

This definition belongs to the current hypercube spectral layer, but it is built from:

- `Point params = Fin m → Fin q`,
- `ω = exp(2πi/q)`,
- `dotProductZMod : ... → ZMod q`.

So it models Fourier analysis on the additive group `ZMod q` coordinatewise, not on the field
`F_q` with trace-to-`F_p` character.

Conclusion:

- do not reuse `fourierBasisState` as the faithful paper definition;
- after a faithful finite-field layer exists, one could define an analogous
  `paperFourierBasisState`, but it should be separate.

## Question 6: Should we formalize over `GaloisField` or `ZMod q`?

Recommendation: formalize these preliminaries over `GaloisField`/`HonestFq`.

Tradeoff summary:

- `ZMod q` integrates better with existing coded infrastructure.
- `GaloisField` is faithful to the paper.

For this specific scouting target, faithfulness should win.

Reasons:

- the paper's theorem is false as stated if we replace `F_q` by `ZMod q` for nonprime `q`,
  because the paper is not about the ring `ZMod(p^t)`;
- the trace map is central, and there is no faithful trace-to-prime-field story on `ZMod q`;
- the paper explicitly distinguishes `p` from `q`, and the current `ω = exp(2πi/q)` erases that.

The integration cost is real, but manageable:

- the repo already has `PrimePowerFieldSpec`;
- the repo already has `HonestFq`;
- Mathlib already has `GaloisField`, `Algebra.trace`, finite-field trace formulas,
  and trace nondegeneracy.

So the right compromise is:

- add a small faithful layer for the paper preliminaries over `HonestFq params spec`;
- keep existing `Fin q` / `ZMod q` code for encoded combinatorial infrastructure;
- bridge between them only when needed, instead of pretending they are the same object.

## Question 7: Proposed Lean signatures

Below are signatures aimed at maximum faithfulness while still fitting the current repo.

### Core aliases

```lean
namespace MIPStarRE.LDT

noncomputable abbrev PaperField (params : Parameters) (spec : PrimePowerFieldSpec params) :=
  HonestFq params spec

abbrev PaperPoint (params : Parameters) (spec : PrimePowerFieldSpec params) :=
  Fin params.m → PaperField params spec
```

Using separate names avoids overloading the existing coded `Fq` and `Point`.

### Trace

```lean
noncomputable abbrev finiteFieldTrace
    (params : Parameters) (spec : PrimePowerFieldSpec params) :
    PaperField params spec →+ ZMod spec.p :=
  (Algebra.trace (ZMod spec.p) (PaperField params spec)).toAddMonoidHom
```

and optionally an explicit-sum lemma:

```lean
theorem finiteFieldTrace_eq_sum_frobenius
    (params : Parameters) (spec : PrimePowerFieldSpec params)
    (x : PaperField params spec) :
    algebraMap (ZMod spec.p) (PaperField params spec)
        (Algebra.trace (ZMod spec.p) (PaperField params spec) x)
      =
      ∑ i ∈ Finset.range spec.n, x ^ (spec.p ^ i)
```

### Character

```lean
noncomputable def paperAddChar
    (params : Parameters) (spec : PrimePowerFieldSpec params) :
    AddChar (PaperField params spec) ℂ :=
  (ZMod.stdAddChar (N := spec.p)).compAddMonoidHom
    (finiteFieldTrace params spec)
```

### Dot product

```lean
noncomputable def paperDotProduct
    (params : Parameters) (spec : PrimePowerFieldSpec params)
    (u v : PaperPoint params spec) :
    PaperField params spec :=
  ∑ i : Fin params.m, u i * v i
```

### Scalar orthogonality: unnormalized and expectation forms

```lean
theorem sum_paperAddChar_mul
    (params : Parameters) (spec : PrimePowerFieldSpec params)
    (a : PaperField params spec) :
    ∑ x : PaperField params spec, paperAddChar params spec (x * a) =
      ((if a = 0 then Fintype.card (PaperField params spec) else 0 : ℕ) : ℂ)
```

```lean
theorem fourier_fact_scalar
    (params : Parameters) (spec : PrimePowerFieldSpec params)
    (a : PaperField params spec) :
    (𝔼 x : PaperField params spec, paperAddChar params spec (x * a)) =
      if a = 0 then 1 else 0
```

This is the faithful Lean version of `prop:fourier-fact-scalar`.

### Vector orthogonality

```lean
theorem fourier_fact_vector
    (params : Parameters) (spec : PrimePowerFieldSpec params)
    (v : PaperPoint params spec) :
    (𝔼 u : PaperPoint params spec,
        paperAddChar params spec (paperDotProduct params spec u v)) =
      if v = 0 then 1 else 0
```

This is the faithful Lean version of `prop:fourier-fact-vector`.

## Final Recommendation

The most faithful formalization is:

1. model the paper's `F_q` by `HonestFq params spec` / `GaloisField p t`,
2. model the paper's trace by `Algebra.trace (ZMod p) F`,
3. define the character by composing `ZMod.stdAddChar (N := p)` with that trace,
4. state expectations with `Finset.expect` over the honest field or honest vector space,
5. keep the current `ZMod q` Fourier layer as a separate prime-field/coded layer,
   not as the formalization of the paper's preliminaries.

In short: for integration, the current codebase likes `Fin q` and `ZMod q`; for faithfulness,
the paper wants `GaloisField p t`, trace-to-`ZMod p`, and `p`-th-root characters. For these two
propositions, the faithful layer should be separate and should use the honest finite field.
