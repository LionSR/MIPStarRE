# Stream C Faithfulness: Cauchy-Schwarz Propositions

Date: 2026-04-04

This note compares the exact paper statements in `references/ldt-paper/preliminaries.tex`
with the current Lean family types in:

- `MIPStarRE/LDT/Test/Defs.lean`
- `MIPStarRE/LDT/Basic/SubMeasurement.lean`
- `MIPStarRE/LDT/Basic/OpFamily.lean`
- `MIPStarRE/LDT/Basic/Operator.lean`
- `MIPStarRE/LDT/Basic/Distribution.lean`

## Common baseline

From Definition `def:approx_delta` (paper lines 348-360), `A^x_a ≈_δ B^x_a` is defined for
raw matrix families on a single Hilbert space, together with:

- a single state `|ψ⟩`,
- a distribution on questions `x`,
- an outcome index `a`.

So the paper's primitive notion of `≈_δ` is not intrinsically about submeasurements. It is
about arbitrary matrix families.

Current Lean matches this split as follows:

- `qSDDCore` in `MIPStarRE/LDT/Test/Defs.lean:61-65` is the literal raw formula
  `∑ a, ev ψ ((A a - B a)ᴴ * (A a - B a))`.
- `SDDRel` in `MIPStarRE/LDT/Test/Defs.lean:152-157` packages that formula for
  `IdxSubMeas`.
- `SDDOpRel` in `MIPStarRE/LDT/Test/Defs.lean:159-164` packages it for
  `IdxOpFamily`.
- `SubMeas` in `MIPStarRE/LDT/Basic/SubMeasurement.lean:18-23` is stronger than the paper's
  raw-matrix notion: PSD outcomes, explicit total, and `total ≤ 1`.
- `OpFamily` in `MIPStarRE/LDT/Basic/OpFamily.lean:21-31` is closer to the paper's raw
  matrix families, but it still carries an extra `total` field that many raw-matrix
  propositions do not naturally use.
- `leftTensor` and `rightTensor` exist in `MIPStarRE/LDT/Basic/Operator.lean:50-58`, but
  none of the three target propositions are intrinsically bipartite.

One important Lean-side caveat: Props 1 and 2 use a "bounded by `1`" factor coming from the
fact that the paper state is normalized. In the current code, `QuantumState` does not bundle
normalization, so a faithful Lean theorem matching the paper constants should carry a separate
assumption `hψ : ψ.IsNormalized` for Props 1 and 2.

## 1. `prop:closeness-of-ip` (paper lines 509-536)

### 1. Paper's family types

- `A = {A^x_a}` and `B = {B^x_a}` are raw matrix families.
- `C = {C^x_{a,b}}` is also a raw matrix family.
- The paper does not assume any of these are submeasurements or measurements.
- In particular, forcing `C` into `SubMeas` would be unfaithful: the hypothesis on `C` is a
  row-sum square bound, not positivity or `∑ C ≤ I`.

### 2. Paper's index structure

- `A` and `B` have question index `x` and a single outcome index `a`.
- `C` has question index `x` and a double outcome index `(a, b)`.
- The shared index is `a`: each `C^x_{a,b}` is paired with `A^x_a` or `B^x_a`.

### 3. Paper's hypotheses

There are really two variants in the proposition.

For `eq:closeness3`:

- `A^x_a ≈_γ B^x_a`.
- For every `x`,
  `∑ a, (∑ b, C^x_{a,b}) * (∑ b, C^x_{a,b})† ≤ I`.

For `eq:closeness4`:

- `(A^x_a)† ≈_γ (B^x_a)†`.
- For every `x`,
  `∑ a, (∑ b, C^x_{a,b})† * (∑ b, C^x_{a,b}) ≤ I`.

So the second half is not the same theorem with factors swapped. It genuinely changes both:

- the `≈_γ` hypothesis, and
- the orientation of the operator inequality on `C`.

### 4. Paper's state/distribution

- Single state `|ψ⟩`.
- Single distribution over questions `x`.
- No built-in bipartite structure.
- If later applications live on `ι × ι`, that should happen by instantiating the Hilbert space
  with a product type and explicitly using `leftTensor` or `rightTensor` inside the matrices.
  It should not be baked into this proposition's statement.

### 5. Best Lean types

Most faithful choice:

- `A B : Question → α → Op ι`
- `C : Question → α → β → Op ι`

Why:

- The paper says "matrices", not submeasurements.
- `OpFamily` is acceptable for `A` and `B` only if we want to reuse `SDDOpRel`, but its
  `total` field is irrelevant to this proposition.
- `C` is even less natural as an `OpFamily`, because the theorem only uses the curried
  partial sums `∑ b C x a b`; there is no meaningful `total` field in sight.

So for faithfulness, raw families are better than either `SubMeas` or `OpFamily`.

### 6. Best Lean relation

The conclusion should be a raw scalar inequality:

- `|lhs - rhs| ≤ Real.sqrt γ`

not `SDDRel` or `SDDOpRel`.

Reason:

- The paper's conclusion in lines 514 and 518 is a closeness statement between two scalar
  expectation values.
- The notation `≈_{√γ}` there is informal scalar closeness, not the family-level
  Definition 4.17 from lines 348-360.

For the hypothesis `A ≈_γ B`, either of these is reasonable:

- most faithful: a raw bound using `avgOver 𝒟 (fun x => qSDDCore ψ (A x) (B x)) ≤ γ`,
- API-friendly: `SDDOpRel` after packaging `A` and `B` into `IdxOpFamily`.

### 7. Proposed Lean signature

I would split the proposition into two theorems, because the hypotheses are genuinely
different.

```lean
theorem closenessOfIP_left
    {Question α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized) (𝒟 : Distribution Question)
    (A B : Question → α → MIPStarRE.Quantum.Op ι)
    (C : Question → α → β → MIPStarRE.Quantum.Op ι)
    (γ : Error)
    (hAB :
      avgOver 𝒟 (fun x => qSDDCore ψ (A x) (B x)) ≤ γ)
    (hC :
      ∀ x, (∑ a, (∑ b, C x a b) * (∑ b, C x a b)ᴴ) ≤ 1) :
    |avgOver 𝒟 (fun x => ∑ a, ∑ b, ev ψ (C x a b * A x a)) -
      avgOver 𝒟 (fun x => ∑ a, ∑ b, ev ψ (C x a b * B x a))|
      ≤ Real.sqrt γ
```

```lean
theorem closenessOfIP_right
    {Question α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized) (𝒟 : Distribution Question)
    (A B : Question → α → MIPStarRE.Quantum.Op ι)
    (C : Question → α → β → MIPStarRE.Quantum.Op ι)
    (γ : Error)
    (hAB :
      avgOver 𝒟
        (fun x => qSDDCore ψ (fun a => (A x a)ᴴ) (fun a => (B x a)ᴴ)) ≤ γ)
    (hC :
      ∀ x, (∑ a, (∑ b, C x a b)ᴴ * (∑ b, C x a b)) ≤ 1) :
    |avgOver 𝒟 (fun x => ∑ a, ∑ b, ev ψ (A x a * C x a b)) -
      avgOver 𝒟 (fun x => ∑ a, ∑ b, ev ψ (B x a * C x a b))|
      ≤ Real.sqrt γ
```

### 8. Mismatch warnings

- Using `SubMeas` for `A`, `B`, or `C` is too strong.
- Using `SDDRel` for the hypothesis is too strong, because the paper only assumes raw
  matrices.
- Using `SDDRel` or `SDDOpRel` for the conclusion is wrong in kind: the conclusion is scalar,
  not a new `≈_δ` statement between families.
- Collapsing the two halves into one theorem loses faithfulness, because `eq:closeness4`
  really assumes closeness of adjoints.
- Omitting `hψ : ψ.IsNormalized` would weaken the match to the paper constants.

## 2. `prop:easy-approx-from-approx-delta` (paper lines 547-564)

### 1. Paper's family types

- `A = {A^x_a}`, `B = {B^x_a}`, and `C = {C^x_a}` are all submeasurements.
- This is a real strengthening relative to Definition 4.17: here the paper is no longer
  working with arbitrary matrices.

### 2. Paper's index structure

- Question index `x`.
- Single outcome index `a`.
- No extra `b`.

### 3. Paper's hypotheses

- Explicit hypothesis: `A^x_a ≈_δ B^x_a`.
- Implicit structural hypothesis from "submeasurement": each `C^x_a` is PSD and
  `∑ a C^x_a ≤ I`.

The proof uses exactly that structural content to get

- `(C^x_a)^2 ≤ C^x_a`,
- hence `∑ a ⟨ψ, (C^x_a)^2 ψ⟩ ≤ 1`.

So this proposition is genuinely about submeasurements, not just arbitrary matrix families.

### 4. Paper's state/distribution

- Single state `|ψ⟩`.
- Distribution over `x`.
- No bipartite structure.

Again, a faithful Lean theorem matching the paper's `√1` step should assume
`hψ : ψ.IsNormalized`.

### 5. Best Lean types

Best choice:

- `A B C : IdxSubMeas Question α ι`

Why:

- This is exactly what the paper assumes.
- `SubMeas` in `MIPStarRE/LDT/Basic/SubMeasurement.lean:18-23` already packages the needed
  PSD and `total ≤ 1` properties.
- Using raw families would throw away precisely the structure that makes the proposition easy.
- Using `Measurement` would be too strong, because the paper allows incomplete mass.

### 6. Best Lean relation

- Hypothesis: `SDDRel ψ 𝒟 A B δ`.
- Conclusion: raw scalar inequality, not `SDDRel`.

Reason:

- The conclusion in lines 551-552 is again a scalar closeness statement, not a new family
  `≈_δ` statement.
- Here `SDDRel` is appropriate only for the hypothesis, because the inputs really are
  indexed submeasurements.

### 7. Proposed Lean signature

Using the existing `qMatchMass` is the cleanest fit, since

- `qMatchMass ψ (A x) (C x) = ∑ a, ev ψ (A^x_a * C^x_a)`.

```lean
theorem easyApproxFromApproxDelta
    {Question α ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized) (𝒟 : Distribution Question)
    (A B C : IdxSubMeas Question α ι)
    (δ : Error)
    (hAB : SDDRel ψ 𝒟 A B δ) :
    |avgOver 𝒟 (fun x => qMatchMass ψ (A x) (C x)) -
      avgOver 𝒟 (fun x => qMatchMass ψ (B x) (C x))|
      ≤ Real.sqrt δ
```

### 8. Mismatch warnings

- Using `SDDOpRel` for the hypothesis loses the paper's explicit submeasurement assumption.
- Using `SubMeas.toOpFamily` everywhere would make the theorem look more general than it is.
- Using a family-level relation in the conclusion would again confuse scalar closeness with
  Definition 4.17.
- Requiring `Measurement` instead of `SubMeas` would be strictly less faithful.

## 3. `prop:cab-approx-delta` (paper lines 571-589)

### 1. Paper's family types

- `A = {A^x_a}` and `B = {B^x_a}` are raw matrix families.
- `C = {C^x_{a,b}}` is a raw matrix family.
- Nothing is assumed to be a submeasurement.

### 2. Paper's index structure

- Input families `A` and `B` are indexed by `(x, a)`.
- `C` is indexed by `(x, a, b)`.
- The output families `C^x_{a,b} A^x_a` and `C^x_{a,b} B^x_a` are indexed by `(x, a, b)`.

So the conclusion is a genuine `≈_δ` statement on the product outcome type `α × β`.

### 3. Paper's hypotheses

- `A^x_a ≈_δ B^x_a`.
- For every `x` and `a`,
  `∑ b, (C^x_{a,b})† * C^x_{a,b} ≤ I`.

This is not a submeasurement condition on `b`; it is a contraction condition for the left
multipliers `C^x_{a,b}`.

### 4. Paper's state/distribution

- Single state `|ψ⟩`.
- Distribution over `x`.
- No intrinsic bipartite structure.

Unlike Props 1 and 2, this proof does not use a separate "`= 1` on the identity" step, so no
extra normalization hypothesis is needed to preserve the constant `δ`.

### 5. Best Lean types

Most faithful primary choice:

- `A B : Question → α → Op ι`
- `C : Question → α → β → Op ι`

Why:

- The paper's objects are raw matrix families.
- The output family is indexed by pairs `(a, b)`, but still does not naturally come with a
  meaningful `total`.
- `OpFamily` is usable as a wrapper, but only after inventing irrelevant `total` fields for
  the product family.

### 6. Best Lean relation

The paper's conclusion is a genuine family-level `≈_δ` statement, but the most faithful
Lean statement is still a raw inequality using `qSDDCore`:

- primary theorem: raw `avgOver ... qSDDCore ≤ δ`,
- optional wrapper corollary: `SDDOpRel`.

Why the raw form is slightly better:

- it avoids introducing dummy `OpFamily.total` fields for the constructed product families,
- it matches the paper's actual data, which is only the outcome operators.

If we want to stay inside the current relation API, then `SDDOpRel` is the right wrapper,
not `SDDRel`.

### 7. Proposed Lean signature

```lean
theorem cabApproxDelta
    {Question α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : Question → α → MIPStarRE.Quantum.Op ι)
    (C : Question → α → β → MIPStarRE.Quantum.Op ι)
    (δ : Error)
    (hAB :
      avgOver 𝒟 (fun x => qSDDCore ψ (A x) (B x)) ≤ δ)
    (hC :
      ∀ x a, (∑ b, (C x a b)ᴴ * C x a b) ≤ 1) :
    avgOver 𝒟
      (fun x =>
        qSDDCore ψ
          (fun ab : α × β => C x ab.1 ab.2 * A x ab.1)
          (fun ab : α × β => C x ab.1 ab.2 * B x ab.1))
      ≤ δ
```

If later convenience matters more than perfect faithfulness, add a corollary packaging the
two product families as `IdxOpFamily Question (α × β) ι` and conclude `SDDOpRel`.

### 8. Mismatch warnings

- Using `SubMeas` or `SDDRel` would be too strong and would hide that `C` is merely a
  contraction family, not a submeasurement.
- Using `SDDOpRel` directly is reasonable, but it forces arbitrary `total` fields on the
  output product family.
- Forgetting that the output index is `(a, b)` rather than just `a` loses the exact content
  of the proposition.

## Bottom line

The faithful split is:

- `prop:closeness-of-ip`: raw matrix families in the hypotheses, raw scalar inequality in the
  conclusion.
- `prop:easy-approx-from-approx-delta`: genuine `IdxSubMeas` inputs, `SDDRel` hypothesis,
  raw scalar inequality in the conclusion.
- `prop:cab-approx-delta`: raw matrix families throughout, with a primary raw
  `qSDDCore`-style conclusion and an optional `SDDOpRel` wrapper corollary.

So if the goal is "closest to the paper", we should not force all three propositions into the
same Lean wrapper. The paper really uses two different layers:

- scalar Cauchy-Schwarz consequences for Props 1 and 2,
- a true family-level `≈_δ` contraction statement for Prop 3.
