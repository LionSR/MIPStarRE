# Lean Proof-Evasion Anti-Patterns

Catalog of subtle proof-evasion patterns that pass kernel-level checks
(`sorry`-free, no forbidden tactics, all axioms standard) yet still fail to
prove the claimed mathematics. Complements
[`PROOF_INTEGRITY.md`](./PROOF_INTEGRITY.md), which covers the kernel-level
blockers; this file covers patterns where the Lean code *compiles and the
trick is at the level of what the statement says or what the definitions
bake in*.

Every pattern here is **castle-in-the-air in spirit**: a theorem named after a
paper result that doesn't actually prove it. The named offenders below all
cross-reference a concrete issue or PR so reviewers can see a real example.

## Why this matters

Kernel checks are necessary but not sufficient. A theorem can:

- Be marked `\leanok` in the blueprint,
- Have a sorry-free proof body,
- Have a clean axiom closure (`propext`, `Classical.choice`, `Quot.sound` only),

and still prove **nothing that the paper actually claims**, if the proof
obligation has been displaced into a hypothesis, a definition, or a sentinel
branch. The patterns below are the displacement mechanisms we've seen in this
codebase.

## Catalogue

- [A1 — Conclusion-shaped hypothesis](#a1--conclusion-shaped-hypothesis)
- [A2 — Definitional sleight-of-hand](#a2--definitional-sleight-of-hand)
- [A3 — Zero-fallback branches hiding preconditions](#a3--zero-fallback-branches-hiding-preconditions)
- A4 — Trivial default witnesses for existentials *(forthcoming)*
- A5 — Castle-in-the-air / bypassing Mathlib *(forthcoming)*
- A6 — External `*Statement` smuggles *(forthcoming)*

---

## A1 — Conclusion-shaped hypothesis

**Smell.** The theorem takes a hypothesis whose type is the theorem's own
conclusion (or an `∃`/function that produces the conclusion). The proof body
is a trivial `rcases`/`exact`/`.trans`/`simpa using h` and does no
mathematical work. A variant wraps the hypothesis in a named bundle
(`*BridgePackage`, `*Statement`); see issues [#449], [#451], [#477] for the
catalogue, and [#493] for the inline-existential mutation triggered by
PR [#491].

### Why it's bad

The theorem's named mathematical content is never derived from prior lemmas;
the caller (who supplies the hypothesis) has to discharge it. In practice the
caller then has the same problem, pushing the obligation further up the
stack. The theorem is true under a vacuous hypothesis and the `\leanok` tag
misrepresents the actual state of the proof.

### How to spot it

- The hypothesis type contains, up to `∃` / `∧` / a coercion, the theorem's
  conclusion.
- The proof body is one of:
  - `rcases h with ⟨...⟩; exact ⟨...⟩`
  - `exact h.fieldName` / `exact h.a.trans h.b`
  - `by simpa using h.fieldName`
- The hypothesis is a bundle named `*BridgePackage`, `*Witness`, `*Package`,
  `*Output`, with a field whose type matches the conclusion structure.
- Consumers of the bundle are trivial (field projection + return).

### Concrete example

From `MIPStarRE/LDT/MainInductionStep/Theorems.lean`:

```lean
theorem mainInduction
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (eps delta gamma : Error) (k : ℕ)
    (hbridge : MainInductionBridgePackage params strategy eps delta gamma k) :
    ∃ G : Measurement (Polynomial params) ι,
      ConsRel strategy.state ...
        (mainInductionError params k eps delta gamma) := by
  rcases hbridge.witness with ⟨error, G, hG, herror⟩
  refine ⟨G, ?_⟩
  exact ⟨le_trans hG.offDiagonalBound herror⟩
```

`MainInductionBridgePackage.witness` has type
`∃ error, ∃ G, ConsRel ... error ∧ error ≤ mainInductionError ...` — literally
the conclusion. No theorem in the codebase produces a
`MainInductionBridgePackage`, so the "proof" of `mainInduction` is vacuous.

PR [#491] proposed to delete the `*BridgePackage` by **inlining** the bundle's
fields as explicit hypotheses. That only scatters the same pattern across
individual signatures without producing any proof — it's strictly worse
because the named bundle at least shows up in one tracker. Do not accept PRs
that discharge an ungrounded bridge by flattening it into conclusion-shaped
existential hypotheses.

### How to fix it

Prefer **proving a real intermediate lemma** — one that the paper also uses
— and stating its signature with the paper's hypotheses (not the theorem's
conclusion). Then use it inside the larger theorem. If the missing content
can't be formalized yet, keep the `BridgePackage` (so the obligation is
*named* and trackable) and file a concrete producer sub-issue in
[#449]/[#451].

A signature passes the smell test if:

- Every hypothesis is a **named intermediate fact** that also appears in the
  paper or blueprint proof, not the theorem's output packaged up, and
- Replacing a hypothesis with its negation would produce a *different*
  theorem, not a trivially-false one.

### Related issues and patterns

- [#449] — paper-wide gap tracker
- [#451] — the seven ungrounded `BridgePackage` producers
- [#477] — `QXPLayerData` axiom-field projection (a definitional variant)
- [#493] — the inline-existential mutation of this pattern
- [#491] — PR that introduced the mutation

---

## A2 — Definitional sleight-of-hand

**Smell.** A `def`/`abbrev` is written so its body is the paper's claim, and
a nearby `theorem` restates that claim and proves it by `rfl` (or a one-line
`simp [foo]` where `foo` is the defining equation). The "mathematical
content" has been baked into the definition; the theorem is a tautology. See
issues [#477], [#494].

### Why it's bad

`rfl` proves that a definition equals itself. If the definition is chosen
*so that* it equals the conclusion, the `rfl` "proof" transports none of the
paper's reasoning — it is literally the reflexivity of a shape we invented to
match the conclusion. The real identity the paper proves (e.g.,
`⟨φ_α, φ_β⟩ = δ_αβ` over an actual inner product) is still not stated
anywhere in Lean.

### How to spot it

- A `theorem` whose body is `rfl` / `by rfl` / `by simp [defName]` where
  `defName` is the def that unfolds to the conclusion.
- A `structure` with a `Prop`-typed field whose *role* in the paper is a
  nontrivial identity (SVD, orthonormality, Cauchy–Schwarz), accompanied by a
  constructor that discharges that field with `rfl`.
- A `def foo := if α = β then 1 else 0` followed by a theorem asserting
  `foo α β = if α = β then 1 else 0`.
- Bridge-like structures where every field is itself a function
  `(precondition) → (conclusion-step)` and the consumer applies the field
  directly.

### Concrete example

From `MIPStarRE/LDT/ExpansionHypercubeGraph/Defs/Fourier.lean`:

```lean
/-- The exact inner-product formula for the hypercube Fourier basis. -/
def fourierBasisInnerProduct (params : Parameters)
    (α β : Point params) : Error :=
  if α = β then 1 else 0

structure EigenvectorsStatement (params : Parameters) : Prop where
  orthonormality :
    ∀ α β : Point params,
      fourierBasisInnerProduct params α β = if α = β then 1 else 0
  ...

theorem eigenvectors (params : Parameters) : EigenvectorsStatement params where
  orthonormality _ _ := rfl    -- castle: the def IS the Kronecker delta
  ...
```

The paper's orthonormality claim — that the additive characters `φ_α` form an
orthonormal basis under the actual inner product
`⟨f, g⟩ := (1/|V|) · ∑_u f(u)^* · g(u)` — requires a genuine character-sum
identity. The Lean theorem states and proves only the trivial fact that the
definition equals itself.

### Not every `rfl` is a castle

Distinguish from legitimate bookkeeping where a named equation is literally
how something was defined. Example: `mainFormalError_eq_envelope` in
`Test/ErrorCascade.lean` unfolds the definition of `mainFormalError` to its
envelope factorization. The mathematical content is elsewhere (the envelope
is derived from per-step bounds); the `rfl` theorem is a naming convenience
only. The test is: **does the `def` body encode a paper identity, or does it
just name a compound expression?**

### How to fix it

1. Move the paper's real definition to the concrete one: for Fourier, define
   the inner product as the actual sum over vertices, and the characters
   `φ_α` as functions from `Point params` to `ℂ`.
2. State the paper's identity (`⟨φ_α, φ_β⟩ = δ_αβ`) as a theorem over those
   concrete objects.
3. Prove it via the standard character-sum derivation (or cite the Mathlib
   counterpart if one exists — `Matrix.dotProduct` / `Finset.sum_eq_zero_iff`
   combined with `ZMod.sum_pow_units` style lemmas).
4. If you want to keep the Kronecker shorthand, define it *afterward* as a
   consequence, not as the primitive.

### Related issues

- [#477] — `QXPLayerData` field projections (Ch4 SVD as axiom fields)
- [#494] — the Fourier case and other candidates

---

## A3 — Zero-fallback branches hiding preconditions

**Smell.** A total function is defined by `if eligible then real_value else
default`, where the `default` (usually `0`, `default`, `⊥`, or
`Classical.arbitrary`) is a sentinel for "precondition not met." Downstream
theorems state properties that are only true on the eligible branch, but the
theorem's type signature does not carry the eligibility proof, so the
obligation moves silently from the prover to whoever happens to call the
function. See issue [#495], related to [#307].

### Why it's bad

The signature lies about the domain of validity. A caller passing a
non-eligible input gets `0` back; any theorem proved about "the output" is
proved for `0`, which is trivially true and carries no information. When a
later theorem composes the output with another lemma, the composition
type-checks but the conclusion is vacuous on inputs where the original
precondition failed.

The paper, by contrast, restricts the quantifier in the first place:
"Fix a tuple `(x₁, ..., x_k)` with Hamming weight `≥ d+1`." The Lean should
match.

### How to spot it

- `match ... with | some _ => real | none => 0` or `| _ => 0`.
- `if hEligible : P then ... else default`.
- Identifier names containing `fallback`, `placeholder`, `sentinel`,
  `dummy`, `or0`, `orDefault`.
- Recursive definitions whose base case unconditionally returns a sentinel.
- Functions that return `Polynomial params` but can return the zero polynomial
  on inputs that shouldn't be in the domain.

### Concrete example

From `MIPStarRE/LDT/Pasting/Defs/Interpolation.lean`:

```lean
/-- Extract the polynomial from a completed slice outcome; returns 0 on ⊥. -/
def extractSliceOr0 {params : Parameters} [FieldModel params.q]
    (g : GHatOutcome params) : Polynomial params :=
  match g with
  | some p => p.poly
  | none   => 0
```

The consumer `interpolateCompletedSlicesFromSupport` runs Lagrange
interpolation on `extractSliceOr0`-extracted values. If the support contains
a `none`, the interpolant silently pretends that slice evaluated to zero.
The paper's Lagrange step is quantified over *eligible* slices only, so the
Lean API should carry `∀ i ∈ support, (g i).isSome` as a hypothesis; instead
it carries nothing, and the theorem technically type-checks on inputs for
which its conclusion is meaningless.

### Acceptable uses of this pattern

Not every default branch is a castle. `Inhabited` / `Nonempty` instances
that provide a canonical inhabitant (e.g., the zero polynomial for
`Nonempty (Polynomial params)`) are plumbing, not proof. The test is: **does
any theorem mention the output?** If a theorem says "the output satisfies
P", and P is not trivially satisfied by the sentinel, the fallback is
smuggling a precondition.

### How to fix it

Pick one of:

1. **Make the precondition explicit.** Add `(h : eligible input) :` to the
   signature. Let Lean's type system enforce that non-eligible inputs cannot
   be passed.
2. **Return an `Option`.** The `none` result forces every caller to handle
   the case, so theorems about "the output" now quantify only over the
   `some` branch.
3. **Restrict the domain.** Instead of `(x : X) → Y`, take `(x : {x : X //
   P x}) → Y`. Common for finite-support Lagrange-style constructions where
   the subtype is computable via `Finset.filter`.

### Classical-logic dependencies

A sibling smell in this pattern: `DecidablePred` / `DecidableEq` instances
that silently use `Classical.dec` to fill in decidability that should be
constructive (e.g.,
`interpolationEligibleSandwichFamily` does `open Classical in ...` to gate
a predicate that is actually decidable by a finite-support check). Those
are acceptable only when the predicate is genuinely non-constructive; if a
constructive instance is plausible, write it, don't bottom out in
`Classical.dec`. See [#495] for the full catalogue of classical-logic uses
in `LDT/Pasting/`.

### Related issues

- [#307] — placeholder Lagrange coefficient (original fallback tracker)
- [#495] — the full pasting-interpolation catalogue

[#278]: https://github.com/LionSR/MIPStarRE/issues/278
[#307]: https://github.com/LionSR/MIPStarRE/issues/307
[#449]: https://github.com/LionSR/MIPStarRE/issues/449
[#451]: https://github.com/LionSR/MIPStarRE/issues/451
[#477]: https://github.com/LionSR/MIPStarRE/issues/477
[#491]: https://github.com/LionSR/MIPStarRE/pull/491
[#493]: https://github.com/LionSR/MIPStarRE/issues/493
[#494]: https://github.com/LionSR/MIPStarRE/issues/494
[#495]: https://github.com/LionSR/MIPStarRE/issues/495
