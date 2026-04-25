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
- [A4 — Trivial default witnesses for existentials](#a4--trivial-default-witnesses-for-existentials)
- [A5 — Castle-in-the-air / bypassing Mathlib](#a5--castle-in-the-air--bypassing-mathlib)
- [A6 — External `*Statement` smuggles](#a6--external-statement-smuggles)

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

Historical example (before the MainInductionStep cleanup):

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

Here `MainInductionBridgePackage.witness` has type
`∃ error, ∃ G, ConsRel ... error ∧ error ≤ mainInductionError ...` — literally
the conclusion. The code has since been refactored to remove both this
specific MainInductionStep bridge and the interim theorem alias that exposed
the same witness shape under the paper theorem's name, but the snippet remains
the archetypal example of the anti-pattern.

PR [#491] proposed to delete the `*BridgePackage` by **inlining** the bundle's
fields as explicit hypotheses. That only scatters the same pattern across
individual signatures without producing any proof — it's strictly worse
because the named bundle at least shows up in one tracker. Do not accept PRs
that discharge an ungrounded bridge by flattening it into conclusion-shaped
existential hypotheses, or by reintroducing the same shape under a theorem name
that suggests the paper result has been proved.

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
- [#451] — the tracked `BridgePackage` producer catalogue
- [#595] — resolved the QXP `ProjectiveNonMeasurementBridgePackage` offender by
  deleting the bridge and threading `RoundingToProjectorsWitness` directly
- [#477] — resolved `QXPLayerData` axiom-field projection (a definitional variant)
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

/-- The exact inner-product formula for the hypercube Fourier basis. -/
lemma fourierBasisInnerProduct_eq (params : Parameters)
    (α β : Point params) :
    fourierBasisInnerProduct params α β = if α = β then 1 else 0 := rfl

/-- `prop:eigenvectors`. -/
theorem eigenvectors (params : Parameters) :
    (∀ α β : Point params,
      fourierBasisInnerProduct params α β = if α = β then 1 else 0) ∧ ... := by
  refine ⟨?_, ?_⟩
  · intro α β
    exact fourierBasisInnerProduct_eq params α β    -- castle: def IS Kronecker delta
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

- [#477] — resolved `QXPLayerData` field projections (Ch4 SVD as axiom fields)
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

### Concrete example (historical; resolved by PR #561)

Until PR #561, `MIPStarRE/LDT/Pasting/Defs/Interpolation.lean` contained:

```lean
/-- Extract the polynomial from a completed slice outcome; returns 0 on ⊥. -/
noncomputable def extractSliceOr0 {params : Parameters} [FieldModel params.q]
    (g : GHatOutcome params) : PolynomialModel params :=
  match g with
  | some p => p.poly
  | none   => 0
```

The consumer `interpolateCompletedSlicesFromSupport` ran Lagrange
interpolation on `extractSliceOr0`-extracted values. If the support contained
a `none`, the interpolant silently pretended that slice evaluated to zero.
The paper's Lagrange step is quantified over *eligible* slices only, so the
Lean API should carry `∀ i ∈ support, (g i).isSome` as a hypothesis; instead
it carried nothing, and the theorem technically type-checked on inputs for
which its conclusion was meaningless.

**Current status:** resolved. The live API now removes `extractSliceOr0`,
threads the explicit hypothesis `hσsupport : σ ⊆ gHatTupleSupport gs` into
`interpolateCompletedSlicesFromSupport`, and packages the chosen support subset
as `InterpolationSupportWitness` so the arbitrary choice and its proof fields
are visible at call sites.

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
constructive. The historical `interpolationEligibleSandwichFamily`
implementation was exactly such a case: it used `open Classical in ...` to
gate a predicate that is actually decidable by a finite-support check. PR
#561 fixed that example by adding `interpolationEligible_decidablePred`.
Those classical instances are acceptable only when the predicate is genuinely
non-constructive; if a constructive instance is plausible, write it, don't
bottom out in `Classical.dec`. See [#495] for the full catalogue of
classical-logic uses in `LDT/Pasting/`.

### Related issues

- [#307] — placeholder Lagrange coefficient (original fallback tracker)
- [#495] — the full pasting-interpolation catalogue

---

## A4 — Trivial default witnesses for existentials

**Smell.** A theorem of the shape `∃ x, P x` is closed by picking
`x := default`, `x := 0`, `x := 1`, or `x := Classical.arbitrary`, where the
paper names a *specific, non-trivial* `x` and derives `P x` from real
structure. The Lean claim is *mathematically* weaker because the Lean
theorem guarantees less than the paper's (it proves some-trivial-thing, not
the-specific-paper-thing). See [#449] for the full ledger.

### Why it's bad

The theorem name matches a paper lemma but the witness has been cheapened
into a placeholder. Downstream theorems that inspect the witness get `0` or
`default`, which is almost always useless. Consumers that "use" the lemma
are really using the trivial `∃` and cannot proceed past the first attempt
to pin the witness down.

### How to spot it

- `refine ⟨default, ?_⟩` / `exact ⟨default, ...⟩` / `refine ⟨0, ?_⟩` /
  `exact ⟨1, ...⟩` inside a proof of a paper-cited existential.
- `letI : Inhabited X := ⟨Classical.arbitrary X⟩` followed by a `let x :=
  default`.
- `Classical.arbitrary` / `Classical.choice` / `Nonempty.some` in proof
  bodies (as opposed to typeclass definitions).
- Identifier suffix `...Witness := default` on a bundled output.

### Concrete example

From the ledger in [#449]:

- `lem:sdp` / `sdp` — primal witness is `T := default` (a zero
  submeasurement) and dual witness `Z := 1`. The paper requires a specific
  feasible pair; the Lean version proves only that some arbitrary pair exists,
  which always does.
- `lem:projective-low-rank-sum` / `projectiveLowRankSum` — auxiliary
  projective measurement `t := (default : ProjMeas Outcome ι)`. The paper
  constructs `(auxSpace, T_a)` from the eigenvector basis of each rounded
  `R_a`; the Lean version picks a zero-dimensional placeholder, which is
  disconnected from the paper's SVD derivation.
- ~~`lem:global-rewrite` / `globalRewrite` — decomposition witness is
  `default`~~ (historical; resolved by PRs #527 and #542). The live theorem now
  uses `canonicalGlobalVarianceDecomposition`, and
  `globalVarianceTraceWitness` consumes the centered residual family
  `u ↦ A^u - A_{\mathrm{avg}}` rather than ignoring the witness.

### Acceptable uses

Non-computable instances required for typeclass plumbing —
`Nonempty (Polynomial params)` inhabited by the zero polynomial, `Inhabited
(Measurement ...)` by the trivial one — are fine when they are used only to
*inhabit* a type, not to discharge a paper-cited existential. The smell is
specifically about `default` showing up in the proof of a *theorem named
after a paper result*.

### How to fix it

- Construct the paper's witness explicitly. If the ingredients are not yet
  formalized (e.g., Mathlib SVD, spectral decomposition), extract a bridge
  lemma that *constructs* the witness from the missing Mathlib facts, and
  track the Mathlib gap as a separate issue.
- Keep the existential statement, but strengthen the conclusion so that
  `x := default` no longer satisfies it (e.g., "there exists `x` *with*
  rank `m`", not merely "there exists `x`").
- If the theorem is a scaffold that will later consume a producer, consider
  making that producer an explicit bridge hypothesis (A1-grade placeholder)
  rather than silently picking `default`. The bridge at least appears in
  [#451].

### Related issues

- [#449] — master ledger; all three known cases are already listed

---

## A5 — Castle-in-the-air / bypassing Mathlib

**Smell.** Lean code re-declares or re-proves something that already lives
in Mathlib, or builds a tower of custom lemmas that never bottom out in
Mathlib / Lean core. The proof "works" only because the internal custom
statements are compatible with each other — it is a closed ecosystem that
doesn't ground in the reference library.

This is the "scaffolding that blocks real formalization" section of
[`PROOF_INTEGRITY.md`](./PROOF_INTEGRITY.md) in concrete examples. The two
flavours:

1. **Re-proving Mathlib.** Writing `private lemma my_add_comm : a + b = b + a`
   when `add_comm` exists.
2. **Custom types that shadow Mathlib.** Defining `MyMeasurement` instead of
   using `MeasureTheory.Measure`, `MyMatrix` instead of `Matrix`,
   `MyHermitian` instead of `Matrix.IsHermitian`. The custom version may be
   definitionally equal to (or coercible from) the Mathlib version, but if
   it isn't, every consumer must reprove everything.

### Why it's bad

1. The duplicated statements aren't audited by Mathlib's community, so they
   may be subtly wrong (wrong edge case, wrong universe, wrong typeclass).
2. When the real Mathlib proof is needed (for a key gap lemma), the custom
   tower must be rewritten to interoperate — often via a painful coercion
   layer that reintroduces every fact.
3. Hides real Mathlib gaps. If we decline to use Mathlib because "our
   version is simpler," the gap never gets filed against Mathlib.

### How to spot it

- `private lemma` in a file about well-established algebra/analysis
  (Cauchy–Schwarz, `sqrt`, `rpow`, `PosSemidef`, `Matrix.trace`, etc.).
- Custom structures named `MyX` / `LocalX` / `ProjectX` where `X` is a
  standard concept.
- Proof bodies that chain ten `private lemma`s where the natural Mathlib
  counterpart would be two `exact?` lookups.
- Files with no `import Mathlib.*` above the level of `Mathlib.Tactic.*`
  when the subject matter is clearly Mathlib-adjacent (linear algebra,
  analysis, measure theory).

### How to fix it

Before writing a new lemma, spend one minute on:

- `exact?` / `apply?` on the goal.
- `#find` / `Loogle` for the statement shape.
- `rg -n "theorem.*X" .lake/packages/mathlib/` for a keyword.

If Mathlib has it, use it. If it doesn't, consider whether the missing
lemma should be upstreamed (file an issue against Mathlib, or at least a
TODO pointing at the gap). The project already has this mandate — see the
"Mathlib Integration" section of [`CLAUDE.md`](../CLAUDE.md):

> Scout Mathlib first (`exact?`, `apply?`, `#find?`, grep Mathlib source)

A5 is what happens when that step is skipped.

### Audit cross-reference

`docs/audit/` contains chapter-by-chapter Mathlib dependency scouting
reports. If a section of the code review says "this could use Mathlib
lemma X", it belongs in a specific `docs/audit/*.md` file for that chapter.

---

## A6 — External `*Statement` smuggles

**Smell.** A theorem takes a hypothesis of type `SomeStatement` (or
`SomeWitness`, `SomeOutput`, etc.) that is defined elsewhere and intended
to represent an external mathematical result — but the external result
has no producer and no plan for one. The Lean statement is then:
"assuming the external result, the Lean conclusion holds." That is
sometimes legitimate (e.g., a cite to a book whose formalization we don't
plan to do), and sometimes a cover for locally-unwanted work.

This overlaps with A1 but is subtler: the hypothesis isn't the
*current theorem's* conclusion, it's an *independently-named* claim that
happens to unblock the current proof.

### Acceptable external smuggles

- **Genuine external citations.** `PolishchukSpielmanClassicalSoundnessStatement`
  cites the Polishchuk–Spielman theorem; we don't plan to formalize it.
- **Mathlib gaps we can't fill.** `hMatrixChernoff` in `chernoffBernoulliMatrix`
  is a Mathlib matrix-Chernoff-type statement; we flagged the gap upstream.
- **Placeholder interfaces with a named tracking issue.** A `*Statement`
  that has an open sub-issue saying "produce this" is trackable.

### Unacceptable external smuggles

- A `*Statement` with no open tracking issue, no docstring explaining the
  mathematical gap, and no consumer-side comment flagging the smuggle.
- A `*Statement` whose body is the theorem's conclusion, wearing a different
  name (A1 in disguise).
- A `*Statement` used to close a lemma whose paper version does not require
  any such external assumption (silent strengthening of the Lean theorem
  relative to the paper's).

### How to spot it

Grep for these suffixes: `*Statement`, `*Witness`, `*Claim`,
`*Conclusion`, `*Output`, `*Input`, `*Hypothesis`, `*Requirement`,
`*Assumption`, `*Package` (that isn't a `*BridgePackage`). For each, ask:

- Is there a theorem anywhere that **produces** a value of this type?
- If not, is the absence explained in a docstring / tracking issue /
  `docs/audit/` entry?
- Does the paper depend on an external theorem of this shape?

If any answer is "no", the structure is an unacceptable smuggle.

### Current status (audited 2026-04-18; updated 2026-04-25)

All 34 `*Statement` / 9 `*Conclusion` / 8 `*Witness` structures on `main`
are either grounded (have producer theorems) or are the known tracked
items in [#449] / [#451]. The former QXP
`ProjectiveNonMeasurementBridgePackage` offender has been removed from that
live list (resolved in [#595]), and the old `QXPLayerData` SVD / `pQApprox`
field-projection offender has been removed by the reduced primitive API and
real `pQApprox` proof (issue [#652]). No new unacceptable smuggles were found in
that sweep. If you add a new `*Statement`-style structure to this codebase,
include a docstring explaining its grounding plan and (if no producer exists
yet) file a sub-issue in [#449].

### Related issues

- [#449] — hypothesis-smuggle ledger (⚠️H items)
- [#278] — the original "derive `PermInvState` internally" discussion

---

## Reviewer checklist

Use this alongside the [`PROOF_INTEGRITY.md`](./PROOF_INTEGRITY.md) blocker
list. For any theorem or lemma that claims a paper result, ask:

- [ ] **Hypothesis audit.** Does any hypothesis contain (up to `∃`/`∧`) the
      theorem's conclusion? If yes, that's A1 — reject or strengthen.
- [ ] **Definitional audit.** Is the proof `rfl` or a one-line `simp`? If
      yes, does the unfolded definition do the paper's math, or just match
      the shape of the conclusion? The latter is A2.
- [ ] **Domain audit.** Does the function have a fallback branch (`if
      eligible ... else default`)? If yes, does the theorem's signature
      require eligibility? If not, that's A3.
- [ ] **Witness audit.** Does the proof pick `x := default` for an
      existential named after a paper lemma? That's A4 unless the witness
      is genuinely unique-up-to-isomorphism.
- [ ] **Mathlib audit.** Is there a `private lemma` that duplicates a
      Mathlib fact? Run `exact?` / `apply?` / `#find` before accepting it
      (A5).
- [ ] **External-citation audit.** Does the proof consume a `*Statement` /
      `*Witness` / `*Package`? Is there a tracking issue that names its
      grounding plan (A6)?
- [ ] **Paper-faithfulness.** Does the Lean signature match the paper's
      statement, or does Lean sneak in extra hypotheses? Flag divergences
      as ⚠️S in [#449].

A lemma that passes all of these is a proof. A lemma that fails one is
scaffolding, and should be labelled and tracked as such (don't tag with
`\leanok` until the gap is closed).

## CI prevention

Mechanical detection is possible for many of these patterns:

- **A1 (conclusion-shaped hypothesis).** When [#438] lands (`\leanok` ↔
  `sorryAx` drift), extend it with a heuristic: for each `\leanok`-tagged
  declaration, parse the hypothesis list; if any hypothesis's type (modulo
  `∃`/`∀`/`∧`) contains a prefix of the conclusion structure, warn.
- **A2 (definitional sleight).** Grep for `theorem <Name>.* := rfl` where
  `<Name>` has a blueprint `\lean{}` cross-reference. The only allowed cases
  are ones annotated with `@[paper_bookkeeping]` (proposed attribute) or in
  an allow-list.
- **A3 (zero-fallback).** Grep for identifier suffixes `fallback`, `or0`,
  `orDefault`, `placeholder`, `sentinel` in `Defs/*` files. Each should have
  a docstring citing the downstream eligibility precondition.
- **A4 (default witnesses).** Grep `:= default`, `refine ⟨default`, `exact
  ⟨default`, `Classical.arbitrary` inside proof bodies (not typeclass
  definitions). Cross-reference to [#449]'s witness ledger.
- **A5 (Mathlib bypass).** No reliable CI check, but `docs/audit/` reports
  catch it during per-chapter audits.
- **A6 (external smuggles).** Every new `structure *Statement` without a
  producing theorem should be required to carry a `/-- Grounded by: #NNN
  -/` docstring, enforced by a lint rule over `blueprint/`.

The scripts in `scripts/` (notably `scripts/check_blueprint_sync.py` from
PR [#438]) are the natural home for extensions that add these checks.

## See also

- [`PROOF_INTEGRITY.md`](./PROOF_INTEGRITY.md) — kernel-level blockers
  (`sorry`, `native_decide`, bare `axiom`, etc.).
- [`CONTRIBUTING.md`](./CONTRIBUTING.md) — overall contributor workflow;
  review checklist section should link here.
- [`pr-review.md`](./pr-review.md) — detailed PR review guidelines.
- [`naming.md`](./naming.md) and [`style.md`](./style.md) — Mathlib
  conventions; avoiding A5 (bypassing Mathlib) often starts with using
  Mathlib's names.
- [#449], [#451], [#477], [#493], [#494], [#495] — concrete trackers for
  the anti-patterns documented here.

[#278]: https://github.com/LionSR/MIPStarRE/issues/278
[#438]: https://github.com/LionSR/MIPStarRE/pull/438
[#307]: https://github.com/LionSR/MIPStarRE/issues/307
[#449]: https://github.com/LionSR/MIPStarRE/issues/449
[#451]: https://github.com/LionSR/MIPStarRE/issues/451
[#477]: https://github.com/LionSR/MIPStarRE/issues/477
[#491]: https://github.com/LionSR/MIPStarRE/pull/491
[#493]: https://github.com/LionSR/MIPStarRE/issues/493
[#595]: https://github.com/LionSR/MIPStarRE/issues/595
[#652]: https://github.com/LionSR/MIPStarRE/issues/652
[#494]: https://github.com/LionSR/MIPStarRE/issues/494
[#495]: https://github.com/LionSR/MIPStarRE/issues/495
