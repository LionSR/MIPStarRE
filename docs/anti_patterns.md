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
- A2 — Definitional sleight-of-hand *(forthcoming)*
- A3 — Zero-fallback branches hiding preconditions *(forthcoming)*
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

[#278]: https://github.com/LionSR/MIPStarRE/issues/278
[#307]: https://github.com/LionSR/MIPStarRE/issues/307
[#449]: https://github.com/LionSR/MIPStarRE/issues/449
[#451]: https://github.com/LionSR/MIPStarRE/issues/451
[#477]: https://github.com/LionSR/MIPStarRE/issues/477
[#491]: https://github.com/LionSR/MIPStarRE/pull/491
[#493]: https://github.com/LionSR/MIPStarRE/issues/493
[#494]: https://github.com/LionSR/MIPStarRE/issues/494
[#495]: https://github.com/LionSR/MIPStarRE/issues/495
