# MIPStarRE-local convention addenda

The canonical convention documents live in the `lean-conventions` skill of
[texra-ai/texra-lean-skills](https://github.com/texra-ai/texra-lean-skills)
(auto-installed for Claude Code sessions via `.claude/settings.json`; other
agents: clone the repository and symlink the skill directories, per its
README). This file holds only
MIPStarRE's project-local facts — it restates no shared rule, and shared
rules never move here.

## Style (MATHLIB_style)

### Linter warnings

Do not mask linter warnings instead of fixing them. A cleanup PR should not add
broad `set_option linter.<name> false` blocks, and especially not file-wide
blocks, just to make the build output quieter. Linters exist to expose real
maintenance problems; hiding them makes later proof work and review harder.

Fix the warning at its source whenever possible:

- wrap long lines rather than disabling `linter.style.longLine`;
- remove or narrow unused variables, section variables, and unused typeclass
  assumptions rather than disabling the corresponding unused-* linter;
- remove unused `simp` arguments rather than disabling `linter.unusedSimpArgs`;
- rewrite proof terms or state the simplified goal explicitly rather than
  silencing `linter.flexible`.

If a linter warning is a genuine false positive or a temporary porting
exception, use the narrowest possible scope, preferably
`set_option linter.<name> false in <decl>`, and add a short nearby explanation.
Such exceptions should be rare and reviewable. Never use linter suppression as
the main mechanism for a linter-warning cleanup PR.

## PR review (MATHLIB_pr-review)

### Source-faithfulness checks

For this repository, the first review question is whether a paper-facing Lean
statement still represents the cited result in `references/ldt-paper/`.  Before
applying the general mathlib review checklist in the lean-conventions
`MATHLIB_pr-review` reference, compare every changed
source-labelled theorem, lemma, proposition, corollary, or definition with the
corresponding paper statement and the active blueprint entry.

Reject a paper-facing statement if it has acquired a non-paper bridge, residual,
repair, package, producer, proof-obligation, assumptions-bundle, hypotheses-bundle,
or arbitrary implication hypothesis.  Necessary boundary hypotheses, such as
positivity for division or nonemptiness of a finite type, may be faithful formal
encodings of implicit paper assumptions, but they should be documented when
mathematically load-bearing.

Reviewers should also inspect `\lean{}` and `\leanok` links.  A source-labelled
blueprint entry should point to the source theorem or its faithful construction
theorem, not to conditional helpers whose assumptions are proof obligations.
Auxiliary Lean declarations may be recorded in a separate remark, provided the
remark states that they are not additional hypotheses in the paper theorem.

## Proof integrity (PROOF_INTEGRITY)

### Companion document

> **Companion document:** [`anti_patterns.md`](./anti_patterns.md) catalogues
> subtler proof-evasion patterns that pass every blocker check in the
> lean-conventions `PROOF_INTEGRITY` reference yet still
> fail to prove the claimed mathematics (conclusion-shaped hypotheses,
> definitional sleight-of-hand, zero-fallback branches, trivial default
> witnesses, Mathlib-bypass castles, external `*Statement` smuggles).
> Consult it alongside this file during review.

### Project paper-realignment protocol

The canonical paper-realignment exception in the lean-conventions
`PROOF_INTEGRITY` reference is instantiated here as
follows (the protocol and the `**Unfaithful:**` marker are described in
`AGENTS.md`):

> **Paper-realignment exception:** When a PR is explicitly realigning a
> source-labelled declaration with `references/ldt-paper/`, the `sorry`
> blocker of the lean-conventions `PROOF_INTEGRITY` reference may be
> temporarily relaxed for the affected proof bodies.  The
> PR must restore the source-faithful public statement, name the remaining proof
> obligation as a theorem or lemma, and cite the paper passage plus the
> tracking issue or paper-gap note.  A theorem whose proof still depends on a
> known non-paper bridge, residual, repair input, obligation structure, or
> conditional helper
> must carry the `**Unfaithful:**` docstring marker described in `AGENTS.md`.
> Review such PRs against statement faithfulness and the documented discharge
> plan, not merely against the temporary `sorry` count.

### Axiom policy

When an external mathematical result must remain unformalized temporarily,
prefer a caller-supplied `Prop` hypothesis over a global `axiom`
declaration, and add a regression check (for example a
`Lean.collectAxioms`-based assertion, as in
`MIPStarRE.LDT.Test.AxiomAudit`) so later refactors cannot silently widen
the axiomatic base.

This preference does not license proposition inputs on source-labelled paper
theorems.  If the cited paper theorem does not assume the proposition, a
caller-supplied `Prop` hypothesis is an additional theorem hypothesis, not a
proof of the paper statement.  Use such hypotheses only for explicitly
conditional auxiliary results, and keep the source-labelled theorem statement
faithful to the paper.

### Scaffolding that blocks real formalization

This is a subtle but critical failure mode: **scaffolding definitions or
theorem statements that do not faithfully represent the actual mathematics**,
making them impossible to connect to real Mathlib-based proofs.

Signs to watch for:

- Custom type definitions for objects that already exist in Mathlib (e.g.,
  defining a custom `Measurement` type instead of using Mathlib's
  `MeasureTheory` or operator algebra API)
- Theorem statements whose hypotheses or conclusions use project-local types
  that are not definitionally equal to or coercible from the Mathlib versions
- Scaffolded definitions that compile but encode the wrong mathematical
  semantics (e.g., a "projective measurement" definition that does not enforce
  the correct positivity or completeness conditions)
- Intermediate lemmas stated in terms of scaffolding types that cannot be
  connected upstream to Mathlib's API without reproving everything
- Definitions that "work" for `sorry`-based proofs but fail when you try to
  fill in real proofs using Mathlib lemmas (type mismatches, missing instances,
  incompatible universes)

When reviewing scaffolded code, ask: **Can a real proof be built on top of
this?** If the types, instances, and API surface don't align with Mathlib, the
scaffolding is actively harmful — it creates technical debt that blocks
progress rather than enabling it.

### Paper-labelled theorem statement drift

A theorem advertised as the Lean formalization of a paper theorem is a blocker
if its public statement has drifted from the cited paper statement.
Changing a theorem away from the statement in `references/ldt-paper/` is
strongly discouraged unless it is forced by faithful formal encoding or by a
documented mathematical necessity.

The most common failure mode is replacing an unformalized proof step by an
extra hypothesis on the theorem itself.  This produces a true conditional
theorem, but it is not the theorem stated in the paper.  In particular, do not
repair a theorem such as `mainFormal` by adding assumptions named
`BridgeHypotheses`, `Input`, `Residual`, `Package`, `RepairInput`, `Producer`,
generic `Hypotheses` or `Assumptions` bundles, or similar, unless those
assumptions are explicitly present in the cited paper statement.

Conditional helpers are a last-resort quarantine for proof work that cannot yet
be closed.  Before introducing one, state the missing intermediate fact as a
named lemma or theorem to be proved from the paper hypotheses.  A conditional
helper is permitted only when it has a paper-gap note or tracking issue, a named
obligation-discharger target, and an explicit removal plan.  Its name must show
that it is conditional, for example with `_of_...`, `_assuming_...`, or
`conditional...`.  It must not be the declaration used by a source-labelled
blueprint theorem with `\leanok`.

Existing bridge hypotheses should be treated as proof debt.  Mine their proofs
for reusable arguments, but do not keep a paper-labelled theorem in a
strengthened form merely because the conditional version compiles.  If the
bridge data cannot be derived from the paper hypotheses, the correct repair is
to restore the paper-aligned theorem statement and leave the missing proof as a
tracked `sorry`, rather than to keep the extra assumption on the theorem.

Not every explicit Lean hypothesis is statement drift.  Side conditions needed
to encode the paper's domain, such as nonemptiness, decidability, field-model
instances, positivity of parameters, or denominator nonvanishing, may be
faithful when the paper uses the corresponding objects without comment.  These
conditions should still be reviewed.  The issue is whether the hypothesis is
mathematical domain data implicit in the source, or an unproved intermediate
step of the source proof.

For every paper-labelled theorem change, require a statement integrity audit:

- paper assumptions versus Lean assumptions;
- paper conclusion versus Lean conclusion;
- verdict: exact, faithful boundary hypotheses, extra assumptions, weakened
  conclusion, or strengthened conclusion.

### Source-statement proof gaps

**For source-statement proof gaps**: Read
[`paper-gaps/proof-gap-protocol.tex`](paper-gaps/proof-gap-protocol.tex) when a
proof is blocked by a bridge, residual, repair, input, package, or obligation
structure.  It explains when to introduce an internal obligation theorem, why
conditional helpers are exceptional temporary quarantine objects, and why a
tracked `sorry` is preferable to a strengthened source theorem statement.
