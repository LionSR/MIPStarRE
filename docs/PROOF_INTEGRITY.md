<!-- Pointer: the canonical document lives in the lean-conventions skill of
     texra-ai/texra-lean-skills, installed automatically in Claude Code
     sessions by .claude/settings.json (other agents: see the install
     instructions in that repository's README). Only the project addendum
     below is repo-local. -->

# Lean Proof Integrity Rules

Canonical text: the `lean-conventions` skill —
[PROOF_INTEGRITY.md](https://github.com/texra-ai/texra-lean-skills/blob/main/skills/lean-conventions/references/PROOF_INTEGRITY.md).
Consult it through the installed skill; do not restate its rules here.

## Project addendum (MIPStarRE)

### Companion document

> **Companion document:** [`anti_patterns.md`](./anti_patterns.md) catalogues
> subtler proof-evasion patterns that pass every blocker check above yet still
> fail to prove the claimed mathematics (conclusion-shaped hypotheses,
> definitional sleight-of-hand, zero-fallback branches, trivial default
> witnesses, Mathlib-bypass castles, external `*Statement` smuggles).
> Consult it alongside this file during review.

### Project paper-realignment protocol

The canonical paper-realignment exception above is instantiated here as
follows (the protocol and the `**Unfaithful:**` marker are described in
`AGENTS.md`):

> **Paper-realignment exception:** When a PR is explicitly realigning a
> source-labelled declaration with `references/ldt-paper/`, the `sorry`
> blocker above may be temporarily relaxed for the affected proof bodies.  The
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
