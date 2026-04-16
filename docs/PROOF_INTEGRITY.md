# Lean Proof Integrity Rules

This file is the **single source of truth** for proof integrity checks in this
repository. All CI workflows and review prompts should reference this file
rather than duplicating the rules inline.

> **Lean version**: 4.x (Lean 3 keywords like `constant` do not apply)

---

## Blockers

These patterns **must** be resolved before merging.

### Direct proof holes

| Pattern | Risk |
|---------|------|
| `sorry` | Axiomatically closes any goal — the proof is incomplete |
| `admit` | Tactic alias for `sorry` |

### Kernel / type system bypasses

| Pattern | Risk |
|---------|------|
| `native_decide` | Relies on trusted native evaluation / compiler; banned in Mathlib for soundness and process reasons |
| `unsafeCast`, `unsafeCoerce` | Type system bypass — can fabricate any proof term |
| `lcProof` | Low-level proof fabrication primitive — can prove `False` |
| `ofReduceBool`, `ofReduceNat` | Kernel reduction primitives exploitable for unsound proofs |

### Axiom smuggling

| Pattern | Risk |
|---------|------|
| `axiom` declarations | Introduces unproven assumptions that could be inconsistent; must be explicitly justified |

When an external mathematical result must remain unformalized temporarily,
prefer a caller-supplied `Prop` hypothesis over a global `axiom`
declaration, and add a regression check (for example `#guard_msgs in`
`#print axioms ...`) so later refactors cannot silently widen the axiomatic
base.

### Circular reasoning

Lean's kernel forbids literal declaration cycles, so focus on **mathematical
circularity**:

- Proofs that assume (or trivially reintroduce) the statement being proved as a
  local hypothesis, then immediately close the goal from that hypothesis
- Helper lemmas in the same file that essentially restate the main goal and are
  only used to prove that goal
- Local `have`/`let` bindings that are just the goal rephrased, used to solve
  the goal without any real argument
- Newly introduced `axiom` that makes a difficult statement trivially provable
  without connecting to existing Mathlib / core theorems
- Abuse of `unsafe` features to fabricate proofs instead of giving a genuine
  derivation
- `by exact h` where `h` came from an unjustified assumption identical to the
  goal

### Castle-in-the-air (ungrounded proofs)

Proofs that avoid grounding in Mathlib:

- Custom re-declarations of standard Mathlib lemmas (e.g., re-proving
  `add_comm` instead of importing it)
- `axiom` or `sorry`-based helper lemmas for facts that already exist in
  Mathlib
- Chains of custom lemmas that never bottom out in Mathlib or Lean core
- `private` helper lemmas that duplicate Mathlib API (e.g., custom matrix
  transpose lemmas when `Matrix.transpose_*` exists)
- Overly long proof chains replaceable by a single Mathlib lemma

When flagging, perform an actual lookup (grep, `#find?`, `exact?`,
`library_search`). If an equivalent exists, cite the Mathlib lemma and module
path. If not, state "no equivalent found" with search evidence.

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

---

## Warnings

These should be flagged for review but may be acceptable with justification.

### Placeholder tactics

| Pattern | Risk |
|---------|------|
| `exact?`, `apply?`, `library_search`, `suggest` | Search tactics left as placeholders — replace with the concrete result |

### Safety / termination bypasses

| Pattern | Risk |
|---------|------|
| `unsafe def` | Bypasses Lean safety checks; should not appear in proof-relevant code |
| `partial def` | No termination proof required; unsound if used to build proof terms |
| `implemented_by` / `implementedBy` | Decouples runtime behavior from proven specification |

### Suspicious options

| Pattern | Risk |
|---------|------|
| `set_option maxHeartbeats 0` | Disables timeout — can hide non-terminating proofs |
| `set_option maxHeartbeats` with values >= 4,000,000 | 20x the default (200,000) — likely indicates an inefficient proof |
| `set_option maxRecDepth` with values >= 10,000 | May hide structural issues in proofs |

### Debug artifacts

| Pattern | Risk |
|---------|------|
| `dbg_trace` | Debug trace left in code |
| `stop` | Halts elaboration — development aid only |
| `#check`, `#eval`, `#print` in proof files | Debug commands that should be removed |

---

## How to use this file

**In CI review prompts**: Reference this file instead of inlining the rules:
```
Read `docs/PROOF_INTEGRITY.md` for the complete list of proof integrity
rules. Flag blockers as must-fix issues that should block merge.
Flag warnings as advisory — note them but acknowledge they may be
acceptable with justification.
```

**For manual review**: Use this as a checklist when reviewing Lean PRs.

**Updating rules**: Edit this file and all referencing workflows will
automatically pick up the changes.
