# Contributing to MIPStarRE

This document codifies the conventions for pull requests, issues, code review,
Lean style, and CI automation used in the MIPStarRE project.

---

## 1. Pull Request Conventions

### Title format

Use **conventional-commit** style:

```
type(scope): short description
```

| Type       | When to use                                      |
|------------|--------------------------------------------------|
| `feat`     | New definition, lemma, theorem, or module         |
| `fix`      | Bug fix (broken proof, wrong identifier, etc.)    |
| `refactor` | Restructuring without changing API surface        |
| `docs`     | Documentation or blueprint changes only           |
| `ci`       | CI/CD workflow changes                            |
| `chore`    | Dependency bumps, linting, toolchain updates      |

**Scope** is a shortened module path: `LDT/SelfImprovement`, `Quantum`, `blueprint`,
`LDT/Pasting`, etc. Omit the `MIPStarRE/` prefix.

Examples:
- `feat(LDT/SelfImprovement): add self-improvement induction step`
- `fix(blueprint): resolve broken labels in chapter 7`
- `refactor(LDT): extract shared preliminaries into Basic module`

### Body template

Every PR body must contain three sections:

```markdown
### Motivation
- Why this change is needed (1--3 bullets).

### Description
- What was changed: files added/modified, definitions introduced, lemmas proved.
- Use bullet points.

### Testing
- What was verified and how.
- Examples: `lake env lean MIPStarRE/LDT/Basic.lean`, `lake build MIPStarRE`,
  `rg -n "sorry|axiom" MIPStarRE/LDT/Basic.lean || true`.

---
Addresses #N
```

Use `Addresses #N` (keeps the issue open) or `Closes #N` (auto-closes on merge)
in the footer to link the relevant issue.

### PR template

A PR template (`.github/pull_request_template.md`) auto-fills the
Motivation / Description / Testing sections. Fill in the placeholders — do not
delete the headings.

### Labels

Apply all relevant labels from the taxonomy in [Section 4](#4-label-taxonomy).

---

## 2. Issue Conventions

### Issue templates

Three issue templates are available in `.github/ISSUE_TEMPLATE/`:

| Template | When to use |
|----------|-------------|
| **Formalization Task** | A specific theorem, definition, or lemma to formalize |
| **Bug Report** | Broken proof, type error, sorry regression, CI failure |
| **Tracking Issue** | Umbrella issue tracking a group of sub-issues |

### Formalization issues

Use a descriptive title that names the mathematical content:

```
LDT Section 7: self-improvement step for quantum strategies
```

Label with **area** + **arXiv paper** + **topic** as applicable.

### Multi-part work

For work spanning multiple PRs, use the `Area K/N: title` pattern and create
an umbrella **tracking issue**:

```
LDT 1/5: Preliminaries and basic definitions
LDT 2/5: Self-improvement step
...
```

The tracking issue lists each sub-issue using a **native GitHub tasklist** block
so that child issues display "Tracked by #N" in their sidebar:

````markdown
```[tasklist]
### Tasks
- [ ] #101
- [ ] #102
- [ ] #103
```
````

**Important:** Each `- [ ]` line must contain *only* the issue reference (`#N`).
Do not add descriptions on the same line — put those in the sub-issue titles or
in prose above the tasklist block. Items that are not issue references (plain text
TODOs) cannot go inside the tasklist block; list them as ordinary checkboxes
outside it.

### Tracking issues

Use the **Tracking Issue** template (`.github/ISSUE_TEMPLATE/tracking-issue.yml`).
Label with `tracking`. The `tracking-issue-sync` workflow will automatically:

- Check boxes when referenced issues are closed (including auto-closure by merged PRs).
- Uncheck boxes when referenced issues are reopened.
- Post progress comments on linked issues when PRs merge (what was done, what remains).
- Add the `all-resolved` label when every task is complete.

### Pinned issues

The three most active tracking issues are pinned to the top of the Issues tab.
Update pins when priorities shift (`gh issue pin/unpin`). GitHub allows at most
3 pinned issues.

### Milestones

Use milestones to group issues targeting a shared deadline (e.g., a paper
submission or a toolchain bump). Assign a milestone when the issue has a concrete
target date; remove it when the date no longer applies.

### Discussions

GitHub Discussions is enabled for design questions, proof strategy debates, and
topics that don't map to a single actionable issue. Use issues for concrete work
items; use discussions for open-ended conversations.

### Blueprint sync issues

When the LaTeX blueprint is out of sync with Lean code, open an issue with
the `blueprint-sync` label. Describe which chapter, theorem, or definition
needs `\lean{}` / `\leanok` tags.

Automated drift detection: the [blueprint ↔ Lean sync check][ci-sync] runs
on every PR and fails when a `\leanok` tag sits on a Lean declaration whose
transitive axiom closure still depends on `sorryAx`. See
[`docs/ci-blueprint-sync.md`][ci-sync] for what it checks and how to run it
locally.

[ci-sync]: ci-blueprint-sync.md

---

## 3. Commit Messages

- Use **imperative mood** in the subject line ("Add", not "Added").
- Keep the subject under 72 characters.
- When squash-merging a PR, the commit message should match the PR title format.
- Reference issue numbers where applicable (`(#N)` suffix or `Addresses #N` in body).

---

## 4. Label Taxonomy

### Area labels

| Label            | Description                                |
|------------------|--------------------------------------------|
| `formalization`  | Lean 4 formalization task                  |
| `infrastructure` | Definitions and basic lemmas               |
| `documentation`  | Improvements or additions to documentation |
| `ci`             | CI/CD workflow changes                     |
| `cleanup`        | Code cleanup and style fixes               |

### Paper labels

| Label         | Description                                                        |
|---------------|--------------------------------------------------------------------|
| `2009.12982`  | arXiv:2009.12982 -- Quantum soundness of the classical low individual degree test |

### Topic labels

| Label               | Description                                                           |
|----------------------|-----------------------------------------------------------------------|
| `ldt-basic`          | LDT preliminaries and basic definitions                               |
| `self-improvement`   | Self-improvement step for quantum strategies                          |
| `pasting`            | Pasting lemma for quantum strategies                                  |
| `main-induction`     | Main induction step of the LDT soundness proof                       |
| `commutativity`      | Commutativity of quantum measurements                                 |
| `expansion-graph`    | Expansion properties of hypercube graphs                              |
| `quantum-foundations`| Quantum measurements, outcome families, finite matrices               |

### Workflow labels

| Label            | Description                                    |
|------------------|------------------------------------------------|
| `tracking`       | Tracking issue for a formalization area         |
| `blueprint-sync` | Blueprint out of sync with Lean code            |
| `automation`     | Automated documentation/sync PR                 |
| `follow-up`      | Follow-up work identified from a merged PR      |

### Standard GitHub labels

`bug`, `enhancement`, `good first issue`, `help wanted`, `question`,
`duplicate`, `invalid`, `wontfix`.

---

## 5. Review Checklist

Every PR touching Lean code should be reviewed against these criteria:

1. **Proof correctness** -- No unexplained `sorry`. No `axiom` unless discussed.
   Run `rg -n "sorry|axiom" <file>` to verify.

2. **Mathlib style** -- Follow the naming conventions in [naming.md](naming.md)
   and documentation standards in [doc.md](doc.md). See [pr-review.md](pr-review.md)
   for the full Mathlib review guide.

3. **Type safety** -- No universe mismatches, coercion problems, or unresolved
   metavariables.

4. **Performance** -- Avoid expensive tactics on large types (e.g., `decide` on
   `Fin 1000`). Watch for timeout-prone proof terms.

5. **Modularity** -- Are new lemmas general enough to be reused? Could any be
   upstreamed to Mathlib?

6. **Documentation** -- Every new `def` and major `theorem` must have a docstring.
   Module files should have a header comment with `## References` citing the
   relevant arXiv paper(s).

7. **Blueprint sync** -- If the PR formalizes a statement from the blueprint,
   add `\lean{LeanDeclName}` and `\leanok` tags to the corresponding
   `blueprint/src/chapter/*.tex` file.

8. **Scaffolding integrity** -- If the PR introduces or modifies scaffolded
   definitions (types, theorem statements with `sorry` proofs), verify that
   the types and API surface align with Mathlib. Scaffolding that uses custom
   types incompatible with Mathlib blocks future proof work. See
   [PROOF_INTEGRITY.md](PROOF_INTEGRITY.md) for details.

### Semantic scaffold checklist (required for core math objects)

For semantic objects such as measurements, submeasurements, distributions,
averaged operators, and packaged theorem outputs, reviewers should additionally
verify:

1. **Impossible states check** -- Does the structure exclude states that are
   impossible under the paper definition?
2. **Derived-field check** -- If a field is mathematically derived
   (e.g. `total = ∑ a, outcome a`), is it either derived on demand or stored
   together with an equality proof (e.g. `sum_eq_total`)?
3. **Invariant bundling check** -- Are core invariants (positivity,
   boundedness/normalization, completeness where applicable) encoded directly
   in the structure or constructor, rather than deferred to downstream lemmas?
4. **Stress-test check** -- Is at least one nontrivial theorem in scope of the
   PR provable/stated against the scaffold without adding ad hoc assumptions?

If any answer is "no", treat the scaffold as unsafe and request a follow-up
before broad theorem layering continues.

---

## 6. Lean Code Style

This project follows Mathlib conventions with project-specific additions.

### Reference guides

- **Documentation style**: [doc.md](doc.md) -- module headers, docstrings,
  LaTeX in comments, sectioning comments.
- **Naming conventions**: [naming.md](naming.md) -- capitalization rules,
  symbol-to-name dictionary, variable conventions.
- **Review guide**: [pr-review.md](pr-review.md) -- detailed examples of
  style, documentation, location, and improvement considerations.

### Project-specific conventions

**Module header**: Every `.lean` file should start with a module docstring that
includes:

```lean
/-!
# Title

Summary of what this file contains.

## Main definitions / statements

- `FooBar` : description
- `fooBar_baz` : description

## References

- [arXiv:XXXX.XXXXX](https://arxiv.org/abs/XXXX.XXXXX) -- Author, *Title*
-/
```

**Docstrings**: Required on every `def`, `structure`, `class`, and significant
`theorem`. Encouraged on supporting lemmas. Use Markdown; refer to Lean
identifiers in backticks.

**Sectioning comments**: Use `/-! ### Section Title -/` to organize long files
into logical sections.

**Variable naming**: Follow the conventions in [naming.md](naming.md). For
this project specifically:
- `q` for alphabet size / finite field order
- `n`, `m` for dimension parameters
- `σ` for strategies
- `P` for projective measurements
- `G` for graphs (hypercube expansion)

---

## 7. CI & Automation

The following workflows run automatically:

| Workflow | Trigger | What it does |
|----------|---------|-------------|
| **Lean CI** (`lean_action_ci.yml`) | Push to `main`, PRs touching `.lean`/`lakefile.toml`/`lean-toolchain` | Runs `lake build` with Mathlib cache |
| **Claude Code Review** (`claude-code-review.yml`) | PR opened/synced/reopened touching `.lean`, `.tex`, `lakefile.toml`, `lean-toolchain` | Automated review for sorrys, Mathlib style, type safety, performance, modularity, documentation |
| **Issue Tracker** (`tracking-issue-sync.yml`) | Issue closed/reopened; PR merged/opened; review submitted | Updates tracking-issue checkboxes (checks on close, unchecks on reopen), posts progress comments on linked issues when PRs merge, scans merged PRs for follow-ups (deferred review feedback, new `sorry` markers, missing blueprint tags), creates follow-up issues with `follow-up` label, adds `all-resolved` when all tasks complete |
| **Blueprint Lint** (`lint-blueprint.yml`) | PRs touching blueprint files | Validates LaTeX blueprint for broken labels and references |
| **Docs & Blueprint Sync** (`docs-blueprint-sync.md`) | Daily (weekdays) + manual dispatch | Detects stale documentation and opens a sync PR if needed |
| **Lean Audit** (`lean-audit.yml`) | On demand | Audits Lean code for style and correctness |
| **PR Cleanup** (`pr-cleanup.yml`) | AI-generated PR opened (`claude/*` or `codex/*` branches) | Normalizes title to `type(scope): desc`, restructures body to PR template, copies labels from linked issue, adds `Addresses #N` reference, comments on the issue |
| **Mathlib Scout** (`mathlib-scout.yml`) | Formalization issue opened/labeled | Scouts Mathlib for relevant lemmas and posts a scouting report |

### What CI checks before merge

- `lake build MIPStarRE` must succeed (no type errors, no broken imports).
- No new `sorry` without explicit justification.
- Blueprint labels must resolve (no broken `\ref` or `\label`).
- Claude Code Review should not flag critical issues (proof correctness,
  type safety).
