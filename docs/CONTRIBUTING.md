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
| `style`    | Formatting, naming, or docstring cleanup only     |
| `ci`       | CI/CD workflow changes                            |
| `chore`    | Dependency bumps, linting, toolchain updates      |

**Scope** is a shortened module path: `LDT/SelfImprovement`, `Quantum`, `blueprint`,
`LDT/Pasting`, etc. Omit the `MIPStarRE/` prefix.

Examples:
- `feat(LDT/SelfImprovement): add self-improvement induction step`
- `fix(blueprint): resolve broken labels in chapter 7`
- `refactor(LDT): extract shared preliminaries into Basic module`

### Body template

Every PR body must contain three sections. For mathematical changes, the body
should be readable by someone who has not seen the associated conversation:
cite the paper or blueprint location, give the theorem label when one exists,
and state the mathematical assertion precisely.

```markdown
### Motivation
- Why this mathematical or documentation change is needed.
- Cite the issue and, when applicable, the paper/blueprint file, line, and label.

### Description
- State precisely what changed: definitions introduced, lemmas/theorems proved,
  blueprint labels updated, and any deliberate difference from the paper statement.

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
| **Formalization Issue** | A specific theorem, definition, construction, or lemma to formalize |
| **Bug Report** | Broken proof, type error, sorry regression, statement mismatch, or CI failure |
| **Tracking Issue** | Umbrella issue for a chapter, theorem family, or proof stage, using GitHub sub-issues |

### Formalization issues

Use a descriptive, **bracket-free** title that names the mathematical content:

```
Chapter 9 — finish the sandwich-chain corollaries in BridgeLemmas
```

Avoid prefixes like `[Chapter 9] ...`: bot-generated branch names inherit those
characters, and `]` breaks part of the PR automation stack. See
[`pr_review_management.md`](pr_review_management.md) for the rationale.

For formalization issues, usually start with `formalization` + `2009.12982`,
then add the most specific live chapter or theorem-family labels that apply (for
example `ldt-basic`, `preliminaries`, `commutativity`, `pasting`,
`main-induction`, `proof`, `proof-infra`, `statement-fix`,
`sorry-elimination`, `mismatch`, `follow-up`, `blueprint`, or
`blueprint-sync`). Documentation-only or tooling issues should use
`documentation`, `ci`, `cleanup`, and/or `refactor` instead of
`formalization`.

Every formalization issue must give enough mathematical source information to
make the issue self-contained:

- Paper source: a path under `references/ldt-paper/`, line number, theorem or
  equation label when available, and a short quotation or precise paraphrase.
- Blueprint source: a path under `blueprint/src/chapter/`, line number, label,
  and the matching `\lean{...}` status when relevant.
- Lean target: the expected declaration name and file path, if already known.
- Dependencies: theorem labels, existing Lean declarations, and GitHub
  sub-issues that must precede the statement.

For issues or PRs touching a source-labelled theorem, include a statement
integrity check.  List the paper assumptions, the Lean assumptions, the paper
conclusion, the Lean conclusion, and a verdict: exact, faithful boundary
hypotheses, extra assumptions, weakened conclusion, or strengthened conclusion.
Changing a Lean theorem away from the statement in `references/ldt-paper/` is
strongly discouraged unless it is forced by faithful formal encoding or by a
documented mathematical necessity.
Faithful boundary hypotheses include formal domain data such as nonemptiness,
decidability, field-model instances, positivity of parameters, or denominator
nonvanishing when these are implicit in the source.  Extra bridge, residual,
repair, producer, or package assumptions are not boundary hypotheses; they make
the Lean result conditional.  Do not attach them to a paper-facing theorem.
If they are unavoidable while preserving downstream proof work, quarantine them
in a separately named conditional helper, cite the paper-gap note or tracking
issue, name the producer theorem that must remove them, and keep the source
theorem statement visible even if its proof contains a tracked `sorry`.

Do not describe a mathematical issue only as a "cleanup", "follow-up", "blocked
item", or "Phase N" problem. State the theorem, lemma, definition, or mismatch
in mathematical terms first; repository labels and scheduling details come
afterward.

### Multi-part work

For a chapter or theorem family spanning several PRs, use a title pattern that
names the mathematical region and create an umbrella **tracking issue**:

```
Chapter 7 1/5: Self-improvement hypotheses
Chapter 7 2/5: Self-improvement conclusion
...
```

Attach tracked issues as **GitHub sub-issues** of the umbrella issue so GitHub
shows native progress, relationship navigation, and "Tracked by #N" links. The
issue body can keep a short human-readable index, but markdown checkboxes and
retired fenced tasklist blocks do not create native sub-issue relationships:

```markdown
### Sub-issues to attach
- #101
- #102
- #103
```

Use the issue sidebar's **Add sub-issue** control, or the REST endpoint
`POST /repos/{owner}/{repo}/issues/{issue_number}/sub_issues`, to create the
actual relationship. Put descriptions in the sub-issue titles or in prose above
the index.

### Tracking issues

Use the **Tracking Issue** template (`.github/ISSUE_TEMPLATE/tracking-issue.yml`).
Label with `tracking`; add `chapter-tracking` for the long-lived chapter
overview trackers. A tracking issue should begin by naming the mathematical
objective and citing the paper or blueprint labels that the child issues cover.
The `tracking-issue-sync` workflow will automatically:

- Rely on GitHub's native sub-issue progress instead of editing body checkboxes.
- Post progress comments on linked issues when PRs merge.
- Suggest or create `follow-up` issues for genuine deferred work called out by merged PRs.

The repository does not currently use a live `all-resolved` label, so do not
add one manually.

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

### Stale-issue audits

Issues that cite specific `sorry` sites, file/line locations, or declaration
names drift out of date as `main` moves. Keep those citations precise rather
than replacing them with vague prose: update paths, line numbers, theorem labels,
and short source paraphrases when the source moves. Before starting a new
proof-closing round (or periodically as maintenance), run the audit script to
list open issues whose citations no longer resolve:

```bash
gh issue list --repo LionSR/MIPStarRE --state open --limit 500 \
  --json number,title,body,url,labels > /tmp/open-issues.json
python3 scripts/audit_stale_issues.py --issues /tmp/open-issues.json
```

The tool is report-only. Human review decides which flags warrant closing
the issue, updating its body, or dismissing as a false positive. A weekly
read-only GitHub Actions wrapper runs the same export-and-audit sequence and
uploads an artifact only when citations are flagged. See
[`docs/stale_issue_audit.md`](stale_issue_audit.md) for the full workflow.

---

## 3. Commit Messages

- Use **imperative mood** in the subject line ("Add", not "Added").
- Keep the subject under 72 characters.
- When squash-merging a PR, the commit message should match the PR title format.
- Reference issue numbers where applicable (`(#N)` suffix or `Addresses #N` in body).

---

## 4. Label Taxonomy

This section mirrors the labels that currently exist in the GitHub repository.
If this file and `gh label list` diverge, treat GitHub as the source of truth
and update this guide in the same PR. Most formalization issues combine
`formalization` + `2009.12982` with one or more chapter or theorem-family labels.
Documentation- or tooling-only issues usually skip the paper label. Do **not**
apply legacy labels such as `self-improvement`, `expansion-graph`,
`quantum-foundations`, or `automation`: those names are not part of the live
label set.

### Core work-type labels

| Label            | Description                                                |
|------------------|------------------------------------------------------------|
| `formalization`  | Lean formalization of a mathematical statement             |
| `documentation`  | Documentation-only work                                    |
| `infrastructure` | Foundational definitions, shared APIs, or supporting layers |
| `cleanup`        | Small cleanup, consistency, or style fix                   |
| `refactor`       | Structural change without intended behavior change         |
| `ci`             | CI/CD workflow or repository automation change             |

### Chapter / theorem-family labels

| Label               | Description                                                     |
|---------------------|-----------------------------------------------------------------|
| `ldt-basic`         | Early LDT definitions and low-degree-test scaffolding           |
| `preliminaries`     | Preliminaries chapter / section work                            |
| `commutativity`     | Commutativity chapters and related lemmas                       |
| `pasting`           | Pasting chapter and downstream chains                           |
| `main-induction`    | Main induction step                                             |
| `proof`             | Issue is primarily about proving an existing result             |
| `proof-infra`       | Intermediate lemmas or definitions that mainly support proofs   |
| `sorry-elimination` | Explicitly aimed at discharging remaining `sorry` sites         |
| `statement-fix`     | Paper-to-Lean statement correction / weakening / realignment    |
| `mismatch`          | Explicit paper-code mismatch audit or repair                    |
| `blueprint`         | Blueprint authoring or blueprint-expansion work                 |
| `blueprint-sync`    | Blueprint ↔ Lean synchronization issue                          |

### Paper labels

| Label        | Description                                          |
|--------------|------------------------------------------------------|
| `2009.12982` | The main LDT paper tracked in this repository        |

### Tracking / follow-up labels

| Label              | Description                                           |
|--------------------|-------------------------------------------------------|
| `tracking`         | Umbrella issue using GitHub sub-issues                 |
| `chapter-tracking` | Long-lived chapter progress tracker                   |
| `follow-up`        | A mathematical obligation split out of a PR            |
| `campaign-5`       | Historical label for the session-5 campaign issues    |

### Automation / operational labels

| Label             | Description                                           |
|-------------------|-------------------------------------------------------|
| `auto-fix-claude` | Automation-managed issue queue for Claude follow-ups  |
| `codex`           | Automation-managed issue or PR bookkeeping            |
| `standup`         | Daily mathematical progress issues                    |

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

3. **Paper terminology** -- Public Lean names, module docstrings, declaration
   docstrings, and documentation-visible comments should use terminology from
   the paper and blueprint, not implementation history. See
   [mathematical_language.md](mathematical_language.md) for the project-local
   language rule for Lean documentation and public names. Reviewers should flag
   names that encode historical formalization status rather than mathematical
   content. When an old public identifier cannot be renamed in the current PR,
   record the required migration in the issue, PR description, or an audit file
   under [audits/](../audits/).
   New and substantively updated audit files should follow the term norm and
   format in
   [audits/2026-04-29_audit-document-format.md](../audits/2026-04-29_audit-document-format.md).
   Do not add an empty pass-through abbreviation merely to introduce a second
   public name.
   Review-fix PRs must read the relevant audit files under [audits/](../audits/)
   before changing names or prose. If an audit marks a naming migration or
   historical-formalization term as in scope for the fix, addressing it or
   explicitly updating the audit trail is a merge blocker.

4. **Linter hygiene** -- Linter-warning cleanup must fix warnings, not mask
   them with broad `set_option linter.<name> false` blocks. See
   [style.md](style.md#linter-warnings) for the project rule and the narrow
   exception policy.

5. **Type safety** -- No universe mismatches, coercion problems, or unresolved
   metavariables.

6. **Performance** -- Avoid expensive tactics on large types (e.g., `decide` on
   `Fin 1000`). Watch for timeout-prone proof terms.

7. **Modularity** -- Are new lemmas general enough to be reused? Could any be
   upstreamed to Mathlib?

8. **Documentation** -- Every new `def` and major `theorem` must have a docstring.
   Module files should have a header comment with `## References` citing the
   relevant arXiv paper(s).

9. **Blueprint sync and paper origin** -- If the PR formalizes a statement
   from the blueprint, add `\lean{LeanDeclName}` and `\leanok` tags to the
   corresponding `blueprint/src/chapter/*.tex` file. If the PR adds a public
   auxiliary lemma that is not a named statement in the original paper, record
   that explicitly: the Lean docstring should call it a formalization-only
   auxiliary lemma and the blueprint should either omit it as private/internal
   infrastructure or include it as a clearly subordinate support node connected
   by `\uses{...}`. See
   [blueprint_style_guide.md](blueprint_style_guide.md#recording-formalization-only-lemmas).
   PR descriptions and follow-up issues should cite the corresponding paper or
   blueprint path, line, label, and a short quotation or precise paraphrase.
   Reviewers should also check for early drift from the source: new hypotheses,
   weakened conclusions, changed quantifier order, altered error parameters,
   or renamed data packages that turn a paper theorem into a conditional
   theorem.  If such drift appears, request a statement integrity audit before
   reviewing the proof.  A bridge or residual hypothesis should be treated as
   proof debt to remove, not as evidence that the paper statement has been
   formalized.

10. **Scaffolding integrity** -- If the PR introduces or modifies scaffolded
   definitions (types, theorem statements with `sorry` proofs), verify that
   the types and API surface align with Mathlib. Scaffolding that uses custom
   types incompatible with Mathlib blocks future proof work. See
   [PROOF_INTEGRITY.md](PROOF_INTEGRITY.md) for details.

11. **Proof-evasion anti-patterns** -- Review against
   [anti_patterns.md](anti_patterns.md), which catalogues subtler failure
   modes that pass the `PROOF_INTEGRITY.md` blocker checks but still fail
   to prove the claimed mathematics: conclusion-shaped hypotheses (A1),
   `:= rfl` definitional sleight-of-hand (A2), zero-fallback branches
   hiding preconditions (A3), trivial default witnesses (A4),
   Mathlib-bypass castles (A5), and external `*Statement` smuggles (A6).
   Use the reviewer checklist at the end of that file.

12. **Proof frontier integrity** -- If the PR introduces or threads structure
   fields such as `*Input`, `*Residual`, `*BridgeInputs`, `*Witness`,
   `*Statement`, `*Conclusion`, or `*Package`, review it against
   [proof_frontier_review.md](proof_frontier_review.md). A PR that only
   repackages an assumption should not be described as proving the corresponding
   paper step; it must name the missing producer theorem or link the native
   sub-issue that tracks it.  For source-labelled theorems, the preferred repair
   is to extract any usable proof content into source-faithful lemmas and
   restore the paper-aligned statement, even if the remaining proof is a tracked
   `sorry` during the cleanup.

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

Mathlib-derived references:

- **Documentation style**: [doc.md](doc.md) -- module headers, docstrings,
  LaTeX in comments, sectioning comments.
- **Naming conventions**: [naming.md](naming.md) -- capitalization rules,
  symbol-to-name dictionary, variable conventions.
- **Review guide**: [pr-review.md](pr-review.md) -- detailed examples of
  style, documentation, location, and improvement considerations.

MIPStarRE-local references:

- **Mathematical language**: [mathematical_language.md](mathematical_language.md)
  -- project-local terminology rules for Lean names and documentation.
- **Proof integrity**: [PROOF_INTEGRITY.md](PROOF_INTEGRITY.md) -- blocker and
  warning patterns for proof correctness.
- **Blueprint style**: [blueprint_style_guide.md](blueprint_style_guide.md) --
  notation and section conventions for the active blueprint.

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
| **Claude Code Review** (`claude-code-review.yml`) | PR opened/synced/ready-for-review/reopened touching Lean files, blueprint `.tex` files, `docs/paper-gaps/`, `lakefile.toml`, or `lean-toolchain` | Automated review for proof integrity, Mathlib style, type safety, performance, modularity, mathematical exposition, and documentation |
| **Issue Tracker** (`tracking-issue-sync.yml`) | Issue closed/reopened; PR merged/opened | Uses native sub-issue progress for tracking status, posts progress comments on linked issues when PRs merge, scans merged PRs for genuine deferred mathematical obligations, and creates `follow-up` issues when needed |
| **Blueprint Lint** (`lint-blueprint.yml`) | PRs touching blueprint files | Validates LaTeX blueprint for broken labels and references |
| **Docs & Blueprint Sync** (`docs-blueprint-sync.md`) | Daily (weekdays) + manual dispatch | Detects stale documentation and opens a sync PR if needed |
| **README Freshness Audit** (`readme-freshness-audit.yml`) | Weekly + manual dispatch | Report-only audit for README local paths, LDT submodule count, and hard-coded Lean/Mathlib versions |
| **Lean Audit** (`lean-audit.yml`) | On demand | Audits Lean code for style and correctness |
| **PR Mathematical Description** (`pr-cleanup.yml`) | PR opened from `claude/*` or `codex/*` branches | Normalizes title to `type(scope): desc`, rewrites the PR body as a self-contained mathematical note, preserves source citations from the linked issue, copies labels, adds `Addresses #N`, and comments on the issue |
| **Mathlib Scout** (`mathlib-scout.yml`) | Formalization issue opened/labeled | Scouts Mathlib for relevant lemmas and posts a scouting report |

### What CI checks before merge

- `lake build MIPStarRE` must succeed (no type errors, no broken imports).
- No new `sorry` without explicit justification.
- Blueprint labels must resolve (no broken `\ref` or `\label`).
- Claude Code Review should not flag critical issues (proof correctness,
  type safety).
