Use `gh pr diff <PR_NUMBER>` to see the changes.

Focus your review on the categories below. Each category has a severity level
that determines whether the PR can be approved with outstanding issues.

**Severity levels:**
- 🔴 **Blocker** — must be fixed before merge. Request changes if any are found.
- 🟡 **Requires changes** — must be addressed before approval. These are NOT nits.
  Do NOT approve the PR while issues in this category remain unresolved.
- ℹ️ **Advisory** — flag for awareness, acceptable with justification.

---

1. 🔴 **Proof integrity**: Read `docs/PROOF_INTEGRITY.md` for the complete list of proof
   integrity rules. Flag **blockers** as must-fix issues that should block merge. Flag
   **warnings** as advisory — note them but acknowledge they may be acceptable with justification.
   For each finding, explain WHY it is problematic and suggest the correct alternative.
2. 🔴 **Proof correctness**: Are proof terms well-structured? Do tactic proofs follow a logical
   strategy, or are they brute-forced with `simp` / `omega` / `ring` chains? Are `calc` blocks
   and `conv` rewrites correctly chained? Are hypotheses used or dangling?
   If a mathematical result looks wrong, too strong, or suspiciously general, **scout** the
   source hierarchy: first `references/ldt-paper/`, then the corresponding blueprint material
   in `blueprint/src/chapter/`. Read the relevant sections, compare hypotheses and conclusions,
   and cite the specific source path, label, and line when flagging a discrepancy.
3. 🔴 **Source-statement fidelity**: For every changed theorem, lemma, or definition that is
   named after a paper result, linked from the blueprint by `\lean{...}`, or described as a
   formalization of a cited result, compare its public Lean statement with the corresponding
   statement in `references/ldt-paper/`. Flag any added load-bearing hypothesis, weakened
   conclusion, changed error parameter, or altered quantifier structure. In particular,
   bridge, residual, repair, package, proof-obligation input, hypotheses bundle,
   assumptions bundle, or
   arbitrary implication hypotheses are blockers unless they are explicitly part of the
   paper statement or are documented Lean boundary conditions needed to state the
   mathematics, such as positivity, nonemptiness, decidability, or field-model hypotheses.
   Proof-debt bundles are not boundary conditions.
   If such data are still needed, the paper theorem must remain source-faithful and the
   missing proof should remain as a tracked `sorry`, a source-faithful lemma target to be
   proved from the same hypotheses, or a paper-gap report.  Do not accept a conditional
   helper as the default repair path.
   Existing conditional helpers must have names that make the conditional nature clear,
   cite the unresolved source obligation, state a removal plan, and must not be treated as
   the paper theorem or advertised by `\leanok`.
   A newly introduced conditional helper, proof-debt bundle, producer, or obligation
   package is itself a blocker unless the PR is explicitly a paper-realignment change,
   the new object preserves useful proof content from an already drifting statement, and
   the paper-facing theorem remains source-faithful.
4. 🟡 **Mathlib style**: Does the code follow Mathlib conventions? Check naming (`camelCase` for
   defs, `snake_case` for lemmas), tactic style (prefer `exact` over `apply` + `rfl` when
   equivalent), import hygiene (no unnecessary `open`s, minimal imports), and lemma placement.
   Style violations are NOT nits — they must be fixed before approval.
5. 🔴 **Type safety**: Any type mismatches, universe issues, or coercion problems? Check for
   universe polymorphism issues, missing `[DecidableEq]` or `[Fintype]` instances, and
   coercion chains that may cause unification failures.
6. 🟡 **Performance**: Will any proofs cause timeouts? Watch for `decide` on large types,
   `simp` with unbounded lemma sets, deep `rw` chains, and `norm_num` on symbolic expressions.
   Suggest alternatives like `omega`, `positivity`, or explicit `calc` steps.
   Performance issues that will likely cause timeouts must be fixed before approval.
7. 🟡 **Modularity & duplication**: Are new lemmas general enough? Could any be upstreamed to
   Mathlib? Are there lemmas that are overly specialized to the local context but could be
   stated more generally? Is the file structure consistent with the existing module hierarchy?
   Flag duplicated logic or lemmas that restate existing Mathlib results.
   Modularity and duplication issues must be fixed before approval.
8. 🟡 **Documentation**: Do new definitions and key theorems have docstrings? Are module-level
   doc comments present for new files? Do docstrings explain mathematical meaning, not just
   Lean syntax? Missing documentation must be added before approval.
9. 🟡 **Blueprint coverage for changed declarations**: If the PR has the label
   `enforce-blueprint-coverage` and changes a public paper-facing `def`,
   `theorem`, or `lemma` under `MIPStarRE/`, the corresponding blueprint item
   should carry the appropriate `\lean{...}` tag. You may run
   `python3 scripts/blueprint_lean_sync.py --root . --warn-missing-blueprint
   --fail-on-missing-blueprint --diff-base origin/<base-ref> --changed-files <files>`
   when the changed-file list is clear. On such labelled PRs, a `Blueprint
   update suggested` CI annotation is a requires-changes finding unless the
   declaration is genuinely only an internal helper and the PR explains why it
   should remain outside the blueprint. On unlabelled PRs, mention this only as
   advisory context.
10. 🟡 **Paper-gap notes**: When the PR changes files under `docs/paper-gaps/`, read
   `docs/paper-gaps/policy.tex` before reviewing the changed note. Check that the note is a
   self-contained mathematical account: it introduces its notation, states the cited assertion,
   isolates the calculation or logical obstruction, compares the cited source with the
   blueprint and Lean statement when relevant, and gives a precise verdict. If the note cites
   a paper, blueprint, or project source file, inspect the cited passage and flag unsupported,
   overstated, or ambiguous claims. Paper-gap notes must be written for third-party
   mathematical readers, not as issue logs or implementation diaries.

**Out of scope** (handled by the dedicated `Blueprint Sync & Prose Review` workflow — do
NOT comment on these here, to avoid duplicate review threads):
- General blueprint ↔ Lean sync drift outside the changed Lean declarations
  reviewed above (`\leanok` / `\uses{...}` tags, `\leanok` on proofs, stale
  blueprint entries).
- Prose quality / banned AI-software language in blueprint `.tex` and Lean docstrings.
  This exclusion does not apply to paper-gap notes, which are reviewed here against
  `docs/paper-gaps/policy.tex`.

---

**Review verdict rules:**
- If ANY 🔴 or 🟡 issues are found, submit the review as **REQUEST_CHANGES**.
  Do NOT approve while these issues remain unresolved.
- Only **APPROVE** when all 🔴 and 🟡 issues have been addressed.
- ℹ️ advisory items alone do not block approval.
- Do NOT label issues as "Nit" or "non-blocking" if they fall under a 🟡 or 🔴 category.
  Use clear language: "This must be fixed before merge" or "Requires changes".

For each issue found, post an inline comment on the relevant line using the GitHub CLI.
At the end, post a summary comment on the PR with your overall assessment.
In that assessment, describe mathematical concerns by naming the theorem, lemma,
definition, proof obligation, or paper-gap assertion. When you flag a paper/blueprint
discrepancy, cite the source path, line number, label, and a short quotation or precise
paraphrase. State the theorem, lemma, definition, or proof obligation directly.

**Reading existing feedback:**
Before posting new comments, read ALL existing feedback on this PR using the GitHub MCP tools:
1. Read **inline review threads** via `get_review_comments` — these are code-level comments from previous review cycles.
2. Read **PR conversation comments** via `get_comments` — bots and humans often post feedback, summaries,
   and discussion directly on the PR thread (not as inline review comments). These are equally important.
This includes threads from previous review cycles and any replies from @claude, other bots, or human reviewers.
Use this context to:
- Avoid re-raising issues that have already been discussed, acknowledged, or fixed in either location.
- Understand any ongoing conversation or decisions made in earlier threads or PR comments.

**Resolving previous review comments:**
When this review is triggered by a `synchronize` event (new push to the PR):
1. First, fetch all review threads **with their GraphQL node IDs** using `gh api graphql`.
   The `get_review_comments` MCP method does not return thread IDs, so you MUST use GraphQL.
2. For each unresolved thread where the author login starts with `claude`, `copilot-pull-request-reviewer`, or `chatgpt-codex-connector`
   (note: GitHub may append `[bot]` to app logins — match the base name as a prefix to handle both forms),
   check whether the new changes address the issue raised in that comment.
   Do NOT resolve threads from `cursor`/Bugbot — that bot manages its own thread resolution.
3. If a previous comment has been addressed by the new commits, resolve it using `mcp__github__resolve_review_thread` with the GraphQL thread `id`.
4. If a previous comment is still relevant (the issue was NOT fixed), leave it unresolved.
5. Only resolve bot threads — never resolve threads authored by human reviewers.
   This prevents stale bot comments from accumulating across review cycles.

**Example: How to fetch thread IDs and resolve them**

Step 1 — Query thread IDs via GraphQL (returns up to 100 threads; see Step 3 for pagination):
```bash
gh api graphql -f query='
{
  repository(owner: "<REPOSITORY_OWNER>", name: "<REPOSITORY_NAME>") {
    pullRequest(number: <PR_NUMBER>) {
      reviewThreads(first: 100) {
        nodes {
          id
          isResolved
          isOutdated
          comments(first: 1) {
            nodes {
              author { login }
              body
            }
          }
        }
        pageInfo { hasNextPage endCursor }
      }
    }
  }
}'
```
This returns thread objects with `id` fields like `"PRRT_kwDON..."`. Use pagination if `hasNextPage` is true.

Step 2 — For each unresolved bot thread whose issue is now fixed, resolve it:
```
mcp__github__resolve_review_thread(threadId: "PRRT_kwDON...")
```

Step 3 — If there are more than 100 threads, paginate:
```bash
gh api graphql -f query='
{
  repository(owner: "<REPOSITORY_OWNER>", name: "<REPOSITORY_NAME>") {
    pullRequest(number: <PR_NUMBER>) {
      reviewThreads(first: 100, after: "CURSOR_FROM_PREVIOUS_PAGE") {
        nodes { id isResolved isOutdated comments(first: 1) { nodes { author { login } body } } }
        pageInfo { hasNextPage endCursor }
      }
    }
  }
}'
```
