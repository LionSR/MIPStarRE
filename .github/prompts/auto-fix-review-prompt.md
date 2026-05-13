The automated code review found issues in this PR. Your task is to fix them.

Instructions:

1. First, use the GitHub MCP tools to read the full PR diff and all review threads yourself. Treat the thread summaries from this workflow as seeds only.
1a. Before changing a paper-facing theorem statement, a blueprint `\leanok`
    link, or a proof-debt record, read `AGENTS.md`, `docs/PROOF_INTEGRITY.md`,
    and `docs/paper-gaps/proof-gap-protocol.tex`. The repair must preserve the
    cited statement in `references/ldt-paper/` up to faithful formal encoding.
2. Use your judgment on whether Mathlib scouting is needed for this fix. For review comments about proofs (`sorry` removal, tactic suggestions, proof restructuring), read PR/issue comments for existing **Mathlib Scouting Reports** and use them to inform your fix. For cosmetic comments (naming, docstrings, style), skip scouting and fix directly.
3. Read each review thread conversation and understand the issue being raised, including follow-up replies that may refine the original comment.
4. Fix each issue in the relevant file at the indicated line.
5. If the review state is `"APPROVED"` with no comments requiring changes, do nothing.
6. Common fixes:

   - For an ordinary proof hole not involving source-statement realignment,
     remove `sorry` and fully close the lemma/theorem with a complete proof.
     Do not replace it with another shortcut.
   - Do NOT close a proof obligation by changing a paper-labelled theorem statement or by
     adding bridge, residual, repair, package, proof-obligation input, hypotheses bundle,
     assumptions bundle, or arbitrary implication hypotheses that are not in the
     cited paper statement.
   - If a paper-labelled theorem was previously weakened by such a statement
     change, restore the paper statement and leave the missing proof as a
     tracked `sorry`, with a TODO, issue or paper-gap citation, and statement
     audit. This is preferable to preserving a theorem with non-paper
     hypotheses.
   - If the proof cannot be completed from the paper hypotheses and the source
     statement is already faithful, stop and post a PR comment identifying the
     missing named lemma, internal obligation, or paper-gap note. Do not
     introduce a new conditional helper, producer, repair bundle, or obligation
     package merely to satisfy the review.
   - Fix naming to match Mathlib conventions.
   - Add missing docstrings where requested.
   - Fix type mismatches or tactic failures.
   - Improve proof structure as suggested.
   - Revise paper-gap notes so that they satisfy `docs/paper-gaps/policy.tex`.
7. If you edit a paper-gap note, preserve it as a self-contained mathematical document:

   - introduce the notation,
   - state the cited assertion,
   - isolate the mathematical obstruction,
   - compare with the blueprint and Lean statement when relevant,
   - give a precise verdict.
   Compile or verify the edited LaTeX document when practical; otherwise explain why that check was not run.
8. Your goal is to fully close incomplete lemmas and theorems when this can be
   done without changing the mathematical statement. Do not use `admit`,
   `native_decide` on non-trivial goals, or other shortcuts. Do not introduce
   untracked `sorry`; a tracked `sorry` is allowed only in the paper-realignment
   case above.
9. Run `lake build` to verify your fixes compile with zero errors and no
   unexpected `sorry`.
10. When your fixes add or complete (remove `sorry` from) theorems, lemmas, or definitions, update the corresponding blueprint entry in `blueprint/src/chapter/` — add `\lean{DeclarationName}` and `\leanok` tags for new results, or add `\leanok` to `\begin{proof}` for newly proven results.
11. Make minimal, targeted fixes. Do not refactor unrelated code.
12. Commit and push your fix to the current branch. Prefix commit messages with `[claude-review-fix]`.
13. After pushing, use the GitHub MCP tools to post a comment on the PR with:

   - a summary of which review items were addressed,
   - for paper-gap note changes, the revised mathematical verdict and cited source passage,
   - if you used or discovered Mathlib lemmas during the fix, include a **Mathlib Audit** section (name, module path, and how it was used).
   Skip this section for trivial fixes that did not involve Mathlib.

Quality bar (same rubric as Claude Code Review — your fix MUST satisfy ALL of these before committing):

- Proof integrity (BLOCKER): no untracked `sorry`, no `admit`, no
  `native_decide` on non-trivial goals, no `unsafeCast`, and no new axioms. A
  tracked `sorry` is allowed only when restoring a paper-aligned theorem
  statement under the paper-realignment policy in docs/PROOF_INTEGRITY.md.
- Proof correctness (BLOCKER): structured proofs, not brute-force `simp`/`omega`/`ring` chains. If a result looks wrong, too strong, or suspiciously general, scout `references/ldt-paper/` first, then `blueprint/src/chapter/`, compare hypotheses/conclusions, and cite the specific source path, label, and line.
- Source-statement fidelity (BLOCKER): declarations named after paper results or
  linked by `\lean{...}` must preserve the cited statement up to faithful formal
  encoding. Do not add load-bearing bridge, residual, repair, package,
  proof-obligation input,
  hypotheses bundle, assumptions bundle, or arbitrary implication hypotheses.
  The only acceptable extra hypotheses are
  boundary conditions genuinely needed to state the same mathematics in Lean,
  such as positivity for a division, nonemptiness, decidability, or a
  field-model instance. Proof-debt objects are not boundary conditions. Existing
  conditional helpers are quarantined proof-debt objects: they must be separately
  named, cite the unresolved source obligation, state a removal plan, and must
  not be treated as the paper theorem. Do not add a new conditional helper as a
  substitute for proving or naming the missing source-faithful lemma.
- Mathlib style: camelCase definitions, snake_case lemmas, minimal imports, no unnecessary `open`, prefer `exact` over `apply` + `rfl`.
- Type safety (BLOCKER): no universe issues, missing `[DecidableEq]`/`[Fintype]` instances, or coercion-chain unification failures.
- Performance: avoid `decide` on large types, unbounded `simp` sets, deep `rw` chains, `norm_num` on symbolic expressions. Prefer `omega`, `positivity`, explicit `calc`.
- Modularity: keep new lemmas general; do not duplicate existing Mathlib results.
- Documentation: new definitions and key theorems get docstrings that explain mathematical meaning, not Lean syntax.
- Blueprint sync: when adding or completing (removing `sorry` from) theorems/lemmas/defs, update the corresponding `blueprint/src/chapter/` entry — add `\lean{DeclarationName}` and `\leanok` tags for new results, or add `\leanok` to `\begin{proof}` for newly proven results.
- Paper-gap notes: changed notes under `docs/paper-gaps/` must follow `docs/paper-gaps/policy.tex` by introducing notation, stating the cited assertion, isolating the mathematical obstruction, comparing with blueprint and Lean statements when relevant, and giving a precise verdict for third-party mathematical readers.

If you cannot satisfy a BLOCKER category, STOP and post a PR comment explaining the obstacle instead of pushing a half-fix.
