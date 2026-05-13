A user mentioned @chatgpt on this repository.

Instructions:
1. Read the full context with `gh`: triggering comment/review/issue body, the surrounding thread, the PR diff if applicable, and any relevant source files.
   - PR comment: `gh pr view <num> --json ...` and `gh api repos/<repo>/pulls/<num>/comments`.
   - Issue comment / issue: `gh issue view <num> --json ...`.
   - Review: read all threads via `gh api repos/<repo>/pulls/<num>/reviews`.
2. Decide whether the request is a question (reply only) or a code change (edit + commit + reply).
2a. Before changing a paper-facing theorem statement, a blueprint `\leanok`
    link, or a proof-debt record, read `AGENTS.md`, `docs/PROOF_INTEGRITY.md`,
    and `docs/paper-gaps/proof-gap-protocol.tex`. The repair must preserve the
    cited statement in `references/ldt-paper/` up to faithful formal encoding.
3. Use your judgment on whether Mathlib scouting is needed. Warranted for new proofs, closing sorrys, or choosing proof strategies; unnecessary for cosmetic fixes, docstrings, imports, or renaming. When scouting, first read existing **Mathlib Scouting Reports** in PR/issue comments, then scout yourself with `exact?`, `apply?`, `rw?`, `simp?`, and by grepping `.lake/packages/mathlib/Mathlib/`. If asked explicitly to scout, post a fresh **Mathlib Scouting Report** with sections: Relevant Mathlib definitions, Relevant Mathlib lemmas/theorems, Relevant MIPStarRE definitions, Suggested approach, Gaps to fill.
4. For code changes:
   - On a PR: check out the PR's head branch (`gh pr checkout <num>`), edit, run `lake build` to verify zero errors and no unexpected `sorry`, commit with prefix `[codex]`, push.
   - On an issue: create a new branch `codex/issue-<NUMBER>-<short-description>` from main, edit, build, commit with prefix `[codex]`, push.
5. Reply via `gh pr comment <num>` or `gh issue comment <num>` summarizing what you did or answering the question. For review-thread triggers, reply directly to the triggering thread.
6. Do NOT resolve review threads — leave resolution to humans or the automated review workflow.

Quality bar (your work MUST satisfy ALL of these before committing):
- Proof integrity (BLOCKER): no untracked `sorry`, no `admit`, no
  `native_decide` on non-trivial goals, no `unsafeCast`, and no new axioms. A
  tracked `sorry` is allowed only when restoring a paper-aligned theorem
  statement under the paper-realignment policy in docs/PROOF_INTEGRITY.md.
- Proof correctness (BLOCKER): structured proofs, not brute-force `simp`/`omega`/`ring` chains. If a result looks wrong, too strong, or suspiciously general, scout `references/ldt-paper/` first, then `blueprint/src/chapter/`, compare hypotheses/conclusions, and cite the specific source path, label, and line.
- Source-statement fidelity (BLOCKER): paper-labelled or blueprint-linked
  declarations must preserve the cited statement up to faithful formal encoding.
  Do not add load-bearing bridge, residual, repair, package, proof-obligation input,
  hypotheses bundle, assumptions bundle, or arbitrary implication hypotheses.
  The only acceptable extra hypotheses are
  boundary conditions genuinely needed to state the same mathematics in Lean,
  such as positivity for a division, nonemptiness, decidability, or a
  field-model instance. Proof-debt objects are not boundary conditions. If a
  proof needs such data, report the missing named lemma or internal obligation
  instead of changing the paper theorem.
- Mathlib style: camelCase defs, snake_case lemmas, minimal imports, no unnecessary opens, prefer `exact` over `apply` + `rfl`.
- Type safety (BLOCKER): no universe issues, missing `[DecidableEq]`/`[Fintype]` instances, or coercion-chain unification failures.
- Performance: avoid `decide` on large types, unbounded `simp` sets, deep `rw` chains, `norm_num` on symbolic expressions.
- Modularity: keep new lemmas general; do not duplicate existing Mathlib results.
- Documentation: new definitions and key theorems get docstrings that explain mathematical meaning, not Lean syntax.
- Blueprint sync: when adding or completing (removing `sorry` from) theorems/lemmas/defs, update the corresponding `blueprint/src/chapter/` entry — add `\lean{DeclarationName}` and `\leanok` tags for new results, or add `\leanok` to `\begin{proof}` for newly proven results.
If you cannot satisfy a BLOCKER category, STOP and post a comment explaining the obstacle instead of pushing a half-fix.

Before changing theorem statements, first compare source-labelled statements with
`references/ldt-paper/`.  Do not add bridge, residual, repair, package,
proof-obligation input, hypotheses bundle, assumptions bundle, or arbitrary
hypothesis inputs to a paper-labelled theorem in order to make the proof close.
If such data seem necessary and the current theorem statement has already
drifted away from the paper, restore the paper statement and leave the missing
proof as a tracked `sorry` with a TODO and issue or paper-gap citation. If the
statement is already faithful, report the missing named lemma or paper-gap note.
Do not introduce a conditional helper or proof-debt bundle as a substitute for
the source proof. Existing conditional helpers may be edited only to reduce
proof debt or preserve already separated proof content, and must remain off the
paper theorem's `\leanok` path. Do not leave unrelated new sorrys.
