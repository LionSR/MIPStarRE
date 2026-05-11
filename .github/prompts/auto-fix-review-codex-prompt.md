The automated code review found issues in this PR. Your task is to fix them.

Instructions:
0. First, use the PR number and repository from the runtime context to read the full PR diff and all review threads yourself. The thread summaries above are seeds; read the actual threads for complete context.
1. Use your judgment on whether Mathlib scouting is needed. For proof-level review comments, read PR/issue comments for existing **Mathlib Scouting Reports**. For cosmetic comments (naming, docstrings, style), skip scouting.
2. Read each review thread conversation and understand the issue raised, including any follow-up replies.
3. Fix each issue in the relevant file at the indicated line.
4. If the review state is "APPROVED" with no comments requiring changes, do nothing.
5. Common fixes:
   - Remove `sorry` and fully close the lemma/theorem.
   - Do not close a proof obligation by changing a paper-labelled theorem statement or
     adding bridge, residual, repair, producer, package, or arbitrary implication
     hypotheses absent from the cited statement.
   - If the proof cannot be completed without such a change, stop and post a PR comment
     naming the missing lemma or producer theorem instead of pushing a weakened paper
     theorem.
   - Fix naming to match Mathlib conventions.
   - Add missing docstrings where requested.
   - Fix type mismatches or tactic failures.
   - Improve proof structure as suggested.
   - Revise paper-gap notes so that they satisfy `docs/paper-gaps/policy.tex`.
5a. If you edit a paper-gap note, preserve it as a self-contained mathematical document:
   introduce the notation, state the cited assertion, isolate the mathematical obstruction,
   compare with the blueprint and Lean statement when relevant, and give a precise verdict.
   Compile or otherwise verify the edited LaTeX document when this is practical, and
   otherwise state why that check was not run.
6. Your goal is to fully close every incomplete lemma/theorem. Do not use `sorry`, `admit`, `native_decide` on non-trivial goals, or other shortcuts.
7. Run `lake build` to verify your fixes compile with zero errors and zero `sorry`s.
8. When fixes add or complete (remove sorry from) theorems, update the corresponding blueprint entry in `blueprint/src/chapter/`.
9. Make minimal, targeted fixes. Do not refactor unrelated code.
10. Commit and push your fix to the current branch. Prefix commit messages with `[codex-review-fix]`.
11. After pushing, use the PR number from the runtime context to post a summary of which review items were addressed. For paper-gap note changes, state the revised mathematical verdict and the cited source passage that was checked.

Quality bar (your fix MUST satisfy ALL of these before committing):
- Proof integrity (BLOCKER): no sorry, admit, native_decide on non-trivial goals, unsafeCast, or new axioms. See docs/PROOF_INTEGRITY.md.
- Proof correctness (BLOCKER): structured proofs, not brute-force tactic chains. If a result looks wrong, scout `references/ldt-paper/` first, then `blueprint/src/chapter/`, and cite the specific source path, label, and line.
- Source-statement fidelity (BLOCKER): declarations named after paper results or linked by `\lean{...}` must preserve the cited statement up to faithful formal encoding. Do not add load-bearing bridge, residual, repair, producer, package, or arbitrary implication hypotheses unless they occur in the cited statement or are a documented Lean boundary condition needed to state the mathematics. Existing conditional helpers must be separately named and must not be treated as the paper theorem.
- Mathlib style: camelCase defs, snake_case lemmas, minimal imports, no unnecessary opens.
- Type safety (BLOCKER): no universe issues, missing instances, or coercion failures.
- Performance: avoid `decide` on large types, unbounded `simp`, deep `rw` chains.
- Modularity: keep new lemmas general; do not duplicate Mathlib results.
- Documentation: new definitions and key theorems get docstrings explaining mathematical meaning.
- Blueprint sync: update blueprint entries when proofs are added/completed.
- Paper-gap notes: changed notes under docs/paper-gaps/ must follow `docs/paper-gaps/policy.tex`; they should introduce notation, state the cited assertion, isolate the mathematical obstruction, compare with the blueprint and Lean statement when relevant, and give a precise verdict for third-party mathematical readers.
If you cannot satisfy a BLOCKER category, STOP and post a PR comment explaining the obstacle instead of pushing a half-fix.
