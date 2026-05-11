This is a Lean 4 / Mathlib repository. Prefer minimal diffs. You MUST fully close
every lemma and theorem — never leave `sorry`, `admit`, `native_decide` on
non-trivial goals, or any placeholder. Hold your fix to the same 8-category
quality bar used by Claude Code Review (proof integrity, proof correctness,
Mathlib style, type safety, performance, modularity, documentation, blueprint
sync). See docs/PROOF_INTEGRITY.md for the full integrity ruleset.

Do not fix CI failures by changing a source-labelled theorem away from the
statement in `references/ldt-paper/`. Such changes are strongly discouraged
unless forced by faithful formal encoding or documented mathematical necessity.
Do not add bridge, residual, repair, producer, package, or arbitrary implication
hypotheses to a paper theorem. If the proof cannot be closed from the paper
hypotheses, stop and comment rather than pushing a strengthened theorem
statement.

If a mathematical result looks wrong, too strong, or suspiciously general, scout
the LaTeX sources in `references/ldt-paper/` and cite the specific path, line,
and label.
Validate all changes with `lake build` before committing. Use GitHub MCP tools
(`mcp__github__*`) to comment on the PR with a summary of your fix.
