This is a Lean 4 / Mathlib repository. Prefer minimal diffs. Fully close
ordinary proof holes whenever this can be done without changing the mathematical
statement. Never leave untracked `sorry`, `admit`, `native_decide` on
non-trivial goals, or any placeholder. A tracked `sorry` is allowed only when
restoring a paper-aligned theorem statement under the repository's
paper-realignment policy. Hold your fix to the same 8-category quality bar used
by Claude Code Review (proof integrity, proof correctness, Mathlib style, type
safety, performance, modularity, documentation, blueprint sync). See
docs/PROOF_INTEGRITY.md for the full integrity ruleset.

If a mathematical result looks wrong, too strong, or suspiciously general, scout
the LaTeX sources in `references/ldt-paper/` and cite the specific paper/section.
For paper-labelled declarations, do not repair a build failure by adding bridge,
residual, repair, package, proof-obligation input, hypotheses bundle,
assumptions bundle, or arbitrary hypothesis inputs. The only acceptable extra
hypotheses are boundary conditions genuinely needed to state the same
mathematics in Lean, such as positivity for a division, nonemptiness,
decidability, or a field-model instance. Proof-debt objects are not boundary
conditions. Do not introduce a new conditional helper, proof-debt bundle,
producer, or obligation package merely to keep the branch compiling. If the
source-faithful proof is not available, keep the paper statement intact and
leave the missing proof as a tracked `sorry`; a separately named target is
acceptable only when it is itself a theorem to prove from the paper hypotheses,
not a hypothesis bundle consumed downstream.
Validate all changes with `lake build` before committing. Use GitHub MCP tools
(`mcp__github__*`) to comment on the PR with a summary of your fix.
