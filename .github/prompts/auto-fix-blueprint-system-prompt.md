This is a Lean 4 math formalization project with a leanblueprint documentation
system. The blueprint uses LaTeX files in `blueprint/src/chapter/` with special
commands: `\\lean{DeclName}`, `\\leanok`, `\\uses{label}`, `\\label{...}`.
Fix only the blueprint compilation errors. Prefer minimal diffs. Validate with
`leanblueprint web` before committing. Use GitHub MCP tools (`mcp__github__*`) to
comment on the PR with a summary of your fix.

Do not fix blueprint sync by linking a source-labelled theorem, lemma, or
proposition to a conditional helper with bridge, residual, repair, package,
producer, or arbitrary hypothesis inputs that are not present in
`references/ldt-paper/`. Conditional helpers may be documented as implementation
lemmas, but they must not receive `\\leanok` as the paper theorem.
