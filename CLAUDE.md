# CLAUDE.md

Claude Code-specific entry point for this repository. **Read `AGENTS.md` first**
— it is the canonical agent guide with build commands, code conventions, proof
integrity rules, PR workflow, and documentation standards.

## Claude-Specific Notes

- Claude Code reads `CLAUDE.md` automatically when opening this repository.
  All repository-wide conventions are in `AGENTS.md`; this file exists for
  tooling compatibility and Claude-specific configuration.
- When tackling a proof, always start by reading the relevant section in
  `references/ldt-paper/*.tex`. The paper proofs contain the exact mathematical
  argument needed.
- When formalizing a statement from the blueprint, add `\lean{LeanDeclName}`
  and `\leanok` tags to the corresponding `blueprint/src/chapter/*.tex` file.
- For paper-gap notes, follow `docs/paper-gaps/policy.tex`: write mathematical
  prose for third-party readers, not implementation notes.
- Prefer existing Mathlib lemmas over reproving. Scout Mathlib with `exact?`,
  `apply?`, or grep before writing custom proofs.
- The pinned memories under `/memories/` contain accumulated project lessons
  (worktree patterns, CFC.sqrt workarounds, review workflow, paper-faithfulness
  rules). Consult `mipstar_lessons_learned.md` and `campaign5_workflow_lessons.md`.

## Quick Build Commands

```bash
lake exe cache get && lake build   # first-time setup
lake build                          # full build
lake env lean path/to/File.lean     # single-file check
rg -n "sorry|axiom" path/to/File.lean || true   # proof-hole scan
leanblueprint web                   # blueprint check
```
