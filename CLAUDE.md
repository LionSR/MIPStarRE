# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in
this repository.

**See `AGENTS.md` for all agent conventions, build commands, code style, and
proof-integrity rules.** This repository has a single, consolidated agent guide at
`AGENTS.md`. Read that first.

## Claude-specific notes

- When stuck, read the original paper source in `references/ldt-paper/*.tex`.
- Lean files in this repo often exceed Claude's context window; use `rg`/`grep` to
  locate definitions and search for lemmas in `.lake/packages/mathlib/`.
- Prefer `lake env lean MIPStarRE/Path/To/File.lean` for fast iteration; only run
  `lake build` before pushing.
- The `AGENTS.md` and `CLAUDE.md` files are consumed by the Claude Code
  agent; keep them under 200 lines total.

## Toolchain upgrade notes

- **Current**: Lean v4.28.0 / Mathlib v4.28.0 (from `lean-toolchain`)
- **Planned**: PR #889 upgrades to v4.29.1 (draft, not yet merged)
- After the upgrade: remove any file-scope
  `set_option backward.isDefEq.respectTransparency false` usages and replace
  with local-scope alternatives
- The `backward.isDefEq.respectTransparency` option was introduced in v4.29.0
  and should only be used temporarily for porting; permanent fixes involve
  repairing instance/type-synonym definitions
