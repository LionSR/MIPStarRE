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
