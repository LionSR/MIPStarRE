# Proposals Index

Proposals are short-lived: each one suggests an amendment to `AGENTS.md`,
a script, a workflow, or a new norm. The weekly `repo-evolution` workflow
generates proposals automatically; humans (or follow-up PRs) accept,
refine, or dismiss them.

| Date       | File                                  | Target                              | Status   |
|------------|---------------------------------------|-------------------------------------|----------|
| —          | —                                     | (no proposals yet)                  | —        |

## Status values

- `open` — proposal filed, not yet decided
- `accepted` — turned into a PR (link the PR)
- `dismissed` — declined with a written reason in the file
- `superseded` — replaced by a later proposal (link it)

## File naming

`YYYY-MM-DD-kebab-case-summary.md`. Use the date the proposal was
generated, not the date it was accepted.

## What goes in a proposal

A proposal must include:

1. The observed signal that prompted it (drift metric, friction entries,
   repeated review comments, repeated CI failures).
2. The concrete change — file paths, ideally a diff sketch.
3. A rollback plan (single PR revert is the default).
4. The norm it would create or amend, if any.
