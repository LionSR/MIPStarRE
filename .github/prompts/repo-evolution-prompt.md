## Task

Generate a `repo-evolution` tracking issue for this week.

You will be given, in the workflow context:

- A drift snapshot at `$RUNNER_TEMP/drift.json`
- A CI-waste analysis at `$RUNNER_TEMP/ci-waste.json`
- A summary of recent merged PRs and review comments (inlined below)
- The current contents of `docs/evolution/friction/` (read with `Read`)
- The current `docs/evolution/norms/INDEX.md` (read with `Read`)

## Steps

1. Read the drift snapshot and the CI-waste analysis. Note any `fail` or
   `warn` findings.
2. Read every non-`TEMPLATE.md`, non-`INDEX.md` file under
   `docs/evolution/friction/` whose status is `open` or `proposed`.
3. Read `docs/evolution/norms/INDEX.md` to understand which norms already
   exist; do not propose duplicates.
4. Skim the recent merged PRs / review comments inlined below for repeated
   review patterns. Cite real PR numbers; do not invent.
5. Synthesise 1–5 small, reversible proposals. Each proposal must name the
   file(s) to change and sketch the change.
6. Open a tracking issue with title `repo-evolution: <today's ISO date>`
   labelled `repo-evolution` and `infrastructure`. Body format:

   ```markdown
   ## Summary

   - signal 1
   - signal 2

   ## Proposals

   ### 1. <short title>

   **Signal**: which input motivated this (cite drift metric / PR / friction file).

   **Change**: which file, what to add/remove/edit. Include a brief diff sketch if small.

   **Norm**: NNNN-... (or "—" if no norm change).

   **Rollback**: single revert of PR `<future-PR>`.

   ### 2. ...

   ## Things to drop

   - norm NNNN: ...

   ## Open questions

   - ...
   ```

7. Stop. Do not push commits, do not edit any file outside
   `docs/evolution/proposals/`.

If the inputs show **no actionable signal at all** (no drift, no waste, no
friction, no review-comment patterns), open the issue anyway with a single
section "## No proposals this week" listing the metrics observed. Silence
is informative; an empty week of signals is itself a fact worth recording.
