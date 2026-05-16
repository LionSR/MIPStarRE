# GitHub Actions Source-Statement Guard Audit (2026-05-14)

## Purpose

This audit records the review requested in issue #1575.  The failure mode under
review is statement drift: an automated agent repairs a Lean file or blueprint
link by adding a bridge, residual, repair, package, producer, proof-obligation
input, hypotheses bundle, assumptions bundle, or arbitrary implication
hypothesis to a theorem that is presented as a paper theorem.

The desired invariant is that every route which can edit Lean or blueprint files
distinguishes a source-facing theorem from an internal construction target.  A
missing proof step should remain a named proof obligation or a tracked `sorry`;
it should not become a new public hypothesis of the paper theorem.

## Method

The audit inspected `.github/actions` and the workflows that call
`claude-code-with-provider` or `compose-auto-fix-prompt`.

Commands used:

```bash
find .github -maxdepth 4 -type f | sort
rg -n "compose-auto-fix-prompt|claude-code-with-provider|prompt-file|Source-statement guard" \
  .github/workflows .github/actions
for f in .github/prompts/*prompt.md; do
  rg -q "bridge|residual|repair|package|producer|proof-obligation|source-labelled|paper-facing|references/ldt-paper|proof-gap-protocol|PROOF_INTEGRITY|AGENTS.md" "$f" \
    || echo "MISSING_GUARD $f"
done
```

## Findings

The shared CI and Codex auto-fix workflows call
`.github/actions/compose-auto-fix-prompt/action.yml`.  That action appends a
`Source-statement guard` unless the prompt already contains an equivalent
section.  The guard points agents to `AGENTS.md`,
`docs/PROOF_INTEGRITY.md`, and
`docs/paper-gaps/proof-gap-protocol.tex`; it explicitly forbids adding
bridge, residual, repair, package, producer, proof-obligation input,
hypotheses-bundle, assumptions-bundle, or arbitrary hypothesis inputs to a
source-labelled theorem.

The general mention, review, blueprint, and auto-fix prompts already contain
source-statement language.  In particular, they instruct agents to compare
against `references/ldt-paper/`, to keep source-labelled statements faithful,
and to avoid marking conditional helpers as the paper theorem.

Several direct workflows call `claude-code-with-provider` without going through
`compose-auto-fix-prompt`.  Most of these are non-editing workflows:
issue classification, Mathlib scouting, formalization audit, daily standup, and
PR metadata cleanup either post reports or edit GitHub metadata.  The Mathlib
scout prompt explicitly says not to create files or branches.

The Lean linter-warning autofix workflow is different.  It can edit Lean files
directly, and it uses `.github/prompts/lean-linter-warning-prompt.md` together
with `.github/prompts/lean-linter-warning-system-prompt.md`.  Before this audit,
those prompts said not to change theorem statements or mathematical
definitions, but they did not name the bridge/residual/repair/package
hypothesis failure mode and did not point to the proof-gap protocol.

## Change Made

The linter-warning prompts were tightened so that an automated linter run must:

- read `AGENTS.md`, `docs/PROOF_INTEGRITY.md`, and
  `docs/paper-gaps/proof-gap-protocol.tex` before editing a source-labelled
  declaration;
- preserve paper theorem statements up to faithful formal encoding;
- not fix a warning by adding bridge, residual, repair, package, producer,
  proof-obligation input, hypotheses-bundle, assumptions-bundle, or arbitrary
  implication hypotheses to a paper-facing theorem;
- leave the warning in place when the only available fix would change such a
  statement or add non-paper proof data;
- report whether any public theorem or definition statement changed.

## Verdict

After this change, every identified workflow route that can edit Lean or
blueprint content has an explicit source-statement guard either through
`compose-auto-fix-prompt` or through its own prompt.  The direct non-editing
routes do not need the full guard, but their prompts should continue to avoid
creating files, branches, or proof obligations.

This audit is preventive.  It does not discharge any mathematical proof
obligation in the LDT formalization.
