# Blueprint support script coverage

Issue #925 asks for a single place that says which Python helpers are part of the blueprint-support surface, how they are tested, and which workflow path filters must move with them.

## Scope decision

A script is in scope when it directly parses or validates `blueprint/src/**/*.tex`, checks `\lean{...}` / `\leanok` annotations, or is a wrapper/shared Python utility imported by those checks.

| Script | Blueprint role | Unit-test coverage | Workflow path filters |
|---|---|---|---|
| `scripts/blueprint_lean_sync.py` | Name-level `\lean{...}` / `\leanok` sync and `blueprint/lean_decls` drift checker. | `scripts/tests/test_blueprint_lean_sync.py` | `.github/workflows/blueprint-sync.yml`, `.github/workflows/lint-blueprint.yml` |
| `scripts/blueprint_leanok_axioms.py` | Lean axiom-closure checker for proof-level `\leanok` claims. | `scripts/tests/test_blueprint_leanok_axioms.py` | `.github/workflows/blueprint-sync.yml` |
| `scripts/check_blueprint_sync.py` | Backward-compatible CLI wrapper for the axiom checker. | `scripts/tests/test_check_blueprint_sync.py` | `.github/workflows/blueprint-sync.yml` |
| `scripts/check_blueprint_latex.py` | Blueprint LaTeX convention lint, currently forbidding active `cleveref` / `\Cref` uses. | `scripts/tests/test_check_blueprint_latex.py` | `.githooks/pre-commit` is the active gate; `.github/workflows/lint-blueprint.yml` still exercises the lint's unit tests via the `scripts/tests` discovery step. |
| `scripts/tex_utils.py` | Shared active-TeX-line parsing helper used by both lint and sync scripts. | Covered through `scripts/tests/test_blueprint_lean_sync.py` and `scripts/tests/test_check_blueprint_latex.py`. | `.github/workflows/blueprint-sync.yml`, `.github/workflows/lint-blueprint.yml` |

Both blueprint workflows also watch `scripts/tests/**` and their own workflow files, so changes to tests or path-filter policy re-run the relevant checks.

## Intentionally outside this surface

These scripts may have their own tests or workflows, but they are not part of the blueprint-support surface above:

- `scripts/generate_badges.py` generates repository status badges in `.github/workflows/badges.yml`; it does not parse blueprint LaTeX or enforce blueprint/Lean sync.
- `scripts/audit_conclusion_shaped_hypotheses.py`, `scripts/audit_readme_freshness.py`, `scripts/audit_stale_issues.py`, and `scripts/lean_linter_warning_report.py` are independent audit/reporting tools.
- `scripts/deploy-to-gh-pages.sh` is a deployment helper, not a Python validation helper.
- `scripts/Checkdecls.lean` is a Lean executable used by CI, so it is outside the Python-unit-test convention.

## Convention for new blueprint-support helpers

When adding or renaming a blueprint-support Python helper:

1. Add or update a focused unit test under `scripts/tests/` in the same PR.
2. Update the relevant workflow `paths:` filters so edits to the helper, its shared utilities, `scripts/tests/**`, and the workflow itself trigger CI.
3. Update the table above and the meta-test in `scripts/tests/test_blueprint_script_surface.py` so the documented support surface and CI filters stay synchronized.
4. If a helper is intentionally excluded from this surface, document the exclusion in the previous section rather than relying on reviewer memory.
