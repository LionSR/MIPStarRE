# Norm 0002: Prefer Mathlib over custom helpers

- **Status**: accepted
- **Accepted**: 2026-05-07
- **Scope**: all `MIPStarRE/**/*.lean`
- **Enforcement**: `AGENTS.md` §Mathlib integration; `docs/anti_patterns.md`
  ("Mathlib-bypass castles"); review checklist; `mathlib-scout.yml`
- **Supersedes**: —

## Rationale

Custom re-declarations of standard Mathlib lemmas accumulate maintenance
debt: they need updating when Mathlib changes, they hide whether a proof is
genuinely grounded in Mathlib, and they make future agents reinvent the same
helpers. The "castle in the air" anti-pattern in `docs/anti_patterns.md`
catalogs the failure mode.

## Rule

Before adding a private helper lemma:

1. Search Mathlib (`exact?`, `apply?`, `#find?`, grep
   `.lake/packages/mathlib/`).
2. Check the local API surfaces in `Quantum/` and `LDT/Basic/`.
3. Only add a helper if the Mathlib analogue is genuinely missing or has the
   wrong shape, and document the search in the docstring.

Never re-declare a standard Mathlib lemma under a project name. Never close
a goal that Mathlib already proves with a `sorry` or with an `axiom`.

## Worked example

A PR adds `lemma foo_eq_bar : foo = bar := by simp` where `Mathlib.…foo_eq`
already exists. The reviewer asks for the Mathlib name; the helper is
removed and the call sites use the Mathlib lemma directly.

## Signals that this norm is failing

- `mathlib-scout.yml` repeatedly flags the same kind of duplicate.
- Audits in `audits/` report large lists of project-local helpers that are
  shallow wrappers around Mathlib lemmas.
