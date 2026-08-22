<!-- Pointer: the canonical document lives in the lean-conventions skill of
     texra-ai/texra-lean-skills, installed automatically in Claude Code
     sessions by .claude/settings.json (other agents: see the install
     instructions in that repository's README). Only the project addendum
     below is repo-local. -->

# Mathlib Style Conventions

Canonical text: the `lean-conventions` skill —
[MATHLIB_style.md](https://github.com/texra-ai/texra-lean-skills/blob/main/skills/lean-conventions/references/MATHLIB_style.md).
Consult it through the installed skill; do not restate its rules here.

## Project addendum (MIPStarRE)

### Linter warnings

Do not mask linter warnings instead of fixing them. A cleanup PR should not add
broad `set_option linter.<name> false` blocks, and especially not file-wide
blocks, just to make the build output quieter. Linters exist to expose real
maintenance problems; hiding them makes later proof work and review harder.

Fix the warning at its source whenever possible:

- wrap long lines rather than disabling `linter.style.longLine`;
- remove or narrow unused variables, section variables, and unused typeclass
  assumptions rather than disabling the corresponding unused-* linter;
- remove unused `simp` arguments rather than disabling `linter.unusedSimpArgs`;
- rewrite proof terms or state the simplified goal explicitly rather than
  silencing `linter.flexible`.

If a linter warning is a genuine false positive or a temporary porting
exception, use the narrowest possible scope, preferably
`set_option linter.<name> false in <decl>`, and add a short nearby explanation.
Such exceptions should be rare and reviewable. Never use linter suppression as
the main mechanism for a linter-warning cleanup PR.
