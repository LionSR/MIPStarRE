# AGENTS.md

## Purpose

Instructions for coding agents working in `MIPStarRE`.

This repository is a Lean 4 + Mathlib formalization project for mathematics around
`MIP* = RE`. The active formalization track is the low individual degree test (LDT)
paper:

- `references/ldt-paper/` is the mathematical source of truth
- `blueprint/src/` is the active blueprint
- `MIPStarRE/` is the Lean codebase

Read the paper source before formalizing or changing theorem statements.

## Agent Rule Sources

Checked in this repository snapshot:

- No `.cursorrules`
- No `.cursor/rules/`
- No `.github/copilot-instructions.md`

Use this file together with:

- `CLAUDE.md`
- `docs/CONTRIBUTING.md`
- `docs/PROOF_INTEGRITY.md`
- `docs/style.md`
- `docs/naming.md`
- `docs/doc.md`

## Repository Layout

- `MIPStarRE/Quantum/`: reusable matrix and measurement infrastructure
- `MIPStarRE/LDT/`: active low-degree-test development
- `blueprint/src/`: active LaTeX blueprint
- `references/ldt-paper/`: mirrored TeX paper sources
- `docs/`: contribution, style, audit, and planning documents
- `scripts/Checkdecls.lean`: declaration checker executable

## Toolchain

- Lean: `v4.29.1` from `lean-toolchain`
- Mathlib: `v4.29.1` from `lakefile.toml`

Important `lakefile.toml` options:

- `relaxedAutoImplicit = false`
- `pp.unicode.fun = true`
- `weak.linter.mathlibStandardSet = true`
- `maxSynthPendingDepth = 3`

Because `relaxedAutoImplicit = false`, declare all variables explicitly.

## Build And Check Commands

Run commands from the repository root unless noted otherwise.

### Initial setup

```bash
lake exe cache get
lake build
```

### Full project build

```bash
lake build
```

This is the main CI-equivalent Lean check.

### Fast single-file check

```bash
lake env lean MIPStarRE/LDT/SelfImprovement/Defs.lean
```

Use this as the default "single test" loop while editing Lean files.

General form:

```bash
lake env lean path/to/File.lean
```

### Check for proof holes in one file

```bash
rg -n "sorry|axiom" MIPStarRE/LDT/SelfImprovement/Defs.lean || true
```

### Check for proof holes in the whole project

```bash
rg -n "sorry|axiom" MIPStarRE
```

### Declaration-checker executable

```bash
lake exe checkdecls blueprint/lean_decls
```

Use this when blueprint declaration lists need to match Lean declarations.

### Blueprint build

From the repo root:

```bash
leanblueprint pdf
leanblueprint web
```

In CI, blueprint linting effectively runs `leanblueprint web` from `blueprint/`.

### When editing only blueprint files

Prefer:

```bash
leanblueprint web
```

Use `pdf` only when you need the rendered PDF output.

## What Counts As A Single Test Here

This repository does not have a conventional unit-test suite.

For Lean work, the closest single-test commands are:

1. `lake env lean path/to/File.lean`
2. `rg -n "sorry|axiom" path/to/File.lean || true`

For blueprint-only work:

1. `leanblueprint web`

For whole-repo verification:

1. `lake build`
2. `lake exe checkdecls blueprint/lean_decls` when declaration sync matters

## Recommended Validation Sequence

For a Lean file change:

1. Type-check the edited file with `lake env lean ...`
2. Scan that file for `sorry|axiom`
3. If the change affects imports or shared declarations, run `lake build`

For blueprint changes:

1. Run `leanblueprint web`
2. If declaration links changed, run `lake exe checkdecls blueprint/lean_decls`

## Source-Of-Truth Order

When formalizing mathematics, use this order:

1. `references/ldt-paper/`
2. `blueprint/src/chapter/`
3. `MIPStarRE/`

Do not invent theorem statements from existing scaffold alone if the paper or blueprint
gives a more precise statement.

## Proof-Filling Order

The project guidance says to work in dependency order:

1. Sections 3-4
2. Section 5
3. Sections 7-8
4. Section 9
5. Sections 10-11
6. Section 12
7. Section 6

Do not start from the final theorem and guess intermediate facts.

## Imports

- Keep imports at the top of the file
- One import per line
- Follow existing local import style
- Prefer the smallest correct import set, but do not churn imports unnecessarily
- Preserve barrel-file structure such as `MIPStarRE.lean` and `MIPStarRE/LDT.lean`

Before adding a new import, check whether the needed declaration already comes from an
existing local barrel import.

## File Structure

Every `.lean` file should have:

1. imports
2. a module docstring starting with `/-!`
3. namespace / opens / variables
4. declarations

Project-specific expectation from `CLAUDE.md`:

- every `.lean` file needs a module docstring with a title and references section

## Formatting

- Maximum line length: 100 characters
- Use spaces around `:` and `:=`
- Put `by` at the end of the preceding line, not on a line by itself
- Indent theorem proof bodies by 2 spaces
- Indent continued theorem statements by 4 spaces
- Keep top-level commands flush-left
- Avoid orphaned parentheses
- Prefer readable multiline formatting over dense tactic blocks

## Naming Conventions

Follow Mathlib naming plus project-local conventions.

Mathlib naming:

- theorems / proofs / proposition-valued terms: `snake_case`
- structures / inductives / classes / Prop names / Type names: `UpperCamelCase`
- functions / non-Prop terms: `lowerCamelCase`

Project-preferred variable names:

- `q` for alphabet size
- `n`, `m` for dimensions
- `σ` for strategies
- `P` for projective measurements
- `G` for graphs or slice measurements

Use American English spelling in declaration names.

## Types And Signatures

- Give explicit types for declaration arguments
- Give explicit return types for definitions
- Do not rely on auto-implicit variables
- Prefer existing project structures and Mathlib-compatible types over ad hoc wrappers
- Be skeptical of scaffolding that compiles but cannot support real proofs later

## Documentation

Required:

- docstrings on every `def`, `structure`, `class`, and significant `theorem`
- module docstrings for every file

When formalizing a statement from the blueprint, add corresponding `\lean{...}` and
`\leanok` tags in the relevant `blueprint/src/chapter/*.tex` file.

## Proof Engineering

Search before proving:

- prefer existing Mathlib lemmas
- reuse local API from `Quantum/` and `LDT/Basic/`
- use file-local helper lemmas only when they genuinely reduce duplication

Prefer the validation ladder:

1. `lake env lean path/to/File.lean`
2. `lake build`

Do not jump straight to full builds for every small edit.

## Error Handling And Integrity Rules

Before merge, these are blockers:

- `sorry`
- `admit`
- unjustified `axiom`
- `unsafeCast`
- `unsafeCoerce`
- `lcProof`
- `ofReduceBool`
- `ofReduceNat`
- circular reasoning
- scaffolding that cannot support real Mathlib-grounded proofs

Also avoid leaving behind:

- `exact?`
- `apply?`
- `library_search`
- `dbg_trace`
- `#check`, `#eval`, `#print` in proof files unless intentionally retained

See `docs/PROOF_INTEGRITY.md`.

## Lean-Specific Advice

- Prefer small, composable lemmas over giant fragile proofs
- Reuse `SubMeas`, `Measurement`, tensor-placement, PSD, and trace lemmas already in the repo
- Check `docs/api_surface.md` for useful obligation-closing lemmas
- If changing statements, confirm against paper and blueprint first
- Never add axioms or weaken statements without explicit justification

## Blueprint And Documentation Work

If you modify blueprint material:

- keep chapter structure under `blueprint/src/chapter/`
- ensure `leanblueprint web` succeeds
- keep Lean declaration references valid
- sync theorem labels with Lean names

## PR And Commit Conventions

- PR title format: `type(scope): short description`
- Types: `feat`, `fix`, `refactor`, `docs`, `ci`, `chore`
- Scope: shortened module path like `LDT/SelfImprovement`
- Commit subject: imperative mood, under 72 characters

## Practical Defaults For Agents

When editing Lean code:

1. read the paper source
2. read the target Lean file and nearby supporting files
3. type-check the single file
4. scan for `sorry|axiom`
5. run `lake build` only when the local change is stable

When editing blueprint files:

1. read the matching paper source and chapter file
2. update Lean links carefully
3. run `leanblueprint web`

Prefer minimal, dependency-aware changes that preserve the project's theorem structure.
