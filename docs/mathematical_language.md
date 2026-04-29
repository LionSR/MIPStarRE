# Mathematical Language Guidelines

MIPStarRE Lean names and documentation should be written for readers comparing
the formalization with the paper and blueprint.

This is a project-local supplement to the Mathlib-derived documentation,
naming, and style guides in `docs/doc.md`, `docs/naming.md`, and
`docs/style.md`.

## Scope

These guidelines apply to:

- public Lean declaration names and namespace names;
- module docstrings;
- declaration docstrings;
- documentation-visible section comments;
- explanatory comments that describe the mathematical role of a declaration.

## Source of Truth

Use terminology from the following sources, in this order:

1. `references/ldt-paper/`
2. `blueprint/src/chapter/`
3. established local conventions in nearby Lean files

When the paper has a term for the object, use that term. For Section 5, for
example, prefer orthogonalization lemma, truncation function, rounding to
projectors, rank reduction, and completing to measurement.

## Naming Norm

Names and prose should describe the mathematical object, hypothesis, or
conclusion. They should not encode the history of how the formalization was
assembled.

Avoid presenting words such as `pipeline`, `wrapper`, `package`, `raw`,
`oneShot`, or `liveBlock` as mathematical terminology unless the cited source
uses them with that meaning. Likewise, avoid implementation-local substitutes
such as `projectivization` or `spectral truncation` when the paper gives a
clearer phrase.

If a docstring must mention a legacy Lean identifier, cite it in backticks and
describe the mathematical object in paper terminology. If an old public
identifier cannot be renamed in the current PR, record the required migration
in the issue, PR description, or an audit file under `audits/`.

Do not add an empty pass-through abbreviation merely to introduce a second
public name.

## Review Use

Reviewers should flag public names and documentation prose that encode
historical formalization status rather than mathematical content. Review-fix
PRs touching a surface covered by an active audit should read the relevant
audit before changing names or prose.
