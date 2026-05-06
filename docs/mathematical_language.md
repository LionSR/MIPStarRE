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
- blueprint prose and formalization-support notes;
- issue titles and issue bodies;
- PR titles and PR descriptions.

## Source of Truth

Use terminology from the following sources, in this order:

1. `references/ldt-paper/`
2. `blueprint/src/chapter/`
3. established local conventions in nearby Lean files

When the paper has a term for the object, use that term. For Section 5, for
example, prefer orthogonalization lemma, truncation function, rounding to
projectors, rank reduction, and completing to measurement.

## Reference Notation And Terminology

The notation and terminology of the original reference are the default for
reader-facing mathematical text.  A reader should be able to compare a Lean
docstring, blueprint paragraph, issue, or PR description with the cited source
without first learning a private vocabulary used by the formalization.

When Lean must use a different name or representation, define the deviation in a
location which future readers can find from the affected statement.  Use the
first applicable location in the following order:

1. the declaration docstring of the public object whose name or representation
   differs from the paper;
2. the module docstring of the defining Lean file, when the deviation concerns a
   family of declarations in that file;
3. the relevant blueprint paragraph, when the notation appears only in the
   blueprint;
4. a report under `docs/reports/` or `docs/paper-gaps/`, when the deviation is a
   larger discrepancy between the paper, blueprint, and Lean.

The explanation should say:

- the notation or term used in the paper;
- the Lean object or name which represents it;
- the mathematical reason for the difference, if there is one;
- the scope in which the replacement should be used.

A PR description may mention the deviation, but it should not be the only place
where future readers can learn it.

Formalization-only auxiliary lemmas should be introduced as such.  Their prose
should name the nearby paper equation, theorem, or construction they support,
rather than presenting the auxiliary name as paper terminology.

## Naming Norm

Names and prose should describe the mathematical object, hypothesis, or
conclusion. They should not encode the history of how the formalization was
assembled.

Avoid presenting words such as `pipeline`, `wrapper`, `package`, `raw`,
`oneShot`, or `liveBlock` as mathematical terminology unless the cited source
uses them with that meaning. Likewise, avoid implementation-local substitutes
such as `projectivization` or `spectral truncation` when the paper gives a
clearer phrase.

This is a general rule for the repository, not only a rule for file splits.
Module names, namespace names, public declarations, theorem fields, docstrings,
blueprint-facing names, issue titles, and spec documents should name the
mathematical layer under discussion, not the local workflow step, paper line
number, or implementation history. For example, prefer names such as
`DiagonalCompletion`, `CompletionTransport`, or `ProjectiveConsistency` over
names built from `Line130`, `Line169`, `Step6`, or `FinalAssembly`, unless the
cited paper itself uses that phrase as the mathematical name.

File-split PRs are a common place where this rule matters: new leaves should be
named by the mathematical boundary they isolate, and any public declarations
exposed by the split should be reviewed under the same standard.

If exact or near-exact helper declarations recur across chapters, do not copy
the helper into another chapter-local leaf. Confirm that the statements are
mathematically the same, then move the shared result into an appropriate common
module with a mathematical name and keep chapter-specific wrappers only when
they preserve paper-facing terminology.

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
