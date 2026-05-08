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
number, or implementation history.

### Concrete examples

The table below illustrates the naming norm with real examples from the
codebase.  The "avoid" column lists process-shaped names that encode the
history of how the formalization was assembled; the "prefer" column lists
mathematical names that a reader of the paper or blueprint would recognize.

| Avoid (process-shaped)                        | Prefer (mathematical)                     | Rationale                                              |
|:----------------------------------------------|:------------------------------------------|:-------------------------------------------------------|
| `Line130`                                     | `ProjectiveConsistency`                   | Paper Lemma 5.13, not "the line-130 identity"          |
| `Line169`                                     | `CompletionTransport`                     | Paper Lemma 5.16, step that transports completed data  |
| `Step6`                                       | `Orthonormalization`                      | Paper Section 5, the orthonormalization construction   |
| `FinalAssembly`                               | `DiagonalCompletion`                      | Paper Lemma 5.17, constructing a diagonal POVM         |
| `OneShotIneq`                                 | `SelfConsistencyDataProcessing`           | Paper's data-processing inequality for self-consistency |
| `PipelineCheck`                               | `ErrorPropagationBound`                   | The bound that propagates error through the test       |
| `QxpLayerWrapper`                             | `ProjectivePOVMCompletion`                | The construction from round-projectors to POVMs        |
| `RawSpectralTruncation`                       | `SpectralTruncation`                      | The paper's spectral truncation, not an "unwrapped" version |
| `AddInUStep3To5`                              | `AddInUSupperExcessMass`                  | Paper Addendum in §U, the upper excess-mass estimate   |
| `AddInUStep12`                                | `AddInUcommutationTail`                   | Paper Addendum in §U, the commutation tail estimate    |

An avoided name is acceptable only when the cited paper itself uses that
phrase as the mathematical name (e.g., a lemma the paper calls "Step 2").
In that case the docstring should cite the paper's phrasing.

File-split PRs are a common place where this rule matters: new leaves should be
named by the mathematical boundary they isolate, and any public declarations
exposed by the split should be reviewed under the same standard.

### Shared helpers

When the same (or nearly the same) helper declaration appears in two or
more chapter-local leaves, the copies should be consolidated into a single
shared helper in an appropriate common module.  This avoids duplication and
ensures that fixes, generalizations, or upstream replacements apply to all
call sites at once.  Issue [#1145] tracks this work across the repository.

Procedure:

1. **Confirm equivalence.**  Compare the statement of each copy.  If the
   types differ only by a chapter-specific parameterization (e.g.,
   `SubMeas (Polynomial params) ι` vs `SubMeas (Point params) ι`),
   parameterize the shared helper over that type via a `variable` or
   explicit argument.
2. **Find the right home.**  Prefer a module that is already imported by
   both call sites.  Typical candidates:
   - `MIPStarRE/LDT/Basic/` for parameter-free operators and bounds,
   - `MIPStarRE/LDT/Preliminaries/` for polynomial/field/character lemmas,
   - The highest chapter that is a common dependency of the two sites.
3. **Name mathematically.**  Give the shared helper a name that describes
   what it states, not which chapter it originally came from.
4. **Replace call sites.**  Delete the chapter-local copies and replace
   their uses with the shared helper.  If the chapter-local name was a
   paper-facing term (e.g., "orthogonalization error bound" in Section 5),
   keep a thin wrapper with the paper-facing name that calls the shared
   helper.  Remove the wrapper once the paper-facing name is no longer
   needed for external reference.
5. **Document.**  Add a docstring to the shared helper citing the paper or
   blueprint location it supports.

### Legacy identifier treatment

If a docstring must mention a legacy Lean identifier, cite it in backticks and
describe the mathematical object in paper terminology. If an old public
identifier cannot be renamed in the current PR, record the required migration
in the issue, PR description, or an audit file under `audits/`.

Do not add an empty pass-through abbreviation merely to introduce a second
public name.

## Review Checklist

Reviewers should use this checklist when examining public names and
documentation prose.  Flag any item that fails.

- [ ] **Naming.**  Do public declaration names, namespace names, module names,
      theorem field names, and docstring prose describe a mathematical object,
      hypothesis, or conclusion?  Or do they encode the history of how the
      formalization was assembled (paper line numbers, workflow steps,
      implementation-phase labels)?
- [ ] **Source alignment.**  For the mathematical content under review, does
      the prose use the terminology in `references/ldt-paper/` or the
      blueprint?  Are process words such as `pipeline`, `wrapper`, `package`,
      `raw`, `oneShot`, or `liveBlock` used as mathematical terms when the
      source does not use them that way?
- [ ] **Deviation documented.**  If a Lean name or representation differs from
      the paper, is the deviation documented in a declaration docstring,
      module docstring, blueprint paragraph, or `docs/paper-gaps/` note, in
      that order of preference?
- [ ] **Auxiliary lemmas.**  Are formalization-only auxiliary lemmas introduced
      as such, with prose naming the nearby paper equation, theorem, or
      construction they support?
- [ ] **Shared helpers.**  Does the PR introduce a helper that already exists
      (or near-exists) in another chapter-local leaf?  If so, has it been
      consolidated into a common module with a mathematical name?
- [ ] **Legacy IDs.**  If a legacy Lean identifier is mentioned, is the
      mathematical object described in paper terminology?  If an old public
      identifier cannot be renamed yet, is the required migration recorded in
      the issue, PR description, or an audit file?
- [ ] **Pass-through names.**  Does the PR add an empty pass-through
      abbreviation that introduces a second public name without adding
      mathematical content?  Reject if so.

Review-fix PRs touching a surface covered by an active audit should read the
relevant audit before changing names or prose.

[#1145]: https://github.com/LionSR/MIPStarRE/issues/1145
