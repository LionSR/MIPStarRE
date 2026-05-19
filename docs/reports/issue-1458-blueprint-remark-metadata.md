# Blueprint remark metadata audit

Audit date: 2026-05-19

## Scope

This note records the repair batch for blueprint remarks that carried
proof-bearing metadata.  The public dependency graph on the GitHub Pages branch
contained two `rem:*` nodes:

- `rem:good-strat-characterization`;
- `rem:individual-degree-convention`.

Both labels arose from expository material, not from paper theorems or lemmas.
The same scan found additional remark environments with `\lean{}`, `\leanok`,
or `\uses{}` metadata.  Those metadata lines made remarks behave like
formalizable dependency-graph nodes even though a remark is not a theorem,
lemma, proposition, definition, or corollary.

## Source Comparison

The paper source for `rem:good-strat-characterization` is
`references/ldt-paper/test_definition.tex:137-153`.  It is a remark explaining
the good-strategy conditions in the notation later used for approximate
measurements.  The blueprint had promoted this text to a proposition and had
attached `\lean`, `\leanok`, and `\uses` metadata.

The individual-degree convention is the paragraph following
`references/ldt-paper/preliminaries.tex:89-103`.  It explains that "individual
degree `d`" means degree at most `d` in each coordinate.  The blueprint had
presented the convention as a lemma labelled `rem:individual-degree-convention`
and had attached `\lean`, `\leanok`, and `\uses` metadata.

## Classification

`rem:good-strat-characterization`: obsolete scaffolding.

The source is a remark.  The Lean declaration
`MIPStarRE.LDT.Preliminaries.goodStrategyCharacterization` remains a useful
formal lemma, but the paper-facing entry should not advertise a remark as a
formalized proposition.

`rem:individual-degree-convention`: obsolete scaffolding.

The source is an explanatory convention following the definition of
`\polyfunc{m}{q}{d}`.  The Lean declaration
`MIPStarRE.LDT.Preliminaries.polyFuncMonotone` remains useful internally, but
the paper-facing entry should not advertise the convention as a source lemma.

Remark environments with `\lean{}`, `\leanok`, or `\uses{}`: obsolete
scaffolding.

These were Lean-interface notes or proof-gap notes, not mathematical statements
to be represented as dependency-graph nodes.  The repair removes the metadata
from remarks and leaves the prose in place.

## Repair

The two `rem:*` graph nodes have been restored to remark environments without
Lean or dependency metadata.  All active remark environments in
`blueprint/src/chapter` are now free of `\lean{}`, `\leanok`, and `\uses{}`
metadata.  The existing blueprint LaTeX checker now enforces this rule, and the
local pre-commit and pre-push hooks run the checker when blueprint or checker
sources change.

## Statement Integrity Audit

No Lean theorem statement was changed.

Paper assumptions: none; the repaired entries are remarks or explanatory
conventions.

Lean assumptions: none added.  The PR removes blueprint metadata and does not
attach any Lean declaration to a remark.

Paper conclusion: none; the repaired entries are not theorems.

Lean conclusion: none advertised from these remarks.

Verdict: the previous blueprint presentation was an unfaithful statement
classification.  The repaired presentation is source-faithful: remarks remain
remarks, and useful Lean lemmas are no longer advertised as paper-facing
formalizations of remarks.
