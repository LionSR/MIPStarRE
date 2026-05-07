---
title: "Issue #1287: Reference terminology and notation audit"
date: 2026-05-06
purpose: >
  Record the visible terminology and notation surfaces affected by issue #1287,
  and explain the repository rule introduced by the accompanying documentation
  change.
status: implemented
track: paper2009ldt
kind: terminology-audit
---

# Issue #1287: Reference Terminology and Notation Audit

Issue #1287 asks for a repository-wide writing convention: public mathematical
prose should use the terminology and notation of the original references
whenever possible, and unavoidable Lean-specific replacements should be defined
clearly.

This short audit records the most visible terminology surfaces found before the
documentation rule was added.

## Sources Checked

- `docs/mathematical_language.md`
- `docs/blueprint_style_guide.md`
- `AGENTS.md`
- `blueprint/src/chapter/ch04_projective.tex`
- `blueprint/src/chapter/ch07_self_improvement.tex`
- high-traffic Lean files under `MIPStarRE/LDT/MakingMeasurementsProjective/`,
  `MIPStarRE/LDT/SelfImprovement/`, and `MIPStarRE/LDT/Test/`

The search used terms which usually indicate terminology drift from the paper:
`projectivization`, `Line130`, `Line169`, `Step6`, `totalGap`,
`MatrixSdpCanonical`, `residual-domination`, `pipeline`, `wrapper`, `package`,
`bridge`, `handoff`, and `raw`.

## Findings

1.  The repository already contains a useful local rule in
    `docs/mathematical_language.md`: terminology should come first from
    `references/ldt-paper/`, then from the blueprint, and only then from local
    Lean conventions.  Before this audit, however, the rule did not explicitly
    cover issue bodies, PR descriptions, or the obligation to define
    unavoidable departures from the paper's notation.

2.  The blueprint style guide already warns against invented notation and
    implementation language.  The missing refinement was a paper-first rule:
    when Lean needs a different name or symbol, the blueprint should state its
    relation to the paper notation in prose rather than relying on the
    `\lean{...}` tag to explain it.

3.  Section 5 and the main-induction material still contain names derived from
    the formal development rather than from the paper, such as
    `Projectivization*`, `Line169*`, and Step-6 residual structures.  Many of
    these are now historically entrenched public Lean names.  Future changes
    should either use the paper's phrases, such as orthogonalization, completing
    to a measurement, and the relevant line of the inductive-step proof, or add
    a docstring explaining the correspondence.

4.  Section 9 contains formalization-only SDP and point-consistency interfaces,
    including canonical matrix SDP structures, residual-domination inputs, and
    total-gap variants.  These are legitimate Lean interfaces, but they are not
    named statements of the paper.  They should continue to be documented as
    auxiliary structures supporting the paper's SDP lemma, complementary
    slackness equations, and projective-output point-consistency argument.

5.  Existing reports under `docs/reports/` and `docs/paper-gaps/` already give
    good examples of the desired practice: they introduce the paper notation,
    compare it with the blueprint and Lean statements, and then give a verdict.
    New audit notes should follow that pattern rather than using private
    shorthand from an implementation discussion.

## Resulting Rule

The documentation now states that the original reference controls public
mathematical terminology and notation by default.  If Lean uses a different
name or representation, the documentation must define the paper term, the Lean
representative, the mathematical reason for the difference, and the scope where
the replacement is intended to be used.

## Resolution

This report serves as the concrete implementation for issue #1287.
The repository rule is now in force through `docs/mathematical_language.md`
and the blueprint conventions in `docs/blueprint_style_guide.md`.
For future work, this convention should be enforced at the first review pass
by checking whether a public declaration name or reader-facing prose matches
the source notation, and adding an explicit paper-to-LDT mapping when the
deviation is intentional and unavoidable.

## Validation

- Reviewed the project writing rules in `docs/mathematical_language.md` and
  `docs/blueprint_style_guide.md`.
- Sampled blueprint prose and high-traffic Lean files from Sections 5, 6, and 9
  to identify recurring terminology departures from the LDT paper.
- Checked that the resulting documentation rule distinguishes paper terminology
  from formalization-only auxiliary names.

## Review Use

Reviewers should use this audit when a PR introduces a new public Lean name,
blueprint paragraph, issue description, or PR description whose terminology
differs from `references/ldt-paper/`.  The expected review question is whether
the paper term, the Lean representative, the mathematical reason for the
departure, and the intended scope are all defined in a reader-facing location.
