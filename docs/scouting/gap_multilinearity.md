# Multilinearity Scouting

Date: 2026-04-04

## Bottom line

`references/ldt-paper/multilinearity.tex` is not a standalone mathematical chapter. It is the
root TeX driver for the imported paper source: preamble, macros, title/author block, abstract,
table of contents, and a list of `\input{...}` inclusions for the real body files.

The unusual "0 labels" is therefore not suspicious. This file is unlabeled because it does not
state the paper's definitions or theorems itself.

## 1. What mathematical content is in this file?

Very little direct mathematical content.

What is actually in `references/ldt-paper/multilinearity.tex`:

- document setup (`\documentclass`, `\usepackage{wright}`)
- macro definitions such as `\multi`, `\multimeas`, `\multisub`, `\polyfunc`, `\polymeas`,
  `\polysub`
- title, authors, and abstract
- table of contents
- `\input{...}` lines for the actual paper sections

Mathematical content present directly in this file is limited to the abstract-level statement of
the paper's main result: the two-player low individual degree test is quantum sound, sufficient to
recover applications including `MIP* = RE`.

There are no local definitions, lemmas, propositions, or proofs in this file.

## 2. Is it a standalone section or included by other files?

It is a standalone top-level root file, not a section included elsewhere.

Evidence:

- It begins with `\documentclass[11pt]{article}` and ends with `\end{document}`.
- It is not referenced by any `\input{multilinearity}` or `\include{multilinearity}` command in
  the repo.
- Instead, it includes the actual paper body files in this order:
  1. `introduction.tex`
  2. `test_definition.tex`
  3. `preliminaries.tex`
  4. `orthonormalization.tex`
  5. `inductive_step.tex`
  6. `expansion.tex`
  7. `self_improvement.tex`
  8. `commutativity-points.tex`
  9. `commutativity-G.tex`
  10. `ld-pasting.tex`

So the filename `multilinearity.tex` is legacy naming, not evidence of a current dedicated
"multilinearity chapter". The README in `references/ldt-paper/README.md` also points to an import
path containing `Multilinearity Rewrite`, which likely explains the retained filename.

## 3. Is there blueprint coverage of multilinearity concepts?

Not under the word "multilinearity", but yes indirectly through the general low individual degree
framework.

Findings:

- Searching `blueprint/` for `multilinear` or `multiline` returns no explicit multilinearity
  terminology.
- The blueprint instead works uniformly with the `(m,q,d)` low individual degree test.
- `blueprint/src/chapter/ch02_test.tex` defines the low individual degree test and states the main
  quantum soundness theorem.
- `blueprint/src/chapter/ch03_preliminaries.tex` defines `\polyfunc{m}{q}{d}` and proves the
  individual-degree Schwartz–Zippel lemma.

This matches the paper's actual mathematical stance: multilinearity is only the special case
`d = 1`. The imported paper introduction says exactly that the multilinearity test is the low
individual degree test when `d = 1`.

So:

- there is no separate blueprint chapter for "multilinearity";
- the blueprint already covers the underlying mathematics in more general form;
- multilinearity is present only implicitly as the `d = 1` specialization.

## 4. What Lean coverage exists?

No explicit multilinearity-specific Lean content is present.

Result of the requested codebase grep:

```text
rg -n -i "multilinear|multiline" MIPStarRE --glob '*.lean'
```

This returned no matches.

What does exist is low-individual-degree infrastructure under the more general terminology, for
example:

- `MIPStarRE/LDT/Basic/Parameters.lean`
- `MIPStarRE/LDT/Test/Defs.lean`
- `MIPStarRE/LDT/Preliminaries/Defs.lean`

So the formalization currently targets the general LDT story, not a separate named multilinearity
layer.

## 5. Does the formalization need this file?

Not as a formalization target.

What the project likely needs from `multilinearity.tex`:

- confirmation of the canonical paper input order
- the paper abstract and top-level framing
- a pointer that "multilinearity" is legacy naming and corresponds to the `d = 1` case

What the project does not need:

- a dedicated Lean formalization of `multilinearity.tex` itself
- a separate blueprint chapter just for this file

Practical conclusion:

- Treat `multilinearity.tex` as the root source file for the paper mirror.
- Continue formalizing the included section files and the blueprint chapters.
- Only add explicit multilinearity aliases if the project wants a documented `d = 1` specialization
  for navigation or naming consistency.

## Recommendation

This is not a gap in the mathematical formalization. It is mostly a naming and source-organization
issue.

Recommended status:

- `multilinearity.tex`: covered as source root, not as chapter
- blueprint multilinearity coverage: implicit via general `(m,q,d)` treatment
- Lean multilinearity coverage: no explicit naming, but likely subsumed by the existing LDT APIs

If desired, a small follow-up doc improvement would be to update `references/ldt-paper/README.md`
to say plainly that `multilinearity.tex` is the paper's root TeX file.
