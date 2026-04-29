---
title: LDT source map
date: 2026-03-20
purpose: >
  Maps the LDT paper sources to blueprint chapters and Lean ownership points
  so contributors can locate theorem statements and proof obligations.
status: current
track: paper2009ldt
kind: source-map
---

# LDT source map (2026-03-20)

Source mirror used: `MIPStarRE/references/ldt-paper/`.

## Input order from `multilinearity.tex`

`multilinearity.tex` inputs the body files in the following order:

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

This is the paper order, not the proof-dependency order. In particular, `inductive_step.tex` states the main induction theorem and the two internal black-box steps before the later files prove the variance, self-improvement, commutativity, and pasting machinery those statements require.

## Major labeled results and where they live

| Label | File | Section / subsection | Role |
|---|---|---|---|
| `thm:raz-safra` | `introduction.tex` | Introduction | Classical low-degree test context |
| `thm:classical-test-soundness` | `introduction.tex` | Introduction | Classical axis-parallel soundness benchmark |
| `thm:main-informal` | `introduction.tex` | Introduction | Informal statement of the quantum soundness result |
| `thm:main-formal` | `test_definition.tex` | `\section{The test}` | Formal two-prover soundness target |
| `thm:naimark` | `orthonormalization.tex` | `\section{Making measurements projective}` | Projectivization by dilation |
| `thm:orthonormalization` | `orthonormalization.tex` | `\section{Making measurements projective}` | Projectivization from strong self-consistency |
| `thm:main-induction` | `inductive_step.tex` | `\section{The main induction step}` | Inductive production of a global polynomial measurement |
| `thm:self-improvement-in-induction-section` | `inductive_step.tex` | `\subsection{Self-improvement and pasting}` | Inductive self-improvement step, stated before proof |
| `thm:ld-pasting-in-induction-section` | `inductive_step.tex` | `\subsection{Self-improvement and pasting}` | Inductive pasting step, stated before proof |
| `thm:self-improvement` | `self_improvement.tex` | `\subsection{Self-improving to a projective measurement}` | Restatement and proof of the self-improvement step |
| `thm:commutativity-points` | `commutativity-points.tex` | `\section{Commutativity of the points measurements}` | Approximate commutation of point measurements |
| `thm:com-main` | `commutativity-G.tex` | `\subsection{Commutativity of~$G$}` | Approximate commutation of slice measurements |
| `thm:ld-pasting` | `ld-pasting.tex` | `\section{Pasting}` | Restatement and proof of the pasting step |

Important major support lemmas that sit on the critical path:

| Label | File | Section / subsection | Role |
|---|---|---|---|
| `prop:simeq-data-processing` | `preliminaries.tex` | `\subsubsection{Consistency between measurements}` | Post-processing stability for consistency |
| `lem:orthonormalization-main-lemma` | `orthonormalization.tex` | `\subsection{Orthogonalization lemma}` | Measurement version used to prove `thm:orthonormalization` |
| `lem:local-to-global` | `expansion.tex` | `\subsection{Local and global variance}` | Expander inequality turning local variance into global variance |
| `lem:global-variance-of-points` | `expansion.tex` | `\section{Global variance of the points measurements}` | Global variance bound for point evaluations against a slice measurement |
| `lem:self-improvement-helper` | `self_improvement.tex` | `\section{Self-improvement}` | Non-projective self-improvement output before orthonormalization |
| `lem:comm-data-processed-g` | `commutativity-G.tex` | `\subsection{Commutativity of~$G$ after evaluation}` | Commutes the evaluated slice measurements |
| `lem:h-b-consistency` | `ld-pasting.tex` | `\subsection{Consistency of~$H$ with~$A$}` | Consistency of the pasted object with the line measurement |
| `lem:from-H-to-G` | `ld-pasting.tex` | `\subsection{Completeness of~$H$}` | Rewrites pasted completeness as a polynomial in the aggregate operator `G` |
| `cor:ld-pasting-N-completeness` | `ld-pasting.tex` | `\subsection{Completeness of~$H$}` | Final completeness estimate for the pasted submeasurement |
| `lem:restricted-probabilities` | `inductive_step.tex` | `\subsection{Proof of \Cref{thm:main-induction}}` | Transfers average slice error bounds into the induction step |

## How the later files refine the induction chain

The induction theorem in `inductive_step.tex` has the following schematic form:

1. restrict an `(m+1,q,d)` strategy to each height `x \in \F_q`;
2. apply the induction hypothesis at dimension `m` to obtain one slice measurement `G^x` per height;
3. improve each `G^x` so that its consistency error becomes incompleteness;
4. paste the family `\{G^x\}` into a single global measurement in dimension `m+1`.

The four later files named in the task refine those steps as follows.

### `self_improvement.tex`

This file resolves step 3. It first proves `lem:self-improvement-helper`, which constructs a non-projective submeasurement
\[
H_h = \mathbb E_u\, A^u_{h(u)} T_h A^u_{h(u)}
\]
from an SDP optimum `T`. The variance estimates from `expansion.tex` enter through `lem:add-in-u`, which is the bookkeeping lemma that lets one replace an averaged sandwich by a same-point sandwich. The file then upgrades the non-projective output to the final projective theorem `thm:self-improvement` by applying `thm:orthonormalization` and transferring consistency, completeness, and boundedness across that approximation.

### `commutativity-points.tex`

This file is the first commutation input for pasting. It proves `thm:commutativity-points`, which says that point measurements at independent points approximately commute. The proof uses the diagonal-lines test, so this file converts the diagonal-line part of the test into the algebraic commutation estimate later needed to reorder slice factors.

### `commutativity-G.tex`

This file lifts point commutativity to slice commutativity. First, `lem:comm-data-processed-g` shows that the evaluated slice measurements
\[
G^{u,x}_a := G^x_{[g(u)=a]}
\]
approximately commute. Then `thm:com-main` upgrades that to approximate commutativity of the full slice submeasurements `G_g^x` and `G_h^y`. This is exactly the input needed in `ld-pasting.tex` to commute factors through the sandwiched products that define the pasted measurement.

### `ld-pasting.tex`

This file resolves step 4. It has two layers.

- First, it proves the submeasurement result `lem:ld-pasting-sub-measurement`.
- Then it turns that submeasurement into the full pasting theorem `thm:ld-pasting` by adding the missing mass to one distinguished outcome.

Inside that proof, the file refines the chain further:

1. derive the preliminary slice-to-line consistency bound `G^x_{[g(u)=a]} \simeq B^u_{[f(x)=a]}`;
2. complete each slice measurement by adding the extra outcome `\bot`, giving `\widehat G`;
3. prove strong self-consistency and commutation for `\widehat G` (`lem:g-complete-self-consistency`, `cor:g-bot-self-consistency`, `cor:G-hat-facts`);
4. control the sandwiched products by commuting one distinguished factor to the front (`lem:commute-g-half-sandwich`, `lem:ld-sandwich-line-one-point`);
5. deduce consistency of the pasted object with the line measurement and then with the point measurement (`lem:h-b-consistency`, followed inside the proof of `lem:ld-pasting-sub-measurement`);
6. analyze completeness by first summing over all tuples of outcomes (`lem:over-all-outcomes`), then rewriting that sum as a Bernoulli polynomial in the aggregate operator `G` (`lem:from-H-to-G`), and finally applying the matrix Chernoff estimate (`lem:chernoff-bernoulli-matrix`, `cor:ld-pasting-N-completeness`).

So the real induction chain is not just
\[
\text{induction hypothesis} \to \text{self-improvement} \to \text{pasting}.
\]
It is more precisely
\[
\text{induction hypothesis} \to \text{variance} \to \text{self-improvement} \to \text{point commutativity} \to \text{slice commutativity} \to \text{sandwiched consistency} \to \text{Chernoff-controlled completeness} \to \text{pasting}.
\]

## Blueprint matching decisions

The rebuilt blueprint under `MIPStarRE/blueprint/src/` now keeps separate nodes when duplicated source statements are not literally identical, and a shared node only when the mathematical statement is genuinely the same.

- the self-improvement theorem is now split:
  - `thm:self-improvement` points to
    `MIPStarRE.Paper2009LDT.Section9SelfImprovement.selfImprovement`;
  - `thm:self-improvement-in-induction-section` points to
    `MIPStarRE.Paper2009LDT.Section6MainInductionStep.selfImprovementInInductionSection`.
  This avoids hiding the `\polysub` versus `\polymeas` hypothesis mismatch.
- the blueprint theorem labeled `thm:ld-pasting` still carries both Lean links
  `MIPStarRE.Paper2009LDT.Section6MainInductionStep.ldPastingInInductionSection` and
  `MIPStarRE.Paper2009LDT.Section12Pasting.ldPasting`, because that duplication is still treated as a single mathematical statement.

This keeps the dependency graph honest without duplicating nodes unnecessarily.

## Blueprint build status

Build attempted from the repo root on 2026-03-20 with `leanblueprint pdf`.

- Status: succeeded.
- Output: `MIPStarRE/blueprint/print/print.pdf`.
- Follow-up housekeeping: refreshed `MIPStarRE/blueprint/src/web.bbl` from the generated `print.bbl` so the web build sees the same bibliography.
- Remaining build noise: only minor overfull-box warnings from long theorem headings and formulas; no blocking LaTeX errors remained.
