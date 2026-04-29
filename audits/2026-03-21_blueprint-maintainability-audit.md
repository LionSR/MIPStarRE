---
title: Blueprint maintainability audit
date: 2026-03-21
purpose: >
  Audits blueprint maintainability issues and records structural cleanup
  tasks for theorem dependencies, labels, and reader navigation.
status: snapshot
track: paper2009ldt
kind: maintainability-audit
---

# Structural issues

_Dated audit snapshot: this note records a 2026-03-21 maintainability review of the blueprint. It is preserved as a point-in-time audit, so later fixes and renames may supersede some specific file-path observations._

The chapter split is mostly sound. I did not find broken `\uses` references, and I did not find a bad ownership choice for the duplicated pasting theorem: the single blueprint node for `thm:ld-pasting` is still safe against the source paper. The main structural problems are dependency bookkeeping, label hygiene, and stale support notes.

- `\uses` is being used with two different meanings. Some nodes use theorem-level `\uses` for statement dependencies and proof-level `\uses` for proof dependencies, as in `thm:orthonormalization` and `thm:self-improvement`. Many others put proof dependencies on the theorem line and leave the proof with no `\uses`, as in `lem:local-to-global`, `lem:generalize-b`, and `thm:commutativity-points`. Only 9 of the 62 proof environments currently carry a proof-level `\uses`. That makes the graph harder to trust and harder to maintain.

- Many statement nodes are missing direct dependencies required by their own notation. Concrete examples:
  - `ch02_test.tex`, `thm:main-formal` uses `\simeq` and low-degree polynomial measurement notation, but only declares `\uses{def:projective-strategy}`.
  - `ch07_self_improvement.tex`, `thm:self-improvement` and `ch10_induction.tex`, `thm:self-improvement-in-induction-section` use `\approx` in the statement but do not declare `def:approx_delta`.
  - `ch09_pasting.tex`, `thm:ld-pasting` uses `\approx` in item 3 but does not declare `def:approx_delta`.
  - `ch09_pasting.tex`, `lem:from-H-to-G` refers to `\mathsf{Outcomes}_\tau` but does not declare `def:outcomes-by-type`.
  These omissions do not break compilation, but they do make the dependency graph semantically inaccurate.

- Label prefixes do not match the actual environments. I counted 26 mismatches: 20 `prop:` labels attached to `lemma` environments and 6 `cor:` labels attached to `lemma` environments. Examples include `prop:simeq-for-measurements`, `prop:eigenvectors`, `cor:laplacian-spectral-gap`, and `cor:ld-pasting-N-completeness`. The style guide explicitly asks for label prefixes that match the environment. Right now the label taxonomy is halfway between the source paper and the local blueprint convention.

- `thm:main-formal` is still a theorem-first exception, but the graph does not admit that honestly. The theorem is placed before the notation chapter that defines the comparison symbols and low-degree measurement notation it uses. That can be a reasonable expositional choice, but the current `\uses` list hides the exception instead of documenting it.

- The support notes under `docs/` are partly stale relative to the active blueprint. `audits/2026-03-20_ldt-source-map.md` still says the blueprint uses a single `thm:self-improvement` node carrying both Lean links. The active blueprint now has a separate `thm:self-improvement-in-induction-section` node in `ch10_induction.tex`. `audits/2026-03-20_ldt-blueprint-dependency-review.md` still treats the merged self-improvement node and the missing Schwartz–Zippel edge as open problems, but both are already fixed in the active blueprint. That makes the maintenance notes unreliable as a guide to the current state.

# Readability and style issues

- Several statements are not self-contained in the way the style guide asks for. Chapter 7 opens with a standing assumption on `(\psi,A,B,L)`, and the results in that chapter then use `A_a^u` without restating the ambient strategy. Chapter 9 repeatedly says “Under the hypotheses of Theorem~\ref{thm:ld-pasting}” instead of stating the assumptions locally. This is manageable in the PDF, but it is poor for node-by-node reading in the web graph.

- The proof of `thm:self-improvement-in-induction-section` in `ch10_induction.tex` is not really a proof sketch. It discusses `\texttt{inductive\_step.tex}` and chapter organization instead of the mathematical reduction. The intended sketch is short and mathematical: complete the input submeasurement to a measurement, apply the measurement-level self-improvement theorem, then transfer the result back using completion and data-processing lemmas.

- The bibliography is too thin for the prose. `references.bib` has only four entries. The blueprint cites Kempe--Vidick for orthogonalization and Schwartz–Zippel for the polynomial bound, but later chapters use substantial outside material without saying so: the NW19-style measurement-comparison background mirrored by `preliminaries.tex`, the scalar Chernoff input used in `lem:chernoff-bernoulli-matrix`, and the convex-optimization background behind `lem:sdp`.

- A few internal labels are much noisier than the surrounding prose. `lem:looks-easy-but-took-me-a-while`, `def:G-hat`, `cor:G-hat-facts`, and `prop:ld-dnoteq` are workable as internal identifiers, but they are not the kind of stable, descriptive labels the style guide asks for.

- `macros/common.tex` still defines a `proposition` environment even though the local style guide says not to use propositions. The active chapter files avoid that environment, but the macro file still advertises an older convention.

# Maintainability risks

- Chapter 4 still hides a large amount of proof burden behind `lem:orthonormalization-main-lemma`. The source file `orthonormalization.tex` contains a long internal chain before that lemma closes. As a high-level blueprint this compression is understandable, but it will age badly once real proof filling starts: contributors will underestimate how much work sits behind one node.

- The same risk appears in Chapter 7 and Chapter 9 for `lem:sdp`, `lem:from-H-to-G`, and `lem:chernoff-bernoulli-matrix`. These are not routine one-lemma tasks. If the blueprint keeps them as single nodes, it at least needs explicit citations or an internal checklist so later maintainers know what mathematical subproblems are bundled inside.

- Because many helper nodes inherit hypotheses from a chapter preamble or from `thm:ld-pasting`, small changes to one umbrella hypothesis will force a broad manual audit. That is exactly the kind of hidden coupling that makes blueprints drift.

- The duplicated pasting statement is handled correctly today, but it will need continued auditing. The node `thm:ld-pasting` carries two Lean declarations. If one of those declarations changes later while the other does not, the blueprint could hide the divergence unless someone checks both on purpose.

- The stale source-map and dependency-review notes are themselves a maintenance hazard. A future contributor could easily “fix” the blueprint back toward an already-resolved issue because the surrounding documentation still describes the old structure.

# Recommended fixes before serious proof filling

1. Standardize `\uses` now. Pick one convention and apply it everywhere: theorem-level `\uses` for statement dependencies only, proof-level `\uses` for proof dependencies. Then do one cleanup pass to add missing direct notation dependencies such as `def:approx_delta`, `def:simeq`, and `def:outcomes-by-type`.

2. Fix the label taxonomy. Either rename the `prop:` and `cor:` labels to match the current `lemma` environments, or change the environments consistently if you want corollaries to stay corollaries. Right now the labels encode an obsolete convention.

3. Refresh `audits/2026-03-20_ldt-source-map.md` and `audits/2026-03-20_ldt-blueprint-dependency-review.md` so they describe the current active blueprint, especially the now-split self-improvement node and the already-added Schwartz–Zippel edge.

4. Decide what to do about `thm:main-formal`. Either move the formal theorem after the notation chapter, or explicitly document that Chapter 2 is a deliberate theorem-first exception and give it the missing forward dependencies honestly.

5. Rewrite the proof sketch of `thm:self-improvement-in-induction-section` into mathematical prose and remove the source-file name from the body text.

6. Make the most important nodes more self-contained. The first places to fix are Chapter 7 and the Chapter 9 helper lemmas currently phrased as “Under the hypotheses of Theorem~\ref{thm:ld-pasting}”.

7. Expand the bibliography before proof work goes deeper into Chapters 7 and 9. At minimum add the measurement-comparison source used in the preliminaries, a scalar Chernoff reference, and an SDP duality/complementary-slackness reference.

8. Add an explicit subgoal note or internal checklist for `lem:orthonormalization-main-lemma`, `lem:sdp`, `lem:from-H-to-G`, and `lem:chernoff-bernoulli-matrix`. Those are the places where the current blueprint is most likely to understate the real work.
