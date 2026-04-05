# Blueprint Style Audit

Audit scope:
- `docs/blueprint_style_guide.md`
- `blueprint/src/chapter/ch01_overview.tex` through `blueprint/src/chapter/ch10_induction.tex`
- `blueprint/src/macros/common.tex`

## Findings

### Filler prose / non-blueprint exposition

- `blueprint/src/chapter/ch01_overview.tex:4`
  Problematic text: `This blueprint is organized by theorem ownership and proof dependency ...`
  Fix: remove this project-organization paragraph from the reader-facing blueprint, or replace it with a terse mathematical roadmap outside the blueprint proper. The style guide asks for definitions, statements, and proof sketches only.

- `blueprint/src/chapter/ch02_test.tex:15`
  Problematic text: `This is the textual form of the boxed figure in the source paper.`
  Fix: delete this sentence. If the figure content matters, keep only the formal definition in [ch02_test.tex](../../blueprint/src/chapter/ch02_test.tex).

- `blueprint/src/chapter/ch02_test.tex:32`
  Problematic text: `Using notation which will be introduced in Chapter...`
  Fix: remove the forward-looking remark. Keep the formal characterization as the lemma in Chapter 3, or restate it there only.

- `blueprint/src/chapter/ch02_test.tex:48`
  Problematic text: `Our proof is by induction... To do this, we frequently use...`
  Fix: replace the motivational paragraph with a short notational definition only, e.g. define `B_f^u` for vertical lines without the induction commentary.

- `blueprint/src/chapter/ch03_preliminaries.tex:164`
  Problematic text: `In particular, if ... the question is what hypothesis ... allows one to conclude ...`
  Fix: delete this expository bridge sentence and let Lemma `prop:triangle-sub` follow directly after the definitions.

- `blueprint/src/chapter/ch06_variance.tex:49`
  Problematic text: `We note that ... This can be viewed as a local-variance bound ...`
  Fix: either remove the paragraph or fold the displayed identity into the proof of `lem:local-variance-of-points` as a direct reformulation.

- `blueprint/src/chapter/ch09_pasting.tex:191`
  Problematic text: `We first record the natural construction ... It motivates the eventual argument ...`
  Fix: remove this heuristic subsection from the blueprint, or replace it by a formal lemma/proof sketch that is actually used downstream.

- `blueprint/src/chapter/ch09_pasting.tex:195`
  Problematic text: `The first construction ... Its consistency is governed ... its completeness is subtler. The heuristic comparison is`
  Fix: remove the heuristic discussion or restate it as a precise lemma with a mathematical claim and proof sketch.

### Copy-from-paper / not in the blueprint's own voice

- `blueprint/src/chapter/ch04_projective.tex:373`
  Problematic text: `This is the Cauchy--Schwarz estimate from the paper...`
  Fix: state the actual estimate directly in blueprint voice and cite the lemma or inequality being applied, rather than deferring to the paper.

- `blueprint/src/chapter/ch07_self_improvement.tex:234,252,537`
  Problematic text: `The paper's arithmetic shows ...`, `which the paper bounds by ...`, `The paper's exponent bookkeeping then shows ...`
  Fix: replace each with the explicit inequality chain used here, or cite a precise earlier lemma in the blueprint that gives the bound.

- `blueprint/src/chapter/ch08_commutativity.tex:373`
  Problematic text: `exactly as in the paper.`
  Fix: replace with a one- or two-sentence summary of the bound accumulated from the preceding displayed estimates.

- `blueprint/src/chapter/ch09_pasting.tex:162,454,531,770,1176`
  Problematic text: `The paper estimates ...`, `The paper bounds ...`, `The paper's calculation gives ...`, `the paper estimates ...`, `The paper then absorbs ...`
  Fix: restate the actual bound in blueprint voice. If the estimate is nontrivial, add a lemma or cite a prior blueprint result instead of delegating to the paper.

- `blueprint/src/chapter/ch10_induction.tex:311,324`
  Problematic text: `The same computation as in the source paper ...`, `exactly as in the paper gives`
  Fix: write the unsymmetrization and Schwartz–Zippel argument as an actual proof sketch in the blueprint's own voice.

### `\uses{}` inaccuracies

- `blueprint/src/chapter/ch03_preliminaries.tex:124,170,182`
  Problematic text: statement `\uses{... prop:simeq-for-measurements}` on lemmas whose statements do not mention that lemma.
  Fix: remove `prop:simeq-for-measurements` from the statement `\uses{}` of `lem:good-strategy-characterization`, `prop:triangle-sub`, and `prop:simeq-to-approx`; it is a proof dependency, not a statement dependency.

- `blueprint/src/chapter/ch04_projective.tex:6`
  Problematic text: `\uses{def:submeasurement, lem:naimark-helper}`
  Fix: drop `lem:naimark-helper` from the statement `\uses{}` for `thm:naimark`; it is used only in the proof.

- `blueprint/src/chapter/ch04_projective.tex:26`
  Problematic text: `\uses{def:strong-self-consistency, def:approx_delta, lem:orthonormalization-main-lemma, prop:other-two-notions-of-self-consistency, def:measurement-completion}`
  Fix: keep only the definitions needed to state the theorem. `lem:orthonormalization-main-lemma`, `prop:other-two-notions-of-self-consistency`, and `def:measurement-completion` are proof dependencies.

- `blueprint/src/chapter/ch05_expansion.tex:77`
  Problematic text: `\uses{def:adjacency-laplacian, lem:character-average-vector, lem:character-average-scalar}`
  Fix: remove the character lemmas from the statement `\uses{}` for `prop:eigenvectors`; they are proof dependencies, not statement dependencies.

- `blueprint/src/chapter/ch05_expansion.tex:139`
  Problematic text: `\uses{prop:eigenvectors}`
  Fix: remove `prop:eigenvectors` from the statement `\uses{}` of `cor:laplacian-spectral-gap`; the statement only refers to the eigenvalues of `L`.

- `blueprint/src/chapter/ch05_expansion.tex:278`
  Problematic text: `\uses{cor:laplacian-spectral-gap, lem:local-rewrite, lem:global-rewrite}`
  Fix: replace this statement `\uses{}` with `\uses{def:local-and-variance}`. The current list is proof-only and also omits the definition actually needed to state the variance notation.

- `blueprint/src/chapter/ch06_variance.tex:60`
  Problematic text: `\uses{def:local-and-variance, lem:local-to-global, lem:local-variance-of-points}`
  Fix: remove `def:local-and-variance` from the statement `\uses{}` of `lem:global-variance-of-points`; the statement itself is phrased only in `\approx` notation.

- `blueprint/src/chapter/ch09_pasting.tex:8`
  Problematic text: `\uses{def:polymeasurements, def:simeq}`
  Fix: add `def:approx_delta`, since the theorem statement includes the strong self-consistency hypothesis `G_g^x \ot I \approx_\zeta I \ot G_g^x`.

- `blueprint/src/chapter/ch10_induction.tex:269`
  Problematic text: the proof `\uses{...}` for the proof of `thm:main-formal` omits `thm:main-induction`, even though the proof explicitly says `Theorem~\ref{thm:main-induction} applied to the symmetrized strategy...`
  Fix: add `thm:main-induction` to the proof `\uses{}` list.

### `\lean{...}` tags that do not match current Lean declarations

- `blueprint/src/chapter/ch03_preliminaries.tex:93`
  Problematic text: `\lean{MIPStarRE.LDT.Preliminaries.postProcessing}`
  Fix: point this tag to the real declaration name, which in the current codebase is `postprocess` rather than `postProcessing`, or add a Lean wrapper with the advertised name.

- `blueprint/src/chapter/ch03_preliminaries.tex:102`
  Problematic text: `\lean{MIPStarRE.LDT.Preliminaries.measurementCompletion}`
  Fix: point this tag to the actual completion declaration (`completeAtOutcome` in the current codebase), or add a wrapper theorem/definition with the advertised name.

- `blueprint/src/chapter/ch09_pasting.tex:134`
  Problematic text: `\lean{MIPStarRE.LDT.Pasting.ldPastingSubMeasurement}`
  Fix: rename the tag to `\lean{MIPStarRE.LDT.Pasting.ldPastingSubMeas}` or rename the Lean declaration to match.

### Mathematical language / software-like phrasing

- `blueprint/src/chapter/ch07_self_improvement.tex:6`
  Problematic text: `\section{Non-projective Output}`
  Fix: rename to a mathematical title such as `Non-projective Measurements` or `Self-improvement from a Measurement`.

- `blueprint/src/chapter/ch07_self_improvement.tex:76`
  Problematic text: `the technical transfer from the averaged family ...`
  Fix: replace with standard mathematical language such as `the averaging lemma that relates ...`.

- `blueprint/src/chapter/ch10_induction.tex:81`
  Problematic text: `completion bookkeeping ... because the output is projective ...`
  Fix: rewrite in mathematical terms, e.g. `the completion lemma transfers the estimates back to the original outcomes; since the resulting family is projective, Lemma ... identifies this with the usual strong self-consistency statement.`

### Notation / macro consistency

- `blueprint/src/chapter/ch08_commutativity.tex:21-33` and `blueprint/src/chapter/ch03_preliminaries.tex:430-452,530-536`
  Problematic text: use of raw `\otimes` despite the project macro `\ot`.
  Fix: normalize these occurrences to `\ot` for consistency with `blueprint/src/macros/common.tex`.

- `blueprint/src/chapter/ch05_expansion.tex:49,64,82,96,110,120,128`
  Problematic text: use of raw `\operatorname{tr}` even though `\tr` is defined in `common.tex`.
  Fix: replace `\operatorname{tr}` with `\tr` throughout this chapter.

### Label naming and theorem-label prefix consistency

- `blueprint/src/chapter/ch03_preliminaries.tex:138,169,180,293,304,315,327,352,383,410,418,438,455,466,517`
  Problematic text: lemma environments labeled with `prop:` prefixes, e.g. `\begin{lemma}[Consistency for measurements]\label{prop:simeq-for-measurements}`.
  Fix: rename these labels to `lem:...` to match the style guide's required label prefixes for lemmas.

- `blueprint/src/chapter/ch05_expansion.tex:34,75,137`
  Problematic text: lemma environments labeled `prop:laplacian-rewrite`, `prop:eigenvectors`, and `cor:laplacian-spectral-gap`.
  Fix: rename these to `lem:...` unless the environment itself is changed to theorem/corollary for a mathematically justified reason.

- `blueprint/src/chapter/ch08_commutativity.tex:163,195`
  Problematic text: labels `clm:g-comm-stability` and `clm:g-comm-stability2`.
  Fix: rename to `lem:g-comm-stability` and `lem:g-comm-stability2` to follow the guide's label-prefix rule.

- `blueprint/src/chapter/ch03_preliminaries.tex:477`
  Problematic text: `\label{eq;what-we-want-to-prove-but-on-wrong-side}`
  Fix: change the prefix to `eq:` and give it a mathematical name.

- `blueprint/src/chapter/ch05_expansion.tex:192`, `blueprint/src/chapter/ch06_variance.tex:76`, `blueprint/src/chapter/ch07_self_improvement.tex:95,112,125,155,160,193,199,210`, `blueprint/src/chapter/ch08_commutativity.tex:126,145,340,355`, `blueprint/src/chapter/ch09_pasting.tex:205,211,216,223,379,577,725,852,880,947,989,1028,1136`, `blueprint/src/chapter/ch10_induction.tex:251,366`
  Problematic text: placeholder or jokey internal labels such as `eq:reader-probably-has-no-idea-whats-going-on-yet`, `eq:TODO:bound-this!`, `eq:release-the-kraken`, `eq:dumbo-bound-for-idiots`, and `eq:just-data-processed-the-heck-outta-this`.
  Fix: rename these to short mathematical labels describing the content of the equation. Internal labels are not reader-facing, but the style guide still asks new labels to follow the standard.

## Checklist items with no finding

- I did **not** find duplicate `\label{...}` names across `ch01` through `ch10`.
- I did **not** find definite Lean identifiers leaking into prose outside `\lean{...}` tags.
- I did **not** find banned table terms such as `pipeline`, `bridge`, `handoff`, `assembly`, `honest`, `glue layer`, `re-export`, or `wiring` in the chapter text.

## Notes

- Historical `\begin{proposition}` usage remains in `ch03_preliminaries.tex`, but from the snapshot alone I cannot tell which proposition blocks are legacy and which are new. I therefore did not classify every existing `proposition` as a new-addition finding, even though the current style guide says not to introduce new proposition environments.
