# Lean 4.35.0-rc2 module port: statement integrity

The comparison base is upstream commit
`507e81220d95266ff3d589d125b2f87c7300a9fb`. The mechanical port was recovered
from `Dengnifer/MIPStarRE-QPBT` at
`f7e14c98fb4b75394b516a662e80b1fdb5a09884`. Lean and Mathlib are pinned to
`v4.35.0-rc2` so that the two developments can eventually share a Lake build.

The mathematical declarations retain their statements. Module headers,
public imports, exposed definitions, and meta declarations replace the former
implicit visibility rules. Proof changes accommodate elaboration, simplification,
and Mathlib API changes. In particular, a proof supplied to an exposed structure
definition may need an explicit `by` block to refer to a private theorem.

A comparison of 4,112 normalized declaration headers found no removed
declarations. Apart from visibility and reducibility annotations, the only
changed signature text makes the already existing section variables explicit
in `Quantum.Submeasurement.postprocess` and `Quantum.Measurement.postprocess`.
The types and binder order are preserved. The explicit finite enumeration of
`Role` replaces its derived `Fintype` instance. The new private lemma
`axisParallelBaseLineEvent_some` isolates a simplification step in the existing
point-line comparison; it introduces no hypothesis to a public theorem.

The source-labelled header guard reports no changed public statements. Thus
the paper assumptions, Lean assumptions, paper conclusions, and Lean conclusions
of those entries are identical to their respective versions at the comparison
base. This is a preservation audit, not a new claim that every existing Lean
statement is identical to the printed paper.

For the headline theorem, the comparison is explicit:

| Item | Statement |
| --- | --- |
| Paper assumptions | A projective strategy passes the low individual degree test with probability at least `1 - ε`; the integer `k` satisfies `k ≥ md`. |
| Lean assumptions | The same finite-field and finite-dimensional strategy data, test failure at most `ε`, and the existing corrected conditions `k ≥ 400md` and `0 < k`. |
| Paper conclusion | Two projective polynomial measurements satisfy the two point-consistency conclusions and mutual consistency at the displayed error `ν`. |
| Lean conclusion | The same three conclusions at `mainFormalError`, with unchanged quantifiers, measurements, and error expression. |
| Verdict | Exact preservation of the upstream Lean statement; the existing differences from the printed hypotheses remain documented below. |

The source is `references/ldt-paper/test_definition.tex:180–202`, with proof in
`references/ldt-paper/inductive_step.tex:26–236`. The existing numerical and
zero-sampling corrections are explained in
`docs/paper-gaps/issue-906-main-formal-k-bound.tex` and
`docs/paper-gaps/issue-422-main-formal-zero-k-boundary.tex`. This port changes
neither correction and adds no bridge, conditional input, axiom, or proof hole.

The QPBT strategy and its additional transport lemmas, quantitative measurement
estimates, and sharper consistency bounds are excluded. They can be considered
separately after this upgrade.
