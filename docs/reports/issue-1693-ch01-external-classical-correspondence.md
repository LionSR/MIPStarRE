# Chapter 1 External Classical Correspondence

This note records the dependency-graph repair for the Chapter 1 external
classical soundness nodes.

## Source comparison

| Node | Public graph status | Paper source | Lean declaration | Classification | Repair |
| --- | --- | --- | --- | --- | --- |
| `thm:raz-safra` | Source theorem linked to a Lean declaration, but not formalized | `references/ldt-paper/introduction.tex:43-65` | `MIPStarRE.LDT.Test.razSafra` | Conditional interface | Remove the direct Lean link from the source theorem and add a separate Lean-only conditional corollary with the explicit external hypothesis displayed. |
| `thm:classical-test-soundness` | Source theorem linked to a Lean declaration, but not formalized | `references/ldt-paper/introduction.tex:69-92` | `MIPStarRE.LDT.Test.classicalTestSoundness` | Conditional interface | Remove the direct Lean link from the source theorem and add a separate Lean-only conditional corollary with the explicit external hypothesis displayed. |

## Mathematical content

Both paper theorems are quoted external classical results.  The repository does
not prove Raz--Safra or Polishchuk--Spielman internally.  Instead, Lean keeps
the external result as an explicit specialized hypothesis:

- `RazSafraSoundnessStatement` for the surface-versus-point low-degree test;
- `PolishchukSpielmanClassicalSoundnessStatement` for the low individual degree
  test.

The theorems `razSafra` and `classicalTestSoundness` are therefore conditional
corollaries: they apply the corresponding specialized external hypothesis to
the modeled pass condition.  They are useful Lean interfaces, but they are not
the source theorems themselves.

## Statement integrity audit

### `thm:raz-safra`

Paper assumptions:

- a two-prover strategy passes the \(k=2\) surface-versus-point low-degree test
  with probability \(1-\varepsilon\).

Lean conditional-interface assumptions:

- `SurfaceVsPointPassCondition params a eps`;
- `RazSafraSoundnessStatement params a eps (razSafraSlackBound params eps)`.

Paper conclusion:

- there exists a degree-\(d\) polynomial agreeing with the point answers with
  error at most \(\varepsilon + \operatorname{poly}(m)\operatorname{poly}(d/q)\).

Lean conditional-interface conclusion:

- there exists `slack` satisfying
  `PointAnswerSoundnessConclusion params a (razSafraSlackBound params eps)
  slack`.

Verdict: conditional interface, not the source theorem.

### `thm:classical-test-soundness`

Paper assumptions:

- a two-prover strategy passes the low individual degree test with probability
  \(1-\varepsilon\).

Lean conditional-interface assumptions:

- `TwoProverClassicalLIDPassCondition params a eps`;
- `PolishchukSpielmanClassicalSoundnessStatement params a eps slackBound`.

Paper conclusion:

- there exists an individual-degree-\(d\) polynomial agreeing with the point
  answers with error
  \(\operatorname{poly}(m)(\operatorname{poly}(\varepsilon)+
  \operatorname{poly}(d/q))\).

Lean conditional-interface conclusion:

- there exists `slack` satisfying
  `PointAnswerSoundnessConclusion params a slackBound slack`.

Verdict: conditional interface, not the source theorem.
