# Chapter 1 External Classical Correspondence

This note records the dependency-graph repair for the Chapter 1 external
classical soundness nodes.

## Source comparison

| Node | Public graph status | Paper source | Lean declaration | Classification | Repair |
| --- | --- | --- | --- | --- | --- |
| `thm:classical-test-soundness` | Source theorem linked to a Lean declaration, but not formalized | `references/ldt-paper/introduction.tex:69-92` | `MIPStarRE.LDT.Test.classicalTestSoundness` | Conditional interface | Remove the direct Lean link from the source theorem and add a separate Lean-only conditional corollary with the explicit external hypothesis displayed. |

## Mathematical content

The paper theorem is a quoted external classical result.  The repository does
not prove Polishchuk--Spielman internally.  Instead, Lean keeps the external
result as an explicit specialized hypothesis:

- `PolishchukSpielmanClassicalSoundnessStatement` for the low individual degree
  test.

The theorem `classicalTestSoundness` is therefore a conditional corollary: it
applies the specialized external hypothesis to the modeled pass condition.  It
is a useful Lean interface, but it is not the source theorem itself.

## Statement integrity audit

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
