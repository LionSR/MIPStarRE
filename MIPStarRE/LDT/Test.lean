import MIPStarRE.LDT.Test.Defs
import MIPStarRE.LDT.Test.Strategy
import MIPStarRE.LDT.Test.MainTheorem

/-!
# Section 3 – Test Definition Scaffold

Matching scaffold for Section 3 of the low individual degree paper
(`references/ldt-paper/test_definition.tex`).

The content is split into three submodules:

* `Test.Defs` – evaluation helpers, consistency/distance defects,
  mass/boundedness notions, and polynomial consistency predicates.
* `Test.Strategy` – strategy structures (`SymmetricStrategy`,
  `ProjectiveStrategy`), sampled answer families, failure probabilities,
  and `IndexedPolynomialFamily`.
* `Test.MainTheorem` – `Test.mainFormalError` and
  the `Test.mainFormal` theorem scaffold.
-/
