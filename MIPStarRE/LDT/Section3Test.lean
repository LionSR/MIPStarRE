import MIPStarRE.LDT.Section3Test.Defs
import MIPStarRE.LDT.Section3Test.Strategy
import MIPStarRE.LDT.Section3Test.MainTheorem

/-!
# Section 3 – Test Definition Scaffold

Matching scaffold for Section 3 of the low individual degree paper
(`references/ldt-paper/test_definition.tex`).

The content is split into three submodules:

* `Section3Test.Defs` – evaluation helpers, consistency/distance defects,
  mass/boundedness notions, and polynomial consistency predicates.
* `Section3Test.Strategy` – strategy structures (`SymmetricStrategy`,
  `ProjectiveStrategy`), sampled answer families, failure probabilities,
  and `IndexedPolynomialFamily`.
* `Section3Test.MainTheorem` – `Section3Test.mainFormalError` and
  the `Section3Test.mainFormal` theorem scaffold.
-/
