import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.Core.BernoulliTail
import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.Core.AveragesAndOps
import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.Core.StageMass
import MIPStarRE.LDT.Pasting.Bernoulli.FromHToG.Core.FactBundles

/-!
# Section 12 pasting: from-H-to-G bridge (compatibility module)

This file re-exports all `fromHToG` core lemmas from four submodules:

* `BernoulliTail` — Finset re-indexing and cardinality-grouping lemmas for the
  Bernoulli-tail operator endpoint
* `AveragesAndOps` — average operators, tensor placement, projective
  submeasurement algebra, and GHatMeas sums
* `StageMass` — stage-0 identification, terminal identification,
  adjacent-stage split, and telescoping lemmas
* `FactBundles` — Prop-bundle structures and the paper-total error absorption
  lemma

External code should keep importing this module.
-/
