import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Basic
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Handoff
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.MatchMass
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Line169Repair
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Output

/-!
# Section 5 — orthonormalization projectivization chain

Compatibility module for the orthonormalize-and-complete chain used in the main
inductive step.  The scalar and transport facts, handoff lemmas, completion
match-mass helper, repaired completion transport, and output theorem are now
separated into reviewable leaf modules under `ProjectivizationChain/`.
-/
