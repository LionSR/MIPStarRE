import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Basic
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Handoff
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.MatchMass
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Line169Repair
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain.Output

/-!
# Section 10 — Step 6 projectivization chain

Compatibility module for the orthonormalize-and-complete chain used in Step 6
of the main inductive step.  The scalar and transport facts, handoff lemmas,
match-mass interfaces, line-169 repair, and output theorem are now separated
into reviewable leaf modules under `ProjectivizationChain/`.
-/
