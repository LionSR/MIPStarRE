# Issue #218 Investigation: `G` Hypothesis in Commutativity

Date: 2026-04-09

## Conclusion

This issue appears to already be addressed in the current codebase. No Lean code
change is needed in `Commutativity/Theorems.lean` or `Commutativity/Defs.lean`.

## Findings

1. `CommDataProcessedGConclusion` still stores the link from the explicit
   parameter `G` back to the family via
   `familyG : ∀ x, G x = (family.meas x).toSubMeas`.
   Source: `MIPStarRE/LDT/Commutativity/Theorems.lean:57-93`.

2. `commDataProcessedG` already requires the corresponding hypothesis
   `hG : ∀ x, G x = (family.meas x).toSubMeas` and immediately packages it into
   the conclusion as `familyG := hG`.
   Source: `MIPStarRE/LDT/Commutativity/Theorems.lean:133-172`.

3. `comMain` also already takes the same hypothesis
   `hG : ∀ x, G x = (family.meas x).toSubMeas` and forwards it to
   `commDataProcessedG`.
   Source: `MIPStarRE/LDT/Commutativity/Theorems.lean:323-350`.

4. In `Commutativity/Defs.lean`, the only remaining bare uses of `G` are the
   four internal stability-family constructors:
   `commDataProcessedGStabilityOneLeft`,
   `commDataProcessedGStabilityOneRight`,
   `commDataProcessedGStabilityTwoLeft`,
   `commDataProcessedGStabilityTwoRight`.
   Source: `MIPStarRE/LDT/Commutativity/Defs.lean:330-388`.

5. Those `Defs.lean` declarations are low-level operator-family constructors,
   not theorem statements. They expose `G` as an input because the actual
   operator weights are written in terms of `G`, but they do not themselves
   assert any theorem-level hypotheses. The theorem layer in
   `Commutativity/Theorems.lean` is where the linkage hypothesis belongs, and it
   is already present there.

6. Downstream consumers use the packaged theorem conclusion rather than
   reintroducing an unconstrained theorem statement. For example,
   `Pasting/Theorems.lean` takes
   `hcom : Commutativity.ComMainConclusion params strategy family G gamma zeta`.
   Source: `MIPStarRE/LDT/Pasting/Theorems.lean:702-711`.

## Close-Worthy Comment

Suggested issue comment:

> Investigated in the current branch: this looks already fixed. Both
> `commDataProcessedG` and `comMain` require
> `hG : ∀ x, G x = (family.meas x).toSubMeas`, and `commDataProcessedG`
> packages that back into `CommDataProcessedGConclusion.familyG`. The only bare
> `G` parameters left in `Commutativity/Defs.lean` are internal operator-family
> constructors for the two stability steps, not theorem statements. I do not see
> a remaining theorem-level API that exposes an unconstrained `G`, so this issue
> looks close-worthy.
