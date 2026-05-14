# Issue #1586: `sorryAx` Inventory

Date: 2026-05-14.

This note records the current `sorryAx` frontier in the LDT formalization.
In Lean, a source-level `sorry` elaborates to the kernel axiom `sorryAx`.
Thus `sorryAx` in a transitive axiom report is not, by itself, evidence that an
agent introduced a separate `axiom` declaration.  It is the expected marker for
an unfinished proof.  For a paper-facing theorem, this is preferable to adding
a non-paper bridge, residual, repair, package, witness, or hypotheses bundle to
the theorem statement.

The command

```bash
rg -n "^\s*sorry\b" MIPStarRE/LDT --glob '*.lean'
```

currently reports the following direct proof holes.

| Site | Declaration | Tracking issue | Mathematical obligation |
|---|---|---|---|
| `MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean:216` | `MainInductionStep.mainInduction` | #1507 | Prove the successor branch of `thm:main-induction` from the paper hypotheses, deriving the restricted probabilities, slice witnesses, self-improvement outputs, and pasting side conditions internally. |
| `MIPStarRE/LDT/MainInductionStep/Theorems/SelfImprovementAssembly/Core.lean:167` | `MainInductionStep.selfImprovementInInductionSection` | #1503 | Prove the induction-section self-improvement theorem without adding a completion or Section 9 obligation bundle to the public statement. |
| `MIPStarRE/LDT/MakingMeasurementsProjective/Orthonormalization.lean:77` | `MakingMeasurementsProjective.orthonormalizationMainLemma` | #1032 | Formalize the spectral truncation and locality-preserving repair construction for `lem:orthonormalization-main-lemma`. |
| `MIPStarRE/LDT/MakingMeasurementsProjective/Producers.lean:522` | `MakingMeasurementsProjective.leftLiftedProjectivizationRepairWithMatchMass` | #1610 | Prove the QXP outcome-expectation preservation inequality for the same projectivization data returned by the repair construction. |
| `MIPStarRE/LDT/Pasting/Bernoulli/Final.lean:679` | `Pasting.ldPastingDegreeZeroBranch` | #1601, #1622 | Prove the degree-zero complementary branch of the unrestricted low-degree pasting theorem without adding `0 < d` to the source theorem. |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/HelperCompleteness/Bracketed.lean:571` | `SelfImprovement.sdp_statement_with_slackness` | #1230 | Prove the Section 9 SDP strong-duality and complementary-slackness statement. |
| `MIPStarRE/LDT/SelfImprovement/Theorems/Results/SelfImprovementTop/Core.lean:362` | `SelfImprovement.selfImprovement` | #1515 | Derive helper strong self-consistency, orthonormalization, and final-field transport from the paper hypotheses. |

The command

```bash
rg -n "^\s*(axiom|constant)\b" MIPStarRE/LDT --glob '*.lean'
```

does not find a top-level Lean `axiom` or `constant` declaration in the LDT
tree.  The dedicated audit

```bash
python3 scripts/audit_lean_axiom_declarations.py --root . --ci
```

also reports no explicit LDT axiom declarations.

Several public declarations are themselves `sorry`-free but still depend
transitively on `sorryAx`.  The file `MIPStarRE/LDT/Test/AxiomAudit.lean`
intentionally records this closure.  In particular:

- `Test.mainFormal` inherits the current final-theorem construction gaps,
  including #1043, #1363, #1369, #1458, #1566, and #1610.
- `SelfImprovement.selfImprovementHelper` inherits the SDP complementary
  slackness gap #1230.
- `Pasting.ldPasting` inherits the degree-zero complementary branch gap #1622
  through `Pasting.ldPastingDegreeZeroBranch`.
- `MainInductionStep.mainInduction`,
  `MainInductionStep.selfImprovementInInductionSection`,
  `SelfImprovement.selfImprovement` inherit their direct `sorry` sites listed
  above.

## Current Native Issue Tree

The current GitHub sub-issue tree keeps the active obligations below the
source-statement bridge-debt tracker #1458, rather than recording them as body
checkboxes.  The relevant open branches are:

| Parent | Current open children | Role in the proof debt |
|---|---|---|
| #1558 | #1566 | Final-theorem residual and package audit; the open child is the line-169 match-mass preservation target for the chosen `mainFormal` witnesses. |
| #1566 | #1610 | QXP outcome-expectation preservation for the projectivization data used by the line-169 match-mass route. |
| #1571 | #1584 | Definition-drift audit; the open child records downstream theorem subtrees that must be repaired from the source object, not patched downstream. |
| #1596 | #1435 | Helper strong-self-consistency and projectivization obligation bundles; the open child records removal of obsolete spectral-truncation and repair-input abbreviations after the #1032 consumer rewire. |
| #1601 | #1622 | Unrestricted low-degree pasting; the open child is the degree-zero complementary branch that cannot be replaced by adding `0 < d` to `thm:ld-pasting`. |

Several other direct `sorry` sites remain first-level children of #1458:
#1230, #1503, #1507, and #1515.  They should stay as proof obligations until
the corresponding paper arguments are formalized.

The public theorem `MakingMeasurementsProjective.orthonormalization` is no
longer on this list: PR #1632 restored the paper constant without making the
theorem depend on the still-unproved heterogeneous
`orthonormalizationMainLemma`.

The repair direction is therefore not to remove `sorryAx` by adding new
assumptions.  The correct cleanup is to prove the listed construction theorems,
or to keep the source-faithful theorem statement with the direct `sorry` until
the corresponding paper proof is formalized.
