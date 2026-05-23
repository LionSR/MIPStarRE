# Issue #834 session 40 mainFormal dependency audit

Audit date: 2026-04-30

Base commit: `53443203` (`origin/main`)

Branch: `gpt55/issue-834-mainformal-residual-session40`

> **Status note, 2026-05-20.**  This is a historical audit of the old
> `Test/MainTheorem.lean` monolith and its role-package/completion residual.
> The current code has split the final-theorem route, removed the residual
> structures named below, and records the same-space Lean interface separately
> as `thm:main-formal-current-interface`.  The source statement
> `thm:main-formal` is no longer linked to a conditional Lean theorem.  The
> current same-space theorem `MIPStarRE.LDT.Test.mainFormal` has no bridge,
> residual, package, or obligation hypotheses; its only remaining `sorryAx`
> dependency is transitive through
> `MIPStarRE.LDT.MainInductionStep.mainInduction`.  The only construction proof
> hole on this same-space route is
> `MIPStarRE.LDT.MainInductionStep.mainInductionSuccessorNext_ofSmallErrorConstruction`
> in `MIPStarRE/LDT/MainInductionStep/Theorems/MainTheorems.lean`, tracked by
> #1507.  The source-labelled blueprint entry `thm:main-formal` is now
> represented by
> `MIPStarRE.LDT.Test.mainFormal_sourceStatement`, which calls the named
> wrapper `MIPStarRE.LDT.Test.mainFormal_sourceConclusion` for the printed
> two-space statement.  At that snapshot, the wrapper proved the saturated-error
> branch and left `MIPStarRE.LDT.Test.mainFormal_sourceSmallErrorConclusion` as
> the direct non-vacuous source-boundary proof hole.  All references below to the live
> `MainTheorem.lean` residual, #834,
> #924, #931, #950, or #958 describe the April 30 audit snapshot, not the
> current proof frontier.
>
> **Status note, 2026-05-23.**  The 2026-05-20 frontier description is also
> historical.  The corrected large-\(k\), nonzero-sampling source route is now
> checked, including the two-space final theorem.  The remaining differences
> from the literal printed theorem are documented statement corrections:
> \(k\ge400md\) and \(0<k\), not live residual or source-boundary obligation
> declarations.

## Executive summary

At the audited April 30 `origin/main` snapshot there was exactly one Lean proof
hole under `MIPStarRE/LDT`, at
`MIPStarRE/LDT/Test/MainTheorem.lean:2950`.  The proof obligation is the split
role-package/completion residual

```lean
MainFormalCascadeRolePackageResidualLeftCompletionLine169Residual
  (params := params) (strategy := strategy) (eps := eps)
  (hpass := hpass) (k := k) (scalars := scalars)
```

The old dependency list in the nearby TODO was already partly stale at the
audit snapshot.  In particular, #601, #707, #672, #714, #715, #732, and #759
were closed on GitHub and no longer explained the local proof hole observed in
that tree.  The actionable blockers at the snapshot were:

1. **Section 6 / role-residual construction:** PR #924 was open and depended
   on #931 for closed self-improvement inputs.  It touched
   `MIPStarRE/LDT/Test/MainTheorem.lean`, so this report deliberately avoided
   editing that file.
2. **Line-169 transport choice:** at the time of this audit, PR #950 was still
   pursuing an exact P-level match-mass bridge instead of the generic
   `triangleSub` route that loses an extra `sqrt ζ₂`.  The current tree has
   since retired that exact bridge and uses the repaired pre-completion
   line-169 route instead.
3. **Signature churn:** PR #958 was open and rewrote
   `ProjStrat`/`MainTheorem` for separate Alice/Bob local spaces.  A proof
   branch closing #834 was expected to rebase after #958, or otherwise to
   require substantial signature repair.

No new residual was found at the snapshot that was not already covered by
#834/#821/#422, #924/#931, #950/#903, #958/#560, or the existing
projectivization umbrella #426.

## Historical Lean target

At the audit snapshot, the public theorem was `MIPStarRE.LDT.Test.mainFormal`,
with statement and final assembly in
`MIPStarRE/LDT/Test/MainTheorem.lean:2878-2967`.  The theorem already contained
the issue-#906 statement fix: the public hypothesis was
`400 * params.m * params.d ≤ k`, not just the paper's printed `md ≤ k`
(`MainTheorem.lean:2885`).

The non-vacuous branch built scalar data and then stopped at the residual:

```lean
let scalars : MainFormalCascadeScalars params eps k :=
  MainFormalCascadeScalars.ofNontrivialMainFormal hepsNN hk0 herr
have roleWitnessResidualLeftCompletionLine169Residual :
    MainFormalCascadeRolePackageResidualLeftCompletionLine169Residual
      (params := params) (strategy := strategy) (eps := eps)
      (hpass := hpass) (k := k) (scalars := scalars) := by
  -- TODO(#427): construct the concrete Section 6 role residual,
  -- left-register completion witnesses, and the construction-level
  -- match-mass monotonicity input for exact polynomial line 169.
  sorry
```

The residual structure is defined at `MainTheorem.lean:2659-2672` and has exactly
two fields:

> **Historical snapshot.**  The residual structures and fields in the next two
> code blocks are session-40 snapshot material.  The current tree has retired
> this exact line-169 residual route in favor of the repaired pre-completion
> transport.

```lean
structure MainFormalCascadeRolePackageResidualLeftCompletionLine169Residual ... where
  roleInductionWitness : MainFormalRoleInductionWitness params strategy eps hpass k
  postRoleResidual :
    MainFormalPostRolePackageLeftCompletionLine169Residual params strategy eps k scalars
      (roleInductionWitness.roleWitness scalars)
```

The second field expands at `MainTheorem.lean:2502-2534` to:

```lean
leftMeasurement : ProjMeas (Polynomial params) ι
rightMeasurement : ProjMeas (Polynomial params) ι
leftCompletionCloseness :
  SDDRel strategy.state (uniformDistribution Unit)
    (constSubMeasFamily (unsymmetrizedLeftPOVM roleWitness.roleMeasurement).toSubMeas.liftLeft)
    (constSubMeasFamily leftMeasurement.toSubMeas.liftLeft)
    scalars.zeta2
rightCompletionClosenessLeft :
  SDDRel strategy.state (uniformDistribution Unit)
    (constSubMeasFamily (unsymmetrizedRightPOVM roleWitness.roleMeasurement).toSubMeas.liftLeft)
    (constSubMeasFamily rightMeasurement.toSubMeas.liftLeft)
    scalars.zeta2
line169MatchMassMonotonicity :
  MakingMeasurementsProjective.ProjectivizationMatchMassMonotonicity strategy.state
    (unsymmetrizedLeftPOVM roleWitness.roleMeasurement)
    (unsymmetrizedRightPOVM roleWitness.roleMeasurement)
    leftMeasurement rightMeasurement
```

Existing downstream conversions are already checked:

- `MainFormalCascadeRolePackageResidualLeftCompletionLine169Residual.toRolePackageResidualCompletionLine169Residual`
  (`MainTheorem.lean:2679-2704`) reconstructs pre-projective consistency from the
  concrete role-measurement record, transports Bob's left-register completion estimate to the
  paper's right-register form using the #869 helper, and derives the two line-169
  consistency links from `line169MatchMassMonotonicity`.
- `MainFormalCascadeRolePackagedCompletionLine169Residual.toCompletionLine169Residual`
  (`MainTheorem.lean:2395-2414`) expands the role-measurement record through
  `UnsymmetrizationConsistency.ofSymConsistency`.
- `MainFormalProjectiveCompletionTransportWitness.selfConsistency`
  reconstructs line 156 and converts it to the native `ζ₃/2` self-consistency
  target.
- `MainFormalProjectiveCompletionTransportWitness.toMainFormal` only
  weakens the native `ζ₄` and `ζ₃/2` estimates to `mainFormalError`.

Thus the proof work in that tree was upstream data construction, not downstream
triangle or scalar absorption.

## Paper anchors

The theorem statement is `references/ldt-paper/test_definition.tex:180-202`:
there exist projective polynomial measurements $G^{\mathrm A},G^{\mathrm B}$ such
that

$$
A^{\mathrm A,u}_a\otimes I \simeq_\nu I\otimes G^{\mathrm B}_{[g(u)=a]},
\qquad
I\otimes A^{\mathrm B,u}_a \simeq_\nu G^{\mathrm A}_{[g(u)=a]}\otimes I,
$$

and

$$
G^{\mathrm A}_g\otimes I \simeq_\nu I\otimes G^{\mathrm B}_g.
$$

The historical residual corresponded to the proof of `thm:main-formal` in
`references/ldt-paper/inductive_step.tex`:

| Paper lines | Paper step | Current Lean status |
| --- | --- | --- |
| 107-108 | `eq:cons-a` / `eq:cons-b`, the factor-two unsymmetrization estimates. | No longer residual fields; reconstructed from the concrete role-measurement record by `UnsymmetrizationConsistency.ofSymConsistency`. |
| 130-133 | `eq:G-self-consistency`, polynomial $G^{\mathrm A}$ / $G^{\mathrm B}$ consistency at `ζ₁`. | Reconstructed from Step 5 wrappers and role-measurement data before line 156. |
| 146-147 | `eq:G-with-Q-A`, completion closeness from $G$ to $Q$ at `ζ₂`. | Still part of `postRoleResidual`: Alice in left-register form, Bob in the left-register form returned by orthonormalize-and-complete. The #869 conversion to Bob's right-register paper form is already checked. |
| 160-166 | `eq:third-goal` and data processing to evaluated $Q$ consistency. | Downstream conversions are checked once the residual fields are supplied. |
| 167-173 | `prop:triangle-sub` line-169 transport to $Q^{\mathrm A}_g \otimes I \simeq_{ζ₁} I\otimes G^{\mathrm B}_g`, then data processing. | The paper's printed `ζ₁` cannot be obtained from generic `triangleSub` plus completion closeness without an extra `sqrt ζ₂`; the current tree therefore uses the repaired pre-completion line-169 route instead of an exact match-mass invariant. |
| 175-185 | Final two `ζ₄` point goals `eq:one-goal` and `eq:another-goal`. | Already formalized by the residual conversions and triangle wrapper. |
| 186-234 | Error cascade into the theorem's `ν`. | Already formalized by `MainFormalCascadeScalars` and `MainFormalProjectiveCompletionTransportWitness.toMainFormal`. |

The exact line-169 constraint is the reason this report does not recommend a quick
`triangleSub` proof: that route is mathematically weaker than the paper's displayed
constant and would not fit the current `mainFormalError` envelope.

## Blueprint / dependency graph context

I regenerated the ignored blueprint web output with `leanblueprint web` in order to
inspect `blueprint/web/dep_graph_document.html`.

- To locate the generated modal reproducibly, search
  `blueprint/web/dep_graph_document.html` for `thm:main-formal` or
  `main-formal` after running `leanblueprint web`. The modal displays the
  strengthened Lean/blueprint statement with `k ≥ 400 md` and links to
  `MIPStarRE.LDT.Test.mainFormal`.
- The generated graph has incoming edges
  - `prop:simeq-triangle-inequality -> thm:main-formal`,
  - `thm:main-induction -> thm:main-formal`,
  - `lem:role-register-symmetrization -> thm:main-formal`, and
  - `thm:zeta-bounds-main-formal -> thm:main-formal`.
- The graph has outgoing edge `thm:main-formal -> thm:main-informal`.

At the snapshot, the more detailed Lean residual context was documented in
`blueprint/src/chapter/ch10_induction.tex:610-651`: it explained that the
active residual was
`MainFormalCascadeRolePackageResidualLeftCompletionLine169Residual`, that Bob's
completion estimate is supplied left-lifted and transported by #869, and that exact
line-169 still needs construction-level match-mass preservation rather than generic
`triangle-sub`.

## Stale or no-longer-local blockers in the snapshot TODO

At the snapshot, the TODO near `MainTheorem.lean:2921-2929` still listed
several issues as active upstream dependencies.  GitHub status on this audit
showed:

| Issue / PR | Current state | Dependency-audit verdict |
| --- | --- | --- |
| #601 full-slice transport | Closed 2026-04-27 | Stale as a `mainFormal` blocker. |
| #707 `fromHToG` pasting bridge | Closed 2026-04-30 | Stale.  Session 37 also confirmed the `MIPStarRE/LDT/Pasting/` directory is sorry-free. |
| #672 reverse `overAllOutcomes` aggregation | Closed 2026-04-30 | Stale. |
| #714 ProcessedG phase 2 | Closed 2026-04-26 | Stale. |
| #715 ProcessedG phase 5 | Closed 2026-04-27 | Stale. |
| #732 ProcessedG phase 6/7 bridge | Closed 2026-04-28 | Stale. |
| #759 reverse insertion bridge | Closed 2026-04-26 | Stale. |
| #869 right-register completion transport | Merged 2026-04-27 | Already consumed by the current residual conversion. |
| #906 `k ≥ 400md` statement fix | Closed 2026-04-29 | Already reflected in `mainFormal`. |

Two older trackers that were open at the snapshot were also not direct fields
of the residual:

- #424 was still open, but the factor-two unsymmetrization estimates were no
  longer explicit residual fields; the current route obtains them from
  `MainFormalRoleMeasurementWitness.toUnsymmetrizationConsistency`.
- #427 was still open, but the scalar cascade bounds and final weakening were
  already checked in `MainFormalCascadeScalars` and
  `MainFormalProjectiveCompletionTransportWitness.toMainFormal`; the local TODO
  marker `TODO(#427)` is stale as a description of the remaining proof term.

A future PR that edited `MainTheorem.lean` was expected to refresh these TODO
comments after #924/#958 landed.  This report intentionally did not do that
refresh, in order to avoid conflicting with the then-active `MainTheorem.lean`
PRs.

## Historical blockers and active PRs

### #924 / #931: Section 6 role residual

At the audit snapshot, PR #924
(`feat(LDT): add answer-valued Section 6 residual bridge`) was open and touched
`MIPStarRE/LDT/Test/MainTheorem.lean`,
`MIPStarRE/LDT/Test/StrategyCore.lean`, and Section 6 files.  Its PR body stated
that it added answer-valued Section 6 restriction plumbing and tightened the
then-live `mainFormal` boundary to a `Nonempty` Step 6 witness residual.  It
explicitly remained blocked on #931.

Issue #931 was open and asked for closed self-improvement inputs for Section 6.
In that tree, `MainFormalRoleInductionWitness` could be produced from the
checked base handoff or a syntactic successor boundary, but the general
successor-boundary construction still needed the Section 6
self-improvement/recursion inputs that #931 tracked.  Therefore the first field
of the residual was not to be attacked in parallel with #924 unless #924 closed
or merged.

### #950 / #903: exact line-169 match mass

Issue #903 is closed, and the later exact-match interface from PR #950 has now
been retired as stale.  The current tree no longer carries a live exact
match-mass bridge route.  The active Step-6 construction instead uses the
repaired line-169 transport already recorded in
`ProjectivizationLine169Repair` and in the projective completion transport
witness.

### #958 / #560: separate local spaces in `ProjStrat`

At the audit snapshot, PR #958 was open and touched
`MIPStarRE/LDT/Test/MainTheorem.lean` plus most `Test/Strategy*.lean` files.
It had failing build / blueprint-sync checks and requested changes.  Because it
could change `ProjStrat` signatures throughout `mainFormal`, any proof PR for
#834 was expected to be based after #958 was resolved, or at least to expect
nontrivial rebase work.

### Other historical overlap to avoid

- #957/#894 is a mathlib-quality cleanup touching commutativity and pasting helper
  files; it was not a direct #834 proof blocker but was not to be overlapped
  for cleanup edits.
- #926/#927 touched `MIPStarRE/LDT/Test/StrategyRole.lean`; the audit advised
  avoiding `StrategyRole` edits while it was open.

## Historical recommended proof PR after #924/#950/#958 land

1. Rebase on a main commit containing the relevant merged PRs, especially #958 and
   #924 if they change `MainTheorem.lean` signatures, and #950 for the line-169
   match-mass bridge.
2. Re-audit the exact target.  If #924 landed as described, the target might no
   longer be the two-field residual listed above; it might be a `Nonempty`
   Step 6 witness residual tied to answer-valued Section 6 data.
3. Refresh the stale TODO block in `MainTheorem.lean` to remove #601/#707/#672/#714/#715/#732/#759
   and to name the actual post-merge blockers, if any.
4. Construct the role residual from the merged Section 6 construction rather than from an
   arbitrary `Classical.choice` role-measurement record.  Preserve the current design principle:
   keep the concrete role-register measurement visible.
5. Build the post-role residual in paper order:
   - use the reconstructed pre-projective `G^A/G^B` consistency at `ζ₁`;
   - run/apply the orthonormalize-and-complete witness for Alice and Bob to obtain
     `leftMeasurement`, `rightMeasurement`, and the two left-lifted completion
     estimates at `ζ₂`;
   - historical session-40 plan: use the then-open #950 match-mass
      preservation theorem to fill `line169MatchMassMonotonicity`;
   - let the existing conversions handle Bob's right-register transport, line-169
     consistency, line 156, the `ζ₄` point goals, and final error weakening.
6. Validate with at least `lake env lean MIPStarRE/LDT/Test/MainTheorem.lean`,
   proof-integrity grep on touched Lean files, `git diff --check`, and the blueprint
   sync checks if blueprint references are edited.

## Commands run for this audit

```text
rg -n "\bsorry\b" MIPStarRE/LDT --glob '*.lean'
rg -n "\b(sorry|axiom|admit|unsafe|native_decide)\b" MIPStarRE/LDT/Test/MainTheorem.lean
leanblueprint web
gh issue view / gh pr view for #834 #821 #422 #601 #707 #672 #714 #715 #732 #759 #924 #931 #950 #903 #958 #560 #957 #894 #926 #927 #424 #426 #427 #906 #869
```

The targeted `lake env lean MIPStarRE/LDT/Test/MainTheorem.lean` check was also
attempted for confirmation, but it timed out at the 600-second tool limit on this
worktree.  No Lean files were changed by this audit.
