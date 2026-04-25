import MIPStarRE.LDT.MainInductionStep
import MIPStarRE.LDT.Test.ErrorCascade
import MIPStarRE.LDT.Test.SymmetrizationBridge

/-!
# Section 3 — Main theorem

The main formal output of the low individual degree test (`thm:main-formal`).
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

/-- Placeholder polynomial-size slack for the overview Raz–Safra statement.

The Chapter 1 overview records the dependence as `eps + poly(m) * poly(d/q)`;
the exact constants are intentionally left to the future direct formalization of
the classical result. -/
noncomputable def razSafraSlackBound (params : Parameters) (eps : Error) : Error :=
  eps + (params.m : Error) * ((params.d : Error) / (params.q : Error))

/-- Overview-level soundness conclusion: a low individual degree polynomial
agrees with the point-answer function except on `slack` average mass, with
explicit bound `slackBound`. -/
def PointAnswerSoundnessConclusion (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (slackBound slack : Error) : Prop :=
  0 ≤ slack ∧
    slack ≤ slackBound ∧
      ∃ g : Polynomial params,
        avgOver (uniformDistribution (Point params))
            (fun u => if g u = a u then (1 : Error) else 0) ≥
          1 - slack

/-- Pass condition for the classical `k = 2` surface-versus-point low-degree
test from `references/ldt-paper/introduction.tex`.

This records only the paper-faithful classical test-passing data:
- a deterministic classical strategy for the surface-versus-point test,
- a proof that Alice's point-answer function is the ambient `a`, and
- a proof that the strategy passes the modeled distribution of genuine
  2-dimensional framed surface/point pairs with probability at least `1 - eps`.

In that modeled distribution the hidden surface parameter remains uniform once a
genuine surface frame is chosen, so the induced queried-point marginal is still
uniform on `Point params`.

This is intentionally NOT `PassesLowIndividualDegreeTest`, which models a
different test. -/
def SurfaceVsPointPassCondition (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error) : Prop :=
  ∃ strategy : TwoProverClassicalSurfaceVsPointStrategy params,
    strategy.pointAnswerA = a ∧
      strategy.ClassicallyPassesSurfaceVsPointTest eps

/-- Pass condition for the paper's deterministic two-prover classical low
individual degree test.

This records only the paper-faithful classical test-passing data:
- a deterministic classical strategy for the two-prover low individual degree
  test from `references/ldt-paper/test_definition.tex`,
- a proof that Alice's point-answer function is the ambient `a`, and
- a proof that the strategy passes that classical test with acceptance
  probability at least `1 - eps`.

The quoted Polishchuk–Spielman soundness implication is kept separate in
`PolishchukSpielmanClassicalSoundnessStatement` so downstream theorems state the
external dependency explicitly, without making it ambient proof power. -/
def TwoProverClassicalLIDPassCondition (params : Parameters)
    [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error) : Prop :=
  ∃ strategy : TwoProverClassicalLIDStrategy params,
    strategy.pointAnswerA = a ∧
      strategy.ClassicallyPassesLowIndividualDegreeTest eps

/-- Hypothesis-style interface for the classical Raz--Safra
surface-versus-point soundness theorem.

This keeps the quoted classical theorem explicit, rather than making it an
ambient axiom. As with `PolishchukSpielmanClassicalSoundnessStatement`, the
ambient point-answer function `a`, error parameter `eps`, and chosen slack bound
`slackBound` are explicit parameters of the statement, so downstream wrappers
ask only for the specialized instance they actually use. -/
def RazSafraSoundnessStatement (params : Parameters)
    [FieldModel params.q]
    (a : Point params → Fq params) (eps slackBound : Error) : Prop :=
  SurfaceVsPointPassCondition params a eps →
    ∃ slack : Error,
      PointAnswerSoundnessConclusion params a slackBound slack

/-- Hypothesis-style interface for the classical low-individual-degree
soundness result of Polishchuk and Spielman.

This issue-#408 `Prop`-valued interface replaces the earlier ambient axiom with
an explicit hypothesis at each call site. The external witness carries its own
slack bound parameter `slackBound`, so downstream users must supply the specific
error dependence they want to quote rather than inheriting any
repository-chosen placeholder formula for the schematic Chapter 1
`poly(m) * (poly(eps) + poly(d/q))` bound. The regression audit in
`MIPStarRE.LDT.Test.AxiomAudit` checks that `classicalTestSoundness` remains
kernel-clean apart from the standard Lean axioms. -/
def PolishchukSpielmanClassicalSoundnessStatement (params : Parameters)
    [FieldModel params.q]
    (a : Point params → Fq params) (eps slackBound : Error) : Prop :=
  TwoProverClassicalLIDPassCondition params a eps →
    ∃ slack : Error,
      PointAnswerSoundnessConclusion params a slackBound slack

/-- `thm:raz-safra`.

Quoted overview theorem wrapper: from paper-faithful surface-versus-point
classical test-passing data together with an explicit witness of the external
Raz--Safra soundness statement, conclude that Alice's point-answer function is
close to a low-degree polynomial with slack bounded by
`razSafraSlackBound params eps`. -/
theorem razSafra
    (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (eps : Error)
    (hpass : SurfaceVsPointPassCondition params a eps)
    (hRS : RazSafraSoundnessStatement params a eps (razSafraSlackBound params eps)) :
    ∃ slack : Error,
      PointAnswerSoundnessConclusion params a (razSafraSlackBound params eps) slack := by
  exact hRS hpass

/-- `thm:classical-test-soundness`.

Quoted classical overview theorem wrapper: from paper-faithful classical LID
test-passing data together with an explicit witness of the
Polishchuk–Spielman soundness statement at a chosen slack bound `slackBound`,
conclude that prover A's point-answer function is close to a low-degree
polynomial with that same bound. Any concrete overview-style rate must
therefore be supplied by instantiating `slackBound` and the external hypothesis
`hPS`; this module intentionally maintains no repository-chosen placeholder
bound. -/
theorem classicalTestSoundness
    (params : Parameters) [FieldModel params.q]
    (a : Point params → Fq params) (eps slackBound : Error)
    (hpass : TwoProverClassicalLIDPassCondition params a eps)
    (hPS : PolishchukSpielmanClassicalSoundnessStatement params a eps slackBound) :
    ∃ slack : Error,
      PointAnswerSoundnessConclusion params a slackBound slack := by
  exact hPS hpass

/-- Vacuous-regime fallback for `thm:main-formal`.

Whenever the envelope `mainFormalError params k eps` has already saturated past
`1`, the three target `ConsRel` relations hold trivially because
`bipartiteConsError` under a probability question distribution is bounded by
`1`. This is in the spirit of the paper's observation (see the proof of
`thm:main-induction` in `references/ldt-paper/inductive_step.tex`) that the
bound it is proving is vacuous whenever the error scale is at least `1`.

In the `mainFormal` assembly this wrapper handles the regime
`params.m * params.d ≤ k < 400 * params.m * params.d`, where the Section 6 /
Pasting-side hypothesis `400 * params.m * params.d ≤ k` fails. The
complementary regime `400 * params.m * params.d ≤ k` feeds directly into the
public induction/pasting wrappers (`mainInductionByRecursionOnM` in
`MIPStarRE.LDT.MainInductionStep`). The arithmetic bridge
`1 ≤ mainFormalError params k eps` itself is discharged inside the proof of
`mainFormal` from the envelope inflation chain already packaged by
`errorCascade_le_mainFormalError`; see TODO(#634).

Witness choice: we pick an arbitrary `ProjMeas` via `default` — the proof only
needs the generic bound `bipartiteConsError ≤ 1`, not any specific
distributional property of the witness, so the lemma is insensitive to how the
ambient `Inhabited (ProjMeas …)` instance is realized. -/
theorem mainFormal_trivial_witness
    (params : Parameters) [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι)
    (eps : Error) (k : ℕ)
    (herr : 1 ≤ mainFormalError params k eps) :
    ∃ G_A G_B : ProjMeas (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
          (polynomialEvaluationFamily params G_B.toSubMeas)
          (mainFormalError params k eps) ∧
        ConsRel strategy.state (uniformDistribution (Point params))
          (polynomialEvaluationFamily params G_A.toSubMeas)
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
          (mainFormalError params k eps) ∧
        ConsRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily G_A.toSubMeas)
          (constSubMeasFamily G_B.toSubMeas)
          (mainFormalError params k eps) := by
  classical
  haveI : Inhabited (Polynomial params) :=
    ⟨⟨0, by intro i; simp [MvPolynomial.degreeOf_zero]⟩⟩
  let trivialG : ProjMeas (Polynomial params) ι := default
  refine ⟨trivialG, trivialG, ?_, ?_, ?_⟩
  all_goals exact ⟨le_trans
    (bipartiteConsError_uniform_le_one strategy.state strategy.isNormalized _ _) herr⟩

/-- Step 1 + Section 6 base case for `mainFormal`.

If the ambient test dimension is `m = 1`, Step 1 symmetrizes the original
projective strategy and `MainInductionStep.mainInductionBaseCase` supplies the
Section 6 global polynomial measurement on the role-register symmetrized
strategy. This packages that handoff in the exact form consumed later by
`mainFormal`. -/
theorem strategySymmetrization_mainInductionBaseCase
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (hm1 : params.m = 1) :
    ∃ G : Measurement (Polynomial params) (Role × ι),
      ConsRel (strategy.strategySymmetrization).state
        (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        (MainInductionStep.mainInductionError params k
          (3 * eps) (3 * eps) (3 * eps)) := by
  exact
    MainInductionStep.mainInductionBaseCase params
      (strategy := strategy.strategySymmetrization)
      (eps := 3 * eps) (delta := 3 * eps) (gamma := 3 * eps) (k := k) hm1
      (ProjStrat.strategySymmetrization_isGood_three_mul
        (strategy := strategy) (eps := eps) hpass)

/-- Weighted restricted-axis input expected by the Section 6 successor wrapper
on the role-register symmetrization. -/
def MainFormalSuccessorAxisWeightedBound (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params.next ι) (eps : Error) : Prop :=
  avgOver (uniformDistribution (Fq params))
    (fun x => MainInductionStep.sliceTransverseDirectionWeight params *
      (MainInductionStep.xRestrictedStrategy params
        strategy.strategySymmetrization x).axisParallelFailureProbability) ≤
    3 * eps

/-- Weighted restricted-diagonal input expected by the Section 6 successor
wrapper on the role-register symmetrization.

Per `lem:restricted-probabilities` (see `docs/audit/lean_code_audit.md`) the
paper's slice argument uses the same transverse-direction factor `m / (m + 1)`
for both the axis-parallel and diagonal branches. `restrictedProbabilities`
therefore expects `sliceTransverseDirectionWeight` on both weighted bounds. -/
def MainFormalSuccessorDiagonalWeightedBound (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params.next ι) (eps : Error) : Prop :=
  avgOver (uniformDistribution (Fq params))
    (fun x => MainInductionStep.sliceTransverseDirectionWeight params *
      (MainInductionStep.xRestrictedStrategy params
        strategy.strategySymmetrization x).diagonalFailureProbability) ≤
    3 * eps

/-- The restricted-probability package on the role-register symmetrization used
in the successor branch of `mainFormal`. -/
noncomputable def mainFormalSuccessorRestrictionPackage
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (haxisWeightedBound : MainFormalSuccessorAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound : MainFormalSuccessorDiagonalWeightedBound params strategy eps) :
    MainInductionStep.SliceRestrictionPackage params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) :=
  MainInductionStep.mainInductionPublicRestrictionPackage
    params strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
    (ProjStrat.strategySymmetrization_isGood_three_mul
      (strategy := strategy) (eps := eps) hpass)
    haxisWeightedBound hdiagonalWeightedBound

/-- Successor-case recursive slice witnesses expected by the public Section 6
boundary wrapper. -/
def MainFormalSuccessorRecursiveSlices (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorDiagonalWeightedBound params strategy eps) : Prop :=
  let hrestrict :=
    mainFormalSuccessorRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  ∀ x,
    ∃ error : Error, ∃ G : Measurement (Polynomial params) (Role × ι),
      ConsRel (strategy.strategySymmetrization).state
        (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas
          (MainInductionStep.xRestrictedStrategy params
            strategy.strategySymmetrization x).pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        error ∧
      error ≤
        MainInductionStep.mainInductionError params k
          (hrestrict.profile.axisParallel x)
          (hrestrict.profile.selfConsistency x)
          (hrestrict.profile.diagonal x)

/-- Successor-case restricted-strategy self-improvement producer expected by the
public Section 6 boundary wrapper. -/
def MainFormalSuccessorSelfImprovementProducer (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorDiagonalWeightedBound params strategy eps) : Type _ :=
  let hrestrict :=
    mainFormalSuccessorRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  ∀ hinduction :
    MainInductionStep.PerSliceInductionPackage params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) hrestrict k,
    MainInductionStep.SelfImprovementPackage params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) k
      hrestrict hinduction

/-- Successor-case Section 6 boundary inputs for `mainFormal`.

Assume the ambient projective strategy lives over `params.next`. Step 1 already
turns `hpass` into the `(3 * eps, 3 * eps, 3 * eps)`-good role-register
symmetrization `strategy.strategySymmetrization`. What still remains to apply
`MainInductionStep.mainInductionPublicWrapper` are exactly the public Section 6
inputs tracked by issues #631 and #632:
1. weighted restricted-axis and restricted-diagonal bounds,
2. recursive slice witnesses for the restricted strategies, and
3. a restricted-strategy self-improvement producer.

Bundling them into a single named boundary package gives the successor branch
of `mainFormal` one honest issue-#634 interface, rather than four independent
hypothesis holes. -/
structure MainFormalSuccessorBoundary (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ) where
  axisWeightedBound :
    MainFormalSuccessorAxisWeightedBound params strategy eps
  diagonalWeightedBound :
    MainFormalSuccessorDiagonalWeightedBound params strategy eps
  recursiveSlices :
    MainFormalSuccessorRecursiveSlices params strategy eps hpass k
      axisWeightedBound diagonalWeightedBound
  selfImprovementProducer :
    MainFormalSuccessorSelfImprovementProducer params strategy eps hpass k
      axisWeightedBound diagonalWeightedBound

/--
`thm:main-formal` from `test_definition.tex`.

The bipartite tensor placement follows the paper:
- **1a**: `A^A_u ⊗ I ≈_ν I ⊗ G^B_{[g(u)=a]}` — G_B on **right**
- **1b**: `I ⊗ A^B_u ≈_ν G^A_{[g(u)=a]} ⊗ I` — G_A on **left**, A^B on **right**
- **2**: `G^A_g ⊗ I ≈_ν I ⊗ G^B_g` — G_B on **right**

The `k`-bound boundary matches the paper (`references/ldt-paper/test_definition.tex:183`):
the public hypothesis is `params.m * params.d ≤ k`, not the stronger
`400 * params.m * params.d ≤ k` used by the Section 6 / Pasting-side wrappers.
The planned assembly case-splits on `k`:

* Regime `400 * params.m * params.d ≤ k`: invoke the public Section 6
  wrapper `MIPStarRE.LDT.MainInductionStep.mainInductionPublicWrapper`,
  using the base-case handoff
  `strategySymmetrization_mainInductionBaseCase` and the successor-boundary
  package `MainFormalSuccessorBoundary`, to discharge the three `ConsRel`
  targets through the paper's cascade.
* Regime `params.m * params.d ≤ k < 400 * params.m * params.d`: the final
  envelope `mainFormalError params k eps` saturates past `1` (in the spirit of
  the paper's standard trivial-case observation in the proof of
  `thm:main-induction`), and `mainFormal_trivial_witness` supplies the witness
  directly.

Fixes #137, #239.
-/
theorem mainFormal
    (params : Parameters) [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params ι)
    (eps : Error)
    (hd : 0 < params.d)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : params.m * params.d ≤ k)
    (hk0 : 0 < k) :
    ∃ G_A G_B : ProjMeas (Polynomial params) ι,
      ConsRel strategy.state (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
          (polynomialEvaluationFamily params G_B.toSubMeas)
          (mainFormalError params k eps) ∧
        ConsRel strategy.state (uniformDistribution (Point params))
          (polynomialEvaluationFamily params G_A.toSubMeas)
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
          (mainFormalError params k eps) ∧
        ConsRel strategy.state (uniformDistribution Unit)
          (constSubMeasFamily G_A.toSubMeas)
          (constSubMeasFamily G_B.toSubMeas)
          (mainFormalError params k eps) := by
  -- TODO(#634): The remaining proof still case-splits on the `k`-bound
  -- boundary made explicit above.
  -- * `hlarge : 400 * params.m * params.d ≤ k` branch: Step 1 symmetrization
  --   (`strategySymmetrization_*`) and the final scalar envelope
  --   (`errorCascade_le_mainFormalError`) are already formalized. Section 6 now
  --   exposes the public induction-step boundary theorem
  --   `mainInductionPublicWrapper`, so the remaining induction-side gap is to
  --   package the symmetrized strategy inputs into the weighted
  --   restricted-probability bounds, recursive slice witnesses, and
  --   restricted-strategy self-improvement producer that theorem expects. After
  --   that, this file still needs the paper's unsymmetrization,
  --   Schwartz-Zippel, and final orthonormalization/projectivization transport
  --   into the three displayed `ConsRel` conclusions; those last three
  --   transports will apply `errorCascade_le_mainFormalError` directly at the
  --   point-A consistency, point-B consistency, and self-consistency usage
  --   sites.
  -- * `hsmall : k < 400 * params.m * params.d` branch: combine the cascade
  --   bounds with `params.m * params.d ≤ k` and `0 < k` to conclude
  --   `1 ≤ mainFormalError params k eps`, then invoke
  --   `mainFormal_trivial_witness`.
  sorry

end Test

end MIPStarRE.LDT
