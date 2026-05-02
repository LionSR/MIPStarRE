import MIPStarRE.LDT.MainInductionStep.Theorems
import MIPStarRE.LDT.MakingMeasurementsProjective.Orthonormalization
import MIPStarRE.LDT.MakingMeasurementsProjective.ProjectivizationChain
import MIPStarRE.LDT.Preliminaries.ComparisonProjective
import MIPStarRE.LDT.Preliminaries.Triangles
import MIPStarRE.LDT.Test.ErrorCascade
import MIPStarRE.LDT.Test.SchwartzZippelStep
import MIPStarRE.LDT.Test.StrategyFailures
import MIPStarRE.LDT.Test.SymmetrizationBridge
import MIPStarRE.LDT.Test.Unsymmetrization

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

In the `mainFormal` assembly this wrapper handles only branches where the
public envelope has already reached `1`, including the non-paper scalar regimes
`ε > 1` or `d > q`. It is not a replacement for the large-`k` hypothesis needed
by the Section 6 / Pasting path: the public theorem statement now exposes that
side condition directly, while this lemma remains the generic saturated-error
fallback. The complementary non-vacuous branch
`mainFormalError params k eps < 1` supplies the scalar hypotheses needed by the
Step 8 cascade.

Witness choice: we pick an arbitrary `ProjMeas` via `default` — the proof only
needs the generic bound `bipartiteConsError ≤ 1`, not any specific
distributional property of the witness, so the lemma is insensitive to how the
ambient `Inhabited (ProjMeas …)` instance is realized. -/
theorem mainFormal_trivial_witness
    (params : Parameters) [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι)
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
    (strategy : SameSpaceProjStrat params ι) (eps : Error)
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
      (SameSpaceProjStrat.strategySymmetrization_isGood_three_mul
        (strategy := strategy) (eps := eps) hpass)

/-- Weighted restricted-axis input expected by the Section 6 successor step
on the role-register symmetrization. -/
def MainFormalSuccessorAxisWeightedBound (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error) : Prop :=
  avgOver (uniformDistribution (Fq params))
    (fun x => MainInductionStep.sliceTransverseDirectionWeight params *
      (MainInductionStep.xRestrictedStrategy params
        strategy.strategySymmetrization x).axisParallelFailureProbability) ≤
    3 * eps

/-- Weighted restricted-diagonal input expected by the Section 6 successor step
on the role-register symmetrization.

Per `lem:restricted-probabilities` (see
`audits/2026-04-05_lean-code-audit.md`) the paper's slice argument uses the
same transverse-direction factor `m / (m + 1)` for both the axis-parallel and
diagonal branches. `restrictedProbabilities` therefore expects
`sliceTransverseDirectionWeight` on both weighted bounds. -/
def MainFormalSuccessorDiagonalWeightedBound (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error) : Prop :=
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
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (haxisWeightedBound : MainFormalSuccessorAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound : MainFormalSuccessorDiagonalWeightedBound params strategy eps) :
    MainInductionStep.SliceRestrictionPackage params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) :=
  MainInductionStep.mainInductionPublicRestrictionPackage
    params strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
    (SameSpaceProjStrat.strategySymmetrization_isGood_three_mul
      (strategy := strategy) (eps := eps) hpass)
    haxisWeightedBound hdiagonalWeightedBound

/-- Successor-case recursive slice witnesses expected by the public Section 6
boundary wrapper. -/
def MainFormalSuccessorRecursiveSlices (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
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
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
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

/-- Successor-case bridge-input package for the restricted-strategy
self-improvement producer.

For each possible per-slice induction package, this asks for the narrow
`SelfImprovementPackage.SliceBridgeInputs` assumptions: honest per-slice
`SymStrat`s, equality transports to the restricted-slice interfaces, and the
remaining Section 9 bridge inputs for those honest slice strategies. -/
def MainFormalSuccessorSelfImprovementBridgeInputs (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
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
    MainInductionStep.SelfImprovementPackage.SliceBridgeInputs params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) k
      hrestrict hinduction

/-- Convert successor-case bridge inputs into the self-improvement producer
expected by the public Section 6 boundary wrapper.

This does not discharge the bridge-input fields; it only packages them into the
existing `MainFormalSuccessorSelfImprovementProducer` API. -/
noncomputable def mainFormalSuccessorSelfImprovementProducer_ofBridgeInputs
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorDiagonalWeightedBound params strategy eps)
    (hbridge :
      MainFormalSuccessorSelfImprovementBridgeInputs params strategy eps hpass k
        haxisWeightedBound hdiagonalWeightedBound) :
    MainFormalSuccessorSelfImprovementProducer params strategy eps hpass k
      haxisWeightedBound hdiagonalWeightedBound := by
  let hrestrict :=
    mainFormalSuccessorRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  intro hinduction
  exact
    MainInductionStep.SelfImprovementPackage.ofSliceBridgeInputs params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) k
      hrestrict hinduction (hbridge hinduction)

/-- Successor-case Section 6 boundary inputs for `mainFormal`.

Assume the ambient projective strategy lives over `params.next`. Step 1 already
turns `hpass` into the `(3 * eps, 3 * eps, 3 * eps)`-good role-register
symmetrization `strategy.strategySymmetrization`. The public Section 6 wrapper
expects:
1. weighted restricted-axis and restricted-diagonal bounds,
2. recursive slice witnesses for the restricted strategies, and
3. a restricted-strategy self-improvement producer.

The helper lemmas below now discharge the weighted fields from `hpass`; bundling
all fields into a single named package still gives the successor branch of
`mainFormal` one honest issue-#634 interface, rather than four independent
hypothesis holes. -/
structure MainFormalSuccessorBoundary (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
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

/-- The public restricted-probabilities theorem supplies the successor-case
weighted axis-parallel input for the role-register symmetrization used by
`mainFormal`. -/
theorem mainFormalSuccessorAxisWeightedBound_ofPass
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    MainFormalSuccessorAxisWeightedBound params strategy eps :=
  MainInductionStep.weighted_axisParallel_bound params
    strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
    (SameSpaceProjStrat.strategySymmetrization_isGood_three_mul
      (strategy := strategy) (eps := eps) hpass)

/-- The public restricted-probabilities theorem supplies the successor-case
weighted diagonal-line input for the role-register symmetrization used by
`mainFormal`. -/
theorem mainFormalSuccessorDiagonalWeightedBound_ofPass
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    MainFormalSuccessorDiagonalWeightedBound params strategy eps :=
  MainInductionStep.weighted_diagonal_bound params
    strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
    (SameSpaceProjStrat.strategySymmetrization_isGood_three_mul
      (strategy := strategy) (eps := eps) hpass)

/-- Build the successor boundary once the two still-external slice-recursion and
restricted-strategy self-improvement inputs are supplied. The weighted
restricted-probability fields are now discharged from `hpass` by the public
Section 6 weighted-bound lemmas. -/
def mainFormalSuccessorBoundary_ofRecursiveSelfImprovement
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (hrec : MainFormalSuccessorRecursiveSlices params strategy eps hpass k
      (mainFormalSuccessorAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorDiagonalWeightedBound_ofPass params strategy eps hpass))
    (hself : MainFormalSuccessorSelfImprovementProducer params strategy eps hpass k
      (mainFormalSuccessorAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorDiagonalWeightedBound_ofPass params strategy eps hpass)) :
    MainFormalSuccessorBoundary params strategy eps hpass k :=
  let axisBound := mainFormalSuccessorAxisWeightedBound_ofPass params strategy eps hpass
  let diagonalBound :=
    mainFormalSuccessorDiagonalWeightedBound_ofPass params strategy eps hpass
  { axisWeightedBound := axisBound
    diagonalWeightedBound := diagonalBound
    recursiveSlices := hrec
    selfImprovementProducer := hself }

/-- Slice-recursion bridge data for the successor branch of `mainFormal`.

For each field element `x`, this package names the induction-hypothesis transport
fields that the `MainFormalSuccessorRecursiveSlices` definition currently hides:
a same-space projective strategy on the role-register space
`SameSpaceProjStrat params (Role × ι)` together with compatibility proofs
connecting it to the restricted slice from
`MainInductionStep.xRestrictedStrategy`.

When supplied together with a recursive induction hypothesis (see
`mainFormalSuccessorRecursiveSlices_ofSliceData`), this data can close the
`MainFormalSuccessorRecursiveSlices` requirement needed by
`MainFormalSuccessorBoundary`. -/
structure MainFormalSuccessorRecursiveSliceData (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) where
  /-- For each field element `x`, a same-space projective strategy on the
  role-register space that captures the restricted slice at `x`. -/
  sliceStrategy : Fq params → SameSpaceProjStrat params (Role × ι)
  /-- The slice strategy shares the symmetrization's bipartite state. -/
  sliceState_eq : ∀ x, (sliceStrategy x).state = (strategy.strategySymmetrization).state
  /-- The slice strategy's Alice point measurement matches the restricted
  point measurement from the main induction step.  (The Bob measurement is
  not needed for `MainFormalSuccessorRecursiveSlices`.) -/
  slicePoint_eq : ∀ x,
    (sliceStrategy x).pointMeasurementA =
    (MainInductionStep.xRestrictedStrategy params
      strategy.strategySymmetrization x).pointMeasurement
  /-- Each slice strategy passes LDT with the common symmetrized error `3 * eps`.

  Note: this structure constrains only `state` and `pointMeasurementA` of
  `sliceStrategy x` (Bob's measurement, axis-parallel/diagonal data, and the
  symmetry witnesses are unconstrained).  A downstream wiring of this bridge
  into the live `mainFormal` `sorry` will need additional compatibility
  fields before `slicePasses` becomes load-bearing for a recursive
  `mainFormal` call. -/
  slicePasses : ∀ x, (sliceStrategy x).PassesLowIndividualDegreeTest (3 * eps)

/-- Convert per-slice induction-hypothesis data into a
`MainFormalSuccessorRecursiveSlices` witness.

This is the abstract induction-step lemma for #1021.  Given the honest
`MainFormalSuccessorRecursiveSliceData` together with a recursive induction
hypothesis that delivers `mainInductionError`-bounded polynomial measurements
for each slice strategy, this rewrites the state and point-measurement
compatibilities to produce the exact `MainFormalSuccessorRecursiveSlices` field
needed by `MainFormalSuccessorBoundary`.

The induction hypothesis `hrecSlice` mirrors what `mainInductionPublicWrapper`
(or, equivalently, a recursive call to `mainFormal`) returns for the predecessor
dimension: a polynomial measurement on the role-register space with consistency
bounded by the main induction error evaluated at the restricted-profile bounds. -/
theorem mainFormalSuccessorRecursiveSlices_ofSliceData
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorDiagonalWeightedBound params strategy eps)
    (sliceData : MainFormalSuccessorRecursiveSliceData params strategy eps hpass)
    (hrecSlice : ∀ (x : Fq params),
      ∃ error : Error, ∃ G : Measurement (Polynomial params) (Role × ι),
        ConsRel (sliceData.sliceStrategy x).state
          (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas (sliceData.sliceStrategy x).pointMeasurementA)
          (polynomialEvaluationFamily params G.toSubMeas)
          error ∧
        error ≤
          let hrestrict :=
            mainFormalSuccessorRestrictionPackage params strategy eps hpass
              haxisWeightedBound hdiagonalWeightedBound
          MainInductionStep.mainInductionError params k
            (hrestrict.profile.axisParallel x)
            (hrestrict.profile.selfConsistency x)
            (hrestrict.profile.diagonal x)) :
    MainFormalSuccessorRecursiveSlices params strategy eps hpass k
      haxisWeightedBound hdiagonalWeightedBound := by
  intro x
  rcases hrecSlice x with ⟨error, G, hG, herr⟩
  refine ⟨error, G, ?_, herr⟩
  -- Rewrite the state and point measurement using the slice-data compatibilities
  simpa [sliceData.sliceState_eq x, sliceData.slicePoint_eq x] using hG
/-- Build the successor boundary from bridge inputs instead of the
already-packaged self-improvement producer.

This is the public-facing constructor for issue #1020: it wires the
honest per-slice Section 9 bridge inputs through the existing
`mainFormalSuccessorSelfImprovementProducer_ofBridgeInputs` conversion and
packages them together with the weighted restricted-probability fields and
the recursive slice witnesses into a `MainFormalSuccessorBoundary`.

The weighted restricted-probability fields are discharged from `hpass`
by the public Section 6 weighted-bound lemmas, matching the pattern of
`mainFormalSuccessorBoundary_ofRecursiveSelfImprovement`. -/
noncomputable def mainFormalSuccessorBoundary_ofBridgeInputs
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (hrec : MainFormalSuccessorRecursiveSlices params strategy eps hpass k
      (mainFormalSuccessorAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorDiagonalWeightedBound_ofPass params strategy eps hpass))
    (hbridge : MainFormalSuccessorSelfImprovementBridgeInputs params strategy eps hpass k
      (mainFormalSuccessorAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorDiagonalWeightedBound_ofPass params strategy eps hpass)) :
    MainFormalSuccessorBoundary params strategy eps hpass k :=
  let axisBound := mainFormalSuccessorAxisWeightedBound_ofPass params strategy eps hpass
  let diagonalBound :=
    mainFormalSuccessorDiagonalWeightedBound_ofPass params strategy eps hpass
  { axisWeightedBound := axisBound
    diagonalWeightedBound := diagonalBound
    recursiveSlices := hrec
    selfImprovementProducer :=
      mainFormalSuccessorSelfImprovementProducer_ofBridgeInputs params strategy eps hpass k
        axisBound diagonalBound hbridge }

/-- Successor-case Section 6 handoff for `mainFormal`.

This is the actual invocation of
`MainInductionStep.mainInductionPublicWrapper` on the role-register
symmetrization. It proves that, once the `MainFormalSuccessorBoundary` data are
available and the Section 6 side condition `400 * m * d ≤ k` holds, the public
wrapper returns the global polynomial measurement used by the later
unsymmetrization / Schwartz--Zippel / projectivization cascade.

Universe note: the explicit `[FieldModel.{0} params.q]` matches the Section 6
wrapper's universe; the eventual `mainFormal` residual closure must transport or
instantiate this same base-universe field model when choosing predecessor
parameters. -/
theorem mainFormalSuccessorMainInductionPublicWrapper
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (hd : 0 < params.d)
    (boundary : MainFormalSuccessorBoundary params strategy eps hpass k)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) (Role × ι),
      ConsRel (strategy.strategySymmetrization).state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (MainInductionStep.mainInductionError params.next k
          (3 * eps) (3 * eps) (3 * eps)) :=
  MainInductionStep.mainInductionPublicWrapper params
    (strategy := strategy.strategySymmetrization)
    (eps := 3 * eps) (delta := 3 * eps) (gamma := 3 * eps) (k := k)
    (SameSpaceProjStrat.strategySymmetrization_isGood_three_mul
      (strategy := strategy) (eps := eps) hpass)
    hd
    boundary.axisWeightedBound
    boundary.diagonalWeightedBound
    boundary.recursiveSlices
    boundary.selfImprovementProducer
    hk_pos hk

/-- Answer-valued successor-case weighted restricted-axis input for the
role-register symmetrization used by `mainFormal`. -/
def MainFormalSuccessorAnswerAxisWeightedBound (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error) : Prop :=
  avgOver (uniformDistribution (Fq params))
    (fun x => MainInductionStep.sliceTransverseDirectionWeight params *
      (MainInductionStep.xRestrictedAnswerSymStrat params
        strategy.strategySymmetrization x).axisParallelFailureProbability) ≤
    3 * eps

/-- Answer-valued successor-case weighted restricted-diagonal input for the
role-register symmetrization used by `mainFormal`. -/
def MainFormalSuccessorAnswerDiagonalWeightedBound (params : Parameters)
    [FieldModel params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error) : Prop :=
  avgOver (uniformDistribution (Fq params))
    (fun x => MainInductionStep.sliceTransverseDirectionWeight params *
      (MainInductionStep.xRestrictedAnswerSymStrat params
        strategy.strategySymmetrization x).diagonalFailureProbability) ≤
    3 * eps

/-- The answer-valued restricted-probability package on the role-register
symmetrization used in the successor branch of `mainFormal`. -/
noncomputable def mainFormalSuccessorAnswerRestrictionPackage
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (haxisWeightedBound : MainFormalSuccessorAnswerAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps) :
    MainInductionStep.AnswerSliceRestrictionPackage params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) :=
  MainInductionStep.answerMainInductionPublicRestrictionPackage
    params strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
    (SameSpaceProjStrat.strategySymmetrization_isGood_three_mul
      (strategy := strategy) (eps := eps) hpass)
    haxisWeightedBound hdiagonalWeightedBound

/-- Successor-case recursive slice witnesses for answer-valued restricted
strategies. -/
def MainFormalSuccessorAnswerRecursiveSlices (params : Parameters)
    [FieldModel.{0} params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAnswerAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps) : Prop :=
  let hrestrict :=
    mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  ∀ x,
    ∃ error : Error, ∃ G : Measurement (Polynomial params) (Role × ι),
      ConsRel (strategy.strategySymmetrization).state
        (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas
          (MainInductionStep.xRestrictedAnswerSymStrat params
            strategy.strategySymmetrization x).pointMeasurement)
        (polynomialEvaluationFamily params G.toSubMeas)
        error ∧
      error ≤
        MainInductionStep.mainInductionError params k
          (hrestrict.profile.axisParallel x)
          (hrestrict.profile.selfConsistency x)
          (hrestrict.profile.diagonal x)

/-- Successor-case answer-valued restricted-strategy self-improvement producer. -/
def MainFormalSuccessorAnswerSelfImprovementProducer (params : Parameters)
    [FieldModel.{0} params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (haxisWeightedBound : MainFormalSuccessorAnswerAxisWeightedBound params strategy eps)
    (hdiagonalWeightedBound :
      MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps) : Type _ :=
  let hrestrict :=
    mainFormalSuccessorAnswerRestrictionPackage params strategy eps hpass
      haxisWeightedBound hdiagonalWeightedBound
  ∀ hinduction :
    MainInductionStep.AnswerPerSliceInductionPackage params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) hrestrict k,
    MainInductionStep.AnswerSelfImprovementPackage params
      strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps) k
      hrestrict hinduction

/-- Answer-valued successor-case Section 6 boundary inputs for `mainFormal`. -/
structure MainFormalSuccessorAnswerBoundary (params : Parameters)
    [FieldModel.{0} params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ) where
  axisWeightedBound :
    MainFormalSuccessorAnswerAxisWeightedBound params strategy eps
  diagonalWeightedBound :
    MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps
  recursiveSlices :
    MainFormalSuccessorAnswerRecursiveSlices params strategy eps hpass k
      axisWeightedBound diagonalWeightedBound
  selfImprovementProducer :
    MainFormalSuccessorAnswerSelfImprovementProducer params strategy eps hpass k
      axisWeightedBound diagonalWeightedBound

/-- The answer-valued restricted-probabilities theorem supplies the successor-case
weighted axis-parallel input. -/
theorem mainFormalSuccessorAnswerAxisWeightedBound_ofPass
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    MainFormalSuccessorAnswerAxisWeightedBound params strategy eps :=
  MainInductionStep.answer_weighted_axisParallel_bound params
    strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
    (SameSpaceProjStrat.strategySymmetrization_isGood_three_mul
      (strategy := strategy) (eps := eps) hpass)

/-- The answer-valued restricted-probabilities theorem supplies the successor-case
weighted diagonal-line input. -/
theorem mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    MainFormalSuccessorAnswerDiagonalWeightedBound params strategy eps :=
  MainInductionStep.answer_weighted_diagonal_bound params
    strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
    (SameSpaceProjStrat.strategySymmetrization_isGood_three_mul
      (strategy := strategy) (eps := eps) hpass)

/-- Build the answer-valued successor boundary once the two still-external slice
recursion and restricted-strategy self-improvement inputs are supplied. -/
def mainFormalSuccessorAnswerBoundary_ofRecursiveSelfImprovement
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (hrec : MainFormalSuccessorAnswerRecursiveSlices params strategy eps hpass k
      (mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass))
    (hself : MainFormalSuccessorAnswerSelfImprovementProducer params strategy eps hpass k
      (mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass)
      (mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass)) :
    MainFormalSuccessorAnswerBoundary params strategy eps hpass k :=
  let axisBound := mainFormalSuccessorAnswerAxisWeightedBound_ofPass params strategy eps hpass
  let diagonalBound :=
    mainFormalSuccessorAnswerDiagonalWeightedBound_ofPass params strategy eps hpass
  { axisWeightedBound := axisBound
    diagonalWeightedBound := diagonalBound
    recursiveSlices := hrec
    selfImprovementProducer := hself }

/-- Answer-valued successor-case Section 6 handoff for `mainFormal`. -/
theorem mainFormalSuccessorAnswerMainInductionPublicWrapper
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (hd : 0 < params.d)
    (boundary : MainFormalSuccessorAnswerBoundary params strategy eps hpass k)
    (hk_pos : 1 ≤ k)
    (hk : 400 * params.m * params.d ≤ k) :
    ∃ G : Measurement (Polynomial params.next) (Role × ι),
      ConsRel (strategy.strategySymmetrization).state
        (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement)
        (polynomialEvaluationFamily params.next G.toSubMeas)
        (MainInductionStep.mainInductionError params.next k
          (3 * eps) (3 * eps) (3 * eps)) :=
  MainInductionStep.answerMainInductionPublicWrapper params
    (strategy := strategy.strategySymmetrization)
    (eps := 3 * eps) (delta := 3 * eps) (gamma := 3 * eps) (k := k)
    (SameSpaceProjStrat.strategySymmetrization_isGood_three_mul
      (strategy := strategy) (eps := eps) hpass)
    hd
    boundary.axisWeightedBound
    boundary.diagonalWeightedBound
    boundary.recursiveSlices
    boundary.selfImprovementProducer
    hk_pos hk

/-- The Section 3 specialization of the main-induction `ν` after Step 1
symmetrization.

Paper lines 68--75 apply `thm:main-induction` to the symmetrized strategy with
errors `(3ε, 3ε, 3ε)` and then coarsen its `ν` to the Section 3 scalar cascade.
This definition keeps the pre-coarsened main-induction quantity available for the
final assembly. -/
noncomputable def mainFormalInductionNu (params : Parameters) (k : ℕ) (eps : Error) : Error :=
  MainInductionStep.mainInductionNu params k (3 * eps) (3 * eps) (3 * eps)

/-- The `σ` built from `mainFormalInductionNu` is definitionally the Section 6
main-induction error at `(3ε, 3ε, 3ε)`.

This is the exact scalar handoff between paper lines 75--81 and the cascade
notation used from line 133 onward. -/
theorem mainFormalCascadeSigma_eq_mainInductionError (params : Parameters)
    (k : ℕ) (eps : Error) :
    cascadeSigma params k (mainFormalInductionNu params k eps) =
      MainInductionStep.mainInductionError params k (3 * eps) (3 * eps) (3 * eps) :=
  rfl

/-- Nonnegativity of the symmetrized main-induction `ν` under the standing
cascade hypotheses. -/
theorem mainFormalInductionNu_nonneg {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    0 ≤ mainFormalInductionNu params k eps := by
  unfold mainFormalInductionNu MainInductionStep.mainInductionNu
  have hthree_eps_nonneg : 0 ≤ 3 * eps := by nlinarith [h.hepsNN]
  have hthree_term : 0 ≤ Real.rpow (3 * eps) (1 / (1024 : Error)) :=
    Real.rpow_nonneg hthree_eps_nonneg _
  have hdq_term : 0 ≤ Real.rpow ((params.d : Error) / (params.q : Error))
      (1 / (1024 : Error)) :=
    Real.rpow_nonneg h.dqNN _
  have hsum : 0 ≤ Real.rpow (3 * eps) (1 / (1024 : Error)) +
      Real.rpow (3 * eps) (1 / (1024 : Error)) +
      Real.rpow (3 * eps) (1 / (1024 : Error)) +
      Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)) := by
    nlinarith
  have hcoeff : 0 ≤ 1000 * ((k : Error) ^ (2 : ℕ)) *
      ((params.m : Error) ^ (2 : ℕ)) := by
    positivity
  exact mul_nonneg hcoeff hsum

/-- Paper lines 71--73: after applying main induction to the symmetrized strategy,
the resulting `ν` at errors `(3ε,3ε,3ε)` is bounded by the coarser Section 3
quantity `10000 k² m² (ε^(1/1024) + (d/q)^(1/1024))`. -/
theorem mainFormalInductionNu_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) :
    mainFormalInductionNu params k eps ≤
      10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
        (Real.rpow eps (1 / (1024 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))) := by
  unfold mainFormalInductionNu MainInductionStep.mainInductionNu
  set r : Error := 1 / (1024 : Error)
  set e : Error := Real.rpow eps r
  set dq : Error := Real.rpow ((params.d : Error) / (params.q : Error)) r
  have he_nonneg : 0 ≤ e := by
    simpa [e, r] using Real.rpow_nonneg h.hepsNN (1 / (1024 : Error))
  have hdq_nonneg : 0 ≤ dq := by
    simpa [dq, r] using Real.rpow_nonneg h.dqNN (1 / (1024 : Error))
  have hthree_pow_le : Real.rpow (3 * eps) r ≤ 3 * e := by
    calc
      Real.rpow (3 * eps) r = Real.rpow (3 : Error) r * e := by
        simpa [e, r] using
          (Real.mul_rpow (x := (3 : Error)) (y := eps) (z := (1 / (1024 : Error)))
            (by norm_num) h.hepsNN)
      _ ≤ 3 * e := by
        have h3 : Real.rpow (3 : Error) r ≤ 3 := by
          simpa [r, Real.rpow_one] using
            Real.rpow_le_self_of_one_le (x := (3 : Error)) (y := (1 / (1024 : Error)))
              (by norm_num) (by norm_num)
        exact mul_le_mul_of_nonneg_right h3 he_nonneg
  have hsum :
      Real.rpow (3 * eps) r + Real.rpow (3 * eps) r + Real.rpow (3 * eps) r + dq ≤
        10 * (e + dq) := by
    nlinarith [hthree_pow_le, he_nonneg, hdq_nonneg]
  have hcoeff_nonneg :
      0 ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) := by
    positivity
  calc
    1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
        (Real.rpow (3 * eps) r + Real.rpow (3 * eps) r + Real.rpow (3 * eps) r + dq)
      ≤ 1000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
          (10 * (e + dq)) := by
        exact mul_le_mul_of_nonneg_left hsum hcoeff_nonneg
    _ = 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
          (e + dq) := by ring

/-- If the unscaled Step 8 envelope is already at least `1`, then the public
`mainFormalError` envelope is also at least `1`. -/
theorem mainFormalError_ge_one_of_one_le_envelope
    (params : Parameters) (k : ℕ) (eps : Error)
    (hk0 : 0 < k)
    (henv : 1 ≤ mainFormalEnvelope params k eps) :
    1 ≤ mainFormalError params k eps := by
  rw [mainFormalError_eq_envelope]
  have hk : (1 : Error) ≤ (k : Error) := by exact_mod_cast hk0
  have hm : (1 : Error) ≤ (params.m : Error) := by exact_mod_cast params.hm
  have hk2 : (1 : Error) ≤ ((k : Error) ^ (2 : ℕ)) := by
    simpa using one_le_pow₀ (n := (2 : ℕ)) hk
  have hm4 : (1 : Error) ≤ ((params.m : Error) ^ (4 : ℕ)) := by
    simpa using one_le_pow₀ (n := (4 : ℕ)) hm
  have hcoeff :
      (1 : Error) ≤ 100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
    nlinarith
  have hcoeffNN :
      0 ≤ 100000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (4 : ℕ)) := by
    positivity
  have hmul := mul_le_mul hcoeff henv (by norm_num : (0 : Error) ≤ 1) hcoeffNN
  simpa using hmul

/-- If `ε > 1`, then the final error envelope has already saturated past `1`.
This discharges the non-paper regime before invoking the paper's Step 8 cascade,
which assumes `ε ≤ 1`. -/
theorem mainFormalError_ge_one_of_one_lt_eps
    (params : Parameters) (k : ℕ) {eps : Error}
    (hk0 : 0 < k) (heps : 1 < eps) :
    1 ≤ mainFormalError params k eps := by
  have hepsPow : 1 ≤ Real.rpow eps (1 / (40000 : Error)) := by
    exact Real.one_le_rpow heps.le (by positivity)
  have hdqPowNN : 0 ≤ Real.rpow ((params.d : Error) / (params.q : Error))
      (1 / (40000 : Error)) := by
    exact Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) params.q_cast_pos.le) _
  have hExpNN :
      0 ≤ Real.exp (-((k : Error) / (2560000 * ((params.m : Error) ^ (2 : ℕ))))) :=
    Real.exp_nonneg _
  have henv : 1 ≤ mainFormalEnvelope params k eps := by
    unfold mainFormalEnvelope
    linarith
  exact mainFormalError_ge_one_of_one_le_envelope params k eps hk0 henv

/-- If `d > q`, then the final error envelope has already saturated past `1`.
Thus the nontrivial Step 8 branch may assume the paper's ambient `d/q ≤ 1`
regime. -/
theorem mainFormalError_ge_one_of_q_lt_d
    (params : Parameters) (k : ℕ) (eps : Error)
    (hk0 : 0 < k) (hepsNN : 0 ≤ eps)
    (hqd : (params.q : Error) < (params.d : Error)) :
    1 ≤ mainFormalError params k eps := by
  have hdq_gt_one : 1 < (params.d : Error) / (params.q : Error) := by
    exact (one_lt_div params.q_cast_pos).2 hqd
  have hdqPow : 1 ≤ Real.rpow ((params.d : Error) / (params.q : Error))
      (1 / (40000 : Error)) := by
    exact Real.one_le_rpow hdq_gt_one.le (by positivity)
  have hepsPowNN : 0 ≤ Real.rpow eps (1 / (40000 : Error)) :=
    Real.rpow_nonneg hepsNN _
  have hExpNN :
      0 ≤ Real.exp (-((k : Error) / (2560000 * ((params.m : Error) ^ (2 : ℕ))))) :=
    Real.exp_nonneg _
  have henv : 1 ≤ mainFormalEnvelope params k eps := by
    unfold mainFormalEnvelope
    linarith
  exact mainFormalError_ge_one_of_one_le_envelope params k eps hk0 henv

/-- In the non-vacuous branch of `mainFormal`, the standing scalar hypotheses of
Step 8 follow from the theorem's basic positivity data.

If either `ε > 1` or `d > q`, the final error `mainFormalError` is already at
least `1`, so `mainFormal_trivial_witness` handles the theorem. Hence under
`¬ 1 ≤ mainFormalError params k eps` we may safely enter the paper's cascade
regime `0 ≤ ε ≤ 1` and `d/q ≤ 1`. -/
theorem cascadeHypotheses_of_not_mainFormalError_ge_one
    {params : Parameters} {k : ℕ} {eps : Error}
    (hepsNN : 0 ≤ eps) (hk0 : 0 < k)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    CascadeHypotheses params k eps where
  hk := by exact_mod_cast hk0
  hm := by exact_mod_cast params.hm
  hepsNN := hepsNN
  hepsOne := by
    by_contra heps_not
    exact hsmall (mainFormalError_ge_one_of_one_lt_eps params k hk0 (lt_of_not_ge heps_not))
  hdq := by
    by_contra hdq_not
    exact hsmall (mainFormalError_ge_one_of_q_lt_d params k eps hk0 hepsNN
      (lt_of_not_ge hdq_not))
  hqPos := params.q_cast_pos

/-- Scalar hypotheses for the Section 3 error cascade of `mainFormal`.

This package is intentionally scalar-only. It does not assert any measurement
transport. Its fields are precisely the hypotheses needed to invoke the already
formalized Step 8 bound `errorCascade_le_mainFormalError` on the
main-induction `ν` produced after symmetrization (paper lines 68--75). The
remaining proof of `mainFormal` must still derive these scalar side conditions
from the theorem hypotheses or route to the vacuous branch when they fail. -/
structure MainFormalCascadeScalars (params : Parameters) (eps : Error) (k : ℕ) : Prop where
  /-- Standing scalar regime for the paper's cascade estimates. -/
  cascadeHypotheses : CascadeHypotheses params k eps
  /-- Nonnegativity of the main-induction `ν` at `(3ε, 3ε, 3ε)`. -/
  inductionNu_nonneg : 0 ≤ mainFormalInductionNu params k eps
  /-- Paper line 71--73 coarsening of the main-induction `ν`. -/
  inductionNu_bound :
    mainFormalInductionNu params k eps ≤
      10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
        (Real.rpow eps (1 / (1024 : Error)) +
          Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error)))

namespace MainFormalCascadeScalars

/-- Build the scalar package once the standing cascade hypotheses hold; the
main-induction `ν` nonnegativity and paper line 71--73 coarsening are discharged
by the checked scalar lemmas above. -/
theorem ofCascadeHypotheses {params : Parameters} {eps : Error} {k : ℕ}
    (h : CascadeHypotheses params k eps) :
    MainFormalCascadeScalars params eps k where
  cascadeHypotheses := h
  inductionNu_nonneg := mainFormalInductionNu_nonneg h
  inductionNu_bound := mainFormalInductionNu_bound h

/-- Build the scalar package in the non-vacuous branch of `mainFormal`.

The branch hypothesis `¬ 1 ≤ mainFormalError params k eps` rules out the
non-paper regimes `ε > 1` and `d > q`, while `hepsNN` and `hk0` supply the
remaining scalar positivity hypotheses. -/
theorem ofNontrivialMainFormal {params : Parameters} {eps : Error} {k : ℕ}
    (hepsNN : 0 ≤ eps) (hk0 : 0 < k)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    MainFormalCascadeScalars params eps k :=
  ofCascadeHypotheses (cascadeHypotheses_of_not_mainFormalError_ge_one hepsNN hk0 hsmall)

/-- The paper's `σ`, built from the symmetrized main-induction `ν`. -/
noncomputable def sigma {params : Parameters} {eps : Error} {k : ℕ}
    (_scalars : MainFormalCascadeScalars params eps k) : Error :=
  cascadeSigma params k (mainFormalInductionNu params k eps)

/-- The paper's `ζ₁ = 2σ + 2√(3ε + 2σ) + md/q`. -/
noncomputable def zeta1 {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) : Error :=
  cascadeZeta1 params eps scalars.sigma

/-- The formal Step 6 scalar
`ζ₂ = 200ζ₁^(1/4) + 42ζ₁^(1/8)`, widening the paper's printed coefficient
`40` to absorb the residual completion term. -/
noncomputable def zeta2 {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) : Error :=
  cascadeZeta2 scalars.zeta1

/-- The paper's self-consistency scalar `ζ₃ = 6ζ₁ + 6ζ₂`. -/
noncomputable def zeta3 {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) : Error :=
  cascadeZeta3 scalars.zeta1 scalars.zeta2

/-- The paper's point-consistency scalar `ζ₄ = 2σ + 2√(ζ₁ + ζ₃/2)`. -/
noncomputable def zeta4 {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) : Error :=
  cascadeZeta4 scalars.sigma scalars.zeta1 scalars.zeta3

private theorem cascadeBounds {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) :
    scalars.sigma ≤ mainFormalError params k eps ∧
      scalars.zeta1 ≤ mainFormalError params k eps ∧
      scalars.zeta2 ≤ mainFormalError params k eps ∧
      scalars.zeta3 ≤ 2 * mainFormalError params k eps ∧
      scalars.zeta4 ≤ mainFormalError params k eps := by
  exact errorCascade_le_mainFormalError
    (params := params) (k := k) (eps := eps)
    (ν := mainFormalInductionNu params k eps)
    (σ := scalars.sigma) (ζ₁ := scalars.zeta1)
    (ζ₂ := scalars.zeta2) (ζ₃ := scalars.zeta3)
    scalars.cascadeHypotheses scalars.inductionNu_nonneg scalars.inductionNu_bound
    rfl rfl rfl rfl

/-- Nonnegativity of the native cascade `σ`. -/
theorem sigma_nonneg {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) :
    0 ≤ scalars.sigma := by
  unfold sigma cascadeSigma
  positivity [scalars.inductionNu_nonneg]

/-- Nonnegativity of the native cascade `ζ₁`. -/
theorem zeta1_nonneg {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) :
    0 ≤ scalars.zeta1 := by
  have hσ : 0 ≤ scalars.sigma := sigma_nonneg scalars
  have hdq : 0 ≤ (params.d : Error) / (params.q : Error) :=
    scalars.cascadeHypotheses.dqNN
  unfold zeta1 cascadeZeta1
  positivity [hσ, scalars.cascadeHypotheses.hepsNN, hdq]

/-- Step 8 absorption for the native `ζ₁` target. -/
theorem zeta1_le_mainFormalError {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) :
    scalars.zeta1 ≤ mainFormalError params k eps :=
  (cascadeBounds scalars).2.1

/-- In the non-vacuous branch, the cascade scalar `ζ₁` lies in the unit interval. -/
theorem zeta1_le_one_of_not_mainFormalError_ge_one
    {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    scalars.zeta1 ≤ 1 := by
  exact le_of_lt <|
    (zeta1_le_mainFormalError scalars).trans_lt (lt_of_not_ge hsmall)

/-- The formal `ζ₂` scalar absorbs the literal Step 6 orthonormalize-and-complete
error in the non-vacuous branch. -/
theorem orthonormalizeAndCompleteError_zeta1_le_zeta2
    {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1 ≤
      scalars.zeta2 := by
  have hζ0 : 0 ≤ scalars.zeta1 := zeta1_nonneg scalars
  have hζ1 : scalars.zeta1 ≤ 1 :=
    zeta1_le_one_of_not_mainFormalError_ge_one scalars hsmall
  simpa [zeta2, cascadeZeta2] using
    MakingMeasurementsProjective.orthonormalizeAndCompleteError_le_absorbedZeta2
      (ζ := scalars.zeta1) hζ0 hζ1

/-- Step 8 absorption for the native `ζ₄` point-consistency targets. -/
theorem zeta4_le_mainFormalError {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) :
    scalars.zeta4 ≤ mainFormalError params k eps :=
  (cascadeBounds scalars).2.2.2.2

/-- Step 8 absorption for the native `ζ₃/2` self-consistency target. -/
theorem zeta3_div_two_le_mainFormalError {params : Parameters} {eps : Error} {k : ℕ}
    (scalars : MainFormalCascadeScalars params eps k) :
    scalars.zeta3 / 2 ≤ mainFormalError params k eps := by
  have hzeta3 := (cascadeBounds scalars).2.2.2.1
  linarith

end MainFormalCascadeScalars

/-- Section 6 role-register induction output used by the `mainFormal` assembly.

The main-induction call is applied to `strategy.strategySymmetrization`, whose
local Hilbert space is indexed by `Role × ι`. This structure records exactly the
piece of that call needed by the later unsymmetrization step: a polynomial POVM
on the role register together with its symmetrized point-consistency estimate at
the cascade scalar `σ`.  It deliberately does not assert the factor-two
unsymmetrized estimates; those remain the separate content of
`UnsymmetrizationBridgePackage`. -/
structure MainFormalRoleMeasurementPackage
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The role-register polynomial POVM produced by Section 6. -/
  roleMeasurement : Measurement (Polynomial params) (Role × ι)
  /-- The Section 6 consistency estimate, rewritten to the Section 3 scalar `σ`. -/
  symConsistency :
    ConsRel (strategy.strategySymmetrization).state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement)
      (polynomialEvaluationFamily params roleMeasurement.toSubMeas)
      scalars.sigma

namespace MainFormalRoleMeasurementPackage

/-- View a Section 6 main-induction witness as a
`MainFormalRoleMeasurementPackage`.

The only proof step is scalar bookkeeping: `scalars.sigma` is definitionally
`cascadeSigma params k (mainFormalInductionNu params k eps)`, and
`mainFormalCascadeSigma_eq_mainInductionError` identifies that quantity with the
`MainInductionStep.mainInductionError` returned by the Section 6 theorem at the
symmetrized errors `(3ε,3ε,3ε)`. -/
theorem ofMainInductionWitness
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (hsection6 :
      ∃ G : Measurement (Polynomial params) (Role × ι),
        ConsRel (strategy.strategySymmetrization).state
          (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement)
          (polynomialEvaluationFamily params G.toSubMeas)
          (MainInductionStep.mainInductionError params k
            (3 * eps) (3 * eps) (3 * eps))) :
    Nonempty (MainFormalRoleMeasurementPackage params strategy eps k scalars) := by
  rcases hsection6 with ⟨G, hG⟩
  refine ⟨{ roleMeasurement := G, symConsistency := ?_ }⟩
  simpa [MainFormalCascadeScalars.sigma, mainFormalCascadeSigma_eq_mainInductionError]
    using hG

/-- Base-case constructor for the role-register Section 6 induction output.

When `params.m = 1`, the checked `strategySymmetrization_mainInductionBaseCase`
produces the Section 6 measurement on the role-register symmetrization; this
constructor rewrites its error to the `σ` used by the Section 3 cascade. -/
theorem ofBaseCase
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm1 : params.m = 1) :
    Nonempty (MainFormalRoleMeasurementPackage params strategy eps k scalars) :=
  ofMainInductionWitness params strategy eps k scalars
    (strategySymmetrization_mainInductionBaseCase params strategy eps hpass k hm1)

/-- Successor-case constructor for the role-register Section 6 induction output.

In the large-dimension branch, the public successor wrapper applies to the
role-register symmetrization once the honest `MainFormalSuccessorBoundary` data
and the Section 6 side condition `400 * params.m * params.d ≤ k` are available.
This lemma exposes the resulting global polynomial measurement in the exact
`σ`-normalized form consumed by the later unsymmetrization bridge. -/
theorem ofSuccessorBoundary
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params.next eps k)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hd : 0 < params.d)
    (boundary : MainFormalSuccessorBoundary params strategy eps hpass k)
    (hk_pos : 1 ≤ k) (hk_large : 400 * params.m * params.d ≤ k) :
    Nonempty (MainFormalRoleMeasurementPackage params.next strategy eps k scalars) :=
  ofMainInductionWitness params.next strategy eps k scalars
    (mainFormalSuccessorMainInductionPublicWrapper params strategy eps hpass k hd boundary
      hk_pos hk_large)

/-- Build the formal unsymmetrization bridge from the role-register Section 6
measurement output.

The lower-level Step 3 theorem
`UnsymmetrizationBridgePackage.ofSymConsistency` proves the two factor-two
principal-block estimates directly from the symmetrized consistency field, so no
extra point-consistency hypotheses are needed here. -/
def toUnsymmetrizationBridge
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (pkg : MainFormalRoleMeasurementPackage params strategy eps k scalars) :
    UnsymmetrizationBridgePackage params strategy pkg.roleMeasurement scalars.sigma :=
  UnsymmetrizationBridgePackage.ofSymConsistency params strategy pkg.roleMeasurement
    scalars.sigma pkg.symConsistency

end MainFormalRoleMeasurementPackage

/-- Residual Section 6 role-register induction witness for `mainFormal`.

This isolates the first field of the former role-register completion residual:
it asks only for the Section 6 role-register polynomial measurement and its
symmetrized consistency estimate at the pre-cascade main-induction error.  The
constructors below show how the already-checked base case and the syntactic
successor wrapper produce this residual. For an arbitrary current parameter
bundle, the inverse predecessor transport needed to apply the successor wrapper
remains explicit upstream work; the public large-`k` hypothesis is supplied to
the successor-branch conversion instead of being hidden in this residual. -/
structure MainFormalRolePackageResidual
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ) where
  /-- Section 6 role-register measurement before rewriting its error to `σ`. -/
  roleMeasurement : Measurement (Polynomial params) (Role × ι)
  /-- Section 6 consistency estimate before rewriting its error to `σ`. -/
  section6Consistency :
    ConsRel (strategy.strategySymmetrization).state
      (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement)
      (polynomialEvaluationFamily params roleMeasurement.toSubMeas)
      (MainInductionStep.mainInductionError params k
        (3 * eps) (3 * eps) (3 * eps))

namespace MainFormalRolePackageResidual

/-- Repackage a raw Section 6 main-induction witness as the isolated role-package
residual consumed by the final `mainFormal` assembly. -/
theorem ofMainInductionWitness
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hsection6 :
      ∃ G : Measurement (Polynomial params) (Role × ι),
        ConsRel (strategy.strategySymmetrization).state
          (uniformDistribution (Point params))
          (IdxProjMeas.toIdxSubMeas (strategy.strategySymmetrization).pointMeasurement)
          (polynomialEvaluationFamily params G.toSubMeas)
          (MainInductionStep.mainInductionError params k
            (3 * eps) (3 * eps) (3 * eps))) :
    Nonempty (MainFormalRolePackageResidual params strategy eps hpass k) := by
  rcases hsection6 with ⟨G, hG⟩
  exact ⟨{ roleMeasurement := G, section6Consistency := hG }⟩

/-- Convert the isolated Section 6 role-register residual into the output consumed
by unsymmetrization. -/
def toRoleMeasurementPackage
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    (residual : MainFormalRolePackageResidual params strategy eps hpass k)
    (scalars : MainFormalCascadeScalars params eps k) :
    MainFormalRoleMeasurementPackage params strategy eps k scalars where
  roleMeasurement := residual.roleMeasurement
  symConsistency := by
    simpa [MainFormalCascadeScalars.sigma, mainFormalCascadeSigma_eq_mainInductionError]
      using residual.section6Consistency

/-- Base-case constructor for the isolated role-register residual. -/
theorem ofBaseCase
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hm1 : params.m = 1) :
    Nonempty (MainFormalRolePackageResidual params strategy eps hpass k) := by
  exact ofMainInductionWitness params strategy eps k hpass
    (strategySymmetrization_mainInductionBaseCase params strategy eps hpass k hm1)

/-- Successor constructor for the isolated role-register residual in the syntactic
`params.next` case.

This exposes the exact remaining Section 6 data for the large-`k` branch:
`MainFormalSuccessorBoundary` plus the side condition
`400 * params.m * params.d ≤ k`.  Turning an arbitrary non-base `params` into this
syntactic successor form still requires a separate predecessor-transport theorem. -/
theorem ofSuccessorBoundary
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hd : 0 < params.d)
    (boundary : MainFormalSuccessorBoundary params strategy eps hpass k)
    (hk_pos : 1 ≤ k) (hk_large : 400 * params.m * params.d ≤ k) :
    Nonempty (MainFormalRolePackageResidual params.next strategy eps hpass k) := by
  exact ofMainInductionWitness params.next strategy eps k hpass
    (mainFormalSuccessorMainInductionPublicWrapper params strategy eps hpass k hd boundary
      hk_pos hk_large)

/-- Build the role-register measurement package produced by a concrete
role-package residual. -/
def rolePackage
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    (residual : MainFormalRolePackageResidual params strategy eps hpass k)
    (scalars : MainFormalCascadeScalars params eps k) :
    MainFormalRoleMeasurementPackage params strategy eps k scalars :=
  residual.toRoleMeasurementPackage scalars

end MainFormalRolePackageResidual

/-- Reuse the current base-universe field model on the predecessor of a
successor decomposition.

If `successor.pred.next = params`, then `successor.pred.q = params.q`; this helper
transports the ambient base-universe field model along that cardinality equality.
The explicit equality cast keeps the transport visible to callers, rather than
hiding it behind a tactic-mode `rw; infer_instance` definition. -/
noncomputable def fieldModelOfSuccessorDecomposition
    {params : Parameters} [FieldModel.{0} params.q]
    (successor : Parameters.SuccessorDecomposition params) :
    FieldModel.{0} successor.pred.q :=
  let h : successor.pred.q = params.q := by
    have hnext := congrArg Parameters.q successor.next_eq
    simpa [Parameters.next] using hnext
  h ▸ inferInstance

/-- View a strategy over `params` as a strategy over the syntactic successor in a
bundled predecessor decomposition.

This helper is intentionally aligned with the base-universe field-model API used
by the current Section 6 public successor wrapper. -/
noncomputable def projStratTransportSuccessor
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι)
    (successor : Parameters.SuccessorDecomposition params) :
    letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
    SameSpaceProjStrat successor.pred.next ι := by
  classical
  rcases successor with ⟨pred, hnext⟩
  subst params
  exact strategy

/-- Transport the low-individual-degree passing proof across a bundled predecessor
identity, using the same base-universe field-model transport as
`projStratTransportSuccessor`. -/
theorem passesLowIndividualDegreeTest_transportSuccessor
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error}
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (successor : Parameters.SuccessorDecomposition params) :
    letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
    (projStratTransportSuccessor strategy successor).PassesLowIndividualDegreeTest eps := by
  rcases successor with ⟨pred, hnext⟩
  subst params
  simpa [projStratTransportSuccessor, fieldModelOfSuccessorDecomposition] using hpass

/-- Successor-branch data for producing the Section 6 role package.

This is narrower than an arbitrary `MainFormalRolePackageResidual`: it contains an
explicit predecessor `pred` with `pred.next = params` and the successor-boundary
data for the transported strategy over `pred.next`. The Section 6 large-`k`
side condition is supplied directly to the conversion from the public theorem's
current-dimension hypothesis and then weakened to the predecessor dimension. -/
structure MainFormalRolePackageSuccessorResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ) where
  /-- A predecessor whose successor is the current parameter bundle. -/
  successor : Parameters.SuccessorDecomposition params
  /-- The bundled successor-boundary inputs for the transported strategy. -/
  boundary :
    letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
    MainFormalSuccessorBoundary successor.pred
      (projStratTransportSuccessor strategy successor) eps
      (passesLowIndividualDegreeTest_transportSuccessor hpass successor) k
  /-- Positivity of the predecessor degree parameter, needed by the Section 6 wrapper. -/
  dimensionPositive : 0 < successor.pred.d
  /-- The positive-`k` side condition used by the Section 6 wrapper. -/
  kPositive : 1 ≤ k

namespace MainFormalRolePackageSuccessorResidual

/-- Convert explicit successor-branch data into the isolated Section 6 role
package residual, using the public current-dimension large-`k` hypothesis. -/
theorem toRolePackageResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    (residual : MainFormalRolePackageSuccessorResidual params strategy eps hpass k)
    (hk_large : 400 * params.m * params.d ≤ k) :
    Nonempty (MainFormalRolePackageResidual params strategy eps hpass k) := by
  rcases residual with ⟨⟨pred, hnext⟩, boundary, hd, hk_pos⟩
  subst params
  have hk_pred : 400 * pred.m * pred.d ≤ k := by
    have hm_le : pred.m ≤ pred.m + 1 := Nat.le_succ pred.m
    have hmono : 400 * pred.m * pred.d ≤ 400 * (pred.m + 1) * pred.d :=
      Nat.mul_le_mul_right pred.d (Nat.mul_le_mul_left 400 hm_le)
    exact le_trans hmono (by simpa [Parameters.next] using hk_large)
  -- Keep the transported predecessor instance explicit: `boundary` was stored
  -- under `fieldModelOfSuccessorDecomposition`, and the synthesized canonical
  -- `FieldModel.{0} pred.q` is not definitionally the same instance.
  letI : FieldModel.{0} pred.q :=
    fieldModelOfSuccessorDecomposition (params := pred.next) ⟨pred, rfl⟩
  let transportedStrategy : SameSpaceProjStrat pred.next ι :=
    projStratTransportSuccessor strategy ⟨pred, rfl⟩
  have transportedPass : transportedStrategy.PassesLowIndividualDegreeTest eps := by
    simpa [transportedStrategy] using
      (passesLowIndividualDegreeTest_transportSuccessor hpass ⟨pred, rfl⟩)
  have boundary' :
      MainFormalSuccessorBoundary pred transportedStrategy eps transportedPass k := by
    simpa [transportedStrategy, transportedPass] using boundary
  rcases MainFormalRolePackageResidual.ofSuccessorBoundary pred transportedStrategy eps k
      transportedPass hd boundary' hk_pos hk_pred with ⟨roleResidual⟩
  refine ⟨{ roleMeasurement := roleResidual.roleMeasurement, section6Consistency := ?_ }⟩
  simpa [transportedStrategy, projStratTransportSuccessor, fieldModelOfSuccessorDecomposition]
    using roleResidual.section6Consistency

/-- Constructor for the common syntactic-successor case. -/
def ofSyntacticSuccessor
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hd : 0 < params.d)
    (boundary : MainFormalSuccessorBoundary params strategy eps hpass k)
    (hk_pos : 1 ≤ k) :
    MainFormalRolePackageSuccessorResidual params.next strategy eps hpass k where
  successor := ⟨params, rfl⟩
  boundary := by
    simpa using boundary
  dimensionPositive := hd
  kPositive := hk_pos

end MainFormalRolePackageSuccessorResidual

/-- Answer-valued successor-branch data for producing the Section 6 role package. -/
structure MainFormalRolePackageAnswerSuccessorResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ) where
  /-- A predecessor whose successor is the current parameter bundle. -/
  successor : Parameters.SuccessorDecomposition params
  /-- The bundled answer-valued successor-boundary inputs for the transported strategy. -/
  boundary :
    letI : FieldModel.{0} successor.pred.q := fieldModelOfSuccessorDecomposition successor
    MainFormalSuccessorAnswerBoundary successor.pred
      (projStratTransportSuccessor strategy successor) eps
      (passesLowIndividualDegreeTest_transportSuccessor hpass successor) k
  /-- Positivity of the predecessor degree parameter, needed by the Section 6 wrapper. -/
  dimensionPositive : 0 < successor.pred.d
  /-- The positive-`k` side condition used by the Section 6 wrapper. -/
  kPositive : 1 ≤ k

namespace MainFormalRolePackageAnswerSuccessorResidual

/-- Convert explicit answer-valued successor-branch data into the isolated Section 6
role-package residual, using the public current-dimension large-`k` hypothesis. -/
theorem toRolePackageResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    (residual : MainFormalRolePackageAnswerSuccessorResidual params strategy eps hpass k)
    (hk_large : 400 * params.m * params.d ≤ k) :
    Nonempty (MainFormalRolePackageResidual params strategy eps hpass k) := by
  rcases residual with ⟨⟨pred, hnext⟩, boundary, hd, hk_pos⟩
  subst params
  have hk_pred : 400 * pred.m * pred.d ≤ k := by
    have hm_le : pred.m ≤ pred.m + 1 := Nat.le_succ pred.m
    have hmono : 400 * pred.m * pred.d ≤ 400 * (pred.m + 1) * pred.d :=
      Nat.mul_le_mul_right pred.d (Nat.mul_le_mul_left 400 hm_le)
    exact le_trans hmono (by simpa [Parameters.next] using hk_large)
  letI : FieldModel.{0} pred.q :=
    fieldModelOfSuccessorDecomposition (params := pred.next) ⟨pred, rfl⟩
  let transportedStrategy : SameSpaceProjStrat pred.next ι :=
    projStratTransportSuccessor strategy ⟨pred, rfl⟩
  have transportedPass : transportedStrategy.PassesLowIndividualDegreeTest eps := by
    simpa [transportedStrategy] using
      (passesLowIndividualDegreeTest_transportSuccessor hpass ⟨pred, rfl⟩)
  have boundary' :
      MainFormalSuccessorAnswerBoundary pred transportedStrategy eps transportedPass k := by
    simpa [transportedStrategy, transportedPass] using boundary
  rcases mainFormalSuccessorAnswerMainInductionPublicWrapper pred transportedStrategy eps
      transportedPass k hd boundary' hk_pos hk_pred with ⟨G, hG⟩
  refine ⟨{ roleMeasurement := G, section6Consistency := ?_ }⟩
  simpa [transportedStrategy, projStratTransportSuccessor, fieldModelOfSuccessorDecomposition]
    using hG

/-- Constructor for the common syntactic-successor answer-valued case. -/
def ofSyntacticSuccessor
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params.next ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (hd : 0 < params.d)
    (boundary : MainFormalSuccessorAnswerBoundary params strategy eps hpass k)
    (hk_pos : 1 ≤ k) :
    MainFormalRolePackageAnswerSuccessorResidual params.next strategy eps hpass k where
  successor := ⟨params, rfl⟩
  boundary := by
    simpa using boundary
  dimensionPositive := hd
  kPositive := hk_pos

end MainFormalRolePackageAnswerSuccessorResidual

/-- Branch-level residual for producing the Section 6 role package.

The two constructors expose the real alternatives in the current proof state:
base dimension, or a successor dimension together with explicit predecessor
transport and successor-boundary data. The large-`k` condition is supplied once,
from the public theorem hypothesis, when converting the branch to a concrete
role-package residual. -/
inductive MainFormalRolePackageBranchResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ) : Type _ where
  /-- Base dimension, handled by the checked base-case handoff. -/
  | base (hm1 : params.m = 1) :
      MainFormalRolePackageBranchResidual params strategy eps hpass k
  /-- Successor dimension with explicit predecessor and successor-boundary data. -/
  | successor
      (successorResidual :
        MainFormalRolePackageSuccessorResidual params strategy eps hpass k) :
      MainFormalRolePackageBranchResidual params strategy eps hpass k

namespace MainFormalRolePackageBranchResidual

/-- Convert the branch-level role residual into the isolated Section 6 role-package
residual consumed by the downstream assembly. -/
theorem toRolePackageResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    (residual : MainFormalRolePackageBranchResidual params strategy eps hpass k)
    (hk_large : 400 * params.m * params.d ≤ k) :
    Nonempty (MainFormalRolePackageResidual params strategy eps hpass k) := by
  cases residual with
  | base hm1 =>
      exact MainFormalRolePackageResidual.ofBaseCase params strategy eps k hpass hm1
  | successor successorResidual =>
      exact successorResidual.toRolePackageResidual hk_large

end MainFormalRolePackageBranchResidual

/-- Evaluate a polynomial-valued complete measurement at every point.

The public `polynomialEvaluationFamily` forgets completeness because most later
statements only need submeasurements.  The triangle inequality used in the
main-formal assembly is stated for complete measurements, so this local helper
keeps the same postprocessing while retaining the proof that totals remain `1`. -/
private noncomputable def polynomialEvaluationMeasurementFamily
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (G : Measurement (Polynomial params) ι) :
    IdxMeas (Point params) (Fq params) ι :=
  fun u =>
    { toSubMeas := evaluateAt params u G.toSubMeas
      total_eq_one := by
        simpa [evaluateAt, postprocess_total] using G.total_eq_one }

/-- Paper lines 84--117 after applying the Section 6 polynomial measurement and
unsymmetrizing it.

The fields are the two `2σ` consistency estimates obtained from the role-register
block extraction, corresponding to `eq:cons-a` and `eq:cons-b` in
`references/ldt-paper/inductive_step.tex` lines 97--109.  The theorem
`toPreProjectiveSelfConsistency` below combines these with the original
point-measurement agreement from the test to prove paper line 116 by
`prop:simeq-triangle-inequality`. -/
structure MainFormalCascadeUnsymmetrizedPOVMTargets
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The POVM denoted $G^{\mathrm A}$ after unsymmetrizing the Section 6 measurement. -/
  leftPOVM : Measurement (Polynomial params) ι
  /-- The POVM denoted $G^{\mathrm B}$ after unsymmetrizing the Section 6 measurement. -/
  rightPOVM : Measurement (Polynomial params) ι
  /-- Paper `eq:cons-a`: $G^{\mathrm A}_{[g(u)=a]}\otimes I
  \simeq_{2\sigma} I\otimes A^{\mathrm B,u}_a$. -/
  leftPOVMPointBConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params leftPOVM.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      (2 * scalars.sigma)
  /-- Paper `eq:cons-b`: $A^{\mathrm A,u}_a\otimes I
  \simeq_{2\sigma} I\otimes G^{\mathrm B}_{[g(u)=a]}$. -/
  pointARightPOVMConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params rightPOVM.toSubMeas)
      (2 * scalars.sigma)

namespace MainFormalCascadeUnsymmetrizedPOVMTargets

/-- Build the line-97--109 unsymmetrized POVM target package from the standalone
Step 3 bridge package.

The extracted POVMs are definitionally the principal role blocks
`unsymmetrizedLeftPOVM G` and `unsymmetrizedRightPOVM G` supplied by
`MIPStarRE.LDT.Test.Unsymmetrization`; the two consistency fields are exactly the
factor-two estimates recorded in `UnsymmetrizationBridgePackage`. -/
noncomputable def ofUnsymmetrizationBridge
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (G : Measurement (Polynomial params) (Role × ι))
    (bridge : UnsymmetrizationBridgePackage params strategy G scalars.sigma) :
    MainFormalCascadeUnsymmetrizedPOVMTargets params strategy eps k scalars where
  leftPOVM := unsymmetrizedLeftPOVM G
  rightPOVM := unsymmetrizedRightPOVM G
  leftPOVMPointBConsistency := bridge.pointBConsistency
  pointARightPOVMConsistency := bridge.pointAConsistency

end MainFormalCascadeUnsymmetrizedPOVMTargets

/-- The geometry/transport part of the remaining Section 3 assembly at the exact
cascade errors.

Compared with `MainFormalNativeTargets`, this package removes the final Step 8
weakening obligations: the point and self-consistency errors are fixed to the
paper's cascade quantities derived from `MainFormalCascadeScalars`. Constructing
this package is still the substantive unsymmetrization, Schwartz--Zippel, and
projectivization work of `inductive_step.tex` lines 84--185. -/
structure MainFormalCascadeTargets
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ) where
  /-- Scalar side conditions and the paper-defined `ν, σ, ζᵢ` cascade. -/
  scalars : MainFormalCascadeScalars params eps k
  /-- The projective measurement denoted $Q^{\mathrm A}$ in the paper. -/
  leftMeasurement : ProjMeas (Polynomial params) ι
  /-- The projective measurement denoted $Q^{\mathrm B}$ in the paper. -/
  rightMeasurement : ProjMeas (Polynomial params) ι
  /-- Native form of `eq:one-goal` at the paper-defined `ζ₄`. -/
  pointAConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params rightMeasurement.toSubMeas)
      scalars.zeta4
  /-- Native form of `eq:another-goal` at the paper-defined `ζ₄`. -/
  pointBConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params leftMeasurement.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      scalars.zeta4
  /-- Native form of `eq:third-goal` at the paper-defined `ζ₃/2`. -/
  selfConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily leftMeasurement.toSubMeas)
      (constSubMeasFamily rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2)

/-- The transport-only part of the remaining Section 3 assembly once the scalar
cascade has been discharged.

Compared with `MainFormalCascadeTargets`, this package is parameterized by an
already-constructed `MainFormalCascadeScalars`. The field shapes intentionally
mirror the transport fields of `MainFormalCascadeTargets`, so downstream changes
to the native `ConsRel` targets should keep the two records synchronized. It
therefore records only the unsymmetrization, Schwartz--Zippel, and
projectivization targets from `inductive_step.tex` lines 84--185. -/
structure MainFormalCascadeTransportTargets
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The projective measurement denoted $Q^{\mathrm A}$ in the paper. -/
  leftMeasurement : ProjMeas (Polynomial params) ι
  /-- The projective measurement denoted $Q^{\mathrm B}$ in the paper. -/
  rightMeasurement : ProjMeas (Polynomial params) ι
  /-- Native form of `eq:one-goal` at the paper-defined `ζ₄`. -/
  pointAConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params rightMeasurement.toSubMeas)
      scalars.zeta4
  /-- Native form of `eq:another-goal` at the paper-defined `ζ₄`. -/
  pointBConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params leftMeasurement.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      scalars.zeta4
  /-- Native form of `eq:third-goal` at the paper-defined `ζ₃/2`. -/
  selfConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily leftMeasurement.toSubMeas)
      (constSubMeasFamily rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2)

/-- The pre-projectivization Step 5 handoff for `mainFormal`.

This package stops at paper line 116, before the Schwartz--Zippel expansion.  The
field `evaluatedSelfConsistency` is the evaluated consistency estimate

`G^A_[g(u)=a] \otimes I \simeq_{2σ + 2√(3ε+2σ)} I \otimes G^B_[g(u)=a]`.

The theorem `fullSelfConsistency` below applies the already-formalized Step 5
Schwartz--Zippel bridge (`inductive_step.tex` lines 119--133) to obtain the
full-polynomial consistency estimate at exactly `ζ₁`. -/
structure MainFormalCascadePreProjectiveSelfConsistency
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The POVM denoted $G^{\mathrm A}$ in the paper, before projectivization. -/
  leftPOVM : Measurement (Polynomial params) ι
  /-- The POVM denoted $G^{\mathrm B}$ in the paper, before projectivization. -/
  rightPOVM : Measurement (Polynomial params) ι
  /-- Paper line 116, before the Step 5 Schwartz--Zippel loss `md/q`. -/
  evaluatedSelfConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params leftPOVM.toSubMeas)
      (polynomialEvaluationFamily params rightPOVM.toSubMeas)
      (2 * scalars.sigma + 2 * Real.sqrt (3 * eps + 2 * scalars.sigma))

namespace MainFormalCascadePreProjectiveSelfConsistency

/-- Step 5 of `mainFormal`: evaluated consistency plus Schwartz--Zippel gives
full-polynomial consistency at the paper-defined error `ζ₁`.

This is the Lean counterpart of `inductive_step.tex` lines 119--133.  The
algebraic expansion and the `md/q` collision bound are both already proved in
`MIPStarRE.LDT.Test.SchwartzZippelStep`; this theorem only specializes that API
to the cascade notation used by the final assembly. -/
theorem fullSelfConsistency {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (pre : MainFormalCascadePreProjectiveSelfConsistency params strategy eps k scalars) :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily pre.leftPOVM.toSubMeas)
      (constSubMeasFamily pre.rightPOVM.toSubMeas)
      scalars.zeta1 := by
  simpa [MainFormalCascadeScalars.zeta1, cascadeZeta1, Nat.cast_mul, add_assoc,
    add_left_comm, add_comm] using
    (mainFormalStep5_selfConsistency_ofExpansionResidual params strategy.state
      strategy.isNormalized pre.leftPOVM.toSubMeas pre.rightPOVM.toSubMeas
      (2 * scalars.sigma + 2 * Real.sqrt (3 * eps + 2 * scalars.sigma))
      pre.evaluatedSelfConsistency)

end MainFormalCascadePreProjectiveSelfConsistency

namespace MainFormalCascadeUnsymmetrizedPOVMTargets

/-- Paper line 116 from the two unsymmetrized consistency estimates and the
original point-measurement agreement.

This is the `prop:simeq-triangle-inequality` step in
`references/ldt-paper/inductive_step.tex` lines 110--117.  The two fields of
`MainFormalCascadeUnsymmetrizedPOVMTargets` provide the `2σ` links
`eq:cons-a`/`eq:cons-b`; `SameSpaceProjStrat.point_agreement_le_three_mul` provides the
middle `3ε` agreement from the low-individual-degree test. -/
noncomputable def toPreProjectiveSelfConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (targets : MainFormalCascadeUnsymmetrizedPOVMTargets params strategy eps k scalars)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    MainFormalCascadePreProjectiveSelfConsistency params strategy eps k scalars where
  leftPOVM := targets.leftPOVM
  rightPOVM := targets.rightPOVM
  evaluatedSelfConsistency := by
    let leftEval : IdxMeas (Point params) (Fq params) ι :=
      polynomialEvaluationMeasurementFamily params targets.leftPOVM
    let rightEval : IdxMeas (Point params) (Fq params) ι :=
      polynomialEvaluationMeasurementFamily params targets.rightPOVM
    let pointA : IdxMeas (Point params) (Fq params) ι :=
      IdxProjMeas.toIdxMeas strategy.pointMeasurementA
    let pointB : IdxMeas (Point params) (Fq params) ι :=
      IdxProjMeas.toIdxMeas strategy.pointMeasurementB
    have hleft :
        ConsRel strategy.state (uniformDistribution (Point params))
          (IdxMeas.toIdxSubMeas leftEval)
          (IdxMeas.toIdxSubMeas pointB)
          (2 * scalars.sigma) := by
      change ConsRel strategy.state (uniformDistribution (Point params))
        (polynomialEvaluationFamily params targets.leftPOVM.toSubMeas)
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
        (2 * scalars.sigma)
      exact targets.leftPOVMPointBConsistency
    have hpoint :
        ConsRel strategy.state (uniformDistribution (Point params))
          (IdxMeas.toIdxSubMeas pointA)
          (IdxMeas.toIdxSubMeas pointB)
          (3 * eps) := by
      exact ⟨SameSpaceProjStrat.point_agreement_le_three_mul hpass⟩
    have hright :
        ConsRel strategy.state (uniformDistribution (Point params))
          (IdxMeas.toIdxSubMeas pointA)
          (IdxMeas.toIdxSubMeas rightEval)
          (2 * scalars.sigma) := by
      change ConsRel strategy.state (uniformDistribution (Point params))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
        (polynomialEvaluationFamily params targets.rightPOVM.toSubMeas)
        (2 * scalars.sigma)
      exact targets.pointARightPOVMConsistency
    have htriangle :=
      Preliminaries.simeqTriangleInequality strategy.state
        (uniformDistribution (Point params)) strategy.isNormalized
        (uniformDistribution_weight_sum_le_one (Point params))
        leftEval pointB pointA rightEval
        (2 * scalars.sigma) (3 * eps) (2 * scalars.sigma)
        hleft hpoint hright
    simpa [leftEval, rightEval, pointA, pointB, polynomialEvaluationMeasurementFamily]
      using htriangle

end MainFormalCascadeUnsymmetrizedPOVMTargets

namespace MainFormalRolePackageResidual

/-- Reconstruct paper line 130 directly from a concrete Section 6 role residual.

This names the paper-order handoff used several times below: first extract the
role package, then unsymmetrize it, prove line 116 by the point-measurement
triangle, and finally apply the checked Schwartz--Zippel Step 5 bridge. -/
noncomputable def line130Consistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    (residual : MainFormalRolePackageResidual params strategy eps hpass k)
    (scalars : MainFormalCascadeScalars params eps k) :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM (residual.rolePackage scalars).roleMeasurement).toSubMeas)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM (residual.rolePackage scalars).roleMeasurement).toSubMeas)
      scalars.zeta1 := by
  let rolePackage := residual.rolePackage scalars
  let bridge := rolePackage.toUnsymmetrizationBridge
  let targets : MainFormalCascadeUnsymmetrizedPOVMTargets params strategy eps k scalars :=
    MainFormalCascadeUnsymmetrizedPOVMTargets.ofUnsymmetrizationBridge
      rolePackage.roleMeasurement bridge
  let pre := targets.toPreProjectiveSelfConsistency hpass
  simpa [rolePackage, pre] using pre.fullSelfConsistency

end MainFormalRolePackageResidual

/-- The remaining projective-stage transport package for `mainFormal`.

Compared with `MainFormalCascadeTransportTargets`, this package has already
split off the Step 5 Schwartz--Zippel handoff.  It asks for the line-156
projective approximation as a bridge out of the proved pre-projective
self-consistency at `ζ₁`; the conversion from that `≈_{ζ₃}` statement to the
native `eq:third-goal` consistency statement is proved by
`toTransportTargets` using the projective converse of `prop:simeq-to-approx`.
The two point-consistency targets remain explicit residual fields at the paper's
`ζ₄`, corresponding to `eq:one-goal` and `eq:another-goal`. -/
structure MainFormalCascadeProjectiveStageTargets
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- Pre-projective `G^A,G^B` data through the Step 5 evaluated estimate. -/
  preSelfConsistency :
    MainFormalCascadePreProjectiveSelfConsistency params strategy eps k scalars
  /-- The projective measurement denoted $Q^{\mathrm A}$ in the paper. -/
  leftMeasurement : ProjMeas (Polynomial params) ι
  /-- The projective measurement denoted $Q^{\mathrm B}$ in the paper. -/
  rightMeasurement : ProjMeas (Polynomial params) ι
  /-- Native form of `eq:one-goal` at the paper-defined `ζ₄`. -/
  pointAConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params rightMeasurement.toSubMeas)
      scalars.zeta4
  /-- Native form of `eq:another-goal` at the paper-defined `ζ₄`. -/
  pointBConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params leftMeasurement.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      scalars.zeta4
  /-- Paper line 156, produced from the Step 5 full-polynomial consistency at `ζ₁`
  and the projectivization/completion approximation chain. -/
  line156Approx :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily preSelfConsistency.leftPOVM.toSubMeas)
      (constSubMeasFamily preSelfConsistency.rightPOVM.toSubMeas)
      scalars.zeta1 →
    Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily leftMeasurement.toSubMeas)
      (constSubMeasFamily rightMeasurement.toSubMeas)
      scalars.zeta3

namespace MainFormalCascadeProjectiveStageTargets

/-- Convert the line-156 projective approximation package into the transport-only
cascade targets.

The only mathematical step performed here is the projective converse of
`prop:simeq-to-approx`: for projective measurements, an `≈_{ζ₃}` relation gives
`≃_{ζ₃/2}`, which is exactly paper `eq:third-goal` (lines 159--162). -/
noncomputable def toTransportTargets {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (targets : MainFormalCascadeProjectiveStageTargets params strategy eps k scalars) :
    MainFormalCascadeTransportTargets params strategy eps k scalars where
  leftMeasurement := targets.leftMeasurement
  rightMeasurement := targets.rightMeasurement
  pointAConsistency := targets.pointAConsistency
  pointBConsistency := targets.pointBConsistency
  selfConsistency := by
    let leftConst : IdxProjMeas Unit (Polynomial params) ι := fun _ => targets.leftMeasurement
    let rightConst : IdxProjMeas Unit (Polynomial params) ι := fun _ => targets.rightMeasurement
    have hpre := targets.preSelfConsistency.fullSelfConsistency
    have happroxLine := targets.line156Approx hpre
    have happroxAtZeta :
        Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
          (IdxProjMeas.toIdxSubMeas leftConst)
          (IdxProjMeas.toIdxSubMeas rightConst)
          scalars.zeta3 := by
      change Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily targets.leftMeasurement.toSubMeas)
        (constSubMeasFamily targets.rightMeasurement.toSubMeas)
        scalars.zeta3
      exact happroxLine
    have happrox :
        Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
          (IdxProjMeas.toIdxSubMeas leftConst)
          (IdxProjMeas.toIdxSubMeas rightConst)
          (2 * (scalars.zeta3 / 2)) := by
      convert happroxAtZeta using 1
      ring
    have hcons :=
      Preliminaries.approxToSimeq strategy.state (uniformDistribution Unit)
        leftConst rightConst (scalars.zeta3 / 2) happrox
    simpa [leftConst, rightConst, constSubMeasFamily, IdxProjMeas.toIdxSubMeas]
      using hcons

end MainFormalCascadeProjectiveStageTargets

/-- Paper-faithful residual for the projective assembly after the line-116
triangle step has been factored out.

This package asks for the unsymmetrized `G^A,G^B` POVMs with their two `2σ`
links (`inductive_step.tex` lines 97--109), then records the still-open
projectivization/completion and point-transport outputs from lines 135--185:
the line-156 `≈_{ζ₃}` bridge and the two native `ζ₄` point-consistency goals.
The theorem `toProjectiveStageTargets` proves the line-116 pre-projective
self-consistency from these fields and the low-individual-degree pass hypothesis. -/
structure MainFormalCascadeProjectiveAssemblyResidual
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- Unsymmetrized POVMs and the two paper `2σ` consistency estimates. -/
  unsymmetrized :
    MainFormalCascadeUnsymmetrizedPOVMTargets params strategy eps k scalars
  /-- The projective measurement denoted $Q^{\mathrm A}$ in the paper. -/
  leftMeasurement : ProjMeas (Polynomial params) ι
  /-- The projective measurement denoted $Q^{\mathrm B}$ in the paper. -/
  rightMeasurement : ProjMeas (Polynomial params) ι
  /-- Native form of `eq:one-goal` at the paper-defined `ζ₄`. -/
  pointAConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params rightMeasurement.toSubMeas)
      scalars.zeta4
  /-- Native form of `eq:another-goal` at the paper-defined `ζ₄`. -/
  pointBConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params leftMeasurement.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      scalars.zeta4
  /-- Paper line 156, produced by orthogonalization, completion,
  `prop:simeq-to-approx`, and the `≈_δ` triangle inequality. -/
  line156Approx :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily unsymmetrized.leftPOVM.toSubMeas)
      (constSubMeasFamily unsymmetrized.rightPOVM.toSubMeas)
      scalars.zeta1 →
    Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily leftMeasurement.toSubMeas)
      (constSubMeasFamily rightMeasurement.toSubMeas)
      scalars.zeta3

namespace MainFormalCascadeProjectiveAssemblyResidual

/-- Assemble the previous projective-stage target from the finer residual package.

The proved work here is exactly paper lines 110--117: the two unsymmetrized `2σ`
links and the original `3ε` point agreement are combined by
`prop:simeq-triangle-inequality` to produce the evaluated pre-projective
self-consistency consumed by Step 5. -/
noncomputable def toProjectiveStageTargets
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveAssemblyResidual params strategy eps k scalars)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    MainFormalCascadeProjectiveStageTargets params strategy eps k scalars where
  preSelfConsistency :=
    residual.unsymmetrized.toPreProjectiveSelfConsistency hpass
  leftMeasurement := residual.leftMeasurement
  rightMeasurement := residual.rightMeasurement
  pointAConsistency := residual.pointAConsistency
  pointBConsistency := residual.pointBConsistency
  line156Approx := by
    intro hpre
    exact residual.line156Approx hpre

end MainFormalCascadeProjectiveAssemblyResidual

/-- A constant full-polynomial consistency statement postprocesses to pointwise
polynomial evaluation with the same error.

This is the data-processing move used after paper line 156: once
`Q^A_g \otimes I \simeq I \otimes Q^B_g` is available over the single
polynomial question, evaluating both polynomial outcomes at a point `u` preserves
consistency over the uniform point distribution. -/
private theorem consRel_constPolynomialEvaluation
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι))
    (A B : Measurement (Polynomial params) ι) {δ : Error}
    (h : ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) δ) :
    ConsRel ψ (uniformDistribution (Point params))
      (polynomialEvaluationFamily params A.toSubMeas)
      (polynomialEvaluationFamily params B.toSubMeas) δ := by
  classical
  let Aconst : IdxSubMeas (Point params) (Polynomial params) ι := fun _ => A.toSubMeas
  let Bconst : IdxSubMeas (Point params) (Polynomial params) ι := fun _ => B.toSubMeas
  have hconstPoint :
      ConsRel ψ (uniformDistribution (Point params)) Aconst Bconst δ := by
    rcases h with ⟨hbound⟩
    constructor
    have hpoint_avg :
        avgOver (uniformDistribution (Point params))
            (fun _ : Point params => qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas) =
          qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
      haveI : Nonempty (Point params) := by infer_instance
      simpa using
        (avgOver_uniform_const (α := Point params)
          (qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas))
    have hunit_eq :
        bipartiteConsError ψ (uniformDistribution Unit)
            (constSubMeasFamily A.toSubMeas) (constSubMeasFamily B.toSubMeas) =
          qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
      have hunit_avg :
          avgOver (uniformDistribution Unit)
              (fun _ : Unit => qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas) =
            qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := by
        simpa using
          (avgOver_uniform_const (α := Unit)
            (qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas))
      simpa [bipartiteConsError, constSubMeasFamily] using hunit_avg
    calc
      bipartiteConsError ψ (uniformDistribution (Point params)) Aconst Bconst
          = avgOver (uniformDistribution (Point params))
              (fun _ : Point params => qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas) := by
            rfl
      _ = qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas := hpoint_avg
      _ = bipartiteConsError ψ (uniformDistribution Unit)
            (constSubMeasFamily A.toSubMeas) (constSubMeasFamily B.toSubMeas) :=
            hunit_eq.symm
      _ ≤ δ := hbound
  have hprocessed :=
    Preliminaries.consRelDataProcessing_questionDependent ψ
      (uniformDistribution (Point params)) Aconst Bconst δ (fun u g => g u) hconstPoint
  simpa [Aconst, Bconst, polynomialEvaluationFamily, evaluateAt] using hprocessed

/-- Turn a line-156 projective approximation into the evaluated consistency used
in the final point-consistency triangles.

The proof first applies the projective converse of `prop:simeq-to-approx` at the
polynomial level, then uses question-dependent data processing to evaluate both
projective polynomial measurements at each point. -/
private theorem projectiveEvaluationConsistency_ofLine156
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ψ : QuantumState (ι × ι)}
    (Q_A Q_B : ProjMeas (Polynomial params) ι) {ζ₃ : Error}
    (hline : Preliminaries.BipartiteSDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas)
      (constSubMeasFamily Q_B.toSubMeas) ζ₃) :
    ConsRel ψ (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Q_A.toSubMeas)
      (polynomialEvaluationFamily params Q_B.toSubMeas) (ζ₃ / 2) := by
  let leftConst : IdxProjMeas Unit (Polynomial params) ι := fun _ => Q_A
  let rightConst : IdxProjMeas Unit (Polynomial params) ι := fun _ => Q_B
  have happrox :
      Preliminaries.BipartiteSDDRel ψ (uniformDistribution Unit)
        (IdxProjMeas.toIdxSubMeas leftConst)
        (IdxProjMeas.toIdxSubMeas rightConst) (2 * (ζ₃ / 2)) := by
    change Preliminaries.BipartiteSDDRel ψ (uniformDistribution Unit)
      (constSubMeasFamily Q_A.toSubMeas) (constSubMeasFamily Q_B.toSubMeas)
      (2 * (ζ₃ / 2))
    convert hline using 1
    ring
  have hcons :=
    Preliminaries.approxToSimeq ψ (uniformDistribution Unit)
      leftConst rightConst (ζ₃ / 2) happrox
  simpa [leftConst, rightConst, constSubMeasFamily, IdxProjMeas.toIdxSubMeas]
    using consRel_constPolynomialEvaluation ψ Q_A.toMeasurement Q_B.toMeasurement hcons

/-- Residual after wiring the merged Step 3 and line-156 projectivization packages.

This package is narrower than `MainFormalCascadeProjectiveAssemblyResidual`:

* the unsymmetrized POVMs must be the actual role blocks of a role-register
  measurement `G`, with the two factor-two bounds supplied by
  `UnsymmetrizationBridgePackage`;
* the line-156 approximation must come from
  `MakingMeasurementsProjective.ProjectivizationLine156Handoff`;
* the remaining point-transport work is isolated to the two line-172 style
  evaluated `ζ₁` links from the completed projective measurements back to the
  pre-projective role blocks.  The two native `ζ₄` point goals are then proved
  below by the paper's `prop:simeq-triangle-inequality` route. -/
structure MainFormalCascadeProjectiveHandoffResidual
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The role-register polynomial POVM produced by the Section 6 induction call. -/
  roleMeasurement : Measurement (Polynomial params) (Role × ι)
  /-- Step 3: role-block extraction plus the two factor-two estimates. -/
  unsymmetrization :
    UnsymmetrizationBridgePackage params strategy roleMeasurement scalars.sigma
  /-- The completed projective measurement denoted $Q^{\mathrm A}$. -/
  leftMeasurement : ProjMeas (Polynomial params) ι
  /-- The completed projective measurement denoted $Q^{\mathrm B}$. -/
  rightMeasurement : ProjMeas (Polynomial params) ι
  /-- Step 6 line-156 handoff from pre-projective consistency and completion closeness. -/
  projectivization :
    MakingMeasurementsProjective.ProjectivizationLine156Handoff strategy.state
      (unsymmetrizedLeftPOVM roleMeasurement) (unsymmetrizedRightPOVM roleMeasurement)
      leftMeasurement rightMeasurement scalars.zeta1 scalars.zeta2
  /-- Paper line 172: after evaluating at a point,
  $Q^{\mathrm A}_{[g(u)=a]}\otimes I \simeq_{\zeta_1}
  I\otimes G^{\mathrm B}_{[g(u)=a]}$. -/
  leftProjectiveRightPOVMConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params (unsymmetrizedRightPOVM roleMeasurement).toSubMeas)
      scalars.zeta1
  /-- The Bob-role analogue of paper line 172, used for `eq:another-goal`. -/
  rightProjectiveLeftPOVMConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params rightMeasurement.toSubMeas)
      (polynomialEvaluationFamily params (unsymmetrizedLeftPOVM roleMeasurement).toSubMeas)
      scalars.zeta1

namespace MainFormalCascadeProjectiveHandoffResidual

/-- Evaluated version of the projective self-consistency from the line-156 handoff. -/
theorem projectiveEvaluationConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveHandoffResidual params strategy eps k scalars) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params residual.rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2) := by
  have hlineRaw :=
    MakingMeasurementsProjective.ProjectivizationLine156Handoff.line156Approx
      residual.projectivization
  have hline :
      Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily residual.leftMeasurement.toSubMeas)
        (constSubMeasFamily residual.rightMeasurement.toSubMeas) scalars.zeta3 := by
    simpa [MainFormalCascadeScalars.zeta3, cascadeZeta3] using hlineRaw
  exact projectiveEvaluationConsistency_ofLine156
    residual.leftMeasurement residual.rightMeasurement hline

/-- Derive paper `eq:one-goal` from `eq:cons-b`, line 172, and evaluated line 164. -/
theorem pointAConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveHandoffResidual params strategy eps k scalars) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params residual.rightMeasurement.toSubMeas)
      scalars.zeta4 := by
  let pointA : IdxMeas (Point params) (Fq params) ι :=
    IdxProjMeas.toIdxMeas strategy.pointMeasurementA
  let rightG : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params
      (unsymmetrizedRightPOVM residual.roleMeasurement)
  let leftQ : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params residual.leftMeasurement.toMeasurement
  let rightQ : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params residual.rightMeasurement.toMeasurement
  have hAB : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointA) (IdxMeas.toIdxSubMeas rightG)
      (2 * scalars.sigma) := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params
        (unsymmetrizedRightPOVM residual.roleMeasurement).toSubMeas)
      (2 * scalars.sigma)
    exact residual.unsymmetrization.pointAConsistency
  have hCB : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas leftQ) (IdxMeas.toIdxSubMeas rightG)
      scalars.zeta1 := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params
        (unsymmetrizedRightPOVM residual.roleMeasurement).toSubMeas)
      scalars.zeta1
    exact residual.leftProjectiveRightPOVMConsistency
  have hCD : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas leftQ) (IdxMeas.toIdxSubMeas rightQ)
      (scalars.zeta3 / 2) := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params residual.rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2)
    exact residual.projectiveEvaluationConsistency
  have htriangle :=
    Preliminaries.simeqTriangleInequality strategy.state
      (uniformDistribution (Point params)) strategy.isNormalized
      (uniformDistribution_weight_sum_le_one (Point params))
      pointA rightG leftQ rightQ
      (2 * scalars.sigma) scalars.zeta1 (scalars.zeta3 / 2)
      hAB hCB hCD
  simpa [pointA, rightG, leftQ, rightQ, polynomialEvaluationMeasurementFamily,
    MainFormalCascadeScalars.zeta4, cascadeZeta4] using htriangle

/-- Derive paper `eq:another-goal` by the Bob-role mirror of the `eq:one-goal`
triangle, using swap symmetry to orient the intermediate consistency relations. -/
theorem pointBConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveHandoffResidual params strategy eps k scalars) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.leftMeasurement.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      scalars.zeta4 := by
  let pointB : IdxMeas (Point params) (Fq params) ι :=
    IdxProjMeas.toIdxMeas strategy.pointMeasurementB
  let leftG : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params
      (unsymmetrizedLeftPOVM residual.roleMeasurement)
  let rightQ : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params residual.rightMeasurement.toMeasurement
  let leftQ : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params residual.leftMeasurement.toMeasurement
  have hLeftGPointB : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas leftG) (IdxMeas.toIdxSubMeas pointB)
      (2 * scalars.sigma) := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params
        (unsymmetrizedLeftPOVM residual.roleMeasurement).toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      (2 * scalars.sigma)
    exact residual.unsymmetrization.pointBConsistency
  have hAB : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointB) (IdxMeas.toIdxSubMeas leftG)
      (2 * scalars.sigma) := by
    exact consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (Point params)) (IdxMeas.toIdxSubMeas leftG)
      (IdxMeas.toIdxSubMeas pointB) (2 * scalars.sigma) hLeftGPointB
  have hCB : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas rightQ) (IdxMeas.toIdxSubMeas leftG)
      scalars.zeta1 := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.rightMeasurement.toSubMeas)
      (polynomialEvaluationFamily params
        (unsymmetrizedLeftPOVM residual.roleMeasurement).toSubMeas)
      scalars.zeta1
    exact residual.rightProjectiveLeftPOVMConsistency
  have hLeftQRightQ : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas leftQ) (IdxMeas.toIdxSubMeas rightQ)
      (scalars.zeta3 / 2) := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params residual.rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2)
    exact residual.projectiveEvaluationConsistency
  have hCD : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas rightQ) (IdxMeas.toIdxSubMeas leftQ)
      (scalars.zeta3 / 2) := by
    exact consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (Point params)) (IdxMeas.toIdxSubMeas leftQ)
      (IdxMeas.toIdxSubMeas rightQ) (scalars.zeta3 / 2) hLeftQRightQ
  have htriangle : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointB) (IdxMeas.toIdxSubMeas leftQ)
      scalars.zeta4 := by
    have hraw :=
      Preliminaries.simeqTriangleInequality strategy.state
        (uniformDistribution (Point params)) strategy.isNormalized
        (uniformDistribution_weight_sum_le_one (Point params))
        pointB leftG rightQ leftQ
        (2 * scalars.sigma) scalars.zeta1 (scalars.zeta3 / 2)
        hAB hCB hCD
    simpa [MainFormalCascadeScalars.zeta4, cascadeZeta4] using hraw
  have htarget :=
    consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (Point params)) (IdxMeas.toIdxSubMeas pointB)
      (IdxMeas.toIdxSubMeas leftQ) scalars.zeta4 htriangle
  simpa [pointB, leftG, rightQ, leftQ, polynomialEvaluationMeasurementFamily] using htarget

/-- Assemble the previous projective-assembly residual from the narrower handoff
residual using the checked Step 3, line-156, and point-triangle wrappers above. -/
noncomputable def toProjectiveAssemblyResidual
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveHandoffResidual params strategy eps k scalars) :
    MainFormalCascadeProjectiveAssemblyResidual params strategy eps k scalars where
  unsymmetrized :=
    MainFormalCascadeUnsymmetrizedPOVMTargets.ofUnsymmetrizationBridge
      residual.roleMeasurement residual.unsymmetrization
  leftMeasurement := residual.leftMeasurement
  rightMeasurement := residual.rightMeasurement
  pointAConsistency := residual.pointAConsistency
  pointBConsistency := residual.pointBConsistency
  line156Approx := by
    intro hpre
    have hpre' : ConsRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (unsymmetrizedLeftPOVM residual.roleMeasurement).toSubMeas)
        (constSubMeasFamily (unsymmetrizedRightPOVM residual.roleMeasurement).toSubMeas)
        scalars.zeta1 := by
      simpa [MainFormalCascadeUnsymmetrizedPOVMTargets.ofUnsymmetrizationBridge]
        using hpre
    let handoff : MakingMeasurementsProjective.ProjectivizationLine156Handoff
        strategy.state (unsymmetrizedLeftPOVM residual.roleMeasurement)
        (unsymmetrizedRightPOVM residual.roleMeasurement)
        residual.leftMeasurement residual.rightMeasurement scalars.zeta1 scalars.zeta2 :=
      { preProjectiveConsistency := hpre'
        leftCompletionCloseness := residual.projectivization.leftCompletionCloseness
        rightCompletionCloseness := residual.projectivization.rightCompletionCloseness }
    have hline :=
      MakingMeasurementsProjective.ProjectivizationLine156Handoff.line156Approx handoff
    simpa [MainFormalCascadeScalars.zeta3, cascadeZeta3] using hline

end MainFormalCascadeProjectiveHandoffResidual

/-- Polynomial-level line-169 residual before the line-172 data-processing step.

This package is narrower than `MainFormalCascadeProjectiveHandoffResidual`: the
line-172 evaluated `ζ₁` links are no longer fields.  Instead it asks for the
polynomial-level statements from `inductive_step.tex` lines 167--173,

* `Q^A_g ⊗ I ≃_{ζ₁} I ⊗ G^B_g`, and
* its Bob-role mirror `Q^B_g ⊗ I ≃_{ζ₁} I ⊗ G^A_g`,

both over the constant polynomial question.  The theorem
`toProjectiveHandoffResidual` below proves the paper's data-processing move from
line 171 to line 172 for both links. -/
structure MainFormalCascadeProjectiveLine169HandoffResidual
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The role-register polynomial POVM produced by the Section 6 induction call. -/
  roleMeasurement : Measurement (Polynomial params) (Role × ι)
  /-- Step 3: role-block extraction plus the two factor-two estimates. -/
  unsymmetrization :
    UnsymmetrizationBridgePackage params strategy roleMeasurement scalars.sigma
  /-- The completed projective measurement denoted $Q^{\mathrm A}$. -/
  leftMeasurement : ProjMeas (Polynomial params) ι
  /-- The completed projective measurement denoted $Q^{\mathrm B}$. -/
  rightMeasurement : ProjMeas (Polynomial params) ι
  /-- Step 6 line-156 handoff from pre-projective consistency and completion closeness. -/
  projectivization :
    MakingMeasurementsProjective.ProjectivizationLine156Handoff strategy.state
      (unsymmetrizedLeftPOVM roleMeasurement) (unsymmetrizedRightPOVM roleMeasurement)
      leftMeasurement rightMeasurement scalars.zeta1 scalars.zeta2
  /-- Paper line 169, before the data-processing step at lines 171--173:
  $Q^{\mathrm A}_g\otimes I \simeq_{\zeta_1} I\otimes G^{\mathrm B}_g$. -/
  leftProjectiveRightPOVMPolynomialConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily leftMeasurement.toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM roleMeasurement).toSubMeas)
      scalars.zeta1
  /-- Bob-role mirror of paper line 169, before point-evaluation data processing. -/
  rightProjectiveLeftPOVMPolynomialConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily rightMeasurement.toSubMeas)
      (constSubMeasFamily (unsymmetrizedLeftPOVM roleMeasurement).toSubMeas)
      scalars.zeta1

namespace MainFormalCascadeProjectiveLine169HandoffResidual

/-- Apply the paper's line-171--173 data-processing step to the two polynomial
`ζ₁` links and recover the previous evaluated handoff residual. -/
noncomputable def toProjectiveHandoffResidual
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveLine169HandoffResidual
      params strategy eps k scalars) :
    MainFormalCascadeProjectiveHandoffResidual params strategy eps k scalars where
  roleMeasurement := residual.roleMeasurement
  unsymmetrization := residual.unsymmetrization
  leftMeasurement := residual.leftMeasurement
  rightMeasurement := residual.rightMeasurement
  projectivization := residual.projectivization
  leftProjectiveRightPOVMConsistency := by
    simpa using
      consRel_constPolynomialEvaluation strategy.state
        residual.leftMeasurement.toMeasurement
        (unsymmetrizedRightPOVM residual.roleMeasurement)
        residual.leftProjectiveRightPOVMPolynomialConsistency
  rightProjectiveLeftPOVMConsistency := by
    simpa using
      consRel_constPolynomialEvaluation strategy.state
        residual.rightMeasurement.toMeasurement
        (unsymmetrizedLeftPOVM residual.roleMeasurement)
        residual.rightProjectiveLeftPOVMPolynomialConsistency

end MainFormalCascadeProjectiveLine169HandoffResidual

/-- Finer residual for the projective completion and paper line-169 handoff.

This package is strictly weaker than
`MainFormalCascadeProjectiveLine169HandoffResidual`.  It no longer asks for the
unused Section 6 consistency field inside `UnsymmetrizationBridgePackage`, and it
no longer asks for the pre-projective consistency field inside
`ProjectivizationLine156Handoff`: both are reconstructed downstream from the two
paper factor-two role-block estimates and `hpass` via the checked line-116
triangle and Step 5 Schwartz--Zippel wrapper.  The remaining open data are exactly
what is still missing after those mechanical steps:

* the role-register measurement and the two factor-two estimates from
  `inductive_step.tex` lines 97--108;
* the two completion-closeness estimates from lines 146--147; and
* the two exact polynomial line-169 `ζ₁` links (Alice side and the role-reversed
  Bob-side analogue), before line-171 data processing. -/
structure MainFormalCascadeProjectiveCompletionLine169Residual
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The role-register polynomial POVM produced by the Section 6 induction call. -/
  roleMeasurement : Measurement (Polynomial params) (Role × ι)
  /-- Paper `eq:cons-b` / lines 97--108: original Alice point measurements are
  consistent with the Bob-role extraction, with the factor-two loss. -/
  pointARightPOVMConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params (unsymmetrizedRightPOVM roleMeasurement).toSubMeas)
      (2 * scalars.sigma)
  /-- Paper `eq:cons-a` / lines 105--108: the Alice-role extraction is consistent
  with original Bob point measurements, with the factor-two loss. -/
  leftPOVMPointBConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params (unsymmetrizedLeftPOVM roleMeasurement).toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      (2 * scalars.sigma)
  /-- The completed projective measurement denoted $Q^{\mathrm A}$. -/
  leftMeasurement : ProjMeas (Polynomial params) ι
  /-- The completed projective measurement denoted $Q^{\mathrm B}$. -/
  rightMeasurement : ProjMeas (Polynomial params) ι
  /-- Left-register completion closeness, paper line 146 (`eq:G-with-Q-A`). -/
  leftCompletionCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily leftMeasurement.toSubMeas.liftLeft)
      scalars.zeta2
  /-- Right-register completion closeness, paper line 147. -/
  rightCompletionCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedRightPOVM roleMeasurement).toSubMeas.liftRight)
      (constSubMeasFamily rightMeasurement.toSubMeas.liftRight)
      scalars.zeta2
  /-- Paper line 169, before the data-processing step at lines 171--173:
  $Q^{\mathrm A}_g\otimes I \simeq_{\zeta_1} I\otimes G^{\mathrm B}_g$. -/
  leftProjectiveRightPOVMPolynomialConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily leftMeasurement.toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM roleMeasurement).toSubMeas)
      scalars.zeta1
  /-- Bob-role mirror of paper line 169, before point-evaluation data processing. -/
  rightProjectiveLeftPOVMPolynomialConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily rightMeasurement.toSubMeas)
      (constSubMeasFamily (unsymmetrizedLeftPOVM roleMeasurement).toSubMeas)
      scalars.zeta1

namespace MainFormalCascadeProjectiveCompletionLine169Residual

/-- The older line-169 residual contains all fields needed by the finer
completion-line169 residual; this coercion documents that the new target is a
strict weakening of the previous one. -/
noncomputable def ofLine169HandoffResidual
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveLine169HandoffResidual
      params strategy eps k scalars) :
    MainFormalCascadeProjectiveCompletionLine169Residual params strategy eps k scalars where
  roleMeasurement := residual.roleMeasurement
  pointARightPOVMConsistency := residual.unsymmetrization.pointAConsistency
  leftPOVMPointBConsistency := residual.unsymmetrization.pointBConsistency
  leftMeasurement := residual.leftMeasurement
  rightMeasurement := residual.rightMeasurement
  leftCompletionCloseness := residual.projectivization.leftCompletionCloseness
  rightCompletionCloseness := residual.projectivization.rightCompletionCloseness
  leftProjectiveRightPOVMPolynomialConsistency :=
    residual.leftProjectiveRightPOVMPolynomialConsistency
  rightProjectiveLeftPOVMPolynomialConsistency :=
    residual.rightProjectiveLeftPOVMPolynomialConsistency

/-- View the factor-two role-block fields as the pre-projective target package. -/
noncomputable def toUnsymmetrizedPOVMTargets
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveCompletionLine169Residual
      params strategy eps k scalars) :
    MainFormalCascadeUnsymmetrizedPOVMTargets params strategy eps k scalars where
  leftPOVM := unsymmetrizedLeftPOVM residual.roleMeasurement
  rightPOVM := unsymmetrizedRightPOVM residual.roleMeasurement
  leftPOVMPointBConsistency := residual.leftPOVMPointBConsistency
  pointARightPOVMConsistency := residual.pointARightPOVMConsistency

/-- Reconstruct paper line 116 from the factor-two role-block estimates and the
original point-agreement bound. -/
noncomputable def toPreProjectiveSelfConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveCompletionLine169Residual
      params strategy eps k scalars)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    MainFormalCascadePreProjectiveSelfConsistency params strategy eps k scalars :=
  residual.toUnsymmetrizedPOVMTargets.toPreProjectiveSelfConsistency hpass

/-- Rebuild the Step 6 line-156 handoff from a freshly supplied Step 5
pre-projective consistency proof and the two completion-closeness fields. -/
noncomputable def projectivizationLine156Handoff
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveCompletionLine169Residual
      params strategy eps k scalars)
    (hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM residual.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM residual.roleMeasurement).toSubMeas)
      scalars.zeta1) :
    MakingMeasurementsProjective.ProjectivizationLine156Handoff strategy.state
      (unsymmetrizedLeftPOVM residual.roleMeasurement)
      (unsymmetrizedRightPOVM residual.roleMeasurement)
      residual.leftMeasurement residual.rightMeasurement scalars.zeta1 scalars.zeta2 where
  preProjectiveConsistency := hpre
  leftCompletionCloseness := residual.leftCompletionCloseness
  rightCompletionCloseness := residual.rightCompletionCloseness

/-- Paper line 156, reconstructed from Step 5 and completion closeness rather
than stored as an independent residual field. -/
theorem line156Approx
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveCompletionLine169Residual
      params strategy eps k scalars)
    (hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM residual.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM residual.roleMeasurement).toSubMeas)
      scalars.zeta1) :
    Preliminaries.BipartiteSDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily residual.leftMeasurement.toSubMeas)
      (constSubMeasFamily residual.rightMeasurement.toSubMeas)
      scalars.zeta3 := by
  have hline :=
    MakingMeasurementsProjective.ProjectivizationLine156Handoff.line156Approx
      (residual.projectivizationLine156Handoff hpre)
  simpa [MainFormalCascadeScalars.zeta3, cascadeZeta3] using hline

/-- Evaluated version of the projective self-consistency from reconstructed
line 156. -/
theorem projectiveEvaluationConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveCompletionLine169Residual
      params strategy eps k scalars)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params residual.rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2) := by
  let pre := residual.toPreProjectiveSelfConsistency hpass
  have hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM residual.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM residual.roleMeasurement).toSubMeas)
      scalars.zeta1 := by
    simpa [pre, toPreProjectiveSelfConsistency, toUnsymmetrizedPOVMTargets]
      using pre.fullSelfConsistency
  exact projectiveEvaluationConsistency_ofLine156
    residual.leftMeasurement residual.rightMeasurement (residual.line156Approx hpre)

/-- Derive paper `eq:one-goal` from `eq:cons-b`, line 172 obtained by data
processing line 169, and evaluated line 164. -/
theorem pointAConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveCompletionLine169Residual
      params strategy eps k scalars)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params residual.rightMeasurement.toSubMeas)
      scalars.zeta4 := by
  let pointA : IdxMeas (Point params) (Fq params) ι :=
    IdxProjMeas.toIdxMeas strategy.pointMeasurementA
  let rightG : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params
      (unsymmetrizedRightPOVM residual.roleMeasurement)
  let leftQ : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params residual.leftMeasurement.toMeasurement
  let rightQ : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params residual.rightMeasurement.toMeasurement
  have hAB : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointA) (IdxMeas.toIdxSubMeas rightG)
      (2 * scalars.sigma) := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params
        (unsymmetrizedRightPOVM residual.roleMeasurement).toSubMeas)
      (2 * scalars.sigma)
    exact residual.pointARightPOVMConsistency
  have hCB : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas leftQ) (IdxMeas.toIdxSubMeas rightG)
      scalars.zeta1 := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params
        (unsymmetrizedRightPOVM residual.roleMeasurement).toSubMeas)
      scalars.zeta1
    simpa using
      consRel_constPolynomialEvaluation strategy.state
        residual.leftMeasurement.toMeasurement
        (unsymmetrizedRightPOVM residual.roleMeasurement)
        residual.leftProjectiveRightPOVMPolynomialConsistency
  have hCD : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas leftQ) (IdxMeas.toIdxSubMeas rightQ)
      (scalars.zeta3 / 2) := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params residual.rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2)
    exact residual.projectiveEvaluationConsistency hpass
  have htriangle :=
    Preliminaries.simeqTriangleInequality strategy.state
      (uniformDistribution (Point params)) strategy.isNormalized
      (uniformDistribution_weight_sum_le_one (Point params))
      pointA rightG leftQ rightQ
      (2 * scalars.sigma) scalars.zeta1 (scalars.zeta3 / 2)
      hAB hCB hCD
  simpa [pointA, rightG, leftQ, rightQ, polynomialEvaluationMeasurementFamily,
    MainFormalCascadeScalars.zeta4, cascadeZeta4] using htriangle

/-- Derive paper `eq:another-goal` by the Bob-role mirror of the `eq:one-goal`
triangle, again data-processing the polynomial line-169 mirror first. -/
theorem pointBConsistency
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveCompletionLine169Residual
      params strategy eps k scalars)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.leftMeasurement.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      scalars.zeta4 := by
  let pointB : IdxMeas (Point params) (Fq params) ι :=
    IdxProjMeas.toIdxMeas strategy.pointMeasurementB
  let leftG : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params
      (unsymmetrizedLeftPOVM residual.roleMeasurement)
  let rightQ : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params residual.rightMeasurement.toMeasurement
  let leftQ : IdxMeas (Point params) (Fq params) ι :=
    polynomialEvaluationMeasurementFamily params residual.leftMeasurement.toMeasurement
  have hLeftGPointB : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas leftG) (IdxMeas.toIdxSubMeas pointB)
      (2 * scalars.sigma) := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params
        (unsymmetrizedLeftPOVM residual.roleMeasurement).toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      (2 * scalars.sigma)
    exact residual.leftPOVMPointBConsistency
  have hAB : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointB) (IdxMeas.toIdxSubMeas leftG)
      (2 * scalars.sigma) := by
    exact consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (Point params)) (IdxMeas.toIdxSubMeas leftG)
      (IdxMeas.toIdxSubMeas pointB) (2 * scalars.sigma) hLeftGPointB
  have hCB : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas rightQ) (IdxMeas.toIdxSubMeas leftG)
      scalars.zeta1 := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.rightMeasurement.toSubMeas)
      (polynomialEvaluationFamily params
        (unsymmetrizedLeftPOVM residual.roleMeasurement).toSubMeas)
      scalars.zeta1
    simpa using
      consRel_constPolynomialEvaluation strategy.state
        residual.rightMeasurement.toMeasurement
        (unsymmetrizedLeftPOVM residual.roleMeasurement)
        residual.rightProjectiveLeftPOVMPolynomialConsistency
  have hLeftQRightQ : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas leftQ) (IdxMeas.toIdxSubMeas rightQ)
      (scalars.zeta3 / 2) := by
    change ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params residual.leftMeasurement.toSubMeas)
      (polynomialEvaluationFamily params residual.rightMeasurement.toSubMeas)
      (scalars.zeta3 / 2)
    exact residual.projectiveEvaluationConsistency hpass
  have hCD : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas rightQ) (IdxMeas.toIdxSubMeas leftQ)
      (scalars.zeta3 / 2) := by
    exact consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (Point params)) (IdxMeas.toIdxSubMeas leftQ)
      (IdxMeas.toIdxSubMeas rightQ) (scalars.zeta3 / 2) hLeftQRightQ
  have htriangle : ConsRel strategy.state (uniformDistribution (Point params))
      (IdxMeas.toIdxSubMeas pointB) (IdxMeas.toIdxSubMeas leftQ)
      scalars.zeta4 := by
    have hraw :=
      Preliminaries.simeqTriangleInequality strategy.state
        (uniformDistribution (Point params)) strategy.isNormalized
        (uniformDistribution_weight_sum_le_one (Point params))
        pointB leftG rightQ leftQ
        (2 * scalars.sigma) scalars.zeta1 (scalars.zeta3 / 2)
        hAB hCB hCD
    simpa [MainFormalCascadeScalars.zeta4, cascadeZeta4] using hraw
  have htarget :=
    consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution (Point params)) (IdxMeas.toIdxSubMeas pointB)
      (IdxMeas.toIdxSubMeas leftQ) scalars.zeta4 htriangle
  simpa [pointB, leftG, rightQ, leftQ, polynomialEvaluationMeasurementFamily] using htarget

/-- Assemble the projective-stage targets directly from the finer residual.  This
reconstructs the duplicated pre-projective consistency field from the factor-two
role-block estimates and `hpass`, then combines it with the completion-closeness
fields for line 156. -/
noncomputable def toProjectiveStageTargets
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeProjectiveCompletionLine169Residual
      params strategy eps k scalars)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    MainFormalCascadeProjectiveStageTargets params strategy eps k scalars where
  preSelfConsistency := residual.toPreProjectiveSelfConsistency hpass
  leftMeasurement := residual.leftMeasurement
  rightMeasurement := residual.rightMeasurement
  pointAConsistency := residual.pointAConsistency hpass
  pointBConsistency := residual.pointBConsistency hpass
  line156Approx := by
    intro hpre
    have hpre' : ConsRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily (unsymmetrizedLeftPOVM residual.roleMeasurement).toSubMeas)
        (constSubMeasFamily (unsymmetrizedRightPOVM residual.roleMeasurement).toSubMeas)
        scalars.zeta1 := by
      simpa [toPreProjectiveSelfConsistency, toUnsymmetrizedPOVMTargets] using hpre
    exact residual.line156Approx hpre'

end MainFormalCascadeProjectiveCompletionLine169Residual

/-- Residual after consuming the checked role-register Section 6 package.

This package is narrower than `MainFormalCascadeProjectiveCompletionLine169Residual`:
the role-register measurement and both factor-two unsymmetrization estimates are
no longer independent fields.  They are supplied by
`MainFormalRoleMeasurementPackage`, whose symmetrized consistency field feeds the
proved constructor `UnsymmetrizationBridgePackage.ofSymConsistency`.  The
remaining fields are therefore exactly the projectivization/completion data and
the two polynomial line-169 transport links. -/
structure MainFormalCascadeRolePackagedCompletionLine169Residual
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The role-register Section 6 output at the cascade scalar `σ`. -/
  rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars
  /-- The completed projective measurement denoted $Q^{\mathrm A}$. -/
  leftMeasurement : ProjMeas (Polynomial params) ι
  /-- The completed projective measurement denoted $Q^{\mathrm B}$. -/
  rightMeasurement : ProjMeas (Polynomial params) ι
  /-- Left-register completion closeness, paper line 146 (`eq:G-with-Q-A`). -/
  leftCompletionCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily leftMeasurement.toSubMeas.liftLeft)
      scalars.zeta2
  /-- Right-register completion closeness, paper line 147. -/
  rightCompletionCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas.liftRight)
      (constSubMeasFamily rightMeasurement.toSubMeas.liftRight)
      scalars.zeta2
  /-- Paper line 169, before the data-processing step at lines 171--173:
  $Q^{\mathrm A}_g\otimes I \simeq_{\zeta_1} I\otimes G^{\mathrm B}_g$. -/
  leftProjectiveRightPOVMPolynomialConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily leftMeasurement.toSubMeas)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1
  /-- Bob-role mirror of paper line 169, before point-evaluation data processing. -/
  rightProjectiveLeftPOVMPolynomialConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily rightMeasurement.toSubMeas)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1

namespace MainFormalCascadeRolePackagedCompletionLine169Residual

/-- Convert the role-packaged residual to the previous completion-line169 shape.

The only work is to expand `MainFormalRoleMeasurementPackage` into the
role-register measurement and the two Step 3 factor-two estimates using the
checked unsymmetrization constructor. -/
noncomputable def toCompletionLine169Residual
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeRolePackagedCompletionLine169Residual
      params strategy eps k scalars) :
    MainFormalCascadeProjectiveCompletionLine169Residual params strategy eps k scalars :=
  let bridge := residual.rolePackage.toUnsymmetrizationBridge
  { roleMeasurement := residual.rolePackage.roleMeasurement
    pointARightPOVMConsistency := bridge.pointAConsistency
    leftPOVMPointBConsistency := bridge.pointBConsistency
    leftMeasurement := residual.leftMeasurement
    rightMeasurement := residual.rightMeasurement
    leftCompletionCloseness := residual.leftCompletionCloseness
    rightCompletionCloseness := residual.rightCompletionCloseness
    leftProjectiveRightPOVMPolynomialConsistency :=
      residual.leftProjectiveRightPOVMPolynomialConsistency
    rightProjectiveLeftPOVMPolynomialConsistency :=
      residual.rightProjectiveLeftPOVMPolynomialConsistency }

end MainFormalCascadeRolePackagedCompletionLine169Residual

/-- Projectivization/completion and line-169 residual after a concrete role package
has already been produced.

This is the post-role part of
`MainFormalCascadeRolePackagedCompletionLine169Residual`: the role-register
measurement is no longer a field, so the remaining data are exactly the two
completed projective measurements, their completion closeness to the
unsymmetrized POVMs, and the two polynomial line-169 transport estimates. -/
structure MainFormalPostRolePackageCompletionLine169Residual
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars) where
  /-- The completed projective measurement denoted $Q^{\mathrm A}$. -/
  leftMeasurement : ProjMeas (Polynomial params) ι
  /-- The completed projective measurement denoted $Q^{\mathrm B}$. -/
  rightMeasurement : ProjMeas (Polynomial params) ι
  /-- Left-register completion closeness, paper line 146 (`eq:G-with-Q-A`). -/
  leftCompletionCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily leftMeasurement.toSubMeas.liftLeft)
      scalars.zeta2
  /-- Right-register completion closeness, paper line 147. -/
  rightCompletionCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas.liftRight)
      (constSubMeasFamily rightMeasurement.toSubMeas.liftRight)
      scalars.zeta2
  /-- Paper line 169, before the data-processing step at lines 171--173. -/
  leftProjectiveRightPOVMPolynomialConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily leftMeasurement.toSubMeas)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1
  /-- Bob-role mirror of paper line 169, before point-evaluation data processing. -/
  rightProjectiveLeftPOVMPolynomialConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily rightMeasurement.toSubMeas)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1

namespace MainFormalPostRolePackageCompletionLine169Residual

/-- Reinsert the already-produced role package into the older role-packaged
completion-line169 residual. -/
noncomputable def toRolePackagedCompletionLine169Residual
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (residual : MainFormalPostRolePackageCompletionLine169Residual
      params strategy eps k scalars rolePackage) :
    MainFormalCascadeRolePackagedCompletionLine169Residual params strategy eps k scalars where
  rolePackage := rolePackage
  leftMeasurement := residual.leftMeasurement
  rightMeasurement := residual.rightMeasurement
  leftCompletionCloseness := residual.leftCompletionCloseness
  rightCompletionCloseness := residual.rightCompletionCloseness
  leftProjectiveRightPOVMPolynomialConsistency :=
    residual.leftProjectiveRightPOVMPolynomialConsistency
  rightProjectiveLeftPOVMPolynomialConsistency :=
    residual.rightProjectiveLeftPOVMPolynomialConsistency

end MainFormalPostRolePackageCompletionLine169Residual

/-- Post-role residual whose Bob-side completion estimate is still in the
left-register form returned by the orthonormalize-and-complete chain.

This is the paper Step 6 boundary just before applying the permutation-invariant
right-register transport from #869.  The Alice completion field already matches
`inductive_step.tex` line 146.  For Bob, the analytic completion theorem naturally
returns the left-lifted estimate for `G^B` and `Q^B`; the conversion below uses
`MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv` to recover
the line-147 right-register estimate.  The exact line-169 `ζ₁` links are not
stored directly here: this residual carries the construction-level match-mass
monotonicity invariant, and the outer conversion combines it with the
reconstructed pre-projective consistency proof to derive line 169. -/
structure MainFormalPostRolePackageLeftCompletionLine169Residual
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars) where
  /-- The completed projective measurement denoted $Q^{\mathrm A}$. -/
  leftMeasurement : ProjMeas (Polynomial params) ι
  /-- The completed projective measurement denoted $Q^{\mathrm B}$. -/
  rightMeasurement : ProjMeas (Polynomial params) ι
  /-- Left-register completion closeness, paper line 146 (`eq:G-with-Q-A`). -/
  leftCompletionCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily leftMeasurement.toSubMeas.liftLeft)
      scalars.zeta2
  /-- Bob-side completion closeness in the left-register form returned by the
  orthonormalize-and-complete chain, before #869 transports it to line 147. -/
  rightCompletionClosenessLeft :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily rightMeasurement.toSubMeas.liftLeft)
      scalars.zeta2
  /-- Construction-level invariant that yields the exact paper line-169 `ζ₁`
  transports once combined with the pre-projective `G^A/G^B` consistency proof. -/
  line169MatchMassMonotonicity :
    MakingMeasurementsProjective.ProjectivizationMatchMassMonotonicity strategy.state
      (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
      (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
      leftMeasurement rightMeasurement

namespace MainFormalPostRolePackageLeftCompletionLine169Residual

/-- Build the post-role residual from two orthonormalize-and-complete statements
whose completed measurements are the canonical completions of the produced
projective submeasurements.

The remaining non-analytic inputs are exactly the construction-level match-mass
monotonicity inequalities for the orthonormalized submeasurements; completion then
preserves those inequalities by positivity. -/
noncomputable def ofCompleteAtOutcomeStatements
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (P_A P_B : ProjSubMeas (Polynomial params) ι)
    (a_A a_B : Polynomial params)
    (leftStmt :
      MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
        P_A (Preliminaries.completeAtOutcomeProj P_A a_A) a_A scalars.zeta1)
    (rightStmt :
      MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
        P_B (Preliminaries.completeAtOutcomeProj P_B a_B) a_B scalars.zeta1)
    (hleftMass :
      qBipartiteMatchMass strategy.state P_A.toSubMeas
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas ≥
        qBipartiteMatchMass strategy.state
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
    (hrightMass :
      qBipartiteMatchMass strategy.state P_B.toSubMeas
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas ≥
        qBipartiteMatchMass strategy.state
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas) :
    MainFormalPostRolePackageLeftCompletionLine169Residual
      params strategy eps k scalars rolePackage where
  leftMeasurement := Preliminaries.completeAtOutcomeProj P_A a_A
  rightMeasurement := Preliminaries.completeAtOutcomeProj P_B a_B
  leftCompletionCloseness := by
    exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceRel_mono strategy.state
      (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily (Preliminaries.completeAtOutcomeProj P_A a_A).toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1)
      scalars.zeta2
      (MainFormalCascadeScalars.orthonormalizeAndCompleteError_zeta1_le_zeta2
        scalars hsmall)
      leftStmt.completedCloseness
  rightCompletionClosenessLeft := by
    exact MIPStarRE.LDT.Preliminaries.stateDependentDistanceRel_mono strategy.state
      (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily (Preliminaries.completeAtOutcomeProj P_B a_B).toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1)
      scalars.zeta2
      (MainFormalCascadeScalars.orthonormalizeAndCompleteError_zeta1_le_zeta2
        scalars hsmall)
      rightStmt.completedCloseness
  line169MatchMassMonotonicity :=
    MakingMeasurementsProjective.ProjectivizationMatchMassMonotonicity.of_completeAtOutcomeProj
      P_A P_B a_A a_B hleftMass hrightMass

/-- Produce the post-role residual by running the orthonormalize-and-complete chain
on the two unsymmetrized role-block POVMs.

This wrapper removes the need for callers to prepackage the two
`OrthonormalizeAndCompleteStatement`s.  The remaining analytic inputs are exactly
the strong self-consistency hypotheses and the explicit orthonormalization bridge
data required by `orthonormalizeAndComplete`.  The two match-mass hypotheses are
phrased over the produced projective submeasurements, so the exact line-169
`ζ₁` transport still remains construction-level data rather than a generic
`triangleSub` consequence.

The result is stated as `Nonempty`, rather than as a direct `def`, because
`orthonormalizeAndComplete` is an existential theorem in `Prop`; eliminating that
existential to construct a data-valued residual would require choice. -/
theorem nonempty_ofOrthonormalizeAndCompleteInputs
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (a_A a_B : Polynomial params)
    (leftSelfConsistency :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
        scalars.zeta1)
    (rightSelfConsistency :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
        scalars.zeta1)
    (leftBridge :
      MakingMeasurementsProjective.OrthonormalizationInput strategy.state
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas scalars.zeta1)
    (rightBridge :
      MakingMeasurementsProjective.OrthonormalizationInput strategy.state
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas scalars.zeta1)
    (hleftMass :
      ∀ P_A : ProjSubMeas (Polynomial params) ι,
        MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
          P_A (Preliminaries.completeAtOutcomeProj P_A a_A) a_A scalars.zeta1 →
        qBipartiteMatchMass strategy.state P_A.toSubMeas
            (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas ≥
          qBipartiteMatchMass strategy.state
            (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas
            (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
    (hrightMass :
      ∀ P_B : ProjSubMeas (Polynomial params) ι,
        MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
          P_B (Preliminaries.completeAtOutcomeProj P_B a_B) a_B scalars.zeta1 →
        qBipartiteMatchMass strategy.state P_B.toSubMeas
            (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas ≥
          qBipartiteMatchMass strategy.state
            (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas
            (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas) :
    Nonempty (MainFormalPostRolePackageLeftCompletionLine169Residual
      params strategy eps k scalars rolePackage) := by
  classical
  obtain ⟨P_A, Q_A, hQ_A, leftStmtRaw⟩ :=
    MakingMeasurementsProjective.orthonormalizeAndComplete
      (Outcome := Polynomial params) (ι := ι)
      strategy.state strategy.isNormalized strategy.permInvState
      (unsymmetrizedLeftPOVM rolePackage.roleMeasurement) a_A scalars.zeta1
      leftSelfConsistency leftBridge
  obtain ⟨P_B, Q_B, hQ_B, rightStmtRaw⟩ :=
    MakingMeasurementsProjective.orthonormalizeAndComplete
      (Outcome := Polynomial params) (ι := ι)
      strategy.state strategy.isNormalized strategy.permInvState
      (unsymmetrizedRightPOVM rolePackage.roleMeasurement) a_B scalars.zeta1
      rightSelfConsistency rightBridge
  have hQ_A_canon : Q_A = Preliminaries.completeAtOutcomeProj P_A a_A := by
    have hQ_A_meas : Q_A.toMeasurement =
        (Preliminaries.completeAtOutcomeProj P_A a_A).toMeasurement := by
      simpa using hQ_A
    apply ProjMeas.ext
    intro g
    have h := congrArg
      (fun Q : Measurement (Polynomial params) ι => Q.outcome g) hQ_A_meas
    simpa using h
  have hQ_B_canon : Q_B = Preliminaries.completeAtOutcomeProj P_B a_B := by
    have hQ_B_meas : Q_B.toMeasurement =
        (Preliminaries.completeAtOutcomeProj P_B a_B).toMeasurement := by
      simpa using hQ_B
    apply ProjMeas.ext
    intro g
    have h := congrArg
      (fun Q : Measurement (Polynomial params) ι => Q.outcome g) hQ_B_meas
    simpa using h
  have leftStmt :
      MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
        P_A (Preliminaries.completeAtOutcomeProj P_A a_A) a_A scalars.zeta1 := by
    simpa [hQ_A_canon] using leftStmtRaw
  have rightStmt :
      MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
        P_B (Preliminaries.completeAtOutcomeProj P_B a_B) a_B scalars.zeta1 := by
    simpa [hQ_B_canon] using rightStmtRaw
  exact ⟨ofCompleteAtOutcomeStatements hsmall P_A P_B a_A a_B
    leftStmt rightStmt (hleftMass P_A leftStmt) (hrightMass P_B rightStmt)⟩

/-- Transport the Bob-side completion estimate from the left-register form to the
right-register form and recover the previous post-role residual.

This is the local `mainFormal` consumer of the right-register completion helper
added in #869. -/
noncomputable def toPostRolePackageCompletionLine169Residual
    {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (residual : MainFormalPostRolePackageLeftCompletionLine169Residual
      params strategy eps k scalars rolePackage)
    (hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1) :
    MainFormalPostRolePackageCompletionLine169Residual
      params strategy eps k scalars rolePackage where
  leftMeasurement := residual.leftMeasurement
  rightMeasurement := residual.rightMeasurement
  leftCompletionCloseness := residual.leftCompletionCloseness
  rightCompletionCloseness := by
    have hleft : SDDRel strategy.state (uniformDistribution Unit)
        (IdxSubMeas.liftLeft
          (constSubMeasFamily
            (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas))
        (IdxSubMeas.liftLeft
          (constSubMeasFamily residual.rightMeasurement.toSubMeas))
        scalars.zeta2 := by
      simpa [IdxSubMeas.liftLeft, constSubMeasFamily] using
        residual.rightCompletionClosenessLeft
    have hright :=
      MakingMeasurementsProjective.sddRel_liftRight_of_liftLeft_permInv
        strategy.permInvState (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
        (constSubMeasFamily residual.rightMeasurement.toSubMeas)
        scalars.zeta2 hleft
    simpa [IdxSubMeas.liftRight, constSubMeasFamily] using hright
  leftProjectiveRightPOVMPolynomialConsistency :=
    MakingMeasurementsProjective.ProjectivizationMatchMassMonotonicity.leftConsistency
      residual.line169MatchMassMonotonicity hpre
  rightProjectiveLeftPOVMPolynomialConsistency := by
    have hpre_symm : ConsRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
        (constSubMeasFamily
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
        scalars.zeta1 :=
      consRel_symm_of_density_fixed strategy.state strategy.densityFixed
        (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
        (constSubMeasFamily
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
        scalars.zeta1 hpre
    exact
      MakingMeasurementsProjective.ProjectivizationMatchMassMonotonicity.rightConsistency
        residual.line169MatchMassMonotonicity hpre_symm

end MainFormalPostRolePackageLeftCompletionLine169Residual

/-- Combined live residual after isolating concrete role-package production.

The first field is the actual Section 6 role residual: it carries the concrete
role-register measurement and its symmetrized consistency proof.  The second
field contains only the projectivization/completion and line-169 data for the role
package obtained from that concrete residual.  Thus the live `mainFormal` hole no
longer asks for an arbitrary `MainFormalRoleMeasurementPackage`, an arbitrary raw
Section 6 witness, or a decorative branch witness not tied to the concrete
measurement. The branch-level base/successor constructors remain available on
`MainFormalRolePackageResidual` and `MainFormalRolePackageBranchResidual` as the
intended ways to supply this field; their branch conversion consumes the public
large-`k` hypothesis directly rather than storing it as residual data. -/
structure MainFormalCascadeRolePackageResidualCompletionLine169Residual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The explicit isolated Section 6 residual.  Keeping this field concrete avoids
  hiding the role-register measurement behind `Classical.choice`. -/
  roleResidual : MainFormalRolePackageResidual params strategy eps hpass k
  /-- The remaining projectivization/completion and line-169 data after role production. -/
  postRoleResidual :
    MainFormalPostRolePackageCompletionLine169Residual params strategy eps k scalars
      (roleResidual.rolePackage scalars)

namespace MainFormalCascadeRolePackageResidualCompletionLine169Residual

/-- Convert the split role-residual/post-role package back to the role-packaged
completion-line169 residual consumed by the existing downstream wrappers.

The conversion uses the explicit `roleResidual` field, so the role-register
measurement remains visible to the post-role residual. -/
noncomputable def toRolePackagedCompletionLine169Residual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeRolePackageResidualCompletionLine169Residual
      params strategy eps hpass k scalars) :
    MainFormalCascadeRolePackagedCompletionLine169Residual params strategy eps k scalars :=
  residual.postRoleResidual.toRolePackagedCompletionLine169Residual

end MainFormalCascadeRolePackageResidualCompletionLine169Residual

/-- Combined live residual after isolating concrete role-package production
and the #869 Bob-side completion transport.

Compared with `MainFormalCascadeRolePackageResidualCompletionLine169Residual`, this
package no longer asks the live hole to provide the right-register completion
closeness directly.  Instead the post-role field records the left-register
Bob-side completion estimate returned by the orthonormalize-and-complete chain,
and the conversion below transports it to the right register using permutation
invariance of the strategy state.  The concrete role residual and the
construction-level match-mass invariant for the exact paper line-169 `ζ₁` links
remain explicit. -/
structure MainFormalCascadeRolePackageResidualLeftCompletionLine169Residual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The explicit isolated Section 6 residual.  Keeping this field concrete avoids
  hiding the role-register measurement behind `Classical.choice`. -/
  roleResidual : MainFormalRolePackageResidual params strategy eps hpass k
  /-- The remaining projectivization/completion and line-169 data after role production,
  with Bob-side completion still left-lifted. -/
  postRoleResidual :
    MainFormalPostRolePackageLeftCompletionLine169Residual params strategy eps k scalars
      (roleResidual.rolePackage scalars)

namespace MainFormalCascadeRolePackageResidualLeftCompletionLine169Residual

/-- Combine a concrete Section 6 role residual with the checked post-role
orthonormalize-and-complete constructor.

This is the direct constructor for the current live residual once role production,
completion statements, and the construction-level line-169 match-mass monotonicity
inputs are available. -/
noncomputable def ofRoleResidualAndCompleteAtOutcomeStatements
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (P_A P_B : ProjSubMeas (Polynomial params) ι)
    (a_A a_B : Polynomial params)
    (leftStmt :
      MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
        (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement)
        P_A (Preliminaries.completeAtOutcomeProj P_A a_A) a_A scalars.zeta1)
    (rightStmt :
      MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
        (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement)
        P_B (Preliminaries.completeAtOutcomeProj P_B a_B) a_B scalars.zeta1)
    (hleftMass :
      qBipartiteMatchMass strategy.state P_A.toSubMeas
          (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas ≥
        qBipartiteMatchMass strategy.state
          (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
          (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
    (hrightMass :
      qBipartiteMatchMass strategy.state P_B.toSubMeas
          (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas ≥
        qBipartiteMatchMass strategy.state
          (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
          (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas) :
    MainFormalCascadeRolePackageResidualLeftCompletionLine169Residual
      params strategy eps hpass k scalars where
  roleResidual := roleResidual
  postRoleResidual :=
    MainFormalPostRolePackageLeftCompletionLine169Residual.ofCompleteAtOutcomeStatements
      hsmall P_A P_B a_A a_B leftStmt rightStmt hleftMass hrightMass

open MainFormalPostRolePackageLeftCompletionLine169Residual in
/-- Combine a concrete Section 6 role residual with orthonormalize-and-complete
inputs for the two unsymmetrized role blocks.

Like the post-role producer it calls, this is a `Nonempty` theorem rather than a
data-valued constructor: the two completed projective measurements are obtained
from the existential `orthonormalizeAndComplete` theorem without hiding that
choice behind a definition. -/
theorem nonempty_ofRoleResidualAndOrthonormalizeAndCompleteInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (a_A a_B : Polynomial params)
    (leftSelfConsistency :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
        scalars.zeta1)
    (rightSelfConsistency :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
        scalars.zeta1)
    (leftBridge :
      MakingMeasurementsProjective.OrthonormalizationInput strategy.state
        (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
        scalars.zeta1)
    (rightBridge :
      MakingMeasurementsProjective.OrthonormalizationInput strategy.state
        (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
        scalars.zeta1)
    (hleftMass :
      ∀ P_A : ProjSubMeas (Polynomial params) ι,
        MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
          (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement)
          P_A (Preliminaries.completeAtOutcomeProj P_A a_A) a_A scalars.zeta1 →
        qBipartiteMatchMass strategy.state P_A.toSubMeas
            (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas ≥
          qBipartiteMatchMass strategy.state
            (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
            (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
    (hrightMass :
      ∀ P_B : ProjSubMeas (Polynomial params) ι,
        MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
          (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement)
          P_B (Preliminaries.completeAtOutcomeProj P_B a_B) a_B scalars.zeta1 →
        qBipartiteMatchMass strategy.state P_B.toSubMeas
            (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas ≥
          qBipartiteMatchMass strategy.state
            (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
            (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas) :
    Nonempty (MainFormalCascadeRolePackageResidualLeftCompletionLine169Residual
      params strategy eps hpass k scalars) := by
  rcases
    nonempty_ofOrthonormalizeAndCompleteInputs
        (rolePackage := roleResidual.rolePackage scalars)
        hsmall a_A a_B leftSelfConsistency rightSelfConsistency leftBridge rightBridge
        hleftMass hrightMass with ⟨postRoleResidual⟩
  exact ⟨{ roleResidual := roleResidual, postRoleResidual := postRoleResidual }⟩

/-- Convert the left-completion residual to the previous role-residual completion
line-169 shape by applying the #869 right-register transport to the Bob-side
completion estimate, using the separately reconstructed paper line-130
`G^A/G^B` consistency proof. -/
noncomputable def toRolePackageResidualCompletionLine169Residual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeRolePackageResidualLeftCompletionLine169Residual
      params strategy eps hpass k scalars)
    (hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM
          (residual.roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM
          (residual.roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
      scalars.zeta1) :
    MainFormalCascadeRolePackageResidualCompletionLine169Residual
      params strategy eps hpass k scalars where
  roleResidual := residual.roleResidual
  postRoleResidual := residual.postRoleResidual.toPostRolePackageCompletionLine169Residual hpre

end MainFormalCascadeRolePackageResidualLeftCompletionLine169Residual

/-- Live residual after role production and before eliminating the existential
outputs of the orthonormalize-and-complete theorem.

This is the paper Step 6 input boundary: a concrete Section 6 role residual, the
distinguished completion outcomes, strong self-consistency for the two
unsymmetrized POVMs, the explicit orthonormalization bridge data, and the
construction-level match-mass monotonicity facts for the projective
submeasurements produced by orthonormalization.  The completed projective
measurements themselves are intentionally not fields; they are obtained in the
conversion theorem below by eliminating the `orthonormalizeAndComplete`
existentials while the ambient goal is still a proposition. -/
structure MainFormalCascadeRolePackageResidualOrthonormalizeAndCompleteInputResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The explicit isolated Section 6 residual. -/
  roleResidual : MainFormalRolePackageResidual params strategy eps hpass k
  /-- Alice-side distinguished outcome that receives the completion residual. -/
  a_A : Polynomial params
  /-- Bob-side distinguished outcome that receives the completion residual. -/
  a_B : Polynomial params
  /-- Strong self-consistency for the Alice-role unsymmetrized POVM. -/
  leftSelfConsistency :
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
      scalars.zeta1
  /-- Strong self-consistency for the Bob-role unsymmetrized POVM. -/
  rightSelfConsistency :
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
      scalars.zeta1
  /-- Alice-side orthonormalization bridge input. -/
  leftBridge :
    MakingMeasurementsProjective.OrthonormalizationInput strategy.state
      (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
      scalars.zeta1
  /-- Bob-side orthonormalization bridge input. -/
  rightBridge :
    MakingMeasurementsProjective.OrthonormalizationInput strategy.state
      (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
      scalars.zeta1
  /-- Alice-side construction-level match-mass monotonicity for the projective
  submeasurement produced by orthonormalization. -/
  leftMatchMass :
    ∀ P_A : ProjSubMeas (Polynomial params) ι,
      MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
        (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement)
        P_A (Preliminaries.completeAtOutcomeProj P_A a_A) a_A scalars.zeta1 →
      qBipartiteMatchMass strategy.state P_A.toSubMeas
          (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas ≥
        qBipartiteMatchMass strategy.state
          (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
          (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
  /-- Bob-side construction-level match-mass monotonicity for the projective
  submeasurement produced by orthonormalization. -/
  rightMatchMass :
    ∀ P_B : ProjSubMeas (Polynomial params) ι,
      MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
        (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement)
        P_B (Preliminaries.completeAtOutcomeProj P_B a_B) a_B scalars.zeta1 →
      qBipartiteMatchMass strategy.state P_B.toSubMeas
          (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas ≥
        qBipartiteMatchMass strategy.state
          (unsymmetrizedRightPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas
          (unsymmetrizedLeftPOVM (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas

namespace MainFormalCascadeRolePackageResidualOrthonormalizeAndCompleteInputResidual

open MainFormalCascadeRolePackageResidualLeftCompletionLine169Residual in
/-- Run orthonormalize-and-complete on the two role-block POVMs and recover the
left-completion line-169 residual. -/
theorem nonempty_leftCompletionLine169Residual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual :
      MainFormalCascadeRolePackageResidualOrthonormalizeAndCompleteInputResidual
        params strategy eps hpass k scalars)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    Nonempty (MainFormalCascadeRolePackageResidualLeftCompletionLine169Residual
      params strategy eps hpass k scalars) :=
  nonempty_ofRoleResidualAndOrthonormalizeAndCompleteInputs
      hsmall residual.roleResidual residual.a_A residual.a_B
      residual.leftSelfConsistency residual.rightSelfConsistency
      residual.leftBridge residual.rightBridge residual.leftMatchMass residual.rightMatchMass

end MainFormalCascadeRolePackageResidualOrthonormalizeAndCompleteInputResidual

/-- Post-role Step 6 witness data with the actual projectivization witnesses fixed.

This package corresponds to `inductive_step.tex` lines 135--149 after the
role-register Section 6 output has already been produced and unsymmetrized.  It
stores the concrete projective submeasurements `P^A,P^B`, the distinguished
completion outcomes, and the two orthonormalize-and-complete statements giving
the completed measurements `Q^A,Q^B`.

The match-mass fields are the construction-level line-169 supplement: they are
tied to these chosen witnesses, rather than universally quantified over every
possible orthonormalize-and-complete output. -/
structure MainFormalPostRolePackageStep6WitnessResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars) where
  /-- Alice-side projective submeasurement from paper line 138. -/
  P_A : ProjSubMeas (Polynomial params) ι
  /-- Bob-side projective submeasurement from paper line 138. -/
  P_B : ProjSubMeas (Polynomial params) ι
  /-- Alice-side distinguished outcome receiving the completion residual. -/
  a_A : Polynomial params
  /-- Bob-side distinguished outcome receiving the completion residual. -/
  a_B : Polynomial params
  /-- Alice-side orthonormalize-and-complete statement, paper lines 140 and 146. -/
  leftStatement :
    MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
      (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
      P_A (Preliminaries.completeAtOutcomeProj P_A a_A) a_A scalars.zeta1
  /-- Bob-side orthonormalize-and-complete statement, paper lines 141 and 147. -/
  rightStatement :
    MakingMeasurementsProjective.OrthonormalizeAndCompleteStatement strategy.state
      (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
      P_B (Preliminaries.completeAtOutcomeProj P_B a_B) a_B scalars.zeta1
  /-- Alice-side construction-level match-mass monotonicity for the chosen
  orthonormalization witness. -/
  leftMatchMass :
    qBipartiteMatchMass strategy.state P_A.toSubMeas
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas ≥
      qBipartiteMatchMass strategy.state
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas
  /-- Bob-side construction-level match-mass monotonicity for the chosen
  orthonormalization witness. -/
  rightMatchMass :
    qBipartiteMatchMass strategy.state P_B.toSubMeas
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas ≥
      qBipartiteMatchMass strategy.state
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas

namespace MainFormalPostRolePackageStep6WitnessResidual

/-- Consume the post-role Step 6 witness residual and recover the checked
left-completion line-169 residual. -/
noncomputable def toPostRolePackageLeftCompletionLine169Residual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (residual : MainFormalPostRolePackageStep6WitnessResidual
      params strategy eps k scalars rolePackage)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    MainFormalPostRolePackageLeftCompletionLine169Residual
      params strategy eps k scalars rolePackage :=
  MainFormalPostRolePackageLeftCompletionLine169Residual.ofCompleteAtOutcomeStatements
    hsmall residual.P_A residual.P_B residual.a_A residual.a_B
    residual.leftStatement residual.rightStatement residual.leftMatchMass residual.rightMatchMass

end MainFormalPostRolePackageStep6WitnessResidual

/-- Explicit bridge inputs for applying the paper's cross-consistency
orthonormalization lemma to the two unsymmetrized role measurements.

The fields expose the remaining spectral-truncation and locality-preserving
repair witnesses.  The constructor below consumes line 130's `ConsRel`
`G^A ⊗ I ≃ I ⊗ G^B` and applies it in the forward and symmetry-reversed
directions, instead of asking for independent `BipartiteSSCRel` inputs. -/
structure MainFormalPostRolePackageLine130OrthonormalizationInput
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars) where
  /-- Spectral-truncation input for `G^A`. -/
  leftSpectral :
    MakingMeasurementsProjective.SpectralTruncationInput strategy.state
      (leftLiftedMeasurement (ιB := ι)
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement))
      (MakingMeasurementsProjective.consistencyToAlmostProjectiveError scalars.zeta1)
  /-- Locality-preserving repair input for `G^A`. -/
  leftRepair :
    MakingMeasurementsProjective.LeftLiftedProjectivizationRepairInput strategy.state
      (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
      (MakingMeasurementsProjective.consistencyToAlmostProjectiveError scalars.zeta1)
  /-- Spectral-truncation input for `G^B`. -/
  rightSpectral :
    MakingMeasurementsProjective.SpectralTruncationInput strategy.state
      (leftLiftedMeasurement (ιB := ι)
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement))
      (MakingMeasurementsProjective.consistencyToAlmostProjectiveError scalars.zeta1)
  /-- Locality-preserving repair input for `G^B`. -/
  rightRepair :
    MakingMeasurementsProjective.LeftLiftedProjectivizationRepairInput strategy.state
      (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
      (MakingMeasurementsProjective.consistencyToAlmostProjectiveError scalars.zeta1)

/-- Type alias for line-130 orthonormalization inputs that serves as a named
landing point for future formalizations of the orthonormalization lemma's
truncation and repair steps.
See `MainFormalPostRolePackageLine130OrthonormalizationInput` for the
individual fields. -/
abbrev MainFormalPostRolePackageLine130OrthonormalizationBridgeInputs
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars) :
    Type _ :=
  MainFormalPostRolePackageLine130OrthonormalizationInput
    params strategy eps k scalars rolePackage
/-- The pre-completion projective submeasurements obtained from line 130 by the
cross-consistency orthonormalization wrapper.

This stops before `completeAtOutcome`: the honest paper-shaped boundary records
only the part now derivable from the `G^A/G^B` `ConsRel`; completion closeness is
kept as a separate downstream obligation. -/
structure MainFormalPostRolePackageLine130OrthonormalizationResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars) where
  /-- Alice-side projective submeasurement obtained from line-130 consistency. -/
  P_A : ProjSubMeas (Polynomial params) ι
  /-- Bob-side projective submeasurement obtained from line-130 consistency. -/
  P_B : ProjSubMeas (Polynomial params) ι
  /-- Alice-side line-138 orthonormalization closeness. -/
  leftCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily P_A.toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizationError scalars.zeta1)
  /-- Bob-side line-138 orthonormalization closeness, before right-register transport. -/
  rightCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily P_B.toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizationError scalars.zeta1)

namespace MainFormalPostRolePackageLine130OrthonormalizationResidual

/-- Apply the cross-consistency orthonormalization wrapper to the line-130
`G^A/G^B` consistency proof, producing the two pre-completion projective
submeasurements in the non-vacuous scalar regime. -/
theorem nonempty_ofLine130Inputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (hpre : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1)
    (input : MainFormalPostRolePackageLine130OrthonormalizationInput
      params strategy eps k scalars rolePackage) :
    Nonempty (MainFormalPostRolePackageLine130OrthonormalizationResidual
      params strategy eps k scalars rolePackage) := by
  have hζ0 : 0 ≤ scalars.zeta1 := MainFormalCascadeScalars.zeta1_nonneg scalars
  have hζ1 : scalars.zeta1 ≤ 1 :=
    MainFormalCascadeScalars.zeta1_le_one_of_not_mainFormalError_ge_one scalars hsmall
  obtain ⟨P_A, hP_A⟩ :=
    MakingMeasurementsProjective.orthonormalizationMeasurement_of_consistency
      (ψ := strategy.state) (hψ := strategy.isNormalized)
      (A := unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
      (B := unsymmetrizedRightPOVM rolePackage.roleMeasurement)
      (ζ := scalars.zeta1) hζ0 hζ1 input.leftSpectral input.leftRepair hpre
  have hpre_symm : ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1 :=
    consRel_symm_of_density_fixed strategy.state strategy.densityFixed
      (uniformDistribution Unit)
      (constSubMeasFamily (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
      (constSubMeasFamily (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
      scalars.zeta1 hpre
  obtain ⟨P_B, hP_B⟩ :=
    MakingMeasurementsProjective.orthonormalizationMeasurement_of_consistency
      (ψ := strategy.state) (hψ := strategy.isNormalized)
      (A := unsymmetrizedRightPOVM rolePackage.roleMeasurement)
      (B := unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
      (ζ := scalars.zeta1) hζ0 hζ1 input.rightSpectral input.rightRepair hpre_symm
  exact ⟨{
    P_A := P_A
    P_B := P_B
    leftCloseness := hP_A
    rightCloseness := hP_B }⟩

end MainFormalPostRolePackageLine130OrthonormalizationResidual

/-- Post-orthonormalization Step 6 residual that keeps the line-130 provenance
for `P^A,P^B` and exposes only the completion and match-mass obligations still
not produced by the cross-consistency wrapper. -/
structure MainFormalPostRolePackageLine130CompletionResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars) where
  /-- Projective submeasurements and line-138 closeness derived from line 130. -/
  orthResidual : MainFormalPostRolePackageLine130OrthonormalizationResidual
    params strategy eps k scalars rolePackage
  /-- Alice-side distinguished outcome receiving the completion residual. -/
  a_A : Polynomial params
  /-- Bob-side distinguished outcome receiving the completion residual. -/
  a_B : Polynomial params
  /-- Alice-side completion closeness for the line-130 projective submeasurement. -/
  leftCompletedCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily
        (Preliminaries.completeAtOutcomeProj orthResidual.P_A a_A).toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1)
  /-- Bob-side completion closeness for the line-130 projective submeasurement. -/
  rightCompletedCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily
        (Preliminaries.completeAtOutcomeProj orthResidual.P_B a_B).toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1)
  /-- Alice-side construction-level match-mass monotonicity for the chosen line-130 witness. -/
  leftMatchMass :
    qBipartiteMatchMass strategy.state orthResidual.P_A.toSubMeas
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas ≥
      qBipartiteMatchMass strategy.state
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas
  /-- Bob-side construction-level match-mass monotonicity for the chosen line-130 witness. -/
  rightMatchMass :
    qBipartiteMatchMass strategy.state orthResidual.P_B.toSubMeas
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas ≥
      qBipartiteMatchMass strategy.state
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas

namespace MainFormalPostRolePackageStep6WitnessResidual

/-- Build the fixed Step 6 witness package from a line-130 orthonormalization
residual plus the still-external completion estimates.

This constructor is the honest bridge from the new cross-consistency
orthonormalization wrapper to the existing orthonormalize-and-complete residual:
the projective submeasurements and their line-138 closeness now come from
`ConsRel G^A G^B ζ₁`; only the completion-to-measurement closeness and
match-mass monotonicity remain supplied separately. -/
noncomputable def ofLine130OrthonormalizationAndCompletion
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (orthResidual : MainFormalPostRolePackageLine130OrthonormalizationResidual
      params strategy eps k scalars rolePackage)
    (a_A a_B : Polynomial params)
    (leftCompletedCloseness :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
        (constSubMeasFamily
          (Preliminaries.completeAtOutcomeProj orthResidual.P_A a_A).toSubMeas.liftLeft)
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1))
    (rightCompletedCloseness :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
        (constSubMeasFamily
          (Preliminaries.completeAtOutcomeProj orthResidual.P_B a_B).toSubMeas.liftLeft)
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1))
    (leftMatchMass :
      qBipartiteMatchMass strategy.state orthResidual.P_A.toSubMeas
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas ≥
        qBipartiteMatchMass strategy.state
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
    (rightMatchMass :
      qBipartiteMatchMass strategy.state orthResidual.P_B.toSubMeas
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas ≥
        qBipartiteMatchMass strategy.state
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas) :
    MainFormalPostRolePackageStep6WitnessResidual
      params strategy eps k scalars rolePackage where
  P_A := orthResidual.P_A
  P_B := orthResidual.P_B
  a_A := a_A
  a_B := a_B
  leftStatement :=
    { orthonormalizationCloseness := orthResidual.leftCloseness
      completedCloseness := leftCompletedCloseness }
  rightStatement :=
    { orthonormalizationCloseness := orthResidual.rightCloseness
      completedCloseness := rightCompletedCloseness }
  leftMatchMass := leftMatchMass
  rightMatchMass := rightMatchMass

end MainFormalPostRolePackageStep6WitnessResidual

/-- Explicit completion witnesses for a fixed line-130 orthonormalization residual.

This is the data-valued version of the remaining Step 6 completion producer: it
records the distinguished completion outcomes, the two completed-closeness
statements, and the construction-level orthonormalization match-mass preservation
facts for the chosen line-130 projective submeasurements.  The self-consistency
hypotheses used by `completingToMeasurement` are not stored here after the
completed-closeness fields have been produced; see
`nonempty_ofCompletingToMeasurementInputs` below for the proposition-valued
constructor that derives these fields from `BipartiteSSCRel`. -/
structure MainFormalPostRolePackageLine130CompletionInput
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k)
    (rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars)
    (orthResidual : MainFormalPostRolePackageLine130OrthonormalizationResidual
      params strategy eps k scalars rolePackage) where
  /-- Alice-side distinguished outcome receiving the completion residual. -/
  a_A : Polynomial params
  /-- Bob-side distinguished outcome receiving the completion residual. -/
  a_B : Polynomial params
  /-- Alice-side completed-closeness proof for the line-130 projective submeasurement. -/
  leftCompletedCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily
        (Preliminaries.completeAtOutcomeProj orthResidual.P_A a_A).toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1)
  /-- Bob-side completed-closeness proof in the left-register form returned by
  `completingToMeasurement`. -/
  rightCompletedCloseness :
    SDDRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
      (constSubMeasFamily
        (Preliminaries.completeAtOutcomeProj orthResidual.P_B a_B).toSubMeas.liftLeft)
      (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1)
  /-- Alice-side match-mass preservation for the line-130 orthonormalized
  submeasurement against Bob's unsymmetrized POVM. -/
  leftMatchMassPreservation :
    MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
      (unsymmetrizedLeftPOVM rolePackage.roleMeasurement) orthResidual.P_A
      (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
  /-- Bob-side match-mass preservation, in the role-reversed orientation used by
  the mirror line-169 link. -/
  rightMatchMassPreservation :
    MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
      (unsymmetrizedRightPOVM rolePackage.roleMeasurement) orthResidual.P_B
      (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)

namespace MainFormalPostRolePackageLine130CompletionInput

/-- Convert explicit line-130 completion witnesses into the residual shape
consumed by the live Step 6 assembly.

This is the checked data-valued constructor for the old generic
`completionProducer`: callers may supply a function returning this input for each
line-130 orthonormalization residual and then use `toCompletionResidual` as the
producer. -/
noncomputable def toCompletionResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    {orthResidual : MainFormalPostRolePackageLine130OrthonormalizationResidual
      params strategy eps k scalars rolePackage}
    (input : MainFormalPostRolePackageLine130CompletionInput
      params strategy eps k scalars rolePackage orthResidual) :
    MainFormalPostRolePackageLine130CompletionResidual
      params strategy eps k scalars rolePackage where
  orthResidual := orthResidual
  a_A := input.a_A
  a_B := input.a_B
  leftCompletedCloseness := input.leftCompletedCloseness
  rightCompletedCloseness := input.rightCompletedCloseness
  leftMatchMass := input.leftMatchMassPreservation.matchMassPreservation
  rightMatchMass := input.rightMatchMassPreservation.matchMassPreservation

/-- The completed measurements obtained from a completion input satisfy the
construction-level match-mass monotonicity invariant used for the exact paper
line-169 `ζ₁` links.

This exposes the role of
`ProjectivizationMatchMassMonotonicity.of_submeasurement_match_mass_and_completion`
for callers that reason directly with completed projective measurements, while
`toCompletionResidual` keeps the older residual's P-level match-mass fields. -/
theorem toProjectivizationMatchMassMonotonicity
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    {orthResidual : MainFormalPostRolePackageLine130OrthonormalizationResidual
      params strategy eps k scalars rolePackage}
    (input : MainFormalPostRolePackageLine130CompletionInput
      params strategy eps k scalars rolePackage orthResidual) :
    MakingMeasurementsProjective.ProjectivizationMatchMassMonotonicity strategy.state
      (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
      (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
      (Preliminaries.completeAtOutcomeProj orthResidual.P_A input.a_A)
      (Preliminaries.completeAtOutcomeProj orthResidual.P_B input.a_B) :=
  MakingMeasurementsProjective.ProjectivizationMatchMassMonotonicity.of_submeasurement_match_mass_and_completion
      orthResidual.P_A orthResidual.P_B input.a_A input.a_B
      (Preliminaries.completeAtOutcomeProj orthResidual.P_A input.a_A)
      (Preliminaries.completeAtOutcomeProj orthResidual.P_B input.a_B)
      rfl rfl input.leftMatchMassPreservation input.rightMatchMassPreservation

/-- Produce explicit completion witnesses from the analytic completion theorem.

The only analytic hypotheses are exactly the two strong self-consistency facts
for the unsymmetrized role POVMs.  The line-130 orthonormalization residual
provides the `A ≈ P` closeness input to `completingToMeasurement`; the returned
completed-closeness statements are repackaged for the canonical projective
completions `completeAtOutcomeProj`. -/
theorem nonempty_ofCompletingToMeasurementInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (orthResidual : MainFormalPostRolePackageLine130OrthonormalizationResidual
      params strategy eps k scalars rolePackage)
    (a_A a_B : Polynomial params)
    (leftSelfConsistency :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
        scalars.zeta1)
    (rightSelfConsistency :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
        scalars.zeta1)
    (leftMatchMassPreservation :
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement) orthResidual.P_A
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement))
    (rightMatchMassPreservation :
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
        (unsymmetrizedRightPOVM rolePackage.roleMeasurement) orthResidual.P_B
        (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)) :
    Nonempty (MainFormalPostRolePackageLine130CompletionInput
      params strategy eps k scalars rolePackage orthResidual) := by
  classical
  obtain ⟨C_A, hC_A, hC_Astmt⟩ :=
    Preliminaries.completingToMeasurement
      (Outcome := Polynomial params) (ι := ι) strategy.state strategy.permInvState
      strategy.isNormalized (unsymmetrizedLeftPOVM rolePackage.roleMeasurement)
      orthResidual.P_A.toSubMeas a_A
      (MakingMeasurementsProjective.orthonormalizationError scalars.zeta1)
      scalars.zeta1 leftSelfConsistency orthResidual.leftCloseness
  obtain ⟨C_B, hC_B, hC_Bstmt⟩ :=
    Preliminaries.completingToMeasurement
      (Outcome := Polynomial params) (ι := ι) strategy.state strategy.permInvState
      strategy.isNormalized (unsymmetrizedRightPOVM rolePackage.roleMeasurement)
      orthResidual.P_B.toSubMeas a_B
      (MakingMeasurementsProjective.orthonormalizationError scalars.zeta1)
      scalars.zeta1 rightSelfConsistency orthResidual.rightCloseness
  have leftCompletedCloseness :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
        (constSubMeasFamily
          (Preliminaries.completeAtOutcomeProj orthResidual.P_A a_A).toSubMeas.liftLeft)
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1) := by
    simpa [MakingMeasurementsProjective.orthonormalizeAndCompleteError, hC_A] using
      hC_Astmt.closenessAfterCompletion
  have rightCompletedCloseness :
      SDDRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas.liftLeft)
        (constSubMeasFamily
          (Preliminaries.completeAtOutcomeProj orthResidual.P_B a_B).toSubMeas.liftLeft)
        (MakingMeasurementsProjective.orthonormalizeAndCompleteError scalars.zeta1) := by
    simpa [MakingMeasurementsProjective.orthonormalizeAndCompleteError, hC_B] using
      hC_Bstmt.closenessAfterCompletion
  exact ⟨{
    a_A := a_A
    a_B := a_B
    leftCompletedCloseness := leftCompletedCloseness
    rightCompletedCloseness := rightCompletedCloseness
    leftMatchMassPreservation := leftMatchMassPreservation
    rightMatchMassPreservation := rightMatchMassPreservation }⟩

end MainFormalPostRolePackageLine130CompletionInput

namespace MainFormalPostRolePackageLine130CompletionResidual

/-- Forget only the provenance wrapper after constructing the fixed Step 6
witness package from line-130 orthonormalization plus completion closeness. -/
noncomputable def toStep6WitnessResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    {rolePackage : MainFormalRoleMeasurementPackage params strategy eps k scalars}
    (residual : MainFormalPostRolePackageLine130CompletionResidual
      params strategy eps k scalars rolePackage) :
    MainFormalPostRolePackageStep6WitnessResidual
      params strategy eps k scalars rolePackage :=
  MainFormalPostRolePackageStep6WitnessResidual.ofLine130OrthonormalizationAndCompletion
    residual.orthResidual residual.a_A residual.a_B
    residual.leftCompletedCloseness residual.rightCompletedCloseness
    residual.leftMatchMass residual.rightMatchMass

end MainFormalPostRolePackageLine130CompletionResidual

/-- Paper-shaped residual for the still-external data in the non-vacuous branch.

The proof body consumes this package in paper order: first it reads the concrete
role residual, then derives the unsymmetrized POVMs, line-116 evaluated
consistency, and Step-5 full `G^A/G^B` consistency, and only then consumes the
post-role Step 6 completion data whose `P^A/P^B` provenance is tied to that
line-130 consistency. -/
structure MainFormalCascadeRolePackageResidualStep6WitnessResidual
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) (k : ℕ)
    (scalars : MainFormalCascadeScalars params eps k) where
  /-- The explicit isolated Section 6 residual. -/
  roleResidual : MainFormalRolePackageResidual params strategy eps hpass k
  /-- Step 6 completion data after line-130 orthonormalization of the role blocks. -/
  postRoleLine130Completion :
    MainFormalPostRolePackageLine130CompletionResidual params strategy eps k scalars
      (roleResidual.rolePackage scalars)

namespace MainFormalCascadeRolePackageResidualStep6WitnessResidual

/-- Assemble the final live residual once the concrete Section 6 role residual and
the post-role line-130 completion residual have both been produced. -/
theorem nonempty_ofRoleResidualAndCompletion
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (hcompletion : Nonempty (MainFormalPostRolePackageLine130CompletionResidual
      params strategy eps k scalars (roleResidual.rolePackage scalars))) :
    Nonempty (MainFormalCascadeRolePackageResidualStep6WitnessResidual
      params strategy eps hpass k scalars) := by
  rcases hcompletion with ⟨completion⟩
  exact ⟨{ roleResidual := roleResidual, postRoleLine130Completion := completion }⟩

/-- Assemble the final live residual from a concrete Section 6 role residual, the
line-130 orthonormalization bridge inputs, and a producer for the remaining
completion/match-mass obligations for the projective submeasurements obtained from
line 130.

This is the precise remaining shape of the final `mainFormal` hole after the
paper-order handoffs have been named. -/
theorem nonempty_ofRoleResidualAndLine130Inputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (input : MainFormalPostRolePackageLine130OrthonormalizationInput
      params strategy eps k scalars (roleResidual.rolePackage scalars))
    (completionProducer :
      MainFormalPostRolePackageLine130OrthonormalizationResidual
          params strategy eps k scalars (roleResidual.rolePackage scalars) →
        MainFormalPostRolePackageLine130CompletionResidual
          params strategy eps k scalars (roleResidual.rolePackage scalars)) :
    Nonempty (MainFormalCascadeRolePackageResidualStep6WitnessResidual
      params strategy eps hpass k scalars) := by
  have hpre := roleResidual.line130Consistency scalars
  rcases MainFormalPostRolePackageLine130OrthonormalizationResidual.nonempty_ofLine130Inputs
      hsmall hpre input with ⟨orthResidual⟩
  exact nonempty_ofRoleResidualAndCompletion roleResidual ⟨completionProducer orthResidual⟩

/-- Assemble the final live residual using explicit completion inputs rather than
an opaque `completionProducer`.

A caller supplies, for each line-130 orthonormalization residual produced from
the bridge inputs, the concrete distinguished outcomes, completed-closeness
proofs, and orthonormalization match-mass preservation facts packaged as
`MainFormalPostRolePackageLine130CompletionInput`.  This theorem converts that
package into the old producer shape by `toCompletionResidual`. -/
theorem nonempty_ofRoleResidualAndLine130InputsAndCompletionInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (input : MainFormalPostRolePackageLine130OrthonormalizationInput
      params strategy eps k scalars (roleResidual.rolePackage scalars))
    (completionInputProducer :
      ∀ orthResidual : MainFormalPostRolePackageLine130OrthonormalizationResidual
          params strategy eps k scalars (roleResidual.rolePackage scalars),
        MainFormalPostRolePackageLine130CompletionInput
          params strategy eps k scalars (roleResidual.rolePackage scalars) orthResidual) :
    Nonempty (MainFormalCascadeRolePackageResidualStep6WitnessResidual
      params strategy eps hpass k scalars) :=
  nonempty_ofRoleResidualAndLine130Inputs hsmall roleResidual input fun orthResidual =>
    (completionInputProducer orthResidual).toCompletionResidual

/-- Assemble the final live residual from the exact analytic completion witnesses.

This is the paper-shaped replacement for the generic `completionProducer`: after
line 130 produces `P^A` and `P^B`, the caller provides
* distinguished completion outcomes `a_A`, `a_B`,
* strong self-consistency for the two unsymmetrized role POVMs, and
* orthonormalization match-mass preservation for the two produced
  submeasurements.

The proof invokes `completingToMeasurement` to derive the two completed-closeness
fields and then packages them through
`MainFormalPostRolePackageLine130CompletionInput.toCompletionResidual`. -/
theorem nonempty_ofRoleResidualAndLine130InputsAndCompletingToMeasurementInputs
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (input : MainFormalPostRolePackageLine130OrthonormalizationInput
      params strategy eps k scalars (roleResidual.rolePackage scalars))
    (a_A a_B : Polynomial params)
    (leftSelfConsistency :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedLeftPOVM
            (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
        scalars.zeta1)
    (rightSelfConsistency :
      BipartiteSSCRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedRightPOVM
            (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
        scalars.zeta1)
    (leftMatchMassPreservation :
      ∀ orthResidual : MainFormalPostRolePackageLine130OrthonormalizationResidual
          params strategy eps k scalars (roleResidual.rolePackage scalars),
        MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
          (unsymmetrizedLeftPOVM
            (roleResidual.rolePackage scalars).roleMeasurement)
          orthResidual.P_A
          (unsymmetrizedRightPOVM
            (roleResidual.rolePackage scalars).roleMeasurement))
    (rightMatchMassPreservation :
      ∀ orthResidual : MainFormalPostRolePackageLine130OrthonormalizationResidual
          params strategy eps k scalars (roleResidual.rolePackage scalars),
        MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation strategy.state
          (unsymmetrizedRightPOVM
            (roleResidual.rolePackage scalars).roleMeasurement)
          orthResidual.P_B
          (unsymmetrizedLeftPOVM
            (roleResidual.rolePackage scalars).roleMeasurement)) :
    Nonempty (MainFormalCascadeRolePackageResidualStep6WitnessResidual
      params strategy eps hpass k scalars) := by
  have hpre := roleResidual.line130Consistency scalars
  rcases MainFormalPostRolePackageLine130OrthonormalizationResidual.nonempty_ofLine130Inputs
      hsmall hpre input with ⟨orthResidual⟩
  rcases MainFormalPostRolePackageLine130CompletionInput.nonempty_ofCompletingToMeasurementInputs
      orthResidual a_A a_B
        leftSelfConsistency rightSelfConsistency
        (leftMatchMassPreservation orthResidual)
        (rightMatchMassPreservation orthResidual) with ⟨completionInput⟩
  exact nonempty_ofRoleResidualAndCompletion roleResidual
    ⟨completionInput.toCompletionResidual⟩

/-- Bridge-shape alias for
`nonempty_ofRoleResidualAndLine130InputsAndCompletingToMeasurementInputs`
accepting the orthonormalization inputs under the `…BridgeInputs` name.

The alias is definitional (the bridge `abbrev` unfolds in-place) and exists
only as a documented entry point for callers that carry the bridge wrapper. -/
alias nonempty_ofRoleResidualAndBridgeInputsAndCompletingToMeasurementInputs :=
  nonempty_ofRoleResidualAndLine130InputsAndCompletingToMeasurementInputs

/-- Convert the combined residual to the left-completion residual after the paper
line-130 consistency has been derived separately. -/
noncomputable def toLeftCompletionLine169Residual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (residual : MainFormalCascadeRolePackageResidualStep6WitnessResidual
      params strategy eps hpass k scalars)
    (hsmall : ¬ 1 ≤ mainFormalError params k eps) :
    MainFormalCascadeRolePackageResidualLeftCompletionLine169Residual
      params strategy eps hpass k scalars :=
  open MainFormalCascadeRolePackageResidualLeftCompletionLine169Residual in
  { roleResidual := residual.roleResidual
    postRoleResidual :=
      residual.postRoleLine130Completion.toStep6WitnessResidual
        |>.toPostRolePackageLeftCompletionLine169Residual hsmall }

end MainFormalCascadeRolePackageResidualStep6WitnessResidual

namespace MainFormalCascadeTransportTargets

/-- Add the already-discharged scalar package back to the transport-only targets. -/
noncomputable def toCascadeTargets {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {scalars : MainFormalCascadeScalars params eps k}
    (targets : MainFormalCascadeTransportTargets params strategy eps k scalars) :
    MainFormalCascadeTargets params strategy eps k where
  scalars := scalars
  leftMeasurement := targets.leftMeasurement
  rightMeasurement := targets.rightMeasurement
  pointAConsistency := targets.pointAConsistency
  pointBConsistency := targets.pointBConsistency
  selfConsistency := targets.selfConsistency

end MainFormalCascadeTransportTargets

/-- Paper-native final targets for the remaining `mainFormal` assembly.

This structure deliberately stops before the final error-envelope weakening. Its
three consistency fields are exactly the native conclusions reached in
`references/ldt-paper/inductive_step.tex`:

* `eq:one-goal` (lines 175--181):
  $A^{\mathrm A,u}_a \otimes I \simeq_{\zeta_4}
    I \otimes Q^{\mathrm B}_{[g(u)=a]}$;
* `eq:another-goal` (lines 182--185):
  $I \otimes A^{\mathrm B,u}_a \simeq_{\zeta_4}
    Q^{\mathrm A}_{[g(u)=a]} \otimes I$;
* `eq:third-goal` (lines 160--162):
  $Q^{\mathrm A}_g \otimes I \simeq_{\zeta_3/2} I \otimes Q^{\mathrm B}_g$.

The two bound fields record the already-formalized Step 8 absorption of
`\zeta_4` and `\zeta_3/2` into `mainFormalError`. Constructing this package from
Section 6 and the unsymmetrization / Schwartz--Zippel / projectivization chain is
the live residual; the projection theorem below is only the final paper-faithful
packaging step. -/
structure MainFormalNativeTargets
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ) where
  /-- The projective measurement denoted $Q^{\mathrm A}$ in the paper. -/
  leftMeasurement : ProjMeas (Polynomial params) ι
  /-- The projective measurement denoted $Q^{\mathrm B}$ in the paper. -/
  rightMeasurement : ProjMeas (Polynomial params) ι
  /-- The paper's self-consistency error `\zeta_3`. -/
  zeta3 : Error
  /-- The paper's two point-consistency error `\zeta_4`. -/
  zeta4 : Error
  /-- Native form of `eq:one-goal`, before weakening to `mainFormalError`. -/
  pointAConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementA)
      (polynomialEvaluationFamily params rightMeasurement.toSubMeas)
      zeta4
  /-- Native form of `eq:another-goal`, before weakening to `mainFormalError`. -/
  pointBConsistency :
    ConsRel strategy.state (uniformDistribution (Point params))
      (polynomialEvaluationFamily params leftMeasurement.toSubMeas)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurementB)
      zeta4
  /-- Native form of `eq:third-goal`, before its point-evaluation data processing. -/
  selfConsistency :
    ConsRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily leftMeasurement.toSubMeas)
      (constSubMeasFamily rightMeasurement.toSubMeas)
      (zeta3 / 2)
  /-- Step 8 scalar absorption for the two point-consistency targets. -/
  pointErrorLe : zeta4 ≤ mainFormalError params k eps
  /-- Step 8 scalar absorption for the self-consistency target. -/
  selfErrorLe : zeta3 / 2 ≤ mainFormalError params k eps

namespace MainFormalNativeTargets

/-- Final packaging step for `thm:main-formal` once the formal native targets have
been constructed. This only weakens the native `\zeta_4` and `\zeta_3/2` bounds to
`mainFormalError` using `ConsRel.mono`; all substantive transport work is in the
construction of `MainFormalNativeTargets`. -/
theorem toMainFormal {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (targets : MainFormalNativeTargets params strategy eps k) :
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
  refine ⟨targets.leftMeasurement, targets.rightMeasurement, ?_, ?_, ?_⟩
  · exact ConsRel.mono targets.pointErrorLe targets.pointAConsistency
  · exact ConsRel.mono targets.pointErrorLe targets.pointBConsistency
  · exact ConsRel.mono targets.selfErrorLe targets.selfConsistency

end MainFormalNativeTargets

namespace MainFormalCascadeTargets

/-- Convert exact cascade-error targets into `MainFormalNativeTargets` by applying
the already-formalized Step 8 scalar absorption lemmas.

This is still only packaging: the assumptions are the `eq:one-goal`,
`eq:another-goal`, and `eq:third-goal` statements at the formal cascade errors
from `inductive_step.tex` lines 159--185, with the Step 6 `ζ₂` scalar widened
as documented in `ErrorCascade.lean`. -/
noncomputable def toNativeTargets {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    (targets : MainFormalCascadeTargets params strategy eps k) :
    MainFormalNativeTargets params strategy eps k where
  leftMeasurement := targets.leftMeasurement
  rightMeasurement := targets.rightMeasurement
  zeta3 := targets.scalars.zeta3
  zeta4 := targets.scalars.zeta4
  pointAConsistency := targets.pointAConsistency
  pointBConsistency := targets.pointBConsistency
  selfConsistency := targets.selfConsistency
  pointErrorLe := MainFormalCascadeScalars.zeta4_le_mainFormalError targets.scalars
  selfErrorLe := MainFormalCascadeScalars.zeta3_div_two_le_mainFormalError targets.scalars

end MainFormalCascadeTargets

/-! ### Base (m = 1) Step 6 analytic hypotheses

The base case (`m = 1`) generation of the Step 6 witness residual still
requires the same analytic content as the successor case: spectral
truncation and locality-preserving repair witnesses for the unsymmetrized
POVMs, strong self-consistency (`BipartiteSSCRel`), and match-mass
preservation.  These are proof obligations whose formalization
corresponds to unformalized content in Section 5 and Section 6 of the
paper; they are bundled as a single structure to give a single target
for the remaining work.  When these hypotheses are supplied,
`baseStep6WitnessResidual` provides the checked assembly theorem that
fills the base branch of `mainFormal`. -/

/-- Analytic hypotheses that are still unformalized for the
base case (`m = 1`) Step 6 witness residual: orthonormalization
inputs (spectral truncation and repair witnesses), distinguished
outcomes, strong self-consistency (`BipartiteSSCRel`), and
match-mass preservation for the unsymmetrized POVMs.

Supplying these hypotheses yields a complete `baseStep6WitnessResidual`
for the base branch of `mainFormal`; the remaining successor-case
proof obligations are tracked separately. -/
structure MainFormalStep6Hypotheses
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (scalars : MainFormalCascadeScalars params eps k)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k) where
  /-- Line-130 orthonormalization inputs: spectral-truncation and
  locality-preserving repair witnesses for both unsymmetrized POVMs. -/
  orthonormalizationInput :
    MainFormalPostRolePackageLine130OrthonormalizationInput
      params strategy eps k scalars (roleResidual.rolePackage scalars)
  /-- Alice-side distinguished outcome for the completion step. -/
  a_A : Polynomial params
  /-- Bob-side distinguished outcome for the completion step. -/
  a_B : Polynomial params
  /-- Alice-side strong self-consistency for the unsymmetrized POVM
  obtained from the role measurement. -/
  leftSelfConsistency :
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM
          (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
      scalars.zeta1
  /-- Bob-side strong self-consistency for the unsymmetrized POVM
  obtained from the role measurement. -/
  rightSelfConsistency :
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM
          (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
      scalars.zeta1
  /-- Alice-side match-mass preservation: for each line-130 orthonormalization
  residual, the projective submeasurement `P_A` preserves match mass against
  Bob's unsymmetrized POVM. -/
  leftMatchMassPreservation :
    ∀ orthResidual : MainFormalPostRolePackageLine130OrthonormalizationResidual
        params strategy eps k scalars (roleResidual.rolePackage scalars),
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation
        strategy.state
        (unsymmetrizedLeftPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
        orthResidual.P_A
        (unsymmetrizedRightPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
  /-- Bob-side match-mass preservation: for each line-130 orthonormalization
  residual, the projective submeasurement `P_B` preserves match mass against
  Alice's unsymmetrized POVM. -/
  rightMatchMassPreservation :
    ∀ orthResidual : MainFormalPostRolePackageLine130OrthonormalizationResidual
        params strategy eps k scalars (roleResidual.rolePackage scalars),
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation
        strategy.state
        (unsymmetrizedRightPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
        orthResidual.P_B
        (unsymmetrizedLeftPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)

/-- Assemble the Step 6 witness residual from the bundled analytic hypotheses.

This theorem takes an explicit `roleResidual` (obtainable from either
`MainFormalRolePackageResidual.ofBaseCase` or the successor-branch
handoff) and the `MainFormalStep6Hypotheses` bridge, then assembles the
Step 6 witness residual through
`MainFormalCascadeRolePackageResidualStep6WitnessResidual.nonempty_ofRoleResidualAndLine130InputsAndCompletingToMeasurementInputs`.

Refs #1009, #422. -/
theorem baseStep6WitnessResidual
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (bridge : MainFormalStep6Hypotheses params strategy eps k
      hpass scalars roleResidual) :
    Nonempty (MainFormalCascadeRolePackageResidualStep6WitnessResidual
      params strategy eps hpass k scalars) := by
  exact
    MainFormalCascadeRolePackageResidualStep6WitnessResidual.nonempty_ofRoleResidualAndLine130InputsAndCompletingToMeasurementInputs
      hsmall roleResidual bridge.orthonormalizationInput bridge.a_A bridge.a_B
      bridge.leftSelfConsistency bridge.rightSelfConsistency
      bridge.leftMatchMassPreservation bridge.rightMatchMassPreservation


/-- Narrowed base-case bridge hypotheses for Step 6 when `params.m = 1`.

Compared to `MainFormalStep6Hypotheses`, this structure omits the two
distinguished outcomes `a_A` and `a_B`, which can be filled with default
polynomials (the zero polynomial) at `m = 1`.  The remaining five fields
— orthonormalization inputs, strong self-consistency, and match-mass
preservation — are the genuinely analytic obligations that must be supplied
by the caller.

A conversion theorem `baseStep6Hypotheses_ofBaseBridge` constructs the full
`MainFormalStep6Hypotheses` from a `MainFormalBaseBridgeHypotheses` by
providing default distinguished outcomes.

Refs #1043, #1009, #422. -/
structure MainFormalBaseBridgeHypotheses
    (params : Parameters) [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι) (eps : Error) (k : ℕ)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (scalars : MainFormalCascadeScalars params eps k)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k) where
  /-- Line-130 orthonormalization inputs: spectral-truncation and
  locality-preserving repair witnesses for both unsymmetrized POVMs. -/
  orthonormalizationInput :
    MainFormalPostRolePackageLine130OrthonormalizationInput
      params strategy eps k scalars (roleResidual.rolePackage scalars)
  /-- Alice-side strong self-consistency for the unsymmetrized POVM
  obtained from the role measurement. -/
  leftSelfConsistency :
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedLeftPOVM
          (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
      scalars.zeta1
  /-- Bob-side strong self-consistency for the unsymmetrized POVM
  obtained from the role measurement. -/
  rightSelfConsistency :
    BipartiteSSCRel strategy.state (uniformDistribution Unit)
      (constSubMeasFamily
        (unsymmetrizedRightPOVM
          (roleResidual.rolePackage scalars).roleMeasurement).toSubMeas)
      scalars.zeta1
  /-- Alice-side match-mass preservation: for each line-130 orthonormalization
  residual, the projective submeasurement `P_A` preserves match mass against
  Bob's unsymmetrized POVM. -/
  leftMatchMassPreservation :
    ∀ orthResidual : MainFormalPostRolePackageLine130OrthonormalizationResidual
        params strategy eps k scalars (roleResidual.rolePackage scalars),
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation
        strategy.state
        (unsymmetrizedLeftPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
        orthResidual.P_A
        (unsymmetrizedRightPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
  /-- Bob-side match-mass preservation: for each line-130 orthonormalization
  residual, the projective submeasurement `P_B` preserves match mass against
  Alice's unsymmetrized POVM. -/
  rightMatchMassPreservation :
    ∀ orthResidual : MainFormalPostRolePackageLine130OrthonormalizationResidual
        params strategy eps k scalars (roleResidual.rolePackage scalars),
      MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation
        strategy.state
        (unsymmetrizedRightPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)
        orthResidual.P_B
        (unsymmetrizedLeftPOVM
          (roleResidual.rolePackage scalars).roleMeasurement)

/-- Convert narrowed base bridge hypotheses to the full
`MainFormalStep6Hypotheses` by providing default distinguished outcomes.

The distinguished outcomes `a_A` and `a_B` are chosen as the zero polynomial;
`completeAtOutcomeProj` works for any distinguished outcome, so this choice
is sound.  Callers that need specific distinguished outcomes should use
`MainFormalStep6Hypotheses` directly.

Refs #1043. -/
noncomputable def baseStep6Hypotheses_ofBaseBridge
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    {roleResidual : MainFormalRolePackageResidual params strategy eps hpass k}
    (bridge : MainFormalBaseBridgeHypotheses params strategy eps k hpass
      scalars roleResidual) :
    MainFormalStep6Hypotheses params strategy eps k hpass scalars roleResidual where
  orthonormalizationInput := bridge.orthonormalizationInput
  a_A := Classical.choice (inferInstance : Nonempty (Polynomial params))
  a_B := Classical.choice (inferInstance : Nonempty (Polynomial params))
  leftSelfConsistency := bridge.leftSelfConsistency
  rightSelfConsistency := bridge.rightSelfConsistency
  leftMatchMassPreservation := bridge.leftMatchMassPreservation
  rightMatchMassPreservation := bridge.rightMatchMassPreservation

/-- Base-case specialization of `baseStep6WitnessResidual` that explicitly
records the `params.m = 1` hypothesis alongside the narrowed bridge.

The narrowed `MainFormalBaseBridgeHypotheses` omits `a_A` and `a_B`, which
are filled with the zero polynomial by `baseStep6Hypotheses_ofBaseBridge`.
This serves as a future landing point for m=1-specific simplifications
(e.g. single-element POVM orthonormalization).

Refs #1043. -/
theorem baseStep6WitnessResidual_ofBaseBridge
    {params : Parameters} [FieldModel.{0} params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : SameSpaceProjStrat params ι} {eps : Error} {k : ℕ}
    {hpass : strategy.PassesLowIndividualDegreeTest eps}
    {scalars : MainFormalCascadeScalars params eps k}
    (hsmall : ¬ 1 ≤ mainFormalError params k eps)
    (hm1 : params.m = 1)
    (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k)
    (bridge : MainFormalBaseBridgeHypotheses params strategy eps k hpass
      scalars roleResidual) :
    Nonempty (MainFormalCascadeRolePackageResidualStep6WitnessResidual
      params strategy eps hpass k scalars) := by
  exact baseStep6WitnessResidual hsmall roleResidual
    (baseStep6Hypotheses_ofBaseBridge bridge)




/--
`thm:main-formal` from `test_definition.tex`.

The bipartite tensor placement follows the paper:
- **1a**: `A^A_u ⊗ I ≈_ν I ⊗ G^B_{[g(u)=a]}` — G_B on **right**
- **1b**: `I ⊗ A^B_u ≈_ν G^A_{[g(u)=a]} ⊗ I` — G_A on **left**, A^B on **right**
- **2**: `G^A_g ⊗ I ≈_ν I ⊗ G^B_g` — G_B on **right**

The `k`-bound boundary records the statement fix from issue #906: the paper's
successor proof applies the Section 6 / Pasting-side wrappers, whose checked
side condition is `400 * params.m * params.d ≤ k`. The public theorem therefore
exposes this stronger hypothesis instead of trying to derive it from the paper's
printed `params.m * params.d ≤ k` assumption.

After first separating off the saturated-error branch, the checked role-package
infrastructure now exposes the base producer and a branch-level successor
producer:

* the base handoff `strategySymmetrization_mainInductionBaseCase`, packaged as
  `MainFormalRolePackageBranchResidual.base`, and
* the predecessor/successor handoff
  `MainFormalRolePackageBranchResidual.successor`, which carries a bundled
  `Parameters.SuccessorDecomposition`, transported passing strategy, bundled
  `MainFormalSuccessorBoundary`. The branch conversion receives the public
  current-dimension large-`k` hypothesis and weakens it to the predecessor
  side condition `400 * pred.m * pred.d ≤ k`.

For an arbitrary current parameter bundle, the predecessor decomposition itself is
now formalized by `Parameters.successorDecompositionOfNeOne`; what remains
external is producing the successor-boundary data and the later completion /
line-169 residuals. No checked lemma here claims that the former intermediate
range `params.m * params.d ≤ k < 400 * params.m * params.d` is vacuous.

Universe note: the Lean statement uses `[FieldModel.{0} params.q]`, matching the
base-universe field-model assumption of the public Section 6 successor wrapper.
This is a current Lean API limitation, not a paper constraint; once the Section 6
wrapper is universe-polymorphic, this public theorem should be generalized as
well.

Fixes #137, #239, #906.
-/
theorem mainFormal
    (params : Parameters) [FieldModel.{0} params.q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : SameSpaceProjStrat params ι)
    (eps : Error)
    (hd : 0 < params.d)
    (hpass : strategy.PassesLowIndividualDegreeTest eps)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k)
    (hk0 : 0 < k)
    (hbaseBridge : (scalars : MainFormalCascadeScalars params eps k) →
      ∀ (roleResidual : MainFormalRolePackageResidual params strategy eps hpass k),
      MainFormalBaseBridgeHypotheses params strategy eps k hpass scalars roleResidual) :
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
  -- TODO(#422): The induction-side handoffs needed by the final
  -- `mainFormal` assembly are standalone checked declarations:
  -- * base branch: `strategySymmetrization_mainInductionBaseCase`,
  -- * weighted successor boundary fields:
  --   `mainFormalSuccessorAxisWeightedBound_ofPass` and
  --   `mainFormalSuccessorDiagonalWeightedBound_ofPass`,
  -- * successor Section 6 wrapper call:
  --   `mainFormalSuccessorMainInductionPublicWrapper`, and
  -- * vacuous branch: `mainFormal_trivial_witness`.
  --
  -- The remaining paper-faithful target is now narrowed past the Step 5
  -- Schwartz--Zippel handoff, the line-116 triangle step, the duplicated
  -- pre-projective consistency field inside the projectivization handoff, the
  -- unused Section 6 consistency field inside the unsymmetrization package, the
  -- line-171--173 data-processing step for the `ζ₁` links, and the final `ζ₄`
  -- point-triangle assembly to the paper-shaped Step 6 witness residual
  -- `MainFormalCascadeRolePackageResidualStep6WitnessResidual`.  The scalar
  -- cascade side conditions are discharged below: if `mainFormalError ≥ 1`, the
  -- theorem is vacuous; otherwise the pass condition gives `0 ≤ ε`, while
  -- `mainFormalError < 1` rules out `ε > 1` and `d > q`.
  --
  -- The match-mass monotonicity structure
  -- `MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation`, the
  -- lift theorem `of_submeasurement_match_mass_and_completion`, and the
  -- line-130 completion wrapper
  -- `nonempty_ofRoleResidualAndLine130InputsAndCompletingToMeasurementInputs`
  -- are now available.  The self-improvement assumptions are packaged as
  -- `SelfImprovement.SelfImprovementBridgeInputs`.  The remaining `mainFormal` hole
  -- still needs:
  --
  -- 1. **Section 6 role residual** via base/successor branch:
  --    - `MainFormalRolePackageBranchResidual` constructed from either
  --      `base` (if `params.m = 1`) or `successor` (otherwise),
  --    - `MainFormalSuccessorRecursiveSlices` (recursive induction witnesses,
  --      currently external),
  --    - `MainFormalSuccessorSelfImprovementProducer` (per-slice self-improvement
  --      package producer, connecting `SelfImprovement.selfImprovement`
  --      to `MainInductionStep.SelfImprovementPackage`).
  --
  -- 2. **Line-130 orthonormalization inputs**:
  --    - `MainFormalPostRolePackageLine130OrthonormalizationInput`:
  --      spectral-truncation and locality-preserving repair witnesses
  --      for both unsymmetrized POVMs.
  --
  -- 3. **Completion closeness** for the two POVMs, derived through
  --    `completingToMeasurement`.  Needs `BipartiteSSCRel` for the
  --    unsymmetrized POVMs (external).
  --
  -- 4. **Match-mass preservation** values (type
  --    `MakingMeasurementsProjective.OrthonormalizationMatchMassPreservation`)
  --    for both sides.  With these, `of_submeasurement_match_mass_and_completion`
  --    produces the `ProjectivizationMatchMassMonotonicity` needed by
  --    `leftConsistency` / `rightConsistency` for the exact paper `ζ₁` links.
  --
  -- The full downstream cascade from the role package through the projective
  -- targets is already checked; once the residual above is supplied, the
  -- remaining proof is trivial.  Item 4 replaces the older generic `triangleSub`
  -- route whose loss was `ζ₁ + sqrt ζ₂` rather than the printed `ζ₁`.

  by_cases herr : 1 ≤ mainFormalError params k eps
  · exact mainFormal_trivial_witness params strategy eps k herr
  · have hepsNN : 0 ≤ eps := SameSpaceProjStrat.eps_nonneg_of_passes hpass
    let scalars : MainFormalCascadeScalars params eps k :=
      MainFormalCascadeScalars.ofNontrivialMainFormal hepsNN hk0 herr
    have hstep6WitnessResidual :
        Nonempty (MainFormalCascadeRolePackageResidualStep6WitnessResidual
          (params := params) (strategy := strategy) (eps := eps)
          (hpass := hpass) (k := k) (scalars := scalars)) := by
      by_cases hm1 : params.m = 1
      · -- Base case (m = 1): role residual from checked handoff,
        -- bridge from the external `hbaseBridge` hypothesis.
        rcases MainFormalRolePackageResidual.ofBaseCase params strategy eps k hpass hm1 with
          ⟨roleResidual⟩
        exact baseStep6WitnessResidual herr roleResidual
          (baseStep6Hypotheses_ofBaseBridge (hbaseBridge scalars roleResidual))
      · -- Successor case (m > 1): needs recursive slices and self-improvement.
        -- TODO(#931, #834, #422): construct `MainFormalSuccessorRecursiveSlices`
        -- and `MainFormalSuccessorSelfImprovementProducer`.
        sorry
    rcases hstep6WitnessResidual with ⟨step6WitnessResidual⟩
    let rolePackage := step6WitnessResidual.roleResidual.rolePackage scalars
    have hpre : ConsRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedLeftPOVM rolePackage.roleMeasurement).toSubMeas)
        (constSubMeasFamily
          (unsymmetrizedRightPOVM rolePackage.roleMeasurement).toSubMeas)
        scalars.zeta1 := by
      simpa [rolePackage] using step6WitnessResidual.roleResidual.line130Consistency scalars
    let rolePackageResidualLeftCompletionLine169Residual :
        MainFormalCascadeRolePackageResidualLeftCompletionLine169Residual
          (params := params) (strategy := strategy) (eps := eps)
          (hpass := hpass) (k := k) (scalars := scalars) :=
      step6WitnessResidual.toLeftCompletionLine169Residual herr
    have hpreForResidual : ConsRel strategy.state (uniformDistribution Unit)
        (constSubMeasFamily
          (unsymmetrizedLeftPOVM
            (rolePackageResidualLeftCompletionLine169Residual.roleResidual.rolePackage
              scalars).roleMeasurement).toSubMeas)
        (constSubMeasFamily
          (unsymmetrizedRightPOVM
            (rolePackageResidualLeftCompletionLine169Residual.roleResidual.rolePackage
              scalars).roleMeasurement).toSubMeas)
        scalars.zeta1 := by
      simpa [rolePackage, rolePackageResidualLeftCompletionLine169Residual,
        MainFormalCascadeRolePackageResidualStep6WitnessResidual.toLeftCompletionLine169Residual]
        using hpre
    have rolePackageResidualCompletionLine169Residual :
        MainFormalCascadeRolePackageResidualCompletionLine169Residual
          (params := params) (strategy := strategy) (eps := eps)
          (hpass := hpass) (k := k) (scalars := scalars) :=
      rolePackageResidualLeftCompletionLine169Residual
        |>.toRolePackageResidualCompletionLine169Residual hpreForResidual
    have rolePackagedCompletionLine169Residual :
        MainFormalCascadeRolePackagedCompletionLine169Residual params strategy eps k scalars :=
      rolePackageResidualCompletionLine169Residual.toRolePackagedCompletionLine169Residual
    have completionLine169Residual :
        MainFormalCascadeProjectiveCompletionLine169Residual params strategy eps k scalars :=
      rolePackagedCompletionLine169Residual.toCompletionLine169Residual
    have projectiveTargets :
        MainFormalCascadeProjectiveStageTargets params strategy eps k scalars :=
      completionLine169Residual.toProjectiveStageTargets hpass
    exact MainFormalNativeTargets.toMainFormal
      (projectiveTargets.toTransportTargets.toCascadeTargets.toNativeTargets)

end Test

end MIPStarRE.LDT
