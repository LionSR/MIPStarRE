import MIPStarRE.LDT.MainInductionStep
import MIPStarRE.LDT.Test.ErrorCascade
import MIPStarRE.LDT.Test.StrategyFailures
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

In the `mainFormal` assembly this wrapper handles every vacuous envelope branch:
in particular, the non-paper scalar regimes `ε > 1` or `d > q`, and the future
small-`k` branch `params.m * params.d ≤ k < 400 * params.m * params.d` once the
Section 6 / Pasting-side wrapper is threaded into the proof. The complementary
non-vacuous branch `mainFormalError params k eps < 1` supplies the scalar
hypotheses needed by the Step 8 cascade.

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

/-- The public restricted-probabilities theorem supplies the successor-case
weighted axis-parallel input for the role-register symmetrization used by
`mainFormal`. -/
theorem mainFormalSuccessorAxisWeightedBound_ofPass
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    MainFormalSuccessorAxisWeightedBound params strategy eps :=
  MainInductionStep.weighted_axisParallel_bound params
    strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
    (ProjStrat.strategySymmetrization_isGood_three_mul
      (strategy := strategy) (eps := eps) hpass)

/-- The public restricted-probabilities theorem supplies the successor-case
weighted diagonal-line input for the role-register symmetrization used by
`mainFormal`. -/
theorem mainFormalSuccessorDiagonalWeightedBound_ofPass
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params.next ι) (eps : Error)
    (hpass : strategy.PassesLowIndividualDegreeTest eps) :
    MainFormalSuccessorDiagonalWeightedBound params strategy eps :=
  MainInductionStep.weighted_diagonal_bound params
    strategy.strategySymmetrization (3 * eps) (3 * eps) (3 * eps)
    (ProjStrat.strategySymmetrization_isGood_three_mul
      (strategy := strategy) (eps := eps) hpass)

/-- Build the successor boundary once the two still-external slice-recursion and
restricted-strategy self-improvement inputs are supplied. The weighted
restricted-probability fields are now discharged from `hpass` by the public
Section 6 weighted-bound lemmas. -/
def mainFormalSuccessorBoundary_ofRecursiveSelfImprovement
    (params : Parameters) [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (strategy : ProjStrat params.next ι) (eps : Error)
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
    (strategy : ProjStrat params.next ι) (eps : Error)
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
    (ProjStrat.strategySymmetrization_isGood_three_mul
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

/-- The paper's `ζ₂ = 200ζ₁^(1/4) + 40ζ₁^(1/8)`. -/
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
    (strategy : ProjStrat params ι) (eps : Error) (k : ℕ) where
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
    (strategy : ProjStrat params ι) (eps : Error) (k : ℕ)
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

namespace MainFormalCascadeTransportTargets

/-- Add the already-discharged scalar package back to the transport-only targets. -/
noncomputable def toCascadeTargets {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : ProjStrat params ι} {eps : Error} {k : ℕ}
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
    (strategy : ProjStrat params ι) (eps : Error) (k : ℕ) where
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

/-- Final packaging step for `thm:main-formal` once the paper-native targets have
been constructed. This only weakens the native `\zeta_4` and `\zeta_3/2` bounds to
`mainFormalError` using `ConsRel.mono`; all substantive transport work is in the
construction of `MainFormalNativeTargets`. -/
theorem toMainFormal {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : ProjStrat params ι} {eps : Error} {k : ℕ}
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

This is still only packaging: the assumptions are exactly the paper-native
`eq:one-goal`, `eq:another-goal`, and `eq:third-goal` statements at the cascade
errors from `inductive_step.tex` lines 159--185. -/
noncomputable def toNativeTargets {params : Parameters} [FieldModel params.q]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {strategy : ProjStrat params ι} {eps : Error} {k : ℕ}
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

/--
`thm:main-formal` from `test_definition.tex`.

The bipartite tensor placement follows the paper:
- **1a**: `A^A_u ⊗ I ≈_ν I ⊗ G^B_{[g(u)=a]}` — G_B on **right**
- **1b**: `I ⊗ A^B_u ≈_ν G^A_{[g(u)=a]} ⊗ I` — G_A on **left**, A^B on **right**
- **2**: `G^A_g ⊗ I ≈_ν I ⊗ G^B_g` — G_B on **right**

The `k`-bound boundary matches the paper (`references/ldt-paper/test_definition.tex:183`):
the public hypothesis is `params.m * params.d ≤ k`, not the stronger
`400 * params.m * params.d ≤ k` used by the Section 6 / Pasting-side wrappers.
After first separating off the vacuous envelope branch, the planned assembly
case-splits on `k`:

* Regime `400 * params.m * params.d ≤ k`: invoke the public Section 6
  wrapper `MIPStarRE.LDT.MainInductionStep.mainInductionPublicWrapper`,
  using the base-case handoff
  `strategySymmetrization_mainInductionBaseCase` and the successor-boundary
  package `MainFormalSuccessorBoundary`, to discharge the three transport
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
  -- The remaining paper-faithful target is now narrowed to the non-vacuous
  -- transport-only package `MainFormalCascadeTransportTargets`. The scalar
  -- cascade side conditions are discharged below: if `mainFormalError ≥ 1`, the
  -- theorem is vacuous; otherwise the pass condition gives `0 ≤ ε`, while
  -- `mainFormalError < 1` rules out `ε > 1` and `d > q`. Producing the transport
  -- package still depends on the active upstream residuals: the role
  -- unsymmetrization bridge (#424), the full-slice transport chain (#601), the
  -- remaining `fromHToG` pasting bridge (#707), the reverse `overAllOutcomes`
  -- aggregation (#672), and the ProcessedG scalar follow-ups #714, #715, #732,
  -- and #759.
  by_cases herr : 1 ≤ mainFormalError params k eps
  · exact mainFormal_trivial_witness params strategy eps k herr
  · have hepsNN : 0 ≤ eps := ProjStrat.eps_nonneg_of_passes hpass
    let scalars : MainFormalCascadeScalars params eps k :=
      MainFormalCascadeScalars.ofNontrivialMainFormal hepsNN hk0 herr
    have transportTargets :
        MainFormalCascadeTransportTargets params strategy eps k scalars := by
      sorry
    exact MainFormalNativeTargets.toMainFormal
      (transportTargets.toCascadeTargets.toNativeTargets)

end Test

end MIPStarRE.LDT
