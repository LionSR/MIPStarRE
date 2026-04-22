import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.Pasting.Sandwich.GHatSandwich
import MIPStarRE.LDT.Test.StrategyFailures

/-!
# Section 12 — Sandwich constructions: pasted families

Pasted interpolation families, recurrence weights, and final operator families.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Source-style recurrence weight `S_{τtail}` from `lem:from-H-to-G`.

The parameter `prefixLen` is the number of type bits already converted into the
Bernoulli polynomial.  This is exactly `truncatedTypeSums` specialized to the
averaged complete operator `G = E_x ∑_g G^x_g`. -/
noncomputable def fromHToGRecurrenceWeight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (prefixLen : ℕ) {tailLen : ℕ}
    (τtail : GHatType tailLen) : MIPStarRE.Quantum.Op ι :=
  truncatedTypeSums family.averagedSubMeas.total params.d prefixLen τtail

/-- The suffix-specialized recurrence weight used by the `fromHToG` families.

Semantics/indexing fix: the previous grouped Bernoulli encoding
`∑_r C(ℓ-1, r) G^r (I-G)^(ℓ-1-r)` interpreted `ℓ` as the paper's 1-indexed
prefix length, whereas the callers (`FromHToGStatement.recurrenceStep` uses
`∀ ℓ < k`) and the rest of `Pasting/` treat `ℓ` as 0-indexed — the off-by-one
produced a binomial of degree `ℓ - 1` instead of the paper's
`\binom{\ell}{r}` (see `references/ldt-paper/ld-pasting.tex` eq. (S-def)).
The new definition uses `truncatedTypeSums` at `prefixLen = ℓ`, which sums
over `GHatType ℓ` and matches both the 0-indexed convention and the proved
recurrence in `truncatedTypeSumRecurrence`.  The index `ℓ` is zero-based:
the suffix is `τ_{≥ℓ}` and the prefix has length `ℓ`. -/
noncomputable def suffixBernoulliWeightOperator (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) (τ : GHatType k) : MIPStarRE.Quantum.Op ι :=
  fromHToGRecurrenceWeight params family ℓ (gHatTypeSuffix ℓ τ)

/-- Definitional bridge from the suffix API to the proved truncated-sum API.

Not tagged `@[simp]`: eager unfolding would eliminate every mention of the
named `suffixBernoulliWeightOperator` abstraction and leak the
`gHatTypeSuffix` wrapper into downstream goals.  Call sites that need the
expansion should use `unfold` or `show` explicitly. -/
lemma suffixBernoulliWeightOperator_eq_truncatedTypeSums
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k ℓ : ℕ) (τ : GHatType k) :
    suffixBernoulliWeightOperator params family k ℓ τ =
      truncatedTypeSums family.averagedSubMeas.total params.d ℓ (gHatTypeSuffix ℓ τ) := by
  rfl

/-- The interpolated operator `H^{x_1,\dots,x_k}_h` restricted to tuples that are
globally consistent with a single polynomial.

The paper's definition (`references/ldt-paper/ld-pasting.tex` lines 474–495) sums
only tuples `(g_1,…,g_k)` in `Global_τ(x)` — those consistent with a single
polynomial `h` — and then interpolates.  The `|τ| ≥ d+1` eligibility filter is
applied by `interpolationEligibleSandwichFamily`; this definition additionally
restricts to globally consistent tuples via `IsGloballyConsistent`. -/
noncomputable def pastedInterpolationFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (Polynomial params.next) ι :=
  fun xs =>
    postprocess
      (restrictSubMeas
        (interpolationEligibleSandwichFamily params family k xs)
        (IsGloballyConsistent params xs))
      (interpolateCompletedSlices params k xs)

/-- The averaged sandwiched family restricted to outcome tuples of type `τ`
with `|τ| ≥ d+1`, as in `lem:over-all-outcomes`. -/
noncomputable def averagedEligibleSandwichSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    SubMeas (GHatTupleOutcome params k) ι :=
  averageIdxSubMeas
    (distinctTupleDistribution params k)
    (interpolationEligibleSandwichFamily params family k)
    (distinctTupleDistribution_weight_sum_le_one params k)

/-- The specific pasted submeasurement constructed from the sandwich/interpolation scheme. -/
noncomputable def constructedPastedSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) : SubMeas (Polynomial params.next) ι :=
  averageIdxSubMeas
    (distinctTupleDistribution params k)
    (pastedInterpolationFamily params family k)
    (distinctTupleDistribution_weight_sum_le_one params k)

/-- The distinguished fallback polynomial `h₀` that receives the completion mass. -/
noncomputable def pastedFallbackOutcome (params : Parameters) [FieldModel params.q] :
    Polynomial params.next :=
  fallbackInterpolatedPolynomial params

/-- The specific pasted measurement obtained by completing the constructed pasted submeasurement.

The paper adds all missing mass `I - H_total` to a single distinguished polynomial
outcome `h₀` (the fallback interpolant).  So the outcome operator for `h₀` becomes
`H_{h₀} + (I - H_total)` while all other outcomes keep their original operators, and
the total is genuinely the identity `I`. -/
noncomputable def constructedPastedMeasurement (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) : Measurement (Polynomial params.next) ι :=
  Preliminaries.completeAtOutcome
    (constructedPastedSubMeas params family k)
    (pastedFallbackOutcome params)

/-- Placeholder family for the vertical axis-parallel line measurement `B^u_f`. -/
noncomputable def verticalLineMeasurementFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxSubMeas (VerticalLineQuestion params) (AxisLinePolynomial params.next) ι :=
  fun u =>
    let ℓ : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := lastCoord params }
    (strategy.axisParallelMeasurement ℓ).toSubMeas

/-- The canonical vertical line through `u : Point params` reaches `appendPoint u x`
at parameter `x`. -/
theorem verticalLine_pointAt_appendPoint
    (params : Parameters) [FieldModel params.q]
    (u : Point params) (x : Fq params) :
    ({ base := appendPoint params u zeroCoord,
       direction := lastCoord params } : AxisParallelLine params.next).pointAt x =
      appendPoint params u x := by
  ext i
  by_cases hlast : i = lastCoord params
  · subst i
    have hzero : addCoord zeroCoord x = x := by
      unfold addCoord zeroCoord
      rw [decode_encodeScalar]
      simp
    simpa [AxisParallelLine.pointAt, appendPoint, lastCoord] using congrArg Fin.val hzero
  · have him : i.1 < params.m := by
      have hi_lt : i.1 < params.m + 1 := by simpa [Parameters.next] using i.2
      by_cases hlt : i.1 < params.m
      · exact hlt
      · have hi_eq : i.1 = params.m := by omega
        have hi_last : i = lastCoord params := by
          apply Fin.ext
          simp [lastCoord, hi_eq]
        exact (hlast hi_last).elim
    simp [AxisParallelLine.pointAt, appendPoint, him, hlast]

/-- The last-coordinate axis-parallel branch of the strategy, read at the base
point of the sampled vertical line.

This is the ambient-space comparison family used to extract a single
axis-parallel branch from `hgood.axisParallelTest`. -/
noncomputable def rawVerticalLineMeasurementFamily
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxMeas (Point params.next) (Fq params) ι :=
  fun u =>
    (ProjMeas.postprocess
      (strategy.axisParallelMeasurement { base := u, direction := lastCoord params })
      (· zeroCoord)).toMeasurement

/-- The submeasurement family underlying `rawVerticalLineMeasurementFamily`. -/
noncomputable def rawVerticalLineAnswerFamily
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  IdxMeas.toIdxSubMeas (rawVerticalLineMeasurementFamily params strategy)

/-- Extract the last-coordinate axis-parallel branch from
`hgood.axisParallelTest`, losing a factor of `m + 1` when passing from the
uniform coordinate average to a fixed coordinate. -/
theorem rawVerticalLineConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma : Error)
    (hgood : strategy.IsGood eps delta gamma) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (rawVerticalLineAnswerFamily params strategy)
      (((params.next.m : ℕ) : Error) * eps) := by
  let err : Fin params.next.m → Error := fun i =>
    bipartiteConsError strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (fun u =>
        postprocess ((strategy.axisParallelMeasurement { base := u, direction := i }).toSubMeas)
          (· zeroCoord))
  have haxis_avg : avgOver (uniformDistribution (Fin params.next.m)) err ≤ eps := by
    have h_eq :
        avgOver (uniformDistribution (Fin params.next.m)) err =
          strategy.axisParallelFailureProbability := by
      unfold SymStrat.axisParallelFailureProbability err
      calc
        avgOver (uniformDistribution (Fin params.next.m))
            (fun i =>
              bipartiteConsError strategy.state
                (uniformDistribution (Point params.next))
                (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
                (fun u =>
                  postprocess ((strategy.axisParallelMeasurement
                    { base := u, direction := i }).toSubMeas) (· zeroCoord)))
          = avgOver (uniformDistribution (Fin params.next.m))
              (fun i =>
                avgOver (uniformDistribution (Point params.next)) fun u =>
                  qBipartiteConsDefect strategy.state
                    ((strategy.pointMeasurement u).toSubMeas)
                    (postprocess ((strategy.axisParallelMeasurement
                      { base := u, direction := i }).toSubMeas) (· zeroCoord))) := by
                rfl
        _ = avgOver (uniformDistribution (Fin params.next.m × Point params.next))
              (fun iu =>
                qBipartiteConsDefect strategy.state
                  ((strategy.pointMeasurement iu.2).toSubMeas)
                  (postprocess ((strategy.axisParallelMeasurement
                    { base := iu.2, direction := iu.1 }).toSubMeas) (· zeroCoord))) := by
                symm
                simpa using (avgOver_uniform_prod (f := fun i u =>
                  qBipartiteConsDefect strategy.state
                    ((strategy.pointMeasurement u).toSubMeas)
                    (postprocess ((strategy.axisParallelMeasurement
                      { base := u, direction := i }).toSubMeas) (· zeroCoord))))
        _ = avgOver (uniformDistribution (Point params.next × Fin params.next.m))
              (fun ui =>
                qBipartiteConsDefect strategy.state
                  ((strategy.pointMeasurement ui.1).toSubMeas)
                  (postprocess ((strategy.axisParallelMeasurement
                    { base := ui.1, direction := ui.2 }).toSubMeas) (· zeroCoord))) := by
                simpa using (avgOver_uniform_equiv
                  (e := Equiv.prodComm (Fin params.next.m) (Point params.next))
                  (f := fun iu : Fin params.next.m × Point params.next =>
                    qBipartiteConsDefect strategy.state
                      ((strategy.pointMeasurement iu.2).toSubMeas)
                      (postprocess ((strategy.axisParallelMeasurement
                        { base := iu.2, direction := iu.1 }).toSubMeas) (· zeroCoord))))
        _ = strategy.axisParallelFailureProbability := by
              rfl
    rw [h_eq]
    exact hgood.axisParallelTest
  have herr_nonneg : ∀ i : Fin params.next.m, 0 ≤ err i := by
    intro i
    exact bipartiteConsError_nonneg strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (fun u =>
        postprocess ((strategy.axisParallelMeasurement { base := u, direction := i }).toSubMeas)
          (· zeroCoord))
  let mNext : Error := ((params.next.m : ℕ) : Error)
  have hsum_le : ∑ i : Fin params.next.m, err i ≤ mNext * eps := by
    have hcard_pos : 0 < mNext := by
      have hpos : (0 : Error) < ((params.next.m : ℕ) : Error) := by
        exact_mod_cast params.next.hm
      simpa [mNext] using hpos
    have hcard_ne : mNext ≠ 0 := ne_of_gt hcard_pos
    calc
      ∑ i : Fin params.next.m, err i
          = mNext * avgOver (uniformDistribution (Fin params.next.m)) err := by
              simp [avgOver, uniformDistribution, Finset.mul_sum, mNext, hcard_ne]
      _ ≤ mNext * eps := by
            gcongr
  have hlast_le : err (lastCoord params) ≤ mNext * eps := by
    calc
      err (lastCoord params) ≤ ∑ i : Fin params.next.m, err i := by
        exact Finset.single_le_sum (fun i _ => herr_nonneg i) (Finset.mem_univ _)
      _ ≤ ((params.next.m : ℕ) : Error) * eps := hsum_le
  constructor
  simpa [err, rawVerticalLineAnswerFamily, rawVerticalLineMeasurementFamily,
    IdxMeas.toIdxSubMeas] using hlast_le

/-- Pull back the vertical-line answer family along `truncatePoint`, then read
its line polynomial at the lifted point's final coordinate. -/
noncomputable def liftedVerticalLineAnswerFamily
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  fun u =>
    postprocess
      (verticalLineMeasurementFamily params strategy (truncatePoint params u))
      (fun f => f (pointHeight params u))

/-- Reparametrizing the fixed last-coordinate branch to the canonical vertical
base point matches `liftedVerticalLineAnswerFamily`. -/
theorem rawVerticalLineAnswerFamily_eq_lifted
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    rawVerticalLineAnswerFamily params strategy =
      liftedVerticalLineAnswerFamily params strategy := by
  funext u
  let verticalLine : AxisParallelLine params.next :=
    { base := appendPoint params (truncatePoint params u) zeroCoord
      direction := lastCoord params }
  have happend : appendPoint params (truncatePoint params u) (pointHeight params u) = u := by
    exact (CommutativityPoints.pointNextEquiv params).left_inv u
  have hpt : verticalLine.pointAt (pointHeight params u) = u := by
    calc
      verticalLine.pointAt (pointHeight params u)
          = appendPoint params (truncatePoint params u) (pointHeight params u) := by
              simpa [verticalLine] using
                verticalLine_pointAt_appendPoint params
                  (truncatePoint params u) (pointHeight params u)
      _ = u := happend
  have hrebase :
      AxisParallelLine.rebaseAt verticalLine (pointHeight params u) =
        { base := u, direction := lastCoord params } := by
    simpa [AxisParallelLine.rebaseAt, verticalLine] using
      congrArg
        (fun base : Point params.next =>
          ({ base := base, direction := lastCoord params } : AxisParallelLine params.next))
        hpt
  apply SubMeas.ext
  · intro a
    calc
      (rawVerticalLineAnswerFamily params strategy u).outcome a
          = (postprocess
              ((strategy.axisParallelMeasurement
                { base := u, direction := lastCoord params }).toSubMeas)
              (· zeroCoord)).outcome a := by
              rfl
      _ = (postprocess
            ((strategy.axisParallelMeasurement
              (AxisParallelLine.rebaseAt verticalLine (pointHeight params u))).toSubMeas)
            (· zeroCoord)).outcome a := by
              rw [hrebase]
      _ = (postprocess ((strategy.axisParallelMeasurement verticalLine).toSubMeas)
            (fun f => f (pointHeight params u))).outcome a := by
              exact
                (AxisParallelCovariantMeasurement.reparamInvariant
                  strategy.axisParallelMeasurement) _ _ _
      _ = (liftedVerticalLineAnswerFamily params strategy u).outcome a := by
              simp [liftedVerticalLineAnswerFamily, verticalLineMeasurementFamily, verticalLine]
  · calc
      (rawVerticalLineAnswerFamily params strategy u).total
          = (strategy.axisParallelMeasurement
              { base := u, direction := lastCoord params }).total := by
              rfl
      _ = 1 :=
            (strategy.axisParallelMeasurement
              { base := u, direction := lastCoord params }).total_eq_one
      _ = (strategy.axisParallelMeasurement verticalLine).total := by
            symm
            exact (strategy.axisParallelMeasurement verticalLine).total_eq_one
      _ = (postprocess ((strategy.axisParallelMeasurement verticalLine).toSubMeas)
            (fun f => f (pointHeight params u))).total := by
              rfl
      _ = (liftedVerticalLineAnswerFamily params strategy u).total := by
              simp [liftedVerticalLineAnswerFamily, verticalLineMeasurementFamily, verticalLine]

/-- Explicit value extracted from the `i`-th completed slice outcome at the test point. -/
noncomputable def ldSandwichLineOnePointLeftFamily (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
  fun q =>
    postprocess (gHatSandwichFamily params family k q.2) (fun gs =>
      if h : i < k then
        Option.map (fun g => g q.1) (gs ⟨i, h⟩)
      else
        none)

/-- Explicit value extracted from the vertical line measurement `B^u` at the slice height `x_i`. -/
noncomputable def ldSandwichLineOnePointRightFamily (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (_family : IdxPolyFamily params ι)
    (k i : ℕ) : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
  fun q =>
    postprocess (verticalLineMeasurementFamily params strategy q.1) (fun f =>
      if h : i < k then
        some (f (q.2 ⟨i, h⟩))
      else
        none)

/-- Restrict a global polynomial-valued submeasurement to the vertical line through `u`. -/
noncomputable def hRestrictionToVerticalLine (params : Parameters) [FieldModel params.q]
    (H : SubMeas (Polynomial params.next) ι) :
    IdxSubMeas (VerticalLineQuestion params) (AxisLinePolynomial params.next) ι :=
  fun u =>
    let verticalLine : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := ⟨params.m, Nat.lt_succ_self params.m⟩ }
    postprocess H (fun h => Polynomial.restrictToAxisParallelLine params.next h verticalLine)

/-- Collapse a submeasurement to its `Unit`-valued total operator. -/
noncomputable def pastedMeasurementTotal
    {α : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (H : SubMeas α ι) : IdxSubMeas Unit Unit ι :=
  constSubMeasFamily (postprocess H (fun _ => ()))

/-- The total operator of the specifically constructed pasted submeasurement. -/
noncomputable def constructedPastedMeasurementTotal (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas Unit Unit ι :=
  pastedMeasurementTotal (constructedPastedSubMeas params family k)

/-- The expansion over all outcome types `τ`, written as the
total mass of the averaged sandwich family restricted to `|τ| ≥ d+1`. -/
noncomputable def allOutcomesExpansionFamily (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas Unit Unit ι :=
  pastedMeasurementTotal (averagedEligibleSandwichSubMeas params family k)

/-- The Bernoulli-tail polynomial in the averaged complete operator `G = E_x \sum_g G^x_g`. -/
noncomputable def bernoulliTailFromFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas Unit Unit ι :=
  constSubMeasFamily <|
    let Y := bernoulliTailOperator k params.d ((IdxPolyFamily.averagedSubMeas family).total)
    { outcome := fun _ => Y
      total := Y
      outcome_pos := by
        intro _
        let G := (IdxPolyFamily.averagedSubMeas family).total
        have hG : 0 ≤ G := (IdxPolyFamily.averagedSubMeas family).total_nonneg
        have hGle : G ≤ 1 := (IdxPolyFamily.averagedSubMeas family).total_le_one
        simpa [G] using bernoulliTailOperator_nonneg k params.d G hG hGle
      sum_eq_total := by
        simp
      total_le_one := by
        let G := (IdxPolyFamily.averagedSubMeas family).total
        have hG : 0 ≤ G := (IdxPolyFamily.averagedSubMeas family).total_nonneg
        have hGle : G ≤ 1 := (IdxPolyFamily.averagedSubMeas family).total_le_one
        simpa [Y, G] using bernoulliTailOperator_le_one k params.d G hG hGle }

/-- Average the sandwiched completed-slice family over tuples whose completed/
incomplete pattern is exactly `τtail`.

This is the paper's operator
$$
\mathbb E_{x_{\ge \ell}} \sum_{g_{\ge \ell} \in \mathsf{Outcomes}_{\tau_{\ge \ell}}}
  \widehat H^{x_{\ge \ell}}_{g_{\ge \ell}},
$$
written in the existing `SubMeas Unit` API so that its total operator is the
relevant suffix-stage matrix.  Unlike the old `fromHToG` recurrence families,
this keeps the `\widehat H^{x_{\ge \ell}}_{g_{\ge \ell}}` suffix visible instead
of collapsing immediately to the full `k`-step total mass.

When this is used in `fromHToG`, the suffix length is `tailLen = k - ℓ`.  The
paper phrases the expectation as the suffix marginal of
`distinctTupleDistribution params k`; here it is realized directly as
`distinctTupleDistribution params tailLen`.  This is the same distribution by
symmetry of uniform injective tuples, but the explicit marginalization lemma has
not yet been named because the current PR only repairs the family shape. -/
noncomputable def averagedSandwichByTypeSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (tailLen : ℕ) (τtail : GHatType tailLen) :
    SubMeas Unit ι :=
  open Classical in
    averageIdxSubMeas
      (distinctTupleDistribution params tailLen)
      (fun xs =>
        postprocess
          (restrictSubMeas
            (gHatSandwichFamily params family tailLen xs)
            (fun gs => gs ∈ outcomesByType τtail))
          (fun _ => ()))
      (distinctTupleDistribution_weight_sum_le_one params tailLen)

/-- The stage-`ℓ` suffix family from the proof of `lem:from-H-to-G`, for a fixed
full type `τ ∈ {0,1}^k`.

With zero-based indexing, this packages
$$
\mathbb E_{x_{\ge \ell}} \sum_{g_{\ge \ell} \in \mathsf{Outcomes}_{\tau_{\ge \ell}}}
  \widehat H^{x_{\ge \ell}}_{g_{\ge \ell}} \otimes S_{\tau_{\ge \ell}}.
$$
The dependence on `ℓ` now genuinely changes the `\widehat H` suffix rather than
reusing the fully averaged `k`-step operator at every stage. -/
noncomputable def fromHToGIntermediateFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k ℓ : ℕ)
    (τ : GHatType k) :
    IdxOpFamily Unit Unit ι :=
  fun _ =>
    let base := averagedSandwichByTypeSubMeas params family (k - ℓ) (gHatTypeSuffix ℓ τ)
    let weight := suffixBernoulliWeightOperator params family k ℓ τ
    { outcome := fun _ => base.total * weight
      total := base.total * weight }

/-- One recurrence-step left-hand family from the proof of `lem:from-H-to-G`,
parameterised by the full type `τ ∈ {0,1}^k`.

This is the stage-`ℓ` suffix family `\widehat H^{x_{\ge \ell}}_{g_{\ge \ell}} \otimes
S_{\tau_{\ge \ell}}`.  The `strategy` argument is threaded only so the public
family API matches `FromHToGStatement`; the underlying operator depends only on
`family`. -/
noncomputable def fromHToGRecurrenceLeftFamily (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ)
    (τ : GHatType k) :
    IdxOpFamily Unit Unit ι :=
  fromHToGIntermediateFamily params family k ℓ τ

/-- One recurrence-step right-hand family from the proof of `lem:from-H-to-G`,
parameterised by the full type `τ ∈ {0,1}^k`.

This is the next suffix stage `\widehat H^{x_{>\ell}}_{g_{>\ell}} \otimes
S_{\tau_{>\ell}}`, i.e. definitionally the `(ℓ + 1)`-st left family. -/
noncomputable def fromHToGRecurrenceRightFamily (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ)
    (τ : GHatType k) :
    IdxOpFamily Unit Unit ι :=
  fromHToGIntermediateFamily params family k (ℓ + 1) τ

/-- The right-hand recurrence family at step `ℓ` is definitionally the left-hand
family at step `ℓ + 1`, matching the telescoping chain in
`ld-pasting.tex` lines 1354–1376.

The intended use is `ℓ < k`; the theorem is stated for all `ℓ : ℕ` because the
same `rfl` proof continues to hold outside that range under the `Nat`-subtraction
convention built into `gHatTypeSuffix`. -/
theorem fromHToGRecurrenceRightFamily_eq_left_succ (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) (k ℓ : ℕ)
    (τ : GHatType k) :
    fromHToGRecurrenceRightFamily params strategy family k ℓ τ =
      fromHToGRecurrenceLeftFamily params strategy family k (ℓ + 1) τ :=
  rfl

end MIPStarRE.LDT.Pasting
