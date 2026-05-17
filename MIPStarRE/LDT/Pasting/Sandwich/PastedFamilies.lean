import MIPStarRE.LDT.Basic.SubMeasurementFamilies
import MIPStarRE.LDT.CommutativityPoints.Approximation
import MIPStarRE.LDT.Pasting.Sandwich.GHatSandwich
import MIPStarRE.LDT.Preliminaries.Defs
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

/-- The interpolated operator `H^{x_1,\dots,x_k}_h` restricted to tuples that are
globally consistent with a single polynomial.

The paper's definition (`references/ldt-paper/ld-pasting.tex` lines 474–495) sums
only tuples `(g_1,…,g_k)` in `Global_τ(x)` — those consistent with a single
polynomial `h` — and then interpolates. The `|τ| ≥ d+1` eligibility filter is
applied by `interpolationEligibleSandwichFamily`; this definition additionally
restricts to globally consistent tuples via `IsGloballyConsistent`.
Consequently, `pastedInterpolationFamily` is supported only on tuples satisfying
both restrictions, and any fallback or default value in
`interpolateCompletedSlices` is irrelevant off that restricted support. -/
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
    (uniformDistribution (PointTuple params k))
    (interpolationEligibleSandwichFamily params family k)
    (uniformDistribution_weight_sum_le_one (PointTuple params k))

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

/-- Degree-zero candidate pasted submeasurement obtained by averaging the slice
family and viewing each slice polynomial as a polynomial in one more variable.

Paper origin: `references/ldt-paper/ld-pasting.tex:12-55`.  This is a
Lean-only construction for the `d = 0` branch of `thm:ld-pasting`, where the
ordinary interpolation construction is not available because `d + 1 = 1`
collapses the distinct-height argument.  It introduces no additional
hypothesis. -/
noncomputable def averagedSliceAppendedSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) : SubMeas (Polynomial params.next) ι :=
  postprocess family.averagedSubMeas
    (fun g => Polynomial.appendAtHeight params g zeroCoord)

/-- Evaluating the averaged appended-slice submeasurement at a next-level point
is the same as evaluating the averaged slice family at the truncated point.

This is the first formal step in the degree-zero branch of `thm:ld-pasting`;
the remaining work is the consistency rectangle that compares this averaged
slice construction with the point measurement. -/
theorem evaluateAt_averagedSliceAppendedSubMeas
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (u : Point params.next) :
    evaluateAt params.next u (averagedSliceAppendedSubMeas params family) =
      evaluateAt params (truncatePoint params u) family.averagedSubMeas := by
  have hpoint :
      appendPoint params (truncatePoint params u) (pointHeight params u) = u :=
    (CommutativityPoints.pointNextEquiv params).left_inv u
  rw [← hpoint]
  simp [averagedSliceAppendedSubMeas,
    evaluateAt_postprocess_appendAtHeight_appendPoint params
      family.averagedSubMeas zeroCoord (truncatePoint params u) (pointHeight params u)]

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

/-- In degree zero, the lifted vertical-line answer family is independent of
the height coordinate once the old point coordinates are fixed.

Lean-only helper for the degree-zero branch of `thm:ld-pasting`; it formalizes
the fact that a vertical line answer of degree zero is constant in the line
parameter.  The source context is `references/ldt-paper/ld-pasting.tex:12-55`. -/
theorem liftedVerticalLineAnswerFamily_eq_of_same_truncate_degree_zero
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (hd : params.d = 0)
    {u v : Point params.next} (hbase : truncatePoint params u = truncatePoint params v) :
    liftedVerticalLineAnswerFamily params strategy u =
      liftedVerticalLineAnswerFamily params strategy v := by
  unfold liftedVerticalLineAnswerFamily
  rw [hbase]
  congr
  funext f
  have hd_next : params.next.d = 0 := by
    simpa [Parameters.next] using hd
  exact AxisLinePolynomial.apply_eq_apply_of_degree_zero f hd_next
    (pointHeight params u) (pointHeight params v)

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
              rfl
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
              rfl

/-- Explicit value extracted from the `i`-th genuine slice outcome at the test point.

The paper's one-point sandwich comparison only sums over tuples with
`g_i ≠ ⊥`; the `none` mass is therefore removed before postprocessing. -/
noncomputable def ldSandwichLineOnePointLeftFamily (params : Parameters) [FieldModel params.q]
    (_strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k i : ℕ) : IdxSubMeas (SandwichedLineQuestion params k) (Option (Fq params)) ι :=
  fun q =>
    postprocess
      (restrictSubMeas (gHatSandwichFamily params family k q.2)
        (fun gs => if h : i < k then (gs ⟨i, h⟩).isSome = true else False))
      (fun gs => if h : i < k then Option.map (fun g => g q.1) (gs ⟨i, h⟩) else none)

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

When this is used in `fromHToG`, the suffix length is `tailLen = k - ℓ`, and
the expectation is the paper's independent uniform average over the remaining
slice points `x_{≥ℓ}`. -/
noncomputable def averagedSandwichByTypeSubMeas (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (tailLen : ℕ) (τtail : GHatType tailLen) :
    SubMeas Unit ι :=
  open Classical in
    averageIdxSubMeas
      (uniformDistribution (PointTuple params tailLen))
      (fun xs =>
        postprocess
          (restrictSubMeas
            (gHatSandwichFamily params family tailLen xs)
            (fun gs => gs ∈ outcomesByType τtail))
          (fun _ => ()))
      (uniformDistribution_weight_sum_le_one (PointTuple params tailLen))

/-- The stage-`ℓ` suffix family from the proof of `lem:from-H-to-G`, for a fixed
remaining tail type `τ_{≥ℓ}`.

This is the operator-valued quantity displayed termwise in
`references/ldt-paper/ld-pasting.tex`, equation
`eq:i-think-this-is-what-i'm-supposed-to-prove-2` (lines 1386–1391), and in the
parallel blueprint discussion in `blueprint/src/chapter/ch09_pasting.tex`.
The parameter `prefixLen` is the Lean 0-based stage index. In the ambient
`k`-step recurrence where this family is used, the remaining tail length is
`tailLen = k - prefixLen`, so Lean stage `prefixLen` corresponds to the paper's
stage `prefixLen + 1`.

Concretely, this packages
$$
\mathbb E_{x_{\ge \ell}} \sum_{g_{\ge \ell} \in \mathsf{Outcomes}_{\tau_{\ge \ell}}}
  \widehat H^{x_{\ge \ell}}_{g_{\ge \ell}} \otimes S_{\tau_{\ge \ell}}.
$$ -/
noncomputable def fromHToGTailStageFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (prefixLen : ℕ)
    {tailLen : ℕ} (τtail : GHatType tailLen) :
    IdxOpFamily Unit Unit (ι × ι) :=
  fun _ =>
    let base := averagedSandwichByTypeSubMeas params family tailLen τtail
    let weight := fromHToGRecurrenceWeight params family prefixLen τtail
    { outcome := fun _ =>
        leftTensor (ι₂ := ι) base.total * rightTensor (ι₁ := ι) weight
      total := leftTensor (ι₂ := ι) base.total * rightTensor (ι₁ := ι) weight }

end MIPStarRE.LDT.Pasting
