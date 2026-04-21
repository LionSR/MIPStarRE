import Mathlib.Algebra.MvPolynomial.Polynomial
import MIPStarRE.LDT.Pasting.GHatFacts

/-!
# Section 12 pasting: sandwich-chain bridge lemmas

Bridge lemmas for the sandwich chain in the pasting argument.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Bridge lemmas for the sandwich chain

These lemmas capture the infrastructure needed for the `lem:commute-g-half-sandwich`
through `cor:h-a-consistency` chain in `ld-pasting.tex` §9.3.

The n-step SDDOpRel composition lemma (`sddOpRel_chain`) now lives in
`Preliminaries.Theorems` alongside `sddOpRel_triangle`, since it is a
general-purpose result used by multiple chapters. -/

/-- Bridge: the staged move-commute-move chain for `commuteGHalfSandwich`.

Constructs the sequence of `3k` intermediate bipartite operator families
that arise from repeatedly moving `Ĝ₁` through the product
`Ĝ₁ · Ĝ₂ · ⋯ · Ĝₖ` using self-consistency (move to right tensor,
error `2ζ`) and pairwise commutation (swap past neighbor, error `ν₃`),
then composes them via `sddOpRel_chain`.

Paper reference: `lem:commute-g-half-sandwich` computation in
`ld-pasting.tex` lines 881–914. -/
private lemma commuteGHalfSandwich_core
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error) (k : ℕ) (hk : 2 ≤ k)
    (hzeta_le : zeta ≤ 1)
    (hsc : SDDRel ψbi
      (uniformDistribution (SliceQuestion params))
      (gHatSelfConsistencyLeftFamily params family)
      (gHatSelfConsistencyRightFamily params family)
      (gHatSelfConsistencyError zeta))
    (hcom : SDDOpRel ψbi
      (uniformDistribution (SlicePairQuestion params))
      (gHatPairProductLeft params family)
      (gHatPairProductRight params family)
      (gHatCommutationError params gamma zeta)) :
    SDDOpRel ψbi
      (uniformDistribution (PointTuple params k))
      (gHatHalfSandwichLeft params family k)
      (gHatHalfSandwichRight params family k)
      (commuteGHalfSandwichError params gamma zeta k) := by
  sorry

/-- `lem:commute-g-half-sandwich`. -/
lemma commuteGHalfSandwich
    (params : Parameters)
    [FieldModel params.q]
    (ψbi : QuantumState (ι × ι))
    (family : IdxPolyFamily params ι)
    (gamma zeta : Error)
    (k : ℕ)
    (hk : 2 ≤ k)
    (hzeta_le : zeta ≤ 1)
    (hfacts : GHatFactsStatement params ψbi family gamma zeta) :
    CommuteGHalfSandwichStatement params ψbi family gamma zeta k := by
  exact ⟨commuteGHalfSandwich_core params ψbi family gamma zeta k hk
    hzeta_le hfacts.completedSelfConsistency hfacts.completedCommutation⟩

/-- Bridge: Cauchy-Schwarz sandwich elimination for one-point consistency.

Given the half-sandwich commutation bound from `commuteGHalfSandwich`, performs
the Cauchy-Schwarz + measurement-completeness argument that converts the
sandwiched operator distance into a one-point consistency bound.

Paper reference: `lem:ld-sandwich-line-one-point` proof in
`ld-pasting.tex` lines 931–1036.

Steps:
1. Simplify by summing out indices `> i` using measurement completeness
2. Apply Cauchy-Schwarz with `commuteGHalfSandwich` to move `Ĝ₁` left
3. Apply Cauchy-Schwarz again to move `Ĝ₁` right
4. Eliminate `Ĝ_{<i}` product using measurement completeness
5. Reduce to the single-slice bound `eq:ld-gbcon` -/
private lemma ldSandwichLineOnePoint_core
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (hcomm : ∀ j : ℕ, 2 ≤ j →
      CommuteGHalfSandwichStatement params strategy.state family
        gamma zeta j)
    (k i : ℕ) (hi : i < k) :
    ConsRel strategy.state
      (uniformDistribution (SandwichedLineQuestion params k))
      (ldSandwichLineOnePointLeftFamily params strategy family k i)
      (ldSandwichLineOnePointRightFamily params strategy family k i)
      (ldSandwichLineOnePointError params eps delta gamma zeta k) := by
  /-
  The remaining external blocker here is still `ldGbcon`: after the two
  Cauchy–Schwarz sandwich-elimination steps and the completeness simplifications,
  the proof reduces to the single-slice consistency comparison `eq:ld-gbcon`.
  That theorem is currently blocked on the missing `ConsRel` swap API tracked in
  #411 / #550.
  -/
  sorry

/-- `lem:ld-sandwich-line-one-point`. -/
lemma ldSandwichLineOnePoint
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (hfacts : GHatFactsStatement params strategy.state family gamma zeta)
    (k i : ℕ)
    (hi : i < k) :
    LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i := by
  have hcomm :
      ∀ j : ℕ, 2 ≤ j →
        CommuteGHalfSandwichStatement params strategy.state family
          gamma zeta j := by
    intro j hj
    exact commuteGHalfSandwich params strategy.state family gamma zeta
      j hj hzeta_le hfacts
  exact ⟨ldSandwichLineOnePoint_core params strategy eps delta gamma zeta
    hgood hgamma_le hzeta_le hdq_le
    family hcons hself hbound hcomm k i hi⟩

/-- Bridge: aggregate one-point consistency bounds over all slice indices,
plus the distinct-tuple approximation error.

Paper reference: `lem:h-b-consistency` proof in `ld-pasting.tex`
lines 1050–1091.

Steps:
1. Expand using degree constraints to find eligible index `i`
2. Switch from independent to distinct samples (`prop:ld-dnoteq`, cost `k²/q`)
3. Union bound over `k` indices, each contributing `ν₅`
4. Total: `k·ν₅ + k²/q ≤ 44k²m(...)` -/
private lemma hBConsistency_core
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    ConsRel strategy.state
      (uniformDistribution (VerticalLineQuestion params))
      (hRestrictionToVerticalLine params
        (constructedPastedSubMeas params family k))
      (verticalLineMeasurementFamily params strategy)
      (hBConsistencyError params eps delta gamma zeta k) := by
  sorry

/-- `lem:h-b-consistency`. -/
lemma hBConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    HBConsistencyStatement params strategy family
        eps delta gamma zeta k := by
  exact ⟨hBConsistency_core params strategy eps delta gamma zeta
    hgood family hcons hself hbound k hline⟩

private lemma restrictToAxisParallelLine_apply
    (params : Parameters) [FieldModel params.q]
    (g : Polynomial params) (ℓ : AxisParallelLine params) (t : Fq params) :
    Polynomial.restrictToAxisParallelLine params g ℓ t = g (ℓ.pointAt t) := by
  unfold Polynomial.restrictToAxisParallelLine Polynomial.toFun AxisLinePolynomial.toFun
    evalLinePolynomialModel evalPolynomialModel
  change encodeScalar (Polynomial.eval (decodeScalar t)
    (MvPolynomial.eval₂ Polynomial.C (Polynomial.axisCoordinatePolynomial params ℓ) g.poly)) = _
  rw [MvPolynomial.polynomial_eval_eval₂]
  change encodeScalar
    (MvPolynomial.eval₂ ((Polynomial.evalRingHom (decodeScalar t)).comp Polynomial.C)
      (fun s => Polynomial.eval (decodeScalar t) (Polynomial.axisCoordinatePolynomial params ℓ s)) g.poly) =
    encodeScalar (MvPolynomial.eval₂ (RingHom.id _) (decodePoint (ℓ.pointAt t)) g.poly)
  have hcoeff : ((Polynomial.evalRingHom (decodeScalar t)).comp Polynomial.C) = RingHom.id _ := by
    ext a
    simp
  rw [hcoeff]
  have hvars :
      (fun s => Polynomial.eval (decodeScalar t) (Polynomial.axisCoordinatePolynomial params ℓ s)) =
        decodePoint (ℓ.pointAt t) := by
    funext i
    by_cases h : i = ℓ.direction
    · subst h
      simp [Polynomial.axisCoordinatePolynomial, AxisParallelLine.pointAt, decodePoint, addCoord]
    · simp [Polynomial.axisCoordinatePolynomial, AxisParallelLine.pointAt, decodePoint, h]
  rw [hvars]

private lemma verticalLine_pointAt_appendPoint
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

private noncomputable def rawVerticalLineAnswerFamily
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  fun u =>
    postprocess
      ((strategy.axisParallelMeasurement
        { base := u, direction := lastCoord params }).toSubMeas)
      (· zeroCoord)

private lemma rawVerticalLineConsistency
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
                (fun u => postprocess ((strategy.axisParallelMeasurement
                  { base := u, direction := i }).toSubMeas) (· zeroCoord)))
          = avgOver (uniformDistribution (Fin params.next.m))
              (fun i => avgOver (uniformDistribution (Point params.next)) (fun u =>
                qBipartiteConsDefect strategy.state
                  ((strategy.pointMeasurement u).toSubMeas)
                  (postprocess ((strategy.axisParallelMeasurement
                    { base := u, direction := i }).toSubMeas) (· zeroCoord)))) := by
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
  have hsum_le : ∑ i : Fin params.next.m, err i ≤ ((params.next.m : ℕ) : Error) * eps := by
    have hcard_ne : (((params.next.m : ℕ) : Error)) ≠ 0 := by
      have hpos : 0 < (((params.next.m : ℕ) : Error)) := by
        simpa [Parameters.next] using (show 0 < (((params.m + 1 : ℕ) : Error)) by positivity)
      exact ne_of_gt hpos
    have havg :
        ((((params.next.m : ℕ) : Error))⁻¹ * ∑ i : Fin params.next.m, err i) =
          avgOver (uniformDistribution (Fin params.next.m)) err := by
      simp [avgOver, uniformDistribution, Finset.mul_sum]
    calc
      ∑ i : Fin params.next.m, err i
        = ((params.next.m : ℕ) : Error) * ((((params.next.m : ℕ) : Error))⁻¹ * ∑ i : Fin params.next.m, err i) := by
            field_simp [hcard_ne]
      _ = ((params.next.m : ℕ) : Error) * avgOver (uniformDistribution (Fin params.next.m)) err := by
            rw [havg]
      _ ≤ ((params.next.m : ℕ) : Error) * eps := by
            gcongr
  have hlast_le : err (lastCoord params) ≤ ((params.next.m : ℕ) : Error) * eps := by
    calc
      err (lastCoord params) ≤ ∑ i : Fin params.next.m, err i := by
        exact Finset.single_le_sum (fun i _ => herr_nonneg i) (Finset.mem_univ _)
      _ ≤ ((params.next.m : ℕ) : Error) * eps := hsum_le
  constructor
  simpa [err, rawVerticalLineAnswerFamily] using hlast_le

private lemma consRel_uniform_prod_fst
    {α β Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    [Fintype β] [DecidableEq β] [Nonempty β]
    [Fintype Outcome]
    [Fintype ιA] [DecidableEq ιA]
    [Fintype ιB] [DecidableEq ιB]
    (ψ : QuantumState (ιA × ιB))
    (A : IdxSubMeas α Outcome ιA)
    (B : IdxSubMeas α Outcome ιB)
    (δ : Error)
    (hAB : ConsRel ψ (uniformDistribution α) A B δ) :
    ConsRel ψ (uniformDistribution (α × β))
      (fun ab => A ab.1)
      (fun ab => B ab.1)
      δ := by
  rcases hAB with ⟨hAB⟩
  constructor
  unfold bipartiteConsError at *
  calc
    avgOver (uniformDistribution (α × β))
        (fun ab => qBipartiteConsDefect ψ (A ab.1) (B ab.1))
      = avgOver (uniformDistribution α)
          (fun a => qBipartiteConsDefect ψ (A a) (B a)) := by
            exact avgOver_uniform_fst (α := α) (β := β)
              (fun a => qBipartiteConsDefect ψ (A a) (B a))
    _ ≤ δ := hAB

private lemma postprocess_comp
    {α β γ : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) (f : α → β) (g : β → γ) :
    postprocess (postprocess A f) g = postprocess A (fun a => g (f a)) := by
  classical
  refine SubMeas.ext ?_ rfl
  intro c
  calc
    (postprocess (postprocess A f) g).outcome c
      = ∑ b : β,
          if g b = c then
            ∑ a : α, if f a = b then A.outcome a else 0
          else 0 := by
            simp [postprocess, Finset.sum_filter]
    _ = ∑ b : β, ∑ a : α,
          if g b = c ∧ f a = b then A.outcome a else (0 : MIPStarRE.Quantum.Op ι) := by
            refine Finset.sum_congr rfl ?_
            intro b _
            by_cases hgc : g b = c
            · simp [hgc]
            · simp [hgc]
    _ = ∑ a : α, ∑ b : β,
          if g b = c ∧ f a = b then A.outcome a else (0 : MIPStarRE.Quantum.Op ι) := by
            rw [Finset.sum_comm]
    _ = ∑ a : α, if g (f a) = c then A.outcome a else (0 : MIPStarRE.Quantum.Op ι) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            by_cases hgc : g (f a) = c
            · rw [Finset.sum_eq_single (f a)]
              · simp [hgc]
              · intro b _ hb
                by_cases hfa : f a = b
                · exact (hb hfa.symm).elim
                · simp [hfa]
              · simp
            · have hzero :
                  (∑ b : β, if g b = c ∧ f a = b then A.outcome a else (0 : MIPStarRE.Quantum.Op ι)) = 0 := by
                refine Finset.sum_eq_zero ?_
                intro b _
                by_cases hfa : f a = b
                · subst b
                  simp [hgc]
                · simp [hfa]
              simp [hgc, hzero]
    _ = (postprocess A (fun a => g (f a))).outcome c := by
            simp [postprocess, Finset.sum_filter]

private noncomputable def liftedVerticalLineAnswerFamily
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) :
    IdxSubMeas (Point params.next) (Fq params) ι :=
  fun u =>
    postprocess (verticalLineMeasurementFamily params strategy (truncatePoint params u))
      (fun f => f (pointHeight params u))

private lemma liftedVerticalLineConsistency
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (H : SubMeas (Polynomial params.next) ι)
    (η : Error)
    (hHB : ConsRel strategy.state
      (uniformDistribution (Point params))
      (hRestrictionToVerticalLine params H)
      (verticalLineMeasurementFamily params strategy)
      η) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (polynomialEvaluationFamily params.next H)
      (liftedVerticalLineAnswerFamily params strategy)
      η := by
  have hprod :=
    consRel_uniform_prod_fst
      (α := Point params)
      (β := Fq params)
      (Outcome := AxisLinePolynomial params.next)
      (ιA := ι)
      (ιB := ι)
      strategy.state
      (hRestrictionToVerticalLine params H)
      (verticalLineMeasurementFamily params strategy)
      η
      hHB
  have hpost :=
    Preliminaries.consRelDataProcessing_questionDependent
      strategy.state
      (uniformDistribution (Point params × Fq params))
      (fun ux => hRestrictionToVerticalLine params H ux.1)
      (fun ux => verticalLineMeasurementFamily params strategy ux.1)
      η
      (fun ux linePoly => linePoly ux.2)
      hprod
  have hleft :
      ∀ ux : Point params × Fq params,
        postprocess (hRestrictionToVerticalLine params H ux.1) (fun linePoly => linePoly ux.2) =
          polynomialEvaluationFamily params.next H (appendPoint params ux.1 ux.2) := by
    intro ux
    rcases ux with ⟨u, x⟩
    rw [hRestrictionToVerticalLine, postprocess_comp]
    have hpt' :
        ({ base := appendPoint params (u, x).1 zeroCoord,
           direction := lastCoord params } : AxisParallelLine params.next).pointAt (u, x).2 =
          appendPoint params (u, x).1 (u, x).2 := by
      simpa using verticalLine_pointAt_appendPoint params u x
    have hfun :
        (fun a : Polynomial params.next =>
          (Polynomial.restrictToAxisParallelLine params.next a
              { base := appendPoint params (u, x).1 zeroCoord,
                direction := lastCoord params }).toFun (u, x).2) =
          (fun a : Polynomial params.next => a (appendPoint params (u, x).1 (u, x).2)) := by
      funext a
      simpa [hpt'] using
        restrictToAxisParallelLine_apply (params := params.next) a
          { base := appendPoint params (u, x).1 zeroCoord,
            direction := lastCoord params } (u, x).2
    change postprocess H
      (fun a : Polynomial params.next =>
        (Polynomial.restrictToAxisParallelLine params.next a
            { base := appendPoint params (u, x).1 zeroCoord,
              direction := lastCoord params }).toFun (u, x).2) = _
    rw [hfun]
    rfl
  have hright :
      ∀ ux : Point params × Fq params,
        postprocess (verticalLineMeasurementFamily params strategy ux.1) (fun linePoly => linePoly ux.2) =
          liftedVerticalLineAnswerFamily params strategy (appendPoint params ux.1 ux.2) := by
    intro ux
    rcases ux with ⟨u, x⟩
    simp [liftedVerticalLineAnswerFamily, truncatePoint_appendPoint, pointHeight_appendPoint]
  have hprod_next :
      ConsRel strategy.state
        (uniformDistribution (Point params × Fq params))
        (fun ux => polynomialEvaluationFamily params.next H (appendPoint params ux.1 ux.2))
        (fun ux => liftedVerticalLineAnswerFamily params strategy (appendPoint params ux.1 ux.2))
        η := by
    simpa [hleft, hright] using hpost
  exact
    (Preliminaries.consRel_uniform_equiv
      (e := CommutativityPoints.pointNextEquiv params)
      (ψ := strategy.state)
      (A := polynomialEvaluationFamily params.next H)
      (B := liftedVerticalLineAnswerFamily params strategy)
      (δ := η)).mpr (by simpa [CommutativityPoints.pointNextEquiv] using hprod_next)

/-- Bridge: convert vertical-line consistency to point consistency.

Given `hHB : HBConsistencyStatement` (the output of `hBConsistency`), derives
point consistency by restricting the vertical-line bound to individual points.

Paper reference: `cor:h-a-consistency` proof in `ld-pasting.tex`
lines 1098–1117.

Steps:
1. Restrict `hHB.lineConsistency` to a single point on the line
2. Apply `triangleSub` with the `A-B` consistency bound from `hgood`
3. Error bound: `ν₆ + √(8mε + 4δ) ≤ 47k²m(...) ≤ 100k²m(...)` -/
private lemma hAConsistency_submeas_core
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (hcomplete : family.Complete strategy.state kappa)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k)
    (hHB : HBConsistencyStatement params strategy family
        eps delta gamma zeta k) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) := by
  /-
  The non-blocked bookkeeping is now in place:
  * `liftedVerticalLineConsistency` transports `hHB.lineConsistency` from
    `Point params` to full points `Point params.next`.
  * `rawVerticalLineConsistency` extracts the last-coordinate axis-parallel
    branch from `hgood.axisParallelTest`.

  What remains is the final left/right orientation swap. The available chain
  yields the reversed statement
    `ConsRel strategy.state ... (polynomialEvaluationFamily ...)`
    `  (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) ...`
  by combining those helpers with the right-register triangle argument from
  `Preliminaries.Triangles.Consistency`. Closing the theorem *as stated* then
  needs a public `ConsRel` swap lemma (the `PermInvState.consRel_swap`-style API
  tracked in #411). Without that stronger symmetry interface, the final step is
  still blocked paper-faithfully.
  -/
  sorry

/-- `cor:h-a-consistency`.

This is the point-consistency part of the pasted-submeasurement chain.  The
completed-measurement consistency is deliberately separated as
`hAConsistency_completed`, since the paper proves it only after
`cor:ld-pasting-N-completeness`. -/
theorem hAConsistency_submeas
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcomplete : family.Complete strategy.state kappa)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ)
    (hk : 400 * params.m * params.d ≤ k) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta) := by
  have hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i := by
    have hfacts : GHatFactsStatement params strategy.state family gamma zeta := by
      have hzeta_nonneg : 0 ≤ zeta :=
        le_trans (sddError_nonneg _ _ _ _)
          hself.sliceSelfConsistency.squaredDistanceBound
      have hgamma_nonneg : 0 ≤ gamma := by
        have : 0 ≤ strategy.diagonalFailureProbability := by
          unfold SymStrat.diagonalFailureProbability
          exact mul_nonneg (by positivity)
            (Finset.sum_nonneg fun j _ =>
              bipartiteConsError_nonneg strategy.state _ _ _)
        exact le_trans this hgood.diagonalLineTest
      let complete_self :=
        gCompleteSelfConsistency params strategy.state family zeta hself
      let bot_self :=
        gBotSelfConsistency params strategy.state family zeta complete_self
      let com :=
        Commutativity.comMain params strategy eps delta gamma zeta
          strategy.isNormalized hgood family
          (fun x => (family.meas x).toSubMeas) (fun _ => rfl)
          hcons hself hbound
      let withComplete :=
        commutingWithGComplete params strategy family
          (fun x => (family.meas x).toSubMeas) gamma zeta
          hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le
          com complete_self
      let withIncomplete :=
        commutingWithGIncomplete params strategy.state family gamma zeta
          withComplete
      exact gHatFacts params strategy.state family gamma zeta
        hgamma_nonneg hgamma_le hzeta_nonneg hzeta_le hdq_le
        complete_self bot_self withComplete withIncomplete
    intro i hi
    exact ldSandwichLineOnePoint params strategy eps delta gamma zeta
      hgood hgamma_le hzeta_le hdq_le
      family hcons hself hbound hfacts k i hi
  have hHB := hBConsistency params strategy eps delta gamma zeta
    hgood family hcons hself hbound k hline
  exact hAConsistency_submeas_core params strategy family
    eps delta gamma kappa zeta hgood hgamma_le hzeta_le hdq_le
    hcomplete k hk hHB

/-- Completed-measurement version of `cor:h-a-consistency`.

This wrapper is intentionally downstream of `cor:ld-pasting-N-completeness`:
it may use the submeasurement consistency together with the completeness bound
for the constructed pasted submeasurement to control the added completion mass. -/
theorem hAConsistency_completed
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma kappa zeta : Error)
    (family : IdxPolyFamily params ι)
    (k : ℕ)
    (hsubmeas :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        (polynomialEvaluationFamily params.next
          (constructedPastedSubMeas params family k))
        (MainInductionStep.ldPastingInInductionNu params k
          eps delta gamma zeta))
    (hcomplete :
      CompletenessAtLeast strategy.state
        (constructedPastedSubMeas params family k).liftLeft
        (ldPastingCompletenessLowerBound params kappa
          (MainInductionStep.ldPastingInInductionNu params k
            eps delta gamma zeta) k)) :
    ConsRel strategy.state (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (polynomialEvaluationFamily params.next
        (constructedPastedMeasurement params family k).toSubMeas)
      (MainInductionStep.ldPastingInInductionError params k
        eps delta gamma kappa zeta) := by
  let H := constructedPastedSubMeas params family k
  let ν := MainInductionStep.ldPastingInInductionNu params k eps delta gamma zeta
  let completedEval : IdxSubMeas (Point params.next) (Fq params) ι :=
    fun u => (Preliminaries.completeAtOutcome (evaluateAt params.next u H)
      ((pastedFallbackOutcome params) u)).toSubMeas
  have hcompletedEval :
      completedEval =
        polynomialEvaluationFamily params.next
          (constructedPastedMeasurement params family k).toSubMeas := by
    funext u
    simpa [completedEval, H, constructedPastedMeasurement, pastedFallbackOutcome] using
      (Preliminaries.evaluateAt_completeAtOutcome params.next H
        (pastedFallbackOutcome params) u).symm
  have hresidualMass :
      ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total)) ≤
        kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) := by
    have hmass :
        ev strategy.state (leftTensor (ι₂ := ι) H.total) ≥
          ldPastingCompletenessLowerBound params kappa ν k := by
      simpa [H, subMeasMass, SubMeas.liftLeft] using hcomplete.lowerBound
    calc
      ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total))
        = ev strategy.state (leftTensor (ι₂ := ι) (1 - H.total)) := by
            simpa using (strategy.permInvState.swap_ev (1 - H.total)).symm
      _ = 1 - ev strategy.state (leftTensor (ι₂ := ι) H.total) := by
            have hleftSub :
                leftTensor (ι₂ := ι) (1 - H.total) =
                  1 - leftTensor (ι₂ := ι) H.total := by
              ext i j
              rcases i with ⟨i₁, i₂⟩
              rcases j with ⟨j₁, j₂⟩
              by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
                simp [leftTensor, h₁, h₂, sub_eq_add_neg]
            rw [hleftSub, ev_sub]
            simp [ev_one_of_isNormalized strategy.state strategy.isNormalized]
      _ ≤ 1 - ldPastingCompletenessLowerBound params kappa ν k := by
            linarith
      _ = kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))) := by
            simp [ldPastingCompletenessLowerBound, ν]
            ring
  have hcompleted :
      ConsRel strategy.state (uniformDistribution (Point params.next))
        (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
        completedEval
        (ν + (kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
          Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ))))))) := by
    constructor
    calc
      bipartiteConsError strategy.state (uniformDistribution (Point params.next))
          (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
          completedEval
        ≤ avgOver (uniformDistribution (Point params.next)) (fun u =>
            qBipartiteConsDefect strategy.state
                ((strategy.pointMeasurement u).toSubMeas)
                (evaluateAt params.next u H) +
              ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total))) := by
                unfold bipartiteConsError completedEval
                apply avgOver_mono
                intro u
                simpa [H, evaluateAt, postprocess_total, ν] using
                  Preliminaries.qBipartiteConsDefect_completeAtOutcome_right_le
                    strategy.state (strategy.pointMeasurement u).toMeasurement
                    (evaluateAt params.next u H)
                    ((pastedFallbackOutcome params) u)
      _ = bipartiteConsError strategy.state (uniformDistribution (Point params.next))
            (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
            (polynomialEvaluationFamily params.next H) +
          avgOver (uniformDistribution (Point params.next))
            (fun _ => ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total))) := by
              unfold bipartiteConsError
              rw [avgOver_add]
              simp [IdxProjMeas.toIdxSubMeas, polynomialEvaluationFamily]
      _ ≤ ν + avgOver (uniformDistribution (Point params.next))
            (fun _ => ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total))) := by
              exact add_le_add hsubmeas.offDiagonalBound le_rfl
      _ = ν + ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total)) := by
            simpa using avgOver_uniform_const (α := Point params.next)
              (ev strategy.state (rightTensor (ι₁ := ι) (1 - H.total)))
      _ ≤ ν + (kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
            Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) := by
              gcongr
  have hsigma :
      ν + (kappa * (1 + 1 / (100 * (params.m : Error))) + ν +
        Real.exp (-((k : Error) / (80000 * ((params.m : Error) ^ (2 : ℕ)))))) =
        MainInductionStep.ldPastingInInductionError params k
          eps delta gamma kappa zeta := by
    simp [MainInductionStep.ldPastingInInductionError, ν]
    ring
  exact ⟨by
    simpa [hcompletedEval] using le_trans hcompleted.offDiagonalBound hsigma.le⟩

/-- `lem:over-all-outcomes`. -/
lemma overAllOutcomes
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (eps delta gamma zeta : Error)
    (hgood : strategy.IsGood eps delta gamma)
    (hgamma_le : gamma ≤ 1)
    (hzeta_le : zeta ≤ 1)
    (hdq_le : params.d ≤ params.q)
    (family : IdxPolyFamily params ι)
    (hcons : family.ConsistentWithPoints strategy zeta)
    (hself : family.StronglySelfConsistent strategy.state zeta)
    (hbound : IdxPolyFamily.SliceBoundednessInput strategy family zeta)
    (k : ℕ) :
    OverAllOutcomesStatement params strategy family eps delta gamma zeta k := by
  constructor -- OverAllOutcomesStatement
  constructor -- SDDRel
  /- Paper: `lem:over-all-outcomes` (ld-pasting.tex §9.4, lines 1140–1289).
  Expand pasted-measurement total mass over all outcome types τ with |τ| ≥ d+1.
  Steps: (1) expand over distinct k-tuples via `distinctTupleDistribution`,
  (2) decompose by outcome type with |τ| ≥ d+1,
  (3) remove global-polynomial restriction (Schwartz-Zippel: error md/q),
  (4) swap distinct → uniform sampling (`prop:ld-dnoteq`: error 2k²/q),
  (5) bound sandwich errors (`lem:ld-sandwich-line-one-point`: k × ν₅).

  Current blockers after the split audit:
  * the interpolation-to-global-polynomial correctness step still needs the
    missing `Defs/Interpolation` comparison lemmas in the exact shapes consumed
    here;
  * the final sandwich aggregation still depends on `ldSandwichLineOnePoint`,
    whose remaining blocker is `ldGbcon` / the #411 swap API.
  -/
  sorry


end MIPStarRE.LDT.Pasting
