import MIPStarRE.LDT.Pasting.BridgeLemmas.Common

/-!
# Section 12 pasting: line interpolation bridge helpers

Interpolation-support, bad-line, bad-mass, and distribution-comparison helpers used by the line-
consistency chain.

## References

- `references/ldt-paper/ld-pasting.tex`
- `blueprint/src/chapter/ch09_pasting.tex`
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma axisLinePolynomial_ne_gives_support_eval_ne
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (σ : Finset (Fin k))
    (hσcard : σ.card = params.d + 1)
    {f g : AxisLinePolynomial params.next}
    (hne : f ≠ g) :
    ∃ i : Fin k, i ∈ σ ∧ f (xs i) ≠ g (xs i) := by
  classical
  by_contra hcontra
  push_neg at hcontra
  let s : Finset (Scalar params.next) := σ.image (fun i => decodeScalar (xs i))
  have hs_card : s.card = params.d + 1 := by
    rw [Finset.card_image_of_injective]
    · exact hσcard
    · exact fun i j hij => hxs (by simpa using congrArg encodeScalar hij)
  have hs_eval : ∀ y ∈ s, _root_.Polynomial.eval y f.poly = _root_.Polynomial.eval y g.poly := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨i, hiσ, rfl⟩
    have hfg : f (xs i) = g (xs i) := hcontra i hiσ
    exact by
      simpa [AxisLinePolynomial.toFun, evalLinePolynomialModel] using congrArg decodeScalar hfg
  have hdeg_f : f.poly.natDegree ≤ params.d := f.degreeBounded
  have hdeg_g : g.poly.natDegree ≤ params.d := g.degreeBounded
  have hcard : max f.poly.natDegree g.poly.natDegree < s.card := by
    rw [hs_card]
    have hmax_le : max f.poly.natDegree g.poly.natDegree ≤ params.d := by
      exact max_le hdeg_f hdeg_g
    omega
  have hpoly : f.poly = g.poly := by
    exact _root_.Polynomial.eq_of_natDegree_lt_card_of_eval_eq' f.poly g.poly s hs_eval hcard
  apply hne
  cases f
  cases g
  cases hpoly
  rfl

lemma exists_onePoint_family_witness_of_eval_mismatch
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k)
    {f : AxisLinePolynomial params.next}
    (hmismatch :
      ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i)) :
    ∃ i : Fin k,
      Option.map (fun g : Polynomial params => g u) (gs i) ≠ some (f (xs i)) := by
  classical
  rcases hmismatch with ⟨i, hiSome, hiNe⟩
  refine ⟨i, ?_⟩
  cases hgi : gs i with
  | none =>
      simp [Option.isSome, hgi] at hiSome
  | some g =>
      simp [hgi] at hiSome
      simpa [hgi] using hiNe

lemma nonglobal_gives_slice_mismatch_against_interpolant
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k)
    (hNGlobal : ¬ IsGloballyConsistent params xs gs) :
    ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
      Polynomial.restrictAtHeight params
        (interpolateCompletedSlices params k xs gs) (xs i) ≠
      (gs i).get hiSome := by
  classical
  let hStar := interpolateCompletedSlices params k xs gs
  by_contra hcontra
  push_neg at hcontra
  apply hNGlobal
  refine ⟨hStar, ?_⟩
  intro i hiSome
  exact congrArg Polynomial.poly (hcontra i hiSome)

/-- Compatibility alias for the chosen `d+1` interpolation support inside `gHatTupleSupport`. -/
noncomputable def interpolationSupportSubset
    {params : Parameters} [FieldModel params.q]
    {k : ℕ} (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs) : Finset (Fin k) :=
  (interpolationSupportWitness gs hEligible).support

lemma interpolationSupportSubset_subset
    {params : Parameters} [FieldModel params.q]
    {k : ℕ} (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs) :
    interpolationSupportSubset gs hEligible ⊆ gHatTupleSupport gs := by
  simpa [interpolationSupportSubset] using
    (interpolationSupportWitness gs hEligible).subset_support

lemma interpolationSupportSubset_card
    {params : Parameters} [FieldModel params.q]
    {k : ℕ} (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs) :
    (interpolationSupportSubset gs hEligible).card = params.d + 1 := by
  simpa [interpolationSupportSubset] using
    (interpolationSupportWitness gs hEligible).card_eq

lemma restrictToAxisParallelLine_apply
    (params : Parameters) [FieldModel params.q]
    (h : Polynomial params.next)
    (ℓ : AxisParallelLine params.next)
    (t : Fq params.next) :
    (Polynomial.restrictToAxisParallelLine params.next h ℓ) t =
      h (AxisParallelLine.pointAt ℓ t) := by
  have haxis :
      (fun i => _root_.Polynomial.eval (decodeScalar t)
          (Polynomial.axisCoordinatePolynomial params.next ℓ i)) =
        decodePoint (AxisParallelLine.pointAt ℓ t) := by
    funext i
    by_cases hi : i = ℓ.direction
    · subst hi
      simp [AxisParallelLine.pointAt, Polynomial.axisCoordinatePolynomial,
        addCoord, decodePoint, decode_encodeScalar, _root_.Polynomial.eval_add,
        _root_.Polynomial.eval_C, _root_.Polynomial.eval_X]
    · simp [AxisParallelLine.pointAt, Polynomial.axisCoordinatePolynomial,
        hi, decodePoint, _root_.Polynomial.eval_C]
  have hconst :
      (Polynomial.evalRingHom (decodeScalar t)).comp _root_.Polynomial.C = RingHom.id _ := by
    ext a
    simp
  calc
    (Polynomial.restrictToAxisParallelLine params.next h ℓ) t
      = encodeScalar
          (MvPolynomial.eval₂
            ((Polynomial.evalRingHom (decodeScalar t)).comp _root_.Polynomial.C)
            (fun i => _root_.Polynomial.eval (decodeScalar t)
              (Polynomial.axisCoordinatePolynomial params.next ℓ i))
            h.poly) := by
              simp [Polynomial.restrictToAxisParallelLine, AxisLinePolynomial.toFun,
                evalLinePolynomialModel]
              rw [MvPolynomial.polynomial_eval_eval₂]
    _ = encodeScalar
          (MvPolynomial.eval₂ (RingHom.id _)
            (decodePoint (AxisParallelLine.pointAt ℓ t)) h.poly) := by
              rw [hconst]
              simpa using congrArg
                (fun g => encodeScalar (MvPolynomial.eval₂ (RingHom.id _) g h.poly)) haxis
    _ = h (AxisParallelLine.pointAt ℓ t) := by
          rfl

lemma restrictToVerticalLine_eval_eq_restrictAtHeight_eval
    (params : Parameters) [FieldModel params.q]
    (h : Polynomial params.next)
    (u : Point params)
    (x : Fq params) :
    (Polynomial.restrictToAxisParallelLine params.next h
        ({ base := appendPoint params u zeroCoord
         , direction := lastCoord params } : AxisParallelLine params.next)) x =
      (Polynomial.restrictAtHeight params h x) u := by
  let coord := Polynomial.restrictAtHeightCoordinateMap params x
  have hconst :
      (MvPolynomial.eval (decodePoint u)).comp MvPolynomial.C = RingHom.id _ := by
    ext r
    simp
  have hcoord :
      (fun i => MvPolynomial.eval (decodePoint u) (coord i)) =
        decodePoint (appendPoint params u x) := by
    funext i
    by_cases hi : i.1 < params.m
    · simp [coord, Polynomial.restrictAtHeightCoordinateMap, decodePoint, appendPoint, hi]
      rfl
    · simp [coord, Polynomial.restrictAtHeightCoordinateMap, decodePoint, appendPoint, hi]
      rfl
  have hEval := MvPolynomial.eval_eval₂ (x := decodePoint u)
    (f := MvPolynomial.C) (g := coord) (p := h.poly)
  calc
    (Polynomial.restrictToAxisParallelLine params.next h
        ({ base := appendPoint params u zeroCoord
         , direction := lastCoord params } : AxisParallelLine params.next)) x
      = h (appendPoint params u x) := by
          rw [restrictToAxisParallelLine_apply]
          exact congrArg (fun y => h y) (verticalLine_pointAt_appendPoint params u x)
    _ = (Polynomial.restrictAtHeight params h x) u := by
          symm
          calc
            (Polynomial.restrictAtHeight params h x) u
              = encodeScalar
                  (MvPolynomial.eval (decodePoint u)
                    (MvPolynomial.eval₂Hom MvPolynomial.C coord h.poly)) := by
                      rfl
            _ = encodeScalar
                  (MvPolynomial.eval₂
                    ((MvPolynomial.eval (decodePoint u)).comp MvPolynomial.C)
                    (fun i => MvPolynomial.eval (decodePoint u) (coord i)) h.poly) := by
                      simpa using congrArg encodeScalar hEval
            _ = encodeScalar
                  (MvPolynomial.eval₂ (RingHom.id _)
                    (decodePoint (appendPoint params u x)) h.poly) := by
                      rw [hconst]
                      simpa using congrArg
                        (fun g => encodeScalar (MvPolynomial.eval₂ (RingHom.id _) g h.poly)) hcoord
             _ = h (appendPoint params u x) := by
                   rfl

lemma interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get_of_mem
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (σ : Finset (Fin k))
    (hσsubset : σ ⊆ gHatTupleSupport gs)
    (hσcard : σ.card = params.d + 1)
    {i : Fin k} (hi : i ∈ σ) :
    MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
      (interpolateCompletedSlicesFromSupport params xs gs σ hσsubset hσcard).poly =
      ((gs i).get (by simpa [gHatTupleSupport] using hσsubset hi)).poly := by
  let v : Fin k → Scalar params.next := fun j => decodeScalar (xs j)
  have hvinj : Set.InjOn v (↑σ : Set (Fin k)) := by
    intro a ha b hb hab
    apply hxs
    simpa [v] using congrArg encodeScalar hab
  have hcomp :
      ((MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
        MvPolynomial.C) = MvPolynomial.C := by
    ext r
    simp
  have hx :
      MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.X (lastCoord params)) =
        MvPolynomial.C (decodeScalar (xs i)) := by
    simp [Polynomial.restrictAtHeightCoordinateMap, lastCoord]
  unfold interpolateCompletedSlicesFromSupport
  rw [map_sum, Finset.sum_eq_single ⟨i, hi⟩]
  · simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSlicePoly gs i (hσsubset hi)).poly) =
          (extractSlicePoly gs i (hσsubset hi)).poly := by
      rw [MvPolynomial.eval₂Hom_rename, MvPolynomial.eval₂Hom_C_eq_bind₁]
      have hmap :
          Polynomial.restrictAtHeightCoordinateMap params (xs i) ∘ embedCoord params =
            MvPolynomial.X := by
        funext j
        simp [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord]
      rw [hmap, MvPolynomial.bind₁_X_left]
      rfl
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i))) = 1 := by
      calc
        MvPolynomial.eval₂Hom MvPolynomial.C
            (Polynomial.restrictAtHeightCoordinateMap params (xs i))
            (_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
              (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i))
          = _root_.Polynomial.eval₂
              (((MvPolynomial.eval₂Hom MvPolynomial.C
                  (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                MvPolynomial.C))
              (MvPolynomial.eval₂Hom MvPolynomial.C
                (Polynomial.restrictAtHeightCoordinateMap params (xs i))
                (MvPolynomial.X (lastCoord params)))
              (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i) := by
                simpa using (_root_.Polynomial.hom_eval₂
                  (p := Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i)
                  (f := MvPolynomial.C)
                  (g := MvPolynomial.eval₂Hom MvPolynomial.C
                    (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                  (x := MvPolynomial.X (lastCoord params)))
        _ = _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.C (decodeScalar (xs i)))
              (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i) := by
                calc
                  _root_.Polynomial.eval₂
                      ((MvPolynomial.eval₂Hom MvPolynomial.C
                          (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                        MvPolynomial.C)
                      ((MvPolynomial.eval₂Hom MvPolynomial.C
                          (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                        (MvPolynomial.X (lastCoord params)))
                      (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i)
                      = _root_.Polynomial.eval₂
                          ((MvPolynomial.eval₂Hom MvPolynomial.C
                              (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                            MvPolynomial.C)
                          (MvPolynomial.C (decodeScalar (xs i)))
                          (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i) := by
                            simpa using congrArg
                              (fun x =>
                                _root_.Polynomial.eval₂
                                  ((MvPolynomial.eval₂Hom MvPolynomial.C
                                      (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                                    MvPolynomial.C)
                                  x (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i))
                              hx
                  _ = _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.C (decodeScalar (xs i)))
                        (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i) := by
                          simpa [MvPolynomial.eval₂Hom] using congrArg
                            (fun F =>
                              _root_.Polynomial.eval₂ F (MvPolynomial.C (decodeScalar (xs i)))
                                (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i))
                            hcomp
        _ = 1 := by
              rw [_root_.Polynomial.eval₂_at_apply]
              simpa using congrArg
                (fun x : Scalar params => (MvPolynomial.C x : PolynomialModel params))
                (Lagrange.eval_basis_self hvinj hi)
    rw [hLi, hslice]
    simp [extractSlicePoly]
  · intro j hj hji
    have hji' : j.1 ≠ i := by
      intro hEq
      apply hji
      exact Subtype.ext hEq
    simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSlicePoly gs j.1 (hσsubset j.2)).poly) =
          (extractSlicePoly gs j.1 (hσsubset j.2)).poly := by
      rw [MvPolynomial.eval₂Hom_rename, MvPolynomial.eval₂Hom_C_eq_bind₁]
      have hmap :
          Polynomial.restrictAtHeightCoordinateMap params (xs i) ∘ embedCoord params =
            MvPolynomial.X := by
        funext m
        simp [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord]
      rw [hmap, MvPolynomial.bind₁_X_left]
      rfl
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1))) = 0 := by
      calc
        MvPolynomial.eval₂Hom MvPolynomial.C
            (Polynomial.restrictAtHeightCoordinateMap params (xs i))
            (_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
              (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1))
          = _root_.Polynomial.eval₂
              (((MvPolynomial.eval₂Hom MvPolynomial.C
                  (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                MvPolynomial.C))
              (MvPolynomial.eval₂Hom MvPolynomial.C
                (Polynomial.restrictAtHeightCoordinateMap params (xs i))
                (MvPolynomial.X (lastCoord params)))
              (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1) := by
                simpa using (_root_.Polynomial.hom_eval₂
                  (p := Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1)
                  (f := MvPolynomial.C)
                  (g := MvPolynomial.eval₂Hom MvPolynomial.C
                    (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                  (x := MvPolynomial.X (lastCoord params)))
        _ = _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.C (decodeScalar (xs i)))
              (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1) := by
                calc
                  _root_.Polynomial.eval₂
                      ((MvPolynomial.eval₂Hom MvPolynomial.C
                          (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                        MvPolynomial.C)
                      ((MvPolynomial.eval₂Hom MvPolynomial.C
                          (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                        (MvPolynomial.X (lastCoord params)))
                      (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1)
                      = _root_.Polynomial.eval₂
                          ((MvPolynomial.eval₂Hom MvPolynomial.C
                              (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                            MvPolynomial.C)
                          (MvPolynomial.C (decodeScalar (xs i)))
                          (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1) := by
                            simpa using congrArg
                              (fun x =>
                                _root_.Polynomial.eval₂
                                  ((MvPolynomial.eval₂Hom MvPolynomial.C
                                      (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                                    MvPolynomial.C)
                                  x (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1))
                              hx
                  _ = _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.C (decodeScalar (xs i)))
                        (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1) := by
                          simpa [MvPolynomial.eval₂Hom] using congrArg
                            (fun F =>
                              _root_.Polynomial.eval₂ F (MvPolynomial.C (decodeScalar (xs i)))
                                (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1))
                            hcomp
        _ = 0 := by
              have hbasis :
                  (Lagrange.basis σ (fun j' : Fin k => decodeScalar (xs j')) j.1).eval
                    (decodeScalar (xs i)) = 0 := by
                simpa using
                  (Lagrange.eval_basis_of_ne
                    (s := σ) (v := fun j' : Fin k => decodeScalar (xs j'))
                    (i := j.1) (j := i) hji' hi)
              rw [_root_.Polynomial.eval₂_at_apply]
              simpa using congrArg
                (fun x : Scalar params => (MvPolynomial.C x : PolynomialModel params))
                hbasis
    rw [hLi, hslice]
    simp
  · intro hnot
    exact (hnot (by simp : ((⟨i, hi⟩ : {x // x ∈ σ}) ∈ σ.attach))).elim

lemma interpolateCompletedSlices_restrictAtHeight_eq_get_of_mem_supportSubset
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs)
    {i : Fin k} (hi : i ∈ interpolationSupportSubset gs hEligible) :
    (Polynomial.restrictAtHeight params
      (interpolateCompletedSlices params k xs gs) (xs i)).poly =
      ((gs i).get (by
        have hisup : i ∈ gHatTupleSupport gs :=
          interpolationSupportSubset_subset gs hEligible hi
        simpa [gHatTupleSupport] using hisup)).poly := by
  classical
  let σ := interpolationSupportSubset gs hEligible
  have hσcard : σ.card = params.d + 1 := interpolationSupportSubset_card gs hEligible
  cases k with
  | zero => cases i.2
  | succ k =>
      simpa [interpolateCompletedSlices, hEligible, σ, hσcard, Polynomial.restrictAtHeight] using
        interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get_of_mem
          params xs hxs gs σ
          (interpolationSupportSubset_subset gs hEligible) hσcard hi

noncomputable def tupleInterpolatedVerticalLine
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k) : AxisLinePolynomial params.next :=
  Polynomial.restrictToAxisParallelLine params.next
    (interpolateCompletedSlices params k xs gs)
    ({ base := appendPoint params u zeroCoord
     , direction := lastCoord params } : AxisParallelLine params.next)

lemma evaluateAt_averageIdxSubMeas
    (params : Parameters) [FieldModel params.q]
    {Question : Type*}
    (u : Point params)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question (Polynomial params) ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    evaluateAt params u (averageIdxSubMeas 𝒟 A h𝒟) =
      averageIdxSubMeas 𝒟 (fun q => evaluateAt params u (A q)) h𝒟 := by
  classical
  refine SubMeas.ext ?_ ?_
  · intro a
    simp [evaluateAt, postprocess, averageIdxSubMeas, averageOperatorOverDistribution,
      Finset.sum_filter, Finset.sum_comm, Finset.smul_sum]
  · simp [evaluateAt, postprocess, averageIdxSubMeas, averageOperatorOverDistribution]

lemma hRestrictionToVerticalLine_averageIdxSubMeas
    (params : Parameters) [FieldModel params.q]
    {Question : Type*}
    (u : Point params)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question (Polynomial params.next) ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    hRestrictionToVerticalLine params (averageIdxSubMeas 𝒟 A h𝒟) u =
      averageIdxSubMeas 𝒟 (fun q => hRestrictionToVerticalLine params (A q) u) h𝒟 := by
  classical
  refine SubMeas.ext ?_ ?_
  · intro f
    simp [hRestrictionToVerticalLine, postprocess, averageIdxSubMeas,
      averageOperatorOverDistribution, Finset.sum_filter, Finset.sum_comm,
      Finset.smul_sum]
  · simp [hRestrictionToVerticalLine, postprocess, averageIdxSubMeas,
      averageOperatorOverDistribution]

def BadLineEvent
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k)
    (f : AxisLinePolynomial params.next) : Prop :=
  ¬ InterpolationEligible params gs ∨
    ¬ IsGloballyConsistent params xs gs ∨
      ∃ i : Fin k,
        Option.map (fun g : Polynomial params => g u) (gs i) ≠ some (f (xs i))

lemma badLineEvent_of_not_interpolationEligible
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k)
    (f : AxisLinePolynomial params.next)
    (hk : params.d + 1 ≤ k)
    (hNot : ¬ InterpolationEligible params gs) :
    BadLineEvent params u xs gs f := by
  let _ := hk
  refine Or.inl hNot

lemma badLineEvent_of_nonglobal
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k)
    (f : AxisLinePolynomial params.next)
    (hNGlobal : ¬ IsGloballyConsistent params xs gs) :
    BadLineEvent params u xs gs f := by
  rcases nonglobal_gives_slice_mismatch_against_interpolant params xs gs hNGlobal with
    ⟨i, hiSome, hslice⟩
  exact Or.inr <| Or.inl hNGlobal

lemma badLineEvent_of_eval_mismatch
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k)
    (f : AxisLinePolynomial params.next)
    (hmismatch :
      ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i)) :
    BadLineEvent params u xs gs f := by
  exact Or.inr <| Or.inr <|
    exists_onePoint_family_witness_of_eval_mismatch params u xs gs hmismatch

lemma tupleInterpolatedVerticalLine_eq_of_not_badLineEvent
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (f : AxisLinePolynomial params.next)
    (hNotBad : ¬ BadLineEvent params u xs gs f) :
    tupleInterpolatedVerticalLine params u xs gs = f := by
  classical
  have hEligible : InterpolationEligible params gs := by
    by_contra hNot
    exact hNotBad (Or.inl hNot)
  by_contra hne
  let σ := interpolationSupportSubset gs hEligible
  have hσcard : σ.card = params.d + 1 := interpolationSupportSubset_card gs hEligible
  rcases axisLinePolynomial_ne_gives_support_eval_ne params xs hxs σ hσcard hne with
    ⟨i, hiσ, hEvalNe⟩
  have hiSupport : i ∈ gHatTupleSupport gs := interpolationSupportSubset_subset gs hEligible hiσ
  have hiSome : (gs i).isSome = true := by
    simpa [gHatTupleSupport] using hiSupport
  have hslicePoly :
      (Polynomial.restrictAtHeight params
        (interpolateCompletedSlices params k xs gs) (xs i)).poly =
      ((gs i).get hiSome).poly := by
    simpa [hiSome] using
      interpolateCompletedSlices_restrictAtHeight_eq_get_of_mem_supportSubset
        params xs hxs gs hEligible hiσ
  have hsliceEval :
      (Polynomial.restrictAtHeight params
        (interpolateCompletedSlices params k xs gs) (xs i)) u =
      ((gs i).get hiSome) u := by
    simpa using congrArg
      (fun p : PolynomialModel params => encodeScalar (MvPolynomial.eval (decodePoint u) p))
      hslicePoly
  have hlineEval : tupleInterpolatedVerticalLine params u xs gs (xs i) = ((gs i).get hiSome) u := by
    calc
      tupleInterpolatedVerticalLine params u xs gs (xs i)
        = (Polynomial.restrictAtHeight params
            (interpolateCompletedSlices params k xs gs) (xs i)) u := by
              simpa [tupleInterpolatedVerticalLine] using
                restrictToVerticalLine_eval_eq_restrictAtHeight_eval
                  params (interpolateCompletedSlices params k xs gs) u (xs i)
      _ = ((gs i).get hiSome) u := hsliceEval
  have hmismatch :
      ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) := by
    refine ⟨i, hiSome, ?_⟩
    simpa [hlineEval] using hEvalNe
  exact hNotBad (badLineEvent_of_eval_mismatch params u xs gs f hmismatch)

lemma tupleInterpolatedVerticalLine_ne_gives_exists_some_eval_mismatch
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs)
    (_hGlobal : IsGloballyConsistent params xs gs)
    (f : AxisLinePolynomial params.next)
    (hne : tupleInterpolatedVerticalLine params u xs gs ≠ f) :
    ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) := by
  let σ := interpolationSupportSubset gs hEligible
  have hσcard : σ.card = params.d + 1 := interpolationSupportSubset_card gs hEligible
  rcases axisLinePolynomial_ne_gives_support_eval_ne params xs hxs σ hσcard hne with
    ⟨i, hiσ, hEvalNe⟩
  have hiSupport : i ∈ gHatTupleSupport gs := interpolationSupportSubset_subset gs hEligible hiσ
  have hiSome : (gs i).isSome = true := by
    simpa [gHatTupleSupport] using hiSupport
  have hslicePoly :
      (Polynomial.restrictAtHeight params
        (interpolateCompletedSlices params k xs gs) (xs i)).poly =
      ((gs i).get hiSome).poly := by
    simpa [hiSome] using
      interpolateCompletedSlices_restrictAtHeight_eq_get_of_mem_supportSubset
        params xs hxs gs hEligible hiσ
  have hsliceEval :
      (Polynomial.restrictAtHeight params
        (interpolateCompletedSlices params k xs gs) (xs i)) u =
      ((gs i).get hiSome) u := by
    simpa using congrArg
      (fun p : PolynomialModel params => encodeScalar (MvPolynomial.eval (decodePoint u) p))
      hslicePoly
  have hlineEval : tupleInterpolatedVerticalLine params u xs gs (xs i) = ((gs i).get hiSome) u := by
    calc
      tupleInterpolatedVerticalLine params u xs gs (xs i)
        = (Polynomial.restrictAtHeight params
            (interpolateCompletedSlices params k xs gs) (xs i)) u := by
              simpa [tupleInterpolatedVerticalLine] using
                restrictToVerticalLine_eval_eq_restrictAtHeight_eval
                  params (interpolateCompletedSlices params k xs gs) u (xs i)
      _ = ((gs i).get hiSome) u := hsliceEval
  refine ⟨i, hiSome, ?_⟩
  simpa [hlineEval] using hEvalNe

lemma interpolationEligibleSandwich_mismatch_sum_mono
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (f : AxisLinePolynomial params.next) :
    ∑ gs : GHatTupleOutcome params k,
        (if IsGloballyConsistent params xs gs
            ∧ tupleInterpolatedVerticalLine params u xs gs ≠ f then
          (interpolationEligibleSandwichFamily params family k xs).outcome gs
        else 0)
      ≤
      ∑ gs : GHatTupleOutcome params k,
        (if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i) then
          (interpolationEligibleSandwichFamily params family k xs).outcome gs
        else 0) := by
  refine Finset.sum_le_sum ?_
  intro gs _
  by_cases hglob : IsGloballyConsistent params xs gs
  · by_cases hneq : tupleInterpolatedVerticalLine params u xs gs ≠ f
    · by_cases hEligible : InterpolationEligible params gs
      · rcases tupleInterpolatedVerticalLine_ne_gives_exists_some_eval_mismatch
          params u xs hxs gs hEligible hglob f hneq with ⟨i, hiSome, hm⟩
        have hright :
            ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) :=
          ⟨i, hiSome, hm⟩
        simp [hglob, hneq, hright]
      · simp [interpolationEligibleSandwichFamily, restrictSubMeas, hEligible, hglob, hneq]
    · by_cases hright : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
        ((gs i).get hiSome) u ≠ f (xs i)
      · have hnonneg : 0 ≤ (interpolationEligibleSandwichFamily params family k xs).outcome gs :=
          (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs
        simp [hglob, hneq, hright, hnonneg]
      · simp [hglob, hneq, hright]
  · by_cases hright : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i)
    · have hnonneg : 0 ≤ (interpolationEligibleSandwichFamily params family k xs).outcome gs :=
        (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs
      simp [hglob, hright, hnonneg]
    · simp [hglob, hright]

lemma interpolationEligibleSandwich_exists_mismatch_sum_le_sum
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (f : AxisLinePolynomial params.next) :
    (∑ gs : GHatTupleOutcome params k,
        if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i) then
          (interpolationEligibleSandwichFamily params family k xs).outcome gs
        else 0)
      ≤
      ∑ i : Fin k,
        ∑ gs : GHatTupleOutcome params k,
          if ∃ hiSome : (gs i).isSome = true,
              ((gs i).get hiSome) u ≠ f (xs i) then
            (interpolationEligibleSandwichFamily params family k xs).outcome gs
          else 0 := by
  classical
  calc
    (∑ gs : GHatTupleOutcome params k,
        if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
            ((gs i).get hiSome) u ≠ f (xs i) then
          (interpolationEligibleSandwichFamily params family k xs).outcome gs
        else 0)
      ≤ ∑ gs : GHatTupleOutcome params k,
          ∑ j : Fin k,
            if ∃ hiSome : (gs j).isSome = true,
                ((gs j).get hiSome) u ≠ f (xs j) then
              (interpolationEligibleSandwichFamily params family k xs).outcome gs
            else 0 := by
            exact Finset.sum_le_sum (fun (gs : GHatTupleOutcome params k) _ => by
              let P : Fin k → Prop := fun i =>
                ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i)
              let T : Fin k → MIPStarRE.Quantum.Op ι := fun j =>
                if P j then (interpolationEligibleSandwichFamily params family k xs).outcome gs
                else (0 : MIPStarRE.Quantum.Op ι)
              change
                (if ∃ i : Fin k, P i then (
                    interpolationEligibleSandwichFamily params family k xs).outcome gs
                  else (0 : MIPStarRE.Quantum.Op ι)) ≤
                ∑ j : Fin k, T j
              have hT_nonneg : ∀ j : Fin k, 0 ≤ T j := by
                intro j
                by_cases hP : P j <;>
                  simp [T, hP, (interpolationEligibleSandwichFamily params family k
                    xs).outcome_pos gs]
              by_cases hExists : ∃ i : Fin k, P i
              · rcases hExists with ⟨i, hi⟩
                have hExists' : ∃ i : Fin k, P i := ⟨i, hi⟩
                have hsingle :
                    (interpolationEligibleSandwichFamily params family k xs).outcome gs
                        ≤ ∑ j : Fin k, T j := by
                  calc
                    (interpolationEligibleSandwichFamily params family k xs).outcome gs = T i := by
                      simp [T, hi]
                    _ ≤ ∑ j : Fin k, T j := by
                      exact Finset.single_le_sum (fun j _ => hT_nonneg j)
                        (by simp : i ∈ (Finset.univ : Finset (Fin k)))
                simpa [P, hExists'] using hsingle
              · have hnonneg_sum :
                    0 ≤ ∑ j : Fin k, T j := by
                  exact Finset.sum_nonneg fun j _ => hT_nonneg j
                simpa [P, hExists] using hnonneg_sum)
    _ = ∑ i : Fin k,
          ∑ gs : GHatTupleOutcome params k,
            if ∃ hiSome : (gs i).isSome = true,
                ((gs i).get hiSome) u ≠ f (xs i) then
              (interpolationEligibleSandwichFamily params family k xs).outcome gs
            else 0 := by
            rw [Finset.sum_comm]

lemma pastedInterpolation_verticalLine_singleOutcome_postprocess
    (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    (k : ℕ)
    (u : Point params)
    (xs : PointTuple params k)
    (f : AxisLinePolynomial params.next) :
    postprocess
      (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
      (fun h => decide (h = f)) =
    postprocess
      (restrictSubMeas (interpolationEligibleSandwichFamily params family k xs)
        (IsGloballyConsistent params xs))
      (fun gs => decide (tupleInterpolatedVerticalLine params u xs gs = f)) := by
  rw [pastedInterpolationFamily, hRestrictionToVerticalLine]
  rw [postprocess_postprocess, postprocess_postprocess]
  congr 1

noncomputable def singleOutcomeRightSubMeas
    {Outcome : Type*} [Fintype Outcome]
    (B : SubMeas Outcome ι) (a0 : Outcome) : SubMeas Bool ι where
  outcome
    | true => B.outcome a0
    | false => 0
  total := B.outcome a0
  outcome_pos := by
    intro b
    cases b <;> simp [B.outcome_pos a0]
  sum_eq_total := by simp
  total_le_one := le_trans (B.outcome_le_total a0) B.total_le_one

lemma qBipartiteConsDefect_eq_false_mass_of_bool_right_true_local
    (ψ : QuantumState (ι × ι))
    (A B : SubMeas Bool ι)
    (hfalse : B.outcome false = 0)
    (htrue : B.outcome true = B.total) :
    qBipartiteConsDefect ψ A B = ev ψ (opTensor (A.outcome false) B.total) := by
  have hsumA : A.outcome false + A.outcome true = A.total := by
    simpa [add_comm] using A.sum_eq_total
  have hnonneg : 0 ≤ ev ψ (opTensor (A.outcome false) B.total) := by
    exact ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos false) B.total_nonneg
  unfold qBipartiteConsDefect qBipartiteMatchMass
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false,
    not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
  have hexpr :
      ev ψ (opTensor A.total B.total) -
          (ev ψ (opTensor (A.outcome true) (B.outcome true)) +
            ev ψ (opTensor (A.outcome false) (B.outcome false))) =
        ev ψ (opTensor (A.outcome false) B.total) := by
    calc
      ev ψ (opTensor A.total B.total) -
          (ev ψ (opTensor (A.outcome true) (B.outcome true)) +
            ev ψ (opTensor (A.outcome false) (B.outcome false)))
        = ev ψ (opTensor (A.outcome false + A.outcome true) B.total) -
            (ev ψ (opTensor (A.outcome true) B.total) +
              ev ψ (opTensor (A.outcome false) 0)) := by
              rw [hsumA, htrue, hfalse]
      _ = ev ψ (opTensor (A.outcome false) B.total +
            opTensor (A.outcome true) B.total) -
            (ev ψ (opTensor (A.outcome true) B.total) +
              ev ψ (opTensor (A.outcome false) 0)) := by
              rw [show opTensor (A.outcome false + A.outcome true) B.total =
                    opTensor (A.outcome false) B.total +
                      opTensor (A.outcome true) B.total from
                  Matrix.add_kronecker _ _ _]
      _ = ev ψ (opTensor (A.outcome false) B.total) := by
            have hfalse_zero : ev ψ (opTensor (A.outcome false) 0) = 0 := by
              simp [opTensor, ev]
            nlinarith [
              ev_add ψ (opTensor (A.outcome false) B.total)
                (opTensor (A.outcome true) B.total),
              hfalse_zero]
  calc
    max 0
        (ev ψ (opTensor A.total B.total) -
          (ev ψ (opTensor (A.outcome true) (B.outcome true)) +
            ev ψ (opTensor (A.outcome false) (B.outcome false))))
      = max 0 (ev ψ (opTensor (A.outcome false) B.total)) := by
          rw [hexpr]
    _ = ev ψ (opTensor (A.outcome false) B.total) := by
          rw [max_eq_right hnonneg]

lemma qBipartiteConsDefect_postprocess_eq_singleOutcome
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (A B : SubMeas Outcome ι) (a0 : Outcome) :
    qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
      (singleOutcomeRightSubMeas B a0) =
        ev ψ
          (opTensor ((postprocess A (fun a => decide (a = a0))).outcome false)
            (B.outcome a0)) := by
  refine qBipartiteConsDefect_eq_false_mass_of_bool_right_true_local ψ
    (postprocess A (fun a => decide (a = a0))) (singleOutcomeRightSubMeas B a0) ?_ ?_
  · rfl
  · rfl

lemma postprocess_decide_eq_true_outcome
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) (a0 : Outcome) :
    (postprocess A (fun a => decide (a = a0))).outcome true = A.outcome a0 := by
  simp [postprocess, Finset.sum_filter]

lemma postprocess_decide_false_add_true_eq_total
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) (a0 : Outcome) :
    (postprocess A (fun a => decide (a = a0))).outcome false + A.outcome a0 = A.total := by
  have hsum := (postprocess A (fun a => decide (a = a0))).sum_eq_total
  simpa [Bool.forall_bool, add_comm, postprocess_decide_eq_true_outcome] using hsum

lemma postprocess_decide_eq_false_outcome
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (A : SubMeas Outcome ι) (a0 : Outcome) :
    (postprocess A (fun a => decide (a = a0))).outcome false =
      A.total - A.outcome a0 := by
  exact eq_sub_iff_add_eq.mpr (postprocess_decide_false_add_true_eq_total A a0)

lemma qBipartiteConsDefect_eq_sum_singleOutcome
    {Outcome : Type*} [Fintype Outcome] [DecidableEq Outcome]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas Outcome ι)
    (B : Measurement Outcome ι) :
    qBipartiteConsDefect ψ A B.toSubMeas =
      ∑ a0 : Outcome,
        qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
          (singleOutcomeRightSubMeas B.toSubMeas a0) := by
  have hsingle_term : ∀ a0 : Outcome,
      ev ψ (opTensor A.total (B.outcome a0)) =
        qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
          (singleOutcomeRightSubMeas B.toSubMeas a0) +
          ev ψ (opTensor (A.outcome a0) (B.outcome a0)) := by
    intro a0
    calc
      ev ψ (opTensor A.total (B.outcome a0))
        = ev ψ (opTensor ((postprocess A (fun a => decide (a = a0))).outcome false + A.outcome a0)
            (B.outcome a0)) := by
              rw [postprocess_decide_false_add_true_eq_total]
      _ = ev ψ
            (opTensor ((postprocess A (fun a => decide (a = a0))).outcome false) (B.outcome a0) +
              opTensor (A.outcome a0) (B.outcome a0)) := by
              rw [opTensor_add_left_local]
      _ = qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
            (singleOutcomeRightSubMeas B.toSubMeas a0) +
          ev ψ (opTensor (A.outcome a0) (B.outcome a0)) := by
            rw [ev_add, qBipartiteConsDefect_postprocess_eq_singleOutcome]
  have htotal_sum :
      ev ψ (opTensor A.total B.toSubMeas.total) =
        ∑ a0 : Outcome, ev ψ (opTensor A.total (B.outcome a0)) := by
    rw [← B.sum_eq_total]
    rw [opTensor_sum_right_local, ev_finset_sum]
  have hdecomp :
      ev ψ (opTensor A.total B.toSubMeas.total) - qBipartiteMatchMass ψ A B.toSubMeas =
        ∑ a0 : Outcome,
          qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
            (singleOutcomeRightSubMeas B.toSubMeas a0) := by
    rw [htotal_sum, qBipartiteMatchMass]
    calc
      ∑ a0 : Outcome, ev ψ (opTensor A.total (B.outcome a0)) -
          ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))
        = (∑ a0 : Outcome,
            (qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
              (singleOutcomeRightSubMeas B.toSubMeas a0) +
              ev ψ (opTensor (A.outcome a0) (B.outcome a0)))) -
            ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a)) := by
              refine congrArg (fun t => t - ∑ a : Outcome,
                  ev ψ (opTensor (A.outcome a) (B.outcome a))) ?_
              exact Finset.sum_congr rfl fun a _ => hsingle_term a
      _ = ∑ a0 : Outcome,
            qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
              (singleOutcomeRightSubMeas B.toSubMeas a0) := by
            rw [Finset.sum_add_distrib]
            ring
  have hnonneg :
      0 ≤ ∑ a0 : Outcome,
        qBipartiteConsDefect ψ (postprocess A (fun a => decide (a = a0)))
          (singleOutcomeRightSubMeas B.toSubMeas a0) := by
    exact Finset.sum_nonneg fun a0 _ =>
      qBipartiteConsDefect_nonneg ψ _ _
  rw [qBipartiteConsDefect, hdecomp, max_eq_right hnonneg]

noncomputable def hBConsistencyBadMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k) : Error :=
  ∑ f : AxisLinePolynomial params.next,
    ev strategy.state
      (opTensor
        (∑ gs : GHatTupleOutcome params k,
        if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
              ((gs i).get hiSome) u ≠ f (xs i) then
            (interpolationEligibleSandwichFamily params family k xs).outcome gs
          else 0)
        ((verticalLineMeasurementFamily params strategy u).outcome f))

noncomputable def ldSandwichLineOnePointRightMeasurement
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (i : Fin k) (q : SandwichedLineQuestion params k) :
    Measurement (Option (Fq params)) ι where
  toSubMeas := ((ldSandwichLineOnePointRightFamily params strategy family k i.1) q)
  total_eq_one := by
    let ℓ : AxisParallelLine params.next :=
      { base := appendPoint params q.1 zeroCoord
        direction := lastCoord params }
    simpa [ldSandwichLineOnePointRightFamily, verticalLineMeasurementFamily, i.2,
      postprocess_total, ℓ] using (strategy.axisParallelMeasurement ℓ).total_eq_one

lemma ldSandwichLineOnePointRightMeasurement_outcome_none_eq_zero
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (i : Fin k) (q : SandwichedLineQuestion params k) :
    (ldSandwichLineOnePointRightMeasurement params strategy family i q).outcome none = 0 := by
  simp [ldSandwichLineOnePointRightMeasurement, ldSandwichLineOnePointRightFamily,
    postprocess, i.2]

lemma ldSandwichLineOnePointRightMeasurement_outcome_some_eq_sum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (i : Fin k) (q : SandwichedLineQuestion params k) (a : Fq params) :
    (ldSandwichLineOnePointRightMeasurement params strategy family i q).outcome (some a) =
      ∑ f : AxisLinePolynomial params.next,
        if f (q.2 i) = a then
          (verticalLineMeasurementFamily params strategy q.1).outcome f
        else 0 := by
  simp [ldSandwichLineOnePointRightMeasurement, ldSandwichLineOnePointRightFamily,
    postprocess, i.2, Finset.sum_filter]

lemma grouped_coordinate_mismatch_le_left_falseOutcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k)
    (i : Fin k) (a : Fq params) :
    (∑ gs : GHatTupleOutcome params k,
      if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ a then
        (interpolationEligibleSandwichFamily params family k xs).outcome gs
      else 0)
    ≤
    (postprocess
      ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
      (fun o => decide (o = some a))).outcome false := by
  have hrewrite :
      (postprocess
        ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
        (fun o => decide (o = some a))).outcome false =
        ∑ gs : GHatTupleOutcome params k,
          if Option.map (fun g : Polynomial params => g u) (gs i) ≠ some a then
            (restrictSubMeas (gHatSandwichFamily params family k xs)
              (fun gs => (gs i).isSome = true)).outcome gs
          else 0 := by
    rw [ldSandwichLineOnePointLeftFamily, postprocess_postprocess]
    simp [postprocess, Function.comp, i.2, Finset.sum_filter]
  rw [hrewrite]
  refine Finset.sum_le_sum ?_
  intro gs _
  by_cases hm : ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ a
  · rcases hm with ⟨hiSome, hne⟩
    have hneq : Option.map (fun g : Polynomial params => g u) (gs i) ≠ some a := by
      cases hgi : gs i with
      | none =>
          simp [Option.isSome, hgi] at hiSome
      | some g =>
          simp [hgi] at hiSome
          simpa [hgi] using hne
    by_cases hEligible : InterpolationEligible params gs
    · simp [interpolationEligibleSandwichFamily, restrictSubMeas, hiSome, hneq, hEligible,
        hne]
    · have hnonneg : 0 ≤ (gHatSandwichFamily params family k xs).outcome gs :=
        (gHatSandwichFamily params family k xs).outcome_pos gs
      simp [interpolationEligibleSandwichFamily, restrictSubMeas, hiSome, hneq,
        hEligible, hnonneg]
  · by_cases hneq : Option.map (fun g : Polynomial params => g u) (gs i) ≠ some a
    · have hnonneg :
          0 ≤ (restrictSubMeas (gHatSandwichFamily params family k xs)
            (fun gs => (gs i).isSome = true)).outcome gs :=
        (restrictSubMeas (gHatSandwichFamily params family k xs)
          (fun gs => (gs i).isSome = true)).outcome_pos gs
      simp [hm, hneq, hnonneg]
    · simp [hm, hneq]

lemma hBConsistencyCoordMass_le_linePointDefect
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k)
    (i : Fin k) :
    (∑ f : AxisLinePolynomial params.next,
      ev strategy.state
        (opTensor
          (∑ gs : GHatTupleOutcome params k,
            if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
              (interpolationEligibleSandwichFamily params family k xs).outcome gs
            else 0)
          ((verticalLineMeasurementFamily params strategy u).outcome f)))
      ≤ qBipartiteConsDefect strategy.state
          ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
          ((ldSandwichLineOnePointRightFamily params strategy family k i.1) (u, xs)) := by
  let q : SandwichedLineQuestion params k := (u, xs)
  let A := ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
  let Bm := ldSandwichLineOnePointRightMeasurement params strategy family i q
  let leftFalse : Fq params → MIPStarRE.Quantum.Op ι := fun a =>
    (postprocess A (fun o => decide (o = some a))).outcome false
  have hstep :
      ∀ f : AxisLinePolynomial params.next,
        ev strategy.state
          (opTensor
            (∑ gs : GHatTupleOutcome params k,
              if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
                (interpolationEligibleSandwichFamily params family k xs).outcome gs
              else 0)
            ((verticalLineMeasurementFamily params strategy u).outcome f))
          ≤ ev strategy.state
              (opTensor (leftFalse (f (xs i)))
                ((verticalLineMeasurementFamily params strategy u).outcome f)) := by
    intro f
    exact ev_mono strategy.state _ _ <|
      opTensor_mono_left
        (grouped_coordinate_mismatch_le_left_falseOutcome params strategy family u xs i (f (xs i)))
        ((verticalLineMeasurementFamily params strategy u).outcome_pos f)
  have hgrouped :
      (∑ f : AxisLinePolynomial params.next,
        ev strategy.state
          (opTensor (leftFalse (f (xs i)))
            ((verticalLineMeasurementFamily params strategy u).outcome f)))
        = ∑ a : Fq params,
            ev strategy.state
              (opTensor (leftFalse a) (Bm.outcome (some a))) := by
    calc
      (∑ f : AxisLinePolynomial params.next,
        ev strategy.state
          (opTensor (leftFalse (f (xs i)))
            ((verticalLineMeasurementFamily params strategy u).outcome f)))
        = ∑ f : AxisLinePolynomial params.next,
            ∑ a : Fq params,
              if f (xs i) = a then
                ev strategy.state
                  (opTensor (leftFalse a) (
                    (verticalLineMeasurementFamily params strategy u).outcome f))
              else (0 : Error) := by
              refine Finset.sum_congr rfl ?_
              intro f _
              have hsingle :
                  (∑ a : Fq params,
                    if f (xs i) = a then
                      ev strategy.state
                        (opTensor (leftFalse a) (
                          (verticalLineMeasurementFamily params strategy u).outcome f))
                    else (0 : Error)) =
                  ev strategy.state
                    (opTensor (leftFalse (f (xs i))) (
                      (verticalLineMeasurementFamily params strategy u).outcome f)) := by
                simp
              exact hsingle.symm
      _ = ∑ a : Fq params,
            ∑ f : AxisLinePolynomial params.next,
              if f (xs i) = a then
                ev strategy.state
                  (opTensor (leftFalse a) (
                    (verticalLineMeasurementFamily params strategy u).outcome f))
              else (0 : Error) := by
              rw [Finset.sum_comm]
      _ = ∑ a : Fq params,
            ev strategy.state
              (opTensor (leftFalse a) (Bm.outcome (some a))) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              have hgroup :
                  (∑ f : AxisLinePolynomial params.next,
                    if f (xs i) = a then
                      ev strategy.state
                        (opTensor (leftFalse a) (
                          (verticalLineMeasurementFamily params strategy u).outcome f))
                    else (0 : Error))
                    = ∑ f : AxisLinePolynomial params.next,
                        ev strategy.state
                          (opTensor (leftFalse a)
                            (if f (xs i) = a then
                              (verticalLineMeasurementFamily params strategy u).outcome f
                            else 0)) := by
                      refine Finset.sum_congr rfl ?_
                      intro f _
                      by_cases hf : f (xs i) = a
                      · simp [hf]
                      · simp [hf, opTensor, ev]
              rw [hgroup, ← ev_finset_sum, ← opTensor_sum_right_local]
              rw [ldSandwichLineOnePointRightMeasurement_outcome_some_eq_sum]
  have hdefect_expand :
      qBipartiteConsDefect strategy.state A Bm.toSubMeas =
        qBipartiteConsDefect strategy.state
          ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
          ((ldSandwichLineOnePointRightFamily params strategy family k i.1) q) := by
    rfl
  calc
    (∑ f : AxisLinePolynomial params.next,
      ev strategy.state
        (opTensor
          (∑ gs : GHatTupleOutcome params k,
            if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
              (interpolationEligibleSandwichFamily params family k xs).outcome gs
            else 0)
          ((verticalLineMeasurementFamily params strategy u).outcome f)))
      ≤ ∑ f : AxisLinePolynomial params.next,
          ev strategy.state
            (opTensor (leftFalse (f (xs i)))
              ((verticalLineMeasurementFamily params strategy u).outcome f)) := by
            exact Finset.sum_le_sum fun f _ => hstep f
    _ = ∑ a : Fq params,
          ev strategy.state
            (opTensor (leftFalse a) (Bm.outcome (some a))) := hgrouped
    _ = ∑ a : Fq params,
          qBipartiteConsDefect strategy.state
            (postprocess A (fun o => decide (o = some a)))
            (singleOutcomeRightSubMeas Bm.toSubMeas (some a)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            symm
            exact qBipartiteConsDefect_postprocess_eq_singleOutcome strategy.state A
                Bm.toSubMeas (some a)
    _ ≤ qBipartiteConsDefect strategy.state A Bm.toSubMeas := by
            rw [qBipartiteConsDefect_eq_sum_singleOutcome (B := Bm), Fintype.sum_option]
            have hnone_nonneg :
                0 ≤ qBipartiteConsDefect strategy.state
                  (postprocess A (fun o => decide (o = none)))
                  (singleOutcomeRightSubMeas Bm.toSubMeas none) :=
              qBipartiteConsDefect_nonneg strategy.state _ _
            linarith
    _ = qBipartiteConsDefect strategy.state
          ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
          ((ldSandwichLineOnePointRightFamily params strategy family k i.1) q) := hdefect_expand

lemma hBConsistencyBadMass_le_linePointDefectSum
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k) :
    hBConsistencyBadMass params strategy family u xs
      ≤ ∑ i : Fin k,
          qBipartiteConsDefect strategy.state
            ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
            ((ldSandwichLineOnePointRightFamily params strategy family k i.1) (u, xs)) := by
  calc
    hBConsistencyBadMass params strategy family u xs
      ≤ ∑ f : AxisLinePolynomial params.next,
          ev strategy.state
            (opTensor
              (∑ i : Fin k,
                ∑ gs : GHatTupleOutcome params k,
                  if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
                    (interpolationEligibleSandwichFamily params family k xs).outcome gs
                  else 0)
              ((verticalLineMeasurementFamily params strategy u).outcome f)) := by
            unfold hBConsistencyBadMass
            refine Finset.sum_le_sum ?_
            intro f _
            apply ev_mono strategy.state _ _
            exact opTensor_mono_left
              (interpolationEligibleSandwich_exists_mismatch_sum_le_sum params family u xs f)
              ((verticalLineMeasurementFamily params strategy u).outcome_pos f)
    _ = ∑ i : Fin k,
          ∑ f : AxisLinePolynomial params.next,
            ev strategy.state
              (opTensor
                (∑ gs : GHatTupleOutcome params k,
                  if ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
                    (interpolationEligibleSandwichFamily params family k xs).outcome gs
                  else 0)
                ((verticalLineMeasurementFamily params strategy u).outcome f)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro f _
            rw [opTensor_sum_left_local, ev_finset_sum]
    _ ≤ ∑ i : Fin k,
          qBipartiteConsDefect strategy.state
            ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) (u, xs))
            ((ldSandwichLineOnePointRightFamily params strategy family k i.1) (u, xs)) := by
            refine Finset.sum_le_sum ?_
            intro i _
            exact hBConsistencyCoordMass_le_linePointDefect params strategy family u xs i

lemma hBConsistencyBadMass_nonneg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k) :
    0 ≤ hBConsistencyBadMass params strategy family u xs := by
  unfold hBConsistencyBadMass
  refine Finset.sum_nonneg ?_
  intro f _
  apply ev_nonneg_of_psd strategy.state _
  exact opTensor_nonneg
    (by
      refine Finset.sum_nonneg ?_
      intro gs _
      by_cases hbad : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i)
      · simp [hbad, (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs]
      · simp [hbad])
    ((verticalLineMeasurementFamily params strategy u).outcome_pos f)

lemma hBConsistencyBadMass_le_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) (xs : PointTuple params k) :
    hBConsistencyBadMass params strategy family u xs ≤ 1 := by
  let T : MIPStarRE.Quantum.Op ι := (interpolationEligibleSandwichFamily params family k xs).total
  let L : AxisLinePolynomial params.next → MIPStarRE.Quantum.Op ι := fun f =>
    ∑ gs : GHatTupleOutcome params k,
      if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true, ((gs i).get hiSome) u ≠ f (xs i) then
        (interpolationEligibleSandwichFamily params family k xs).outcome gs
      else 0
  have hLle : ∀ f : AxisLinePolynomial params.next, L f ≤ T := by
    intro f
    calc
      L f ≤ ∑ gs : GHatTupleOutcome params k,
          (interpolationEligibleSandwichFamily params family k xs).outcome gs := by
            unfold L
            refine Finset.sum_le_sum ?_
            intro gs _
            by_cases hbad : ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                ((gs i).get hiSome) u ≠ f (xs i)
            · simp [hbad]
            · simp [hbad, (interpolationEligibleSandwichFamily params family k xs).outcome_pos gs]
      _ = T := by
            simpa [T] using (interpolationEligibleSandwichFamily params family k xs).sum_eq_total
  have hsum_le :
      hBConsistencyBadMass params strategy family u xs ≤
        ∑ f : AxisLinePolynomial params.next,
          ev strategy.state (opTensor T (
              (verticalLineMeasurementFamily params strategy u).outcome f)) := by
    unfold hBConsistencyBadMass
    refine Finset.sum_le_sum ?_
    intro f _
    exact ev_mono strategy.state _ _ <|
      opTensor_mono_left (hLle f) ((verticalLineMeasurementFamily params strategy u).outcome_pos f)
  have htotal_eq_one : (verticalLineMeasurementFamily params strategy u).total = 1 := by
    let ℓ : AxisParallelLine params.next :=
      { base := appendPoint params u zeroCoord
        direction := lastCoord params }
    simpa [verticalLineMeasurementFamily, ℓ] using (strategy.axisParallelMeasurement ℓ).total_eq_one
  calc
    hBConsistencyBadMass params strategy family u xs
      ≤ ∑ f : AxisLinePolynomial params.next,
          ev strategy.state (opTensor T (
              (verticalLineMeasurementFamily params strategy u).outcome f)) := hsum_le
    _ = ev strategy.state (opTensor T (verticalLineMeasurementFamily params strategy u).total) := by
          rw [← ev_finset_sum, ← opTensor_sum_right_local]
          rw [(verticalLineMeasurementFamily params strategy u).sum_eq_total]
    _ = ev strategy.state (opTensor T (1 : MIPStarRE.Quantum.Op ι)) := by rw [htotal_eq_one]
    _ ≤ 1 := by
          have hTle : T ≤ 1 := by simpa [T] using (
              interpolationEligibleSandwichFamily params family k xs).total_le_one
          have hop : opTensor T (1 : MIPStarRE.Quantum.Op ι) ≤ 1 := by
            simpa [leftTensor] using leftTensor_le_one (ι₂ := ι) (A := T) hTle
          simpa [ev_one_of_isNormalized strategy.state strategy.isNormalized] using
            (ev_mono strategy.state _ _ hop)

lemma postprocess_restrictSubMeas_outcome
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (A : SubMeas α ι) (p : α → Prop) [DecidablePred p]
    (f : α → β) (b : β) :
    (postprocess (restrictSubMeas A p) f).outcome b =
      ∑ a : α, if p a ∧ f a = b then A.outcome a else 0 := by
  classical
  ext i j
  simp [postprocess, restrictSubMeas, Matrix.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro c _
  by_cases hf : f c = b <;> by_cases hp : p c <;>
    simp [hf, hp]

lemma pastedInterpolation_verticalLine_defect_le_badMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ}
    (u : Point params)
    (xs : PointTuple params k)
    (hxs : Function.Injective xs) :
    qBipartiteConsDefect strategy.state
      (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
      (verticalLineMeasurementFamily params strategy u)
      ≤ hBConsistencyBadMass params strategy family u xs := by
  let ℓ : AxisParallelLine params.next :=
    { base := appendPoint params u zeroCoord
      direction := lastCoord params }
  let Bm : Measurement (AxisLinePolynomial params.next) ι :=
    (strategy.axisParallelMeasurement ℓ).toMeasurement
  have hB : Bm.toSubMeas = verticalLineMeasurementFamily params strategy u := by
    simp [Bm, ℓ, verticalLineMeasurementFamily]
  rw [← hB, qBipartiteConsDefect_eq_sum_singleOutcome (B := Bm)]
  exact Finset.sum_le_sum (fun f _ => by
    calc
      qBipartiteConsDefect strategy.state
          (postprocess (hRestrictionToVerticalLine params (
              pastedInterpolationFamily params family k xs) u)
            (fun h => decide (h = f)))
          (singleOutcomeRightSubMeas Bm.toSubMeas f)
        = ev strategy.state
            (opTensor
              ((postprocess (hRestrictionToVerticalLine params (
                  pastedInterpolationFamily params family k xs) u)
                (fun h => decide (h = f))).outcome false)
              (Bm.outcome f)) := by
                rw [qBipartiteConsDefect_postprocess_eq_singleOutcome]
      _ = ev strategy.state
            (opTensor
              (∑ gs : GHatTupleOutcome params k,
                if IsGloballyConsistent params xs gs
                    ∧ tupleInterpolatedVerticalLine params u xs gs ≠ f then
                  (interpolationEligibleSandwichFamily params family k xs).outcome gs
                else 0)
              (Bm.outcome f)) := by
                rw [pastedInterpolation_verticalLine_singleOutcome_postprocess,
                  postprocess_restrictSubMeas_outcome]
                simp [decide_eq_false_iff_not]
      _ ≤ ev strategy.state
            (opTensor
              (∑ gs : GHatTupleOutcome params k,
                if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                    ((gs i).get hiSome) u ≠ f (xs i) then
                  (interpolationEligibleSandwichFamily params family k xs).outcome gs
                else 0)
              (Bm.outcome f)) := by
                apply ev_mono strategy.state _ _
                exact opTensor_mono_left
                  (interpolationEligibleSandwich_mismatch_sum_mono params family u xs hxs f)
                  (Bm.outcome_pos f)
      _ = ev strategy.state
            (opTensor
              (∑ gs : GHatTupleOutcome params k,
                if ∃ i : Fin k, ∃ hiSome : (gs i).isSome = true,
                    ((gs i).get hiSome) u ≠ f (xs i) then
                  (interpolationEligibleSandwichFamily params family k xs).outcome gs
                else 0)
              ((verticalLineMeasurementFamily params strategy u).outcome f)) := by
                simp [hB])

lemma opTensor_smul_left
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (c : Error)
    (A : MIPStarRE.Quantum.Op ιA)
    (B : MIPStarRE.Quantum.Op ιB) :
    opTensor ((c : ℂ) • A) B = (c : ℂ) • opTensor A B := by
  ext x y
  simp [opTensor, mul_comm, mul_left_comm]

lemma opTensor_sum_left
    {α ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (s : Finset α)
    (f : α → MIPStarRE.Quantum.Op ιA)
    (B : MIPStarRE.Quantum.Op ιB) :
    opTensor (∑ a ∈ s, f a) B = ∑ a ∈ s, opTensor (f a) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [opTensor]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, opTensor_add_left_local, ih]

lemma opTensor_averageOperatorOverDistribution_left
    {Question ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (𝒟 : Distribution Question)
    (A : Question → MIPStarRE.Quantum.Op ιA)
    (B : MIPStarRE.Quantum.Op ιB) :
    opTensor (averageOperatorOverDistribution 𝒟 A) B =
      averageOperatorOverDistribution 𝒟 (fun q => opTensor (A q) B) := by
  classical
  unfold averageOperatorOverDistribution
  rw [opTensor_sum_left]
  refine Finset.sum_congr rfl ?_
  intro q _
  simpa using opTensor_smul_left (c := 𝒟.weight q) (A := A q) (B := B)

lemma avgOver_sub
    {α : Type*}
    (𝒟 : Distribution α)
    (f g : α → Error) :
    avgOver 𝒟 (fun a => f a - g a) = avgOver 𝒟 f - avgOver 𝒟 g := by
  unfold avgOver
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]

lemma avgOver_distinct_bounded_le_avgOver_uniform_add_tv
    (params : Parameters) [FieldModel params.q]
    (k : ℕ) (hk : k ≤ params.q)
    (F : PointTuple params k → Error)
    (hF_nonneg : ∀ xs, 0 ≤ F xs)
    (hF_le_one : ∀ xs, F xs ≤ 1) :
    avgOver (distinctTupleDistribution params k) F
      ≤ avgOver (uniformDistribution (PointTuple params k)) F
        + totalVariationDistance
            (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k) := by
  classical
  let support : Finset (PointTuple params k) :=
    Finset.univ.filter fun xs : PointTuple params k => Function.Injective xs
  let bad : Finset (PointTuple params k) :=
    { xs ∈ Finset.univ | ¬ Function.Injective xs }
  have hsupport_card : support.card = params.q.descFactorial k := by
    rw [← Fintype.card_coe]
    let e : { xs : PointTuple params k // Function.Injective xs } ≃ (Fin k ↪ Fq params) :=
      Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fq params)
    simpa [support, Finset.mem_filter] using
      (Fintype.card_congr e).trans Fintype.card_embedding_eq
  have hqpow_ne : ((params.q : Error) ^ k) ≠ 0 := by
    have hq_ne : (params.q : Error) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt params.hq)
    exact pow_ne_zero k hq_ne
  have hsupport_nonempty : support.Nonempty := by
    refine ⟨fun i => ⟨i.1, Nat.lt_of_lt_of_le i.2 hk⟩, ?_⟩
    refine Finset.mem_filter.mpr ?_
    constructor
    · simp
    · intro i j hij
      exact Fin.ext (by simpa using congrArg Fin.val hij)
  have hsupport_card_ne : support.card ≠ 0 := Finset.card_ne_zero.mpr hsupport_nonempty
  have hsupport_pos : 0 < (support.card : Error) := by
    exact_mod_cast Nat.pos_of_ne_zero hsupport_card_ne
  have hsupport_le_pow_nat : support.card ≤ params.q ^ k := by
    rw [hsupport_card]
    exact Nat.descFactorial_le_pow _ _
  have hweight_le :
      1 / ((params.q : Error) ^ k) ≤ 1 / (support.card : Error) := by
    exact one_div_le_one_div_of_le hsupport_pos (by exact_mod_cast hsupport_le_pow_nat)
  have hpartition_card :
      support.card + bad.card = params.q ^ k := by
    simpa [support, bad, PointTuple, Fintype.card_fun, Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (PointTuple params k)))
        (p := fun xs : PointTuple params k => Function.Injective xs))
  have hpartition_cast :
      (support.card : Error) + bad.card = (params.q : Error) ^ k := by
    exact_mod_cast hpartition_card
  have hdisj : Disjoint support bad := by
    simpa [support, bad] using
      (Finset.disjoint_filter_filter_not
        (Finset.univ : Finset (PointTuple params k))
        (Finset.univ : Finset (PointTuple params k))
        (fun xs : PointTuple params k => Function.Injective xs))
  have huniform_support :
      (uniformDistribution (PointTuple params k)).support = support ∪ bad := by
    simp [uniformDistribution, support, bad, Finset.filter_union_filter_not_eq]
  have hgood :
      ∑ xs ∈ support,
        |(uniformDistribution (PointTuple params k)).weight xs
          - (distinctTupleDistribution params k).weight xs|
        = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
    have hconst :
        ∀ xs ∈ support,
          |(uniformDistribution (PointTuple params k)).weight xs
            - (distinctTupleDistribution params k).weight xs|
            = (1 / (support.card : Error)) - (1 / ((params.q : Error) ^ k)) := by
      intro xs hxs
      rw [show (uniformDistribution (PointTuple params k)).weight xs =
          1 / ((params.q : Error) ^ k) by
            simp [uniformDistribution, PointTuple, Fintype.card_fin]]
      rw [show (distinctTupleDistribution params k).weight xs =
          if xs ∈ support then 1 / (support.card : Error) else 0 by
            simp [distinctTupleDistribution, support]]
      rw [if_pos hxs]
      rw [abs_of_nonpos (sub_nonpos.mpr hweight_le)]
      ring
    calc
      ∑ xs ∈ support,
          |(uniformDistribution (PointTuple params k)).weight xs
            - (distinctTupleDistribution params k).weight xs|
        = ∑ xs ∈ support, ((1 / (support.card : Error)) - (1 / ((params.q : Error) ^ k))) := by
            exact Finset.sum_congr rfl hconst
      _ = (support.card : Error) *
          ((1 / (support.card : Error)) - (1 / ((params.q : Error) ^ k))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
            field_simp [hsupport_card_ne, hqpow_ne]
  have htv_eq :
      totalVariationDistance (uniformDistribution (PointTuple params k))
          (distinctTupleDistribution params k)
        = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
    have hsupp_union :
        (uniformDistribution (PointTuple params k)).support
          ∪ (distinctTupleDistribution params k).support
          = support ∪ bad := by
      simp [uniformDistribution, distinctTupleDistribution, support, bad,
        Finset.filter_union_filter_not_eq]
    have hbad :
        ∑ xs ∈ bad,
          |(uniformDistribution (PointTuple params k)).weight xs
            - (distinctTupleDistribution params k).weight xs|
          = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
      calc
        ∑ xs ∈ bad,
            |(uniformDistribution (PointTuple params k)).weight xs
              - (distinctTupleDistribution params k).weight xs|
          = ∑ xs ∈ bad, (1 / ((params.q : Error) ^ k)) := by
              apply Finset.sum_congr rfl
              intro xs hxs
              have hnotinj : ¬ Function.Injective xs := (Finset.mem_filter.mp hxs).2
              rw [show (uniformDistribution (PointTuple params k)).weight xs =
                  1 / ((params.q : Error) ^ k) by
                    simp [uniformDistribution, PointTuple, Fintype.card_fin]]
              rw [show (distinctTupleDistribution params k).weight xs =
                  if xs ∈ support then 1 / (support.card : Error) else 0 by
                    simp [distinctTupleDistribution, support]]
              rw [if_neg fun hmem => hnotinj ((Finset.mem_filter.mp hmem).2)]
              simp
        _ = (bad.card : Error) / ((params.q : Error) ^ k) := by
              simp [div_eq_mul_inv]
        _ = 1 - (support.card : Error) / ((params.q : Error) ^ k) := by
              field_simp [hqpow_ne]
              nlinarith [hpartition_cast]
    rw [totalVariationDistance, hsupp_union, Finset.sum_union hdisj]
    simp [hgood, hbad]
    ring
  have hsupport_term :
      avgOver (distinctTupleDistribution params k) F ≤
        ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs +
          totalVariationDistance (uniformDistribution (PointTuple params k)) (
              distinctTupleDistribution params k) := by
    calc
      avgOver (distinctTupleDistribution params k) F
        = ∑ xs ∈ support, (distinctTupleDistribution params k).weight xs * F xs := by
            simp [avgOver, distinctTupleDistribution, support]
      _ ≤ ∑ xs ∈ support,
            ((uniformDistribution (PointTuple params k)).weight xs * F xs +
              |(uniformDistribution (PointTuple params k)).weight xs -
                (distinctTupleDistribution params k).weight xs|) := by
            refine Finset.sum_le_sum ?_
            intro xs hxs
            have hFx_le := hF_le_one xs
            have hw :
                (uniformDistribution (PointTuple params k)).weight xs ≤
                  (distinctTupleDistribution params k).weight xs := by
              rw [show (uniformDistribution (PointTuple params k)).weight xs =
                  1 / ((params.q : Error) ^ k) by
                    simp [uniformDistribution, PointTuple, Fintype.card_fin]]
              rw [show (distinctTupleDistribution params k).weight xs =
                  if xs ∈ support then 1 / (support.card : Error) else 0 by
                    simp [distinctTupleDistribution, support]]
              rw [if_pos hxs]
              exact hweight_le
            have habs :
                |(uniformDistribution (PointTuple params k)).weight xs -
                    (distinctTupleDistribution params k).weight xs| =
                  (distinctTupleDistribution params k).weight xs -
                    (uniformDistribution (PointTuple params k)).weight xs := by
              rw [abs_of_nonpos (sub_nonpos.mpr hw)]
              ring
            have hdelta_nonneg :
                0 ≤ (distinctTupleDistribution params k).weight xs -
                    (uniformDistribution (PointTuple params k)).weight xs := by
              linarith
            have hmul :
                ((distinctTupleDistribution params k).weight xs -
                    (uniformDistribution (PointTuple params k)).weight xs) * F xs ≤
                  (distinctTupleDistribution params k).weight xs -
                    (uniformDistribution (PointTuple params k)).weight xs := by
              have := mul_le_mul_of_nonneg_left hFx_le hdelta_nonneg
              simpa [one_mul] using this
            have hsplit :
                (distinctTupleDistribution params k).weight xs * F xs =
                  (uniformDistribution (PointTuple params k)).weight xs * F xs +
                    ((distinctTupleDistribution params k).weight xs -
                      (uniformDistribution (PointTuple params k)).weight xs) * F xs := by
              ring
            rw [hsplit]
            rw [habs]
            linarith
      _ = ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs +
            ∑ xs ∈ support,
              |(uniformDistribution (PointTuple params k)).weight xs -
                (distinctTupleDistribution params k).weight xs| := by
            rw [Finset.sum_add_distrib]
      _ = ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs +
            totalVariationDistance (uniformDistribution (PointTuple params k)) (
                distinctTupleDistribution params k) := by
            rw [hgood, htv_eq]
  have hsupport_le_uniform :
      ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs ≤
        avgOver (uniformDistribution (PointTuple params k)) F := by
    have hbad_nonneg :
        0 ≤ ∑ xs ∈ bad, (uniformDistribution (PointTuple params k)).weight xs * F xs := by
      exact Finset.sum_nonneg fun xs _ =>
        mul_nonneg ((uniformDistribution (PointTuple params k)).nonnegative xs) (hF_nonneg xs)
    calc
      ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs
        ≤ ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs +
            ∑ xs ∈ bad, (uniformDistribution (PointTuple params k)).weight xs * F xs := by
              linarith
      _ = avgOver (uniformDistribution (PointTuple params k)) F := by
            rw [avgOver, huniform_support, Finset.sum_union hdisj]
  calc
    avgOver (distinctTupleDistribution params k) F
      ≤ ∑ xs ∈ support, (uniformDistribution (PointTuple params k)).weight xs * F xs +
          totalVariationDistance (uniformDistribution (PointTuple params k)) (
              distinctTupleDistribution params k) := hsupport_term
    _ ≤ avgOver (uniformDistribution (PointTuple params k)) F +
          totalVariationDistance (uniformDistribution (PointTuple params k)) (
              distinctTupleDistribution params k) := by
            linarith [hsupport_le_uniform]

lemma avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k
    (params : Parameters) [FieldModel params.q]
    (k : ℕ)
    (F : PointTuple params k → Error)
    (hF_nonneg : ∀ xs, 0 ≤ F xs)
    (hF_le_one : ∀ xs, F xs ≤ 1) :
    avgOver (distinctTupleDistribution params k) F
      ≤ avgOver (uniformDistribution (PointTuple params k)) F
        + totalVariationDistance
            (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k) := by
  classical
  by_cases hk : k ≤ params.q
  · exact avgOver_distinct_bounded_le_avgOver_uniform_add_tv params k hk F hF_nonneg hF_le_one
  · have hkq : params.q < k := lt_of_not_ge hk
    let support : Finset (PointTuple params k) :=
      Finset.univ.filter fun xs : PointTuple params k => Function.Injective xs
    have hsupport_card : support.card = params.q.descFactorial k := by
      rw [← Fintype.card_coe]
      let e : { xs : PointTuple params k // Function.Injective xs } ≃ (Fin k ↪ Fq params) :=
        Equiv.subtypeInjectiveEquivEmbedding (Fin k) (Fq params)
      simpa [support, Finset.mem_filter] using
        (Fintype.card_congr e).trans Fintype.card_embedding_eq
    have hsupport_empty : support = ∅ := by
      apply Finset.card_eq_zero.mp
      rw [hsupport_card]
      exact Nat.descFactorial_eq_zero_iff_lt.mpr hkq
    have hdistinct_zero : avgOver (distinctTupleDistribution params k) F = 0 := by
      unfold avgOver
      simp [distinctTupleDistribution, support, hsupport_empty]
    have hright_nonneg :
        0 ≤ avgOver (uniformDistribution (PointTuple params k)) F +
            totalVariationDistance
              (uniformDistribution (PointTuple params k))
              (distinctTupleDistribution params k) := by
      have hunif_nonneg : 0 ≤ avgOver (uniformDistribution (PointTuple params k)) F := by
        unfold avgOver
        exact Finset.sum_nonneg fun xs _ =>
          mul_nonneg ((uniformDistribution (PointTuple params k)).nonnegative xs) (hF_nonneg xs)
      have htv_nonneg :
          0 ≤ totalVariationDistance
            (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k) := by
        unfold totalVariationDistance
        positivity
      linarith
    rw [hdistinct_zero]
    exact hright_nonneg

lemma max_zero_add_le
    (a t : Error) (ha : 0 ≤ a) :
    max 0 (a + t) ≤ a + max 0 t := by
  by_cases ht : 0 ≤ t
  · rw [max_eq_right (add_nonneg ha ht), max_eq_right ht]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    by_cases hat : 0 ≤ a + t
    · rw [max_eq_right hat, max_eq_left ht']
      linarith
    · have hat' : a + t ≤ 0 := le_of_not_ge hat
      rw [max_eq_left hat', max_eq_left ht']
      linarith

lemma max_zero_mul_add_le
    (w a t : Error)
    (hw : 0 ≤ w) :
    max 0 (w * a + t) ≤ w * max 0 a + max 0 t := by
  have hwa : w * a ≤ w * max 0 a := by
    exact mul_le_mul_of_nonneg_left (le_max_right 0 a) hw
  calc
    max 0 (w * a + t) ≤ max 0 (w * max 0 a + t) := by
      have hadd : w * a + t ≤ w * max 0 a + t := by linarith
      exact max_le_max le_rfl hadd
    _ ≤ w * max 0 a + max 0 t := by
      exact max_zero_add_le (w * max 0 a) t (mul_nonneg hw (by positivity))

lemma max_zero_avgOver_le_avgOver_max_zero
    {α : Type*}
    (𝒟 : Distribution α)
    (f : α → Error) :
    max 0 (avgOver 𝒟 f) ≤ avgOver 𝒟 (fun a => max 0 (f a)) := by
  classical
  unfold avgOver
  induction 𝒟.support using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      calc
        max 0 (𝒟.weight a * f a + ∑ x ∈ s, 𝒟.weight x * f x)
          ≤ 𝒟.weight a * max 0 (f a) + max 0 (∑ x ∈ s, 𝒟.weight x * f x) := by
              exact max_zero_mul_add_le (𝒟.weight a) (f a)
                (∑ x ∈ s, 𝒟.weight x * f x) (𝒟.nonnegative a)
        _ ≤ 𝒟.weight a * max 0 (f a) + ∑ x ∈ s, 𝒟.weight x * max 0 (f x) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right ih (𝒟.weight a * max 0 (f a))

lemma qBipartiteMatchMass_averageIdxSubMeas_left
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : SubMeas Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    qBipartiteMatchMass ψ (averageIdxSubMeas 𝒟 A h𝒟) B =
      avgOver 𝒟 (fun q => qBipartiteMatchMass ψ (A q) B) := by
  classical
  unfold qBipartiteMatchMass avgOver averageIdxSubMeas
  calc
    ∑ a,
        ev ψ
          (opTensor (averageOperatorOverDistribution 𝒟 (fun q => (A q).outcome a))
            (B.outcome a))
      = ∑ a,
          ev ψ
            (averageOperatorOverDistribution 𝒟
              (fun q => opTensor ((A q).outcome a) (B.outcome a))) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              exact congrArg (ev ψ)
                (opTensor_averageOperatorOverDistribution_left 𝒟
                  (fun q => (A q).outcome a) (B.outcome a))
    _ = ∑ a, ∑ q ∈ 𝒟.support, 𝒟.weight q * ev ψ (opTensor ((A q).outcome a) (B.outcome a)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          unfold averageOperatorOverDistribution
          rw [ev_finset_sum]
          refine Finset.sum_congr rfl ?_
          intro q _
          simpa using ev_scale ψ (𝒟.weight q)
            (opTensor ((A q).outcome a) (B.outcome a))
    _ = ∑ q ∈ 𝒟.support, ∑ a, 𝒟.weight q * ev ψ (opTensor ((A q).outcome a) (B.outcome a)) := by
          rw [Finset.sum_comm]
    _ = ∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a, ev ψ (opTensor ((A q).outcome a) (B.outcome a)) := by
          refine Finset.sum_congr rfl ?_
          intro q _
          rw [← Finset.mul_sum]
    _ = avgOver 𝒟 (fun q => qBipartiteMatchMass ψ (A q) B) := by
          simp [avgOver, qBipartiteMatchMass]

lemma ev_opTensor_total_averageIdxSubMeas_left
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : SubMeas Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    ev ψ (opTensor (averageIdxSubMeas 𝒟 A h𝒟).total B.total) =
      avgOver 𝒟 (fun q => ev ψ (opTensor (A q).total B.total)) := by
  classical
  unfold avgOver averageIdxSubMeas
  change ev ψ (opTensor (averageOperatorOverDistribution 𝒟 (fun q => (A q).total)) B.total) = _
  rw [opTensor_averageOperatorOverDistribution_left]
  unfold averageOperatorOverDistribution
  rw [ev_finset_sum]
  refine Finset.sum_congr rfl ?_
  intro q _
  simpa using ev_scale ψ (𝒟.weight q) (opTensor (A q).total B.total)

lemma qBipartiteConsDefect_averageIdxSubMeas_left_le
    {Question Outcome : Type*}
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι)
    (B : SubMeas Outcome ι)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    qBipartiteConsDefect ψ (averageIdxSubMeas 𝒟 A h𝒟) B ≤
      avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q) B) := by
  have htotal := ev_opTensor_total_averageIdxSubMeas_left ψ 𝒟 A B h𝒟
  have hmatch := qBipartiteMatchMass_averageIdxSubMeas_left ψ 𝒟 A B h𝒟
  rw [qBipartiteConsDefect, htotal, hmatch]
  rw [← avgOver_sub]
  exact le_trans
    (max_zero_avgOver_le_avgOver_max_zero 𝒟
      (fun q => ev ψ (opTensor (A q).total B.total) - qBipartiteMatchMass ψ (A q) B)) <| by
        refine avgOver_mono 𝒟 _ _ ?_
        intro q
        simp [qBipartiteConsDefect]

lemma hBConsistency_fixed_u_defect_le_avgOver_distinct
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (k : ℕ)
    (u : Point params) :
    qBipartiteConsDefect strategy.state
      (hRestrictionToVerticalLine params (constructedPastedSubMeas params family k) u)
      (verticalLineMeasurementFamily params strategy u) ≤
        avgOver (distinctTupleDistribution params k)
          (fun xs =>
            qBipartiteConsDefect strategy.state
              (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
              (verticalLineMeasurementFamily params strategy u)) := by
  have hleft :
      hRestrictionToVerticalLine params (constructedPastedSubMeas params family k) u =
        averageIdxSubMeas
          (distinctTupleDistribution params k)
          (fun xs => hRestrictionToVerticalLine params (
              pastedInterpolationFamily params family k xs) u)
          (distinctTupleDistribution_weight_sum_le_one params k) := by
    simpa [constructedPastedSubMeas] using
      hRestrictionToVerticalLine_averageIdxSubMeas (params := params) u
        (distinctTupleDistribution params k)
        (pastedInterpolationFamily params family k)
        (distinctTupleDistribution_weight_sum_le_one params k)
  rw [hleft]
  exact qBipartiteConsDefect_averageIdxSubMeas_left_le strategy.state
    (distinctTupleDistribution params k)
    (fun xs => hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
    (verticalLineMeasurementFamily params strategy u)
    (distinctTupleDistribution_weight_sum_le_one params k)

lemma hBConsistencyError_eq_k_mul_ldSandwichLineOnePointError_add
    (params : Parameters)
    (eps delta gamma zeta : Error) (k : ℕ) :
    hBConsistencyError params eps delta gamma zeta k =
      (k : Error) * ldSandwichLineOnePointError params eps delta gamma zeta k +
        ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow gamma (1 / (32 : Error)) +
            Real.rpow zeta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
  simp [hBConsistencyError, ldSandwichLineOnePointError]
  ring

lemma avgOver_sum_fin
    {α : Type*} (𝒟 : Distribution α) (k : ℕ) (f : α → Fin k → Error) :
    avgOver 𝒟 (fun a => ∑ i : Fin k, f a i) =
      ∑ i : Fin k, avgOver 𝒟 (fun a => f a i) :=
  avgOver_sum 𝒟 f

lemma one_div_q_le_rpow_degreeRatio
    (params : Parameters) [FieldModel params.q]
    (hd : 0 < params.d) :
    1 / (params.q : Error)
      ≤ Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error)) := by
  let x : Error := ((params.d : Error) / (params.q : Error))
  have hq_pos : 0 < (params.q : Error) := by exact_mod_cast params.hq
  have hx_nonneg : 0 ≤ x := by positivity
  have hqx : 1 / (params.q : Error) ≤ x := by
    have hd_ge_one : (1 : Error) ≤ (params.d : Error) := by exact_mod_cast hd
    simpa [x] using div_le_div_of_nonneg_right hd_ge_one hq_pos.le
  by_cases hx_le_one : x ≤ 1
  · have hx_le_rpow : x ≤ Real.rpow x (1 / (32 : Error)) := by
      simpa [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge' hx_nonneg hx_le_one (by norm_num : 0
            ≤ (1 / (32 : Error)))
          (by norm_num : (1 / (32 : Error)) ≤ (1 : Error)))
    exact le_trans hqx hx_le_rpow
  · have h1_le_x : (1 : Error) ≤ x := le_of_not_ge hx_le_one
    have hq_le_one : 1 / (params.q : Error) ≤ 1 := by
      have hq_ge_one : (1 : Error) ≤ (params.q : Error) := by exact_mod_cast params.hq
      have hq_ne : (params.q : Error) ≠ 0 := by positivity
      field_simp [hq_ne]
      nlinarith
    have h1_le_rpow : (1 : Error) ≤ Real.rpow x (1 / (32 : Error)) := by
      simpa [Real.rpow_one] using
        (Real.rpow_le_rpow (show 0 ≤ (1 : Error) by positivity) h1_le_x (show 0
            ≤ (1 / (32 : Error)) by positivity))
    exact le_trans hq_le_one h1_le_rpow

lemma dnoteq_term_le_hBConsistency_extra
    (params : Parameters) [FieldModel params.q]
    (eps delta gamma zeta : Error)
    (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    ((k : Error) ^ (2 : ℕ)) / (params.q : Error)
      ≤ ((k : Error) ^ (2 : ℕ)) * (params.m : Error) *
          (Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow gamma (1 / (32 : Error)) +
            Real.rpow zeta (1 / (32 : Error)) +
            Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) := by
  let S : Error :=
    Real.rpow eps (1 / (32 : Error)) +
      Real.rpow delta (1 / (32 : Error)) +
      Real.rpow gamma (1 / (32 : Error)) +
      Real.rpow zeta (1 / (32 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
  have hqterm : 1 / (params.q : Error) ≤ S := by
    have hlast := one_div_q_le_rpow_degreeRatio params hd
    have htail_nonneg :
        0 ≤ Real.rpow eps (1 / (32 : Error)) +
            Real.rpow delta (1 / (32 : Error)) +
            Real.rpow gamma (1 / (32 : Error)) +
            Real.rpow zeta (1 / (32 : Error)) :=
      add_nonneg
        (add_nonneg
          (add_nonneg
            (Real.rpow_nonneg heps_nonneg _)
            (Real.rpow_nonneg hdelta_nonneg _))
          (Real.rpow_nonneg hgamma_nonneg _))
        (Real.rpow_nonneg hzeta_nonneg _)
    dsimp [S] at *
    nlinarith
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast (Nat.succ_le_of_lt params.hm)
  have hS_le_mS : S ≤ (params.m : Error) * S := by
    have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      positivity [heps_nonneg, hdelta_nonneg, hgamma_nonneg, hzeta_nonneg]
    nlinarith
  have hqterm' : 1 / (params.q : Error) ≤ (params.m : Error) * S :=
    le_trans hqterm hS_le_mS
  have hk_nonneg : 0 ≤ ((k : Error) ^ (2 : ℕ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hqterm' hk_nonneg
  simpa [S, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul

lemma hBConsistency_error_bound
    (params : Parameters) [FieldModel params.q]
    (eps delta gamma zeta : Error)
    (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta) :
    (k : Error) * ldSandwichLineOnePointError params eps delta gamma zeta k +
        ((k : Error) ^ (2 : ℕ)) / (params.q : Error)
      ≤ hBConsistencyError params eps delta gamma zeta k := by
  rw [hBConsistencyError_eq_k_mul_ldSandwichLineOnePointError_add]
  have hextra := dnoteq_term_le_hBConsistency_extra params eps delta gamma zeta k hd
    heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg
  linarith

lemma avgOver_distinct_pasted_defect_le_badMass
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) :
    avgOver (distinctTupleDistribution params k) (fun xs =>
      qBipartiteConsDefect strategy.state
        (hRestrictionToVerticalLine params (pastedInterpolationFamily params family k xs) u)
        (verticalLineMeasurementFamily params strategy u))
      ≤ avgOver (distinctTupleDistribution params k) (fun xs =>
          hBConsistencyBadMass params strategy family u xs) := by
  classical
  let support : Finset (PointTuple params k) :=
    Finset.univ.filter fun xs : PointTuple params k => Function.Injective xs
  have hsupport : (distinctTupleDistribution params k).support = support := by
    simp [distinctTupleDistribution, support]
  have hweight :
      ∀ xs, (distinctTupleDistribution params k).weight xs =
        if xs ∈ support then 1 / (support.card : Error) else 0 := by
    intro xs
    simp [distinctTupleDistribution, support]
  unfold avgOver
  rw [hsupport]
  simp_rw [hweight]
  refine Finset.sum_le_sum ?_
  intro xs hxs
  have hinj : Function.Injective xs := (Finset.mem_filter.mp hxs).2
  simp [hxs]
  exact mul_le_mul_of_nonneg_left
    (pastedInterpolation_verticalLine_defect_le_badMass params strategy family u xs hinj)
    (by positivity)

lemma avgOver_distinct_badMass_le_avgOver_uniform_badMass_add_dnoteq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k : ℕ} (u : Point params) :
    avgOver (distinctTupleDistribution params k) (fun xs =>
      hBConsistencyBadMass params strategy family u xs)
      ≤ avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs) +
          ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
  calc
    avgOver (distinctTupleDistribution params k) (fun xs =>
        hBConsistencyBadMass params strategy family u xs)
      ≤ avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs) +
          totalVariationDistance
            (uniformDistribution (PointTuple params k))
            (distinctTupleDistribution params k) := by
            exact avgOver_distinct_bounded_le_avgOver_uniform_add_tv_of_any_k params k
              (fun xs => hBConsistencyBadMass params strategy family u xs)
              (fun xs => hBConsistencyBadMass_nonneg params strategy family u xs)
              (fun xs => hBConsistencyBadMass_le_one params strategy family u xs)
    _ ≤ avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs) +
          ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
            gcongr
            exact ldDnoteq params k

lemma avgOver_uniform_badMass_le_k_mul_ldSandwichLineOnePointError
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error)
    (k : ℕ)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    avgOver (uniformDistribution (Point params)) (fun u =>
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        hBConsistencyBadMass params strategy family u xs))
      ≤ (k : Error) * ldSandwichLineOnePointError params eps delta gamma zeta k := by
  let defect : Fin k → SandwichedLineQuestion params k → Error := fun i q =>
    qBipartiteConsDefect strategy.state
      ((ldSandwichLineOnePointLeftFamily params strategy family k i.1) q)
      ((ldSandwichLineOnePointRightFamily params strategy family k i.1) q)
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
      avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
        hBConsistencyBadMass params strategy family u xs))
      ≤ avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            ∑ i : Fin k, defect i (u, xs))) := by
            exact avgOver_mono _ _ _ (fun u =>
              avgOver_mono _ _ _ (fun xs =>
                hBConsistencyBadMass_le_linePointDefectSum params strategy family u xs))
    _ = avgOver (uniformDistribution (Point params)) (fun u =>
          ∑ i : Fin k,
            avgOver (uniformDistribution (PointTuple params k)) (fun xs => defect i (u, xs))) := by
          apply avgOver_congr
          intro u
          exact avgOver_sum_fin (uniformDistribution (PointTuple params k)) k (fun xs i
              => defect i (u, xs))
    _ = ∑ i : Fin k,
          avgOver (uniformDistribution (Point params)) (fun u =>
            avgOver (uniformDistribution (PointTuple params k)) (fun xs => defect i (u, xs))) := by
          exact (avgOver_sum_fin (uniformDistribution (Point params)) k
            (fun u i => avgOver (uniformDistribution (PointTuple params k)) (fun xs => defect i (u,
                xs))))
    _ = ∑ i : Fin k,
          avgOver (uniformDistribution (SandwichedLineQuestion params k))
            (fun q => defect i q) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          simpa [SandwichedLineQuestion] using
            (avgOver_uniform_prod (f := fun u xs => defect i (u, xs))).symm
    _ ≤ ∑ i : Fin k, ldSandwichLineOnePointError params eps delta gamma zeta k := by
          refine Finset.sum_le_sum ?_
          intro i _
          exact (hline i.1 i.2).linePointComparison.offDiagonalBound
    _ = (k : Error) * ldSandwichLineOnePointError params eps delta gamma zeta k := by
          simp

/-- Aggregate the one-point line comparison statements over all inserted vertical
lines and absorb the distinct-tuple loss into the displayed `hBConsistency`
error.

This is the reusable bad-mass aggregation from `ld-pasting.tex` lines
1186--1202 (also used in the proof of `lem:h-b-consistency`). -/
lemma avgOver_distinct_badMass_le_hBConsistencyError
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (eps delta gamma zeta : Error) (k : ℕ)
    (hd : 0 < params.d)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hline : ∀ i : ℕ, i < k →
      LdSandwichLineOnePointStatement params strategy family
        eps delta gamma zeta k i) :
    avgOver (uniformDistribution (Point params)) (fun u =>
        avgOver (distinctTupleDistribution params k) (fun xs =>
          hBConsistencyBadMass params strategy family u xs)) ≤
      hBConsistencyError params eps delta gamma zeta k := by
  calc
    avgOver (uniformDistribution (Point params)) (fun u =>
        avgOver (distinctTupleDistribution params k) (fun xs =>
          hBConsistencyBadMass params strategy family u xs))
      ≤ avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs) +
          ((k : Error) ^ (2 : ℕ)) / (params.q : Error)) := by
          exact avgOver_mono _ _ _ (fun u =>
            avgOver_distinct_badMass_le_avgOver_uniform_badMass_add_dnoteq
              params strategy family u)
    _ = avgOver (uniformDistribution (Point params)) (fun u =>
          avgOver (uniformDistribution (PointTuple params k)) (fun xs =>
            hBConsistencyBadMass params strategy family u xs)) +
        ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
          rw [avgOver_add]
          simpa using avgOver_uniform_const (α := Point params)
            (((k : Error) ^ (2 : ℕ)) / (params.q : Error))
    _ ≤ (k : Error) * ldSandwichLineOnePointError params eps delta gamma zeta k +
          ((k : Error) ^ (2 : ℕ)) / (params.q : Error) := by
          gcongr
          exact avgOver_uniform_badMass_le_k_mul_ldSandwichLineOnePointError
            params strategy family eps delta gamma zeta k hline
    _ ≤ hBConsistencyError params eps delta gamma zeta k := by
          exact hBConsistency_error_bound params eps delta gamma zeta k hd
            heps_nonneg hdelta_nonneg hgamma_nonneg hzeta_nonneg

/- private lemma interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (σ : Finset (Fin k))
    (hσsubset : σ ⊆ gHatTupleSupport gs)
    (hσcard : σ.card = params.d + 1)
    {i : Fin k} (hi : i ∈ σ) :
    MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
      (interpolateCompletedSlicesFromSupport params xs gs σ hσcard).poly =
      ((gs i).get (by simpa [gHatTupleSupport] using hσsubset hi)).poly := by
  let v : Fin k → Scalar params.next := fun j => decodeScalar (xs j)
  have hgi : (gs i).isSome = true := by
    simpa [gHatTupleSupport] using hσsubset hi
  have hvinj : Set.InjOn v (↑σ : Set (Fin k)) := by
    intro a ha b hb hab
    apply hxs
    simpa [v] using congrArg encodeScalar hab
  have hcomp :
      ((MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
        MvPolynomial.C) = MvPolynomial.C := by
    ext r
    simp
  have hx :
      MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.X (lastCoord params)) =
        MvPolynomial.C (decodeScalar (xs i)) := by
    simp [Polynomial.restrictAtHeightCoordinateMap, lastCoord]
  have hx' :
      Polynomial.restrictAtHeightCoordinateMap params (xs i) (lastCoord params) =
        MvPolynomial.C (decodeScalar (xs i)) := by
    simp [Polynomial.restrictAtHeightCoordinateMap, lastCoord]
  unfold interpolateCompletedSlicesFromSupport
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs i))) =
          extractSliceOr0 (gs i) := by
            rw [MvPolynomial.eval₂Hom_rename, MvPolynomial.eval₂Hom_C_eq_bind₁]
            have hmap :
                Polynomial.restrictAtHeightCoordinateMap params (xs i) ∘ embedCoord params =
                  MvPolynomial.X := by
              funext j
              simp [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord]
            rw [hmap, MvPolynomial.bind₁_X_left]
            rfl
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i))) = 1 := by
            calc
              MvPolynomial.eval₂Hom MvPolynomial.C
                  (Polynomial.restrictAtHeightCoordinateMap params (xs i))
                  (_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
                    (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i))
                  = _root_.Polynomial.eval₂
                      (((MvPolynomial.eval₂Hom MvPolynomial.C
                          (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                        MvPolynomial.C))
                      (MvPolynomial.eval₂Hom MvPolynomial.C
                        (Polynomial.restrictAtHeightCoordinateMap params (xs i))
                        (MvPolynomial.X (lastCoord params)))
                      (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i) := by
                        simpa using (_root_.Polynomial.hom_eval₂
                          (p := Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i)
                          (f := MvPolynomial.C)
                          (g := MvPolynomial.eval₂Hom MvPolynomial.C
                            (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                          (x := MvPolynomial.X (lastCoord params)))
              _ = _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.C (decodeScalar (xs i)))
                    (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i) := by
                      calc
                        _root_.Polynomial.eval₂
                            ((MvPolynomial.eval₂Hom MvPolynomial.C
                                (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                              MvPolynomial.C)
                            ((MvPolynomial.eval₂Hom MvPolynomial.C
                                (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                              (MvPolynomial.X (lastCoord params)))
                            (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i)
                            = _root_.Polynomial.eval₂
                                ((MvPolynomial.eval₂Hom MvPolynomial.C
                                    (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                                  MvPolynomial.C)
                                (MvPolynomial.C (decodeScalar (xs i)))
                                (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i) := by
                                  simpa using congrArg
                                    (fun x =>
                                      _root_.Polynomial.eval₂
                                        ((MvPolynomial.eval₂Hom MvPolynomial.C
                                            (Polynomial.restrictAtHeightCoordinateMap
                                              params (xs i))).comp
                                          MvPolynomial.C)
                                        x (Lagrange.basis σ
                                        (fun j : Fin k =>
                                        decodeScalar (xs j))
                                        i))
                                    hx
                        _ = _root_.Polynomial.eval₂ MvPolynomial.C
                        (MvPolynomial.C (decodeScalar (xs i)))
                              (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i) := by
                                simpa [MvPolynomial.eval₂Hom] using congrArg
                                  (fun F =>
                                    _root_.Polynomial.eval₂ F (MvPolynomial.C (decodeScalar (xs i)))
                                      (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i))
                                  hcomp
              _ = 1 := by
                    rw [_root_.Polynomial.eval₂_at_apply]
                    simpa using congrArg
                      (fun x : Scalar params => (MvPolynomial.C x : PolynomialModel params))
                      (Lagrange.eval_basis_self hvinj hi)
    have hextract {o : GHatOutcome params} (ho : o.isSome = true) :
        extractSliceOr0 o = (o.get ho).poly := by
      cases o with
      | none => simp at ho
      | some p => simp [extractSliceOr0]
    rw [hLi, hslice, hextract hgi]
    simp
  · intro j hj hji
    simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs j))) =
          extractSliceOr0 (gs j) := by
            rw [MvPolynomial.eval₂Hom_rename, MvPolynomial.eval₂Hom_C_eq_bind₁]
            have hmap :
                Polynomial.restrictAtHeightCoordinateMap params (xs i) ∘ embedCoord params =
                  MvPolynomial.X := by
              funext m
              simp [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord]
            rw [hmap, MvPolynomial.bind₁_X_left]
            rfl
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j))) = 0 := by
            calc
              MvPolynomial.eval₂Hom MvPolynomial.C
                  (Polynomial.restrictAtHeightCoordinateMap params (xs i))
                  (_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
                    (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j))
                  = _root_.Polynomial.eval₂
                      (((MvPolynomial.eval₂Hom MvPolynomial.C
                          (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                        MvPolynomial.C))
                      (MvPolynomial.eval₂Hom MvPolynomial.C
                        (Polynomial.restrictAtHeightCoordinateMap params (xs i))
                        (MvPolynomial.X (lastCoord params)))
                      (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j) := by
                        simpa using (_root_.Polynomial.hom_eval₂
                          (p := Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j)
                          (f := MvPolynomial.C)
                          (g := MvPolynomial.eval₂Hom MvPolynomial.C
                            (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                          (x := MvPolynomial.X (lastCoord params)))
              _ = _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.C (decodeScalar (xs i)))
                    (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j) := by
                      calc
                        _root_.Polynomial.eval₂
                            ((MvPolynomial.eval₂Hom MvPolynomial.C
                                (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                              MvPolynomial.C)
                            ((MvPolynomial.eval₂Hom MvPolynomial.C
                                (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
                              (MvPolynomial.X (lastCoord params)))
                            (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j)
                            = _root_.Polynomial.eval₂
                                ((MvPolynomial.eval₂Hom MvPolynomial.C
                                    (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                                  MvPolynomial.C)
                                (MvPolynomial.C (decodeScalar (xs i)))
                                (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j) := by
                                  simpa using congrArg
                                    (fun x =>
                                      _root_.Polynomial.eval₂
                                        ((MvPolynomial.eval₂Hom MvPolynomial.C
                                            (Polynomial.restrictAtHeightCoordinateMap
                                              params (xs i))).comp
                                          MvPolynomial.C)
                                        x (Lagrange.basis σ
                                        (fun j : Fin k =>
                                        decodeScalar (xs j))
                                        j))
                                    hx
                        _ = _root_.Polynomial.eval₂ MvPolynomial.C
                        (MvPolynomial.C (decodeScalar (xs i)))
                              (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j) := by
                                simpa [MvPolynomial.eval₂Hom] using congrArg
                                  (fun F =>
                                    _root_.Polynomial.eval₂ F (MvPolynomial.C (decodeScalar (xs i)))
                                      (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j))
                                  hcomp
              _ = 0 := by
                    have hbasis :
                        (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j).eval
                          (decodeScalar (xs i)) = 0 := by
                      simpa using
                        (Lagrange.eval_basis_of_ne
                          (s := σ) (v := fun j : Fin k => decodeScalar (xs j))
                          (i := j) (j := i) hji hi)
                    rw [_root_.Polynomial.eval₂_at_apply]
                    simpa using congrArg
                      (fun x : Scalar params => (MvPolynomial.C x : PolynomialModel params))
                      hbasis
    rw [hLi, hslice]
    simp
  · intro hnot
    exact (hnot hi).elim -/

lemma not_interpolationEligible_exists_none
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (gs : GHatTupleOutcome params k)
    (hk : params.d + 1 ≤ k)
    (hNot : ¬ InterpolationEligible params gs) :
    ∃ i : Fin k, (gs i).isSome = false := by
  by_contra hnone
  push_neg at hnone
  apply hNot
  unfold InterpolationEligible gHatTupleHammingWeight gHatTupleSupport
  have hfull : (Finset.univ.filter fun i : Fin k => (gs i).isSome).card = k := by
    have hEq : (Finset.univ.filter fun i : Fin k => (gs i).isSome) = Finset.univ := by
      refine Finset.eq_univ_iff_forall.2 ?_
      intro i
      simp [hnone i]
    simp [hEq]
  rw [hfull]
  exact hk

lemma qBipartiteConsDefect_eq_false_mass_of_bool_right_true
    (ψ : QuantumState (ι × ι))
    (A B : SubMeas Bool ι)
    (hfalse : B.outcome false = 0)
    (htrue : B.outcome true = B.total) :
    qBipartiteConsDefect ψ A B = ev ψ (opTensor (A.outcome false) B.total) := by
  have hsumA : A.outcome false + A.outcome true = A.total := by
    simpa [add_comm] using A.sum_eq_total
  have hsumB : B.outcome false + B.outcome true = B.total := by
    simpa [add_comm] using B.sum_eq_total
  have hnonneg : 0 ≤ ev ψ (opTensor (A.outcome false) B.total) := by
    exact ev_nonneg_of_psd ψ _ <| opTensor_nonneg (A.outcome_pos false) B.total_nonneg
  unfold qBipartiteConsDefect qBipartiteMatchMass
  simp only [Fintype.univ_bool, Finset.mem_singleton, Bool.true_eq_false,
    not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
  have hexpr :
      ev ψ (opTensor A.total B.total) -
          (ev ψ (opTensor (A.outcome true) (B.outcome true)) +
            ev ψ (opTensor (A.outcome false) (B.outcome false))) =
        ev ψ (opTensor (A.outcome false) B.total) := by
    calc
      ev ψ (opTensor A.total B.total) -
          (ev ψ (opTensor (A.outcome true) (B.outcome true)) +
            ev ψ (opTensor (A.outcome false) (B.outcome false)))
        = ev ψ (opTensor (A.outcome false + A.outcome true) B.total) -
            (ev ψ (opTensor (A.outcome true) B.total) +
              ev ψ (opTensor (A.outcome false) 0)) := by
              rw [hsumA, htrue, hfalse]
      _ = ev ψ (opTensor (A.outcome false) B.total +
            opTensor (A.outcome true) B.total) -
            (ev ψ (opTensor (A.outcome true) B.total) +
              ev ψ (opTensor (A.outcome false) 0)) := by
              rw [show opTensor (A.outcome false + A.outcome true) B.total =
                    opTensor (A.outcome false) B.total +
                      opTensor (A.outcome true) B.total from
                  Matrix.add_kronecker _ _ _]
      _ = ev ψ (opTensor (A.outcome false) B.total) := by
            have hfalse_zero : ev ψ (opTensor (A.outcome false) 0) = 0 := by
              simp [opTensor, ev]
            nlinarith [
              ev_add ψ (opTensor (A.outcome false) B.total)
                (opTensor (A.outcome true) B.total),
              hfalse_zero]
  calc
    max 0
        (ev ψ (opTensor A.total B.total) -
          (ev ψ (opTensor (A.outcome true) (B.outcome true)) +
            ev ψ (opTensor (A.outcome false) (B.outcome false))))
      = max 0 (ev ψ (opTensor (A.outcome false) B.total)) := by
          rw [hexpr]
    _ = ev ψ (opTensor (A.outcome false) B.total) := by
          rw [max_eq_right hnonneg]

/- private lemma interpolateCompletedSlicesFromSupport_restrictAtHeight_eq_get
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (σ : Finset (Fin k))
    (hσsubset : σ ⊆ gHatTupleSupport gs)
    (hσcard : σ.card = params.d + 1)
    {i : Fin k} (hi : i ∈ σ) :
    (Polynomial.restrictAtHeight params
      (interpolateCompletedSlicesFromSupport params xs gs σ hσcard) (xs i)).poly =
      ((gs i).get (by simpa [gHatTupleSupport] using hσsubset hi)).poly := by
  simpa [Polynomial.restrictAtHeight] using
    interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get
      params xs hxs gs σ hσsubset hσcard hi -/

/- private lemma interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get_active
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (σ : Finset (Fin k))
    (hσsubset : σ ⊆ gHatTupleSupport gs)
    (hσcard : σ.card = params.d + 1)
    {i : Fin k} (hi : i ∈ σ) :
    MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
      (interpolateCompletedSlicesFromSupport params xs gs σ hσcard).poly =
      ((gs i).get (by simpa [gHatTupleSupport] using hσsubset hi)).poly := by
  let v : Fin k → Scalar params.next := fun j => decodeScalar (xs j)
  have hgi : (gs i).isSome = true := by
    simpa [gHatTupleSupport] using hσsubset hi
  have hvinj : Set.InjOn v (↑σ : Set (Fin k)) := by
    intro a ha b hb hab
    apply hxs
    simpa [v] using congrArg encodeScalar hab
  have hcomp :
      ((MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
        MvPolynomial.C) = MvPolynomial.C := by
    ext r
    simp
  have hx :
      MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.X (lastCoord params)) =
        MvPolynomial.C (v i) := by
    change MvPolynomial.C (decodeScalar (xs i)) = MvPolynomial.C (v i)
    simp [v, Polynomial.restrictAtHeightCoordinateMap, lastCoord]
  unfold interpolateCompletedSlicesFromSupport
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs i))) =
          extractSliceOr0 (gs i) := by
      have h0 := MvPolynomial.eval₂Hom_rename
        (f := MvPolynomial.C)
        (g := Polynomial.restrictAtHeightCoordinateMap params (xs i))
        (k := embedCoord params)
        (p := extractSliceOr0 (gs i))
      rw [MvPolynomial.eval₂Hom_C_eq_bind₁] at h0
      have hmap :
          Polynomial.restrictAtHeightCoordinateMap params (xs i) ∘ embedCoord params =
            MvPolynomial.X := by
        funext j
        simp [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord]
      rw [hmap, MvPolynomial.bind₁_X_left] at h0
      simpa using h0
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ v i))) = 1 := by
      have h0 := (_root_.Polynomial.hom_eval₂
        (p := Lagrange.basis σ v i)
        (f := MvPolynomial.C)
        (g := MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
        (x := MvPolynomial.X (lastCoord params)))
      rw [hcomp, hx, _root_.Polynomial.eval₂_at_apply] at h0
      calc
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
            ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
              (Lagrange.basis σ v i)))
          = MvPolynomial.C ((Lagrange.basis σ v i).eval (v i)) := by
              simpa using h0
        _ = 1 := by
              simpa using congrArg
                (fun x : Scalar params.next => (MvPolynomial.C x : PolynomialModel params.next))
                (Lagrange.eval_basis_self hvinj hi)
    have hextract {o : GHatOutcome params} (ho : o.isSome = true) :
        extractSliceOr0 o = (o.get ho).poly := by
      cases o with
      | none => simp at ho
      | some p => simp [extractSliceOr0]
    rw [hslice, hLi, hextract hgi]
    simp
  · intro j hj hji
    simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs j))) =
          extractSliceOr0 (gs j) := by
      have h0 := MvPolynomial.eval₂Hom_rename
        (f := MvPolynomial.C)
        (g := Polynomial.restrictAtHeightCoordinateMap params (xs i))
        (k := embedCoord params)
        (p := extractSliceOr0 (gs j))
      rw [MvPolynomial.eval₂Hom_C_eq_bind₁] at h0
      have hmap :
          Polynomial.restrictAtHeightCoordinateMap params (xs i) ∘ embedCoord params =
            MvPolynomial.X := by
        funext m
        simp [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord]
      rw [hmap, MvPolynomial.bind₁_X_left] at h0
      simpa using h0
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ v j))) = 0 := by
      have h0 := (_root_.Polynomial.hom_eval₂
        (p := Lagrange.basis σ v j)
        (f := MvPolynomial.C)
        (g := MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
        (x := MvPolynomial.X (lastCoord params)))
      rw [hcomp, hx, _root_.Polynomial.eval₂_at_apply] at h0
      calc
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
            ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
              (Lagrange.basis σ v j)))
          = MvPolynomial.C ((Lagrange.basis σ v j).eval (v i)) := by
              simpa using h0
        _ = 0 := by
              simpa using congrArg
                (fun x : Scalar params.next => (MvPolynomial.C x : PolynomialModel params.next))
                (Lagrange.eval_basis_of_ne hji hi)
    rw [hslice, hLi]
    simp
  · intro hnot
    exact (hnot hi).elim -/

/- private lemma interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get'
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (σ : Finset (Fin k))
    (hσsubset : σ ⊆ gHatTupleSupport gs)
    (hσcard : σ.card = params.d + 1)
    {i : Fin k} (hi : i ∈ σ) :
    MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
      (interpolateCompletedSlicesFromSupport params xs gs σ hσcard).poly =
      ((gs i).get (by simpa [gHatTupleSupport] using hσsubset hi)).poly := by
  let v : Fin k → Scalar params.next := fun j => decodeScalar (xs j)
  have hgi : (gs i).isSome = true := by
    simpa [gHatTupleSupport] using hσsubset hi
  have hvinj : Set.InjOn v (↑σ : Set (Fin k)) := by
    intro a ha b hb hab
    apply hxs
    simpa [v] using congrArg encodeScalar hab
  have hcomp :
      ((MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp MvPolynomial.C) =
          MvPolynomial.C := by
    ext r
    simp
  have hx :
      MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.X (lastCoord params)) = MvPolynomial.C (v i) := by
    simpa [v, Polynomial.restrictAtHeightCoordinateMap, lastCoord]
  have hextract {o : GHatOutcome params} (ho : o.isSome = true) :
      extractSliceOr0 o = (o.get ho).poly := by
    cases o with
    | none => simp at ho
    | some p => simp [extractSliceOr0]
  unfold interpolateCompletedSlicesFromSupport
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs i))) =
          extractSliceOr0 (gs i) := by
      rw [MvPolynomial.eval₂Hom_rename]
      simpa [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord] using
        (MvPolynomial.eval₂_eta (extractSliceOr0 (gs i)))
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ v i))) = 1 := by
      have h0 := (_root_.Polynomial.hom_eval₂
        (p := Lagrange.basis σ v i)
        (f := MvPolynomial.C)
        (g := MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
        (x := MvPolynomial.X (lastCoord params)))
      rw [hcomp, hx] at h0
      have h1 := (_root_.Polynomial.eval₂_hom (p := Lagrange.basis σ v i)
        (f := MvPolynomial.C) (x := v i))
      calc
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
            ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
              (Lagrange.basis σ v i)))
          = MvPolynomial.C ((Lagrange.basis σ v i).eval (v i)) := by
              simpa using h0
        _ = 1 := by
              simpa using congrArg
                (fun x : Scalar params.next => (MvPolynomial.C x : PolynomialModel params.next))
                (Lagrange.eval_basis_self hvinj hi)
    rw [hslice, hLi, hextract hgi]
    simp
  · intro j hj hji
    simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs j))) =
          extractSliceOr0 (gs j) := by
      rw [MvPolynomial.eval₂Hom_rename]
      simpa [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord] using
        (MvPolynomial.eval₂_eta (extractSliceOr0 (gs j)))
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ v j))) = 0 := by
      have h0 := (_root_.Polynomial.hom_eval₂
        (p := Lagrange.basis σ v j)
        (f := MvPolynomial.C)
        (g := MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
        (x := MvPolynomial.X (lastCoord params)))
      rw [hcomp, hx] at h0
      calc
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
            ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
              (Lagrange.basis σ v j)))
          = MvPolynomial.C ((Lagrange.basis σ v j).eval (v i)) := by
              simpa using h0
        _ = 0 := by
              simpa using congrArg
                (fun x : Scalar params.next => (MvPolynomial.C x : PolynomialModel params.next))
                (Lagrange.eval_basis_of_ne hji hi)
    rw [hslice, hLi]
    simp
  · intro hnot
    exact (hnot hi).elim -/

/- private lemma interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get'
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (σ : Finset (Fin k))
    (hσsubset : σ ⊆ gHatTupleSupport gs)
    (hσcard : σ.card = params.d + 1)
    {i : Fin k} (hi : i ∈ σ) :
    MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
      (interpolateCompletedSlicesFromSupport params xs gs σ hσcard).poly =
      ((gs i).get (by simpa [gHatTupleSupport] using hσsubset hi)).poly := by
  let v : Fin k → Scalar params.next := fun j => decodeScalar (xs j)
  have hgi : (gs i).isSome = true := by
    simpa [gHatTupleSupport] using hσsubset hi
  have hvinj : Set.InjOn v (↑σ : Set (Fin k)) := by
    intro a ha b hb hab
    apply hxs
    simpa [v] using congrArg encodeScalar hab
  have hcomp :
      ((MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
        MvPolynomial.C) = MvPolynomial.C := by
    ext r
    simp
  have hx :
      MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.X (lastCoord params)) = MvPolynomial.C (v i) := by
    simp [v, Polynomial.restrictAtHeightCoordinateMap, lastCoord]
  have hextract {o : GHatOutcome params} (ho : o.isSome = true) :
      extractSliceOr0 o = (o.get ho).poly := by
    cases o with
    | none => simp at ho
    | some p => simp [extractSliceOr0]
  unfold interpolateCompletedSlicesFromSupport
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs i))) =
          extractSliceOr0 (gs i) := by
      rw [MvPolynomial.eval₂Hom_rename, MvPolynomial.eval₂Hom_C_eq_bind₁]
      have hmap :
          Polynomial.restrictAtHeightCoordinateMap params (xs i) ∘ embedCoord params =
            MvPolynomial.X := by
        funext j
        simp [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord]
      rw [hmap, MvPolynomial.bind₁_X_left]
      rfl
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ v i))) = 1 := by
      have h0 := (_root_.Polynomial.hom_eval₂
        (p := Lagrange.basis σ v i)
        (f := MvPolynomial.C)
        (g := MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
        (x := MvPolynomial.X (lastCoord params)))
      have h0' :
          MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
          params (xs i))
              ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
                (Lagrange.basis σ v i))) =
            MvPolynomial.C ((Lagrange.basis σ v i).eval (v i)) := by
        simpa [hcomp, hx, _root_.Polynomial.eval₂_at_apply] using h0
      calc
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
            ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
              (Lagrange.basis σ v i)))
          = MvPolynomial.C ((Lagrange.basis σ v i).eval (v i)) := by
              exact h0'
        _ = 1 := by
              simpa using congrArg
                (fun x : Scalar params.next => (MvPolynomial.C x : PolynomialModel params))
                (Lagrange.eval_basis_self hvinj hi)
    simpa [hLi, hslice, hextract hgi]
  · intro j hj hji
    simp_rw [map_mul]
    have hslice :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs j))) =
          extractSliceOr0 (gs j) := by
      rw [MvPolynomial.eval₂Hom_rename, MvPolynomial.eval₂Hom_C_eq_bind₁]
      have hmap :
          Polynomial.restrictAtHeightCoordinateMap params (xs i) ∘ embedCoord params =
            MvPolynomial.X := by
        funext m
        simp [Function.comp, Polynomial.restrictAtHeightCoordinateMap, embedCoord]
      rw [hmap, MvPolynomial.bind₁_X_left]
      rfl
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ v j))) = 0 := by
      have h0 := (_root_.Polynomial.hom_eval₂
        (p := Lagrange.basis σ v j)
        (f := MvPolynomial.C)
        (g := MvPolynomial.eval₂Hom MvPolynomial.C
          (Polynomial.restrictAtHeightCoordinateMap params (xs i)))
        (x := MvPolynomial.X (lastCoord params)))
      have h0' :
          MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
          params (xs i))
              ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
                (Lagrange.basis σ v j))) =
            MvPolynomial.C ((Lagrange.basis σ v j).eval (v i)) := by
        simpa [hcomp, hx, _root_.Polynomial.eval₂_at_apply] using h0
      calc
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap
        params (xs i))
            ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
              (Lagrange.basis σ v j)))
          = MvPolynomial.C ((Lagrange.basis σ v j).eval (v i)) := by
              exact h0'
        _ = 0 := by
              simpa using congrArg
                (fun x : Scalar params.next => (MvPolynomial.C x : PolynomialModel params))
                (Lagrange.eval_basis_of_ne hji hi)
    simpa [hLi, hslice]
  · intro hnot
    exact (hnot hi).elim -/

/- private lemma interpolateCompletedSlices_restrictAtHeight_eq_get_of_mem_supportSubset
    (params : Parameters) [FieldModel params.q]
    {k : ℕ} (xs : PointTuple params k)
    (hxs : Function.Injective xs)
    (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs)
    {i : Fin k} (hi : i ∈ interpolationSupportSubset gs hEligible) :
    (Polynomial.restrictAtHeight params
      (interpolateCompletedSlices params k xs gs) (xs i)).poly =
      ((gs i).get (by
        have hisup : i ∈ gHatTupleSupport gs :=
          interpolationSupportSubset_subset gs hEligible hi
        simpa [gHatTupleSupport] using hisup)).poly := by
  classical
  let σ := interpolationSupportSubset gs hEligible
  have hσcard : σ.card = params.d + 1 := interpolationSupportSubset_card gs hEligible
  have hisup : i ∈ gHatTupleSupport gs := interpolationSupportSubset_subset gs hEligible hi
  have hgi : (gs i).isSome = true := by
    simpa [gHatTupleSupport] using hisup
  have hvinj : Set.InjOn (fun j : Fin k => decodeScalar (xs j)) (↑σ : Set (Fin k)) := by
    intro a ha b hb hab
    apply hxs
    simpa using congrArg encodeScalar hab
  cases k with
  | zero => cases i.2
  | succ k =>
      simp [interpolateCompletedSlices, hEligible, σ, hσcard]
  unfold Polynomial.restrictAtHeight interpolateCompletedSlicesFromSupport
  rw [map_sum]
  rw [Finset.sum_eq_single i]
  · simp_rw [MvPolynomial.eval₂Hom_mul]
    have hrename :
        MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs i))) =
          extractSliceOr0 (gs i) := by
            rw [MvPolynomial.eval₂Hom_rename]
            ext j
            simp [Function.comp, restrictAtHeightCoordinateMap, embedCoord]
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) i))) = 1 := by
            rw [_root_.Polynomial.eval₂_at_apply]
            simp [Lagrange.eval_basis_self hvinj hi]
    have hextract : extractSliceOr0 (gs i) = ((gs i).get hgi).poly := by
      cases hgi' : gs i with
      | none => simp [Option.isSome, hgi'] at hgi
      | some p => simp [extractSliceOr0, hgi']
    simpa [hrename, hLi, hextract]
  · intro j hj hji
    simp_rw [MvPolynomial.eval₂Hom_mul]
    have hrename :
        MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params (xs i))
          (MvPolynomial.rename (embedCoord params) (extractSliceOr0 (gs j))) =
          extractSliceOr0 (gs j) := by
            rw [MvPolynomial.eval₂Hom_rename]
            ext m
            simp [Function.comp, restrictAtHeightCoordinateMap, embedCoord]
    have hLi :
        MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params (xs i))
          ((_root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
            (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j))) = 0 := by
            rw [_root_.Polynomial.eval₂_at_apply]
            simp [Lagrange.eval_basis_of_ne hji hi]
    simp [hrename, hLi]
  · intro hnot
    exact (hnot hi).elim -/


end MIPStarRE.LDT.Pasting
