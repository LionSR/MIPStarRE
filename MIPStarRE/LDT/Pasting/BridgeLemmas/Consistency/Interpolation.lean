import MIPStarRE.LDT.Pasting.BridgeLemmas.Common

/-!
# Section 12 pasting: bridge consistency interpolation

Interpolation-side helper lemmas for turning tuplewise failures into linewise bad events.
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
      simpa [AxisParallelLine.pointAt, Polynomial.axisCoordinatePolynomial,
        addCoord, decodePoint, decode_encodeScalar, _root_.Polynomial.eval_add,
        _root_.Polynomial.eval_C, _root_.Polynomial.eval_X]
    · simpa [AxisParallelLine.pointAt, Polynomial.axisCoordinatePolynomial,
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

lemma verticalLine_pointAt_eq_appendPoint
    (params : Parameters) [FieldModel params.q]
    (u : Point params)
    (x : Fq params) :
    AxisParallelLine.pointAt
        ({ base := appendPoint params u zeroCoord
         , direction := lastCoord params } : AxisParallelLine params.next)
        x =
      appendPoint params u x := by
  funext i
  by_cases hi : i = lastCoord params
  · subst hi
    simp [AxisParallelLine.pointAt, appendPoint, lastCoord]
    change addCoord zeroCoord x = x
    rw [← encode_decodeScalar x]
    simp [addCoord, zeroCoord]
  · have hi_lt : i.1 < params.m := by
      have hi_succ : i.1 < params.m + 1 := by
        simpa [Parameters.next] using i.2
      have hne : i.1 ≠ params.m := by
        intro h
        apply hi
        exact Fin.ext h
      omega
    simp [AxisParallelLine.pointAt, appendPoint, hi, hi_lt]

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
          exact congrArg (fun y => h y) (verticalLine_pointAt_eq_appendPoint params u x)
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

/-- Semantic event-enlargement core for `hBConsistency_core`:
if an interpolation-eligible tuple yields a vertical-line polynomial differing from a
candidate line polynomial `f`, then some coordinate already witnesses a one-point
mismatch against the completed-slice family. -/

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
    simpa [hEq]
  rw [hfull]
  exact hk

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
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
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
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
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
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
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
        MvPolynomial.eval₂Hom MvPolynomial.C (Polynomial.restrictAtHeightCoordinateMap params (xs i))
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
                                            (Polynomial.restrictAtHeightCoordinateMap params (xs i))).comp
                                          MvPolynomial.C)
                                        x (Lagrange.basis σ (fun j : Fin k => decodeScalar (xs j)) j))
                                    hx
                        _ = _root_.Polynomial.eval₂ MvPolynomial.C (MvPolynomial.C (decodeScalar (xs i)))
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
    exact (hnot hi).elim

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

end MIPStarRE.LDT.Pasting
