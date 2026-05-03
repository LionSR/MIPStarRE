import MIPStarRE.LDT.Pasting.BridgeLemmas.Common

/-!
# Line interpolation: core API

Interpolation-support, vertical-line restriction, and completed-slice
interpolation lemmas from `ld-pasting.tex` that form the foundation for the
bad-line and bad-mass layers.

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
  exact Polynomial.restrictToAxisParallelLine_apply params.next h ℓ t

lemma restrictToVerticalLine_eval_eq_restrictAtHeight_eval
    (params : Parameters) [FieldModel params.q]
    (h : Polynomial params.next)
    (u : Point params)
    (x : Fq params) :
    (Polynomial.restrictToAxisParallelLine params.next h
        ({ base := appendPoint params u zeroCoord
           direction := lastCoord params } : AxisParallelLine params.next)) x =
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
           direction := lastCoord params } : AxisParallelLine params.next)) x
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

end MIPStarRE.LDT.Pasting
