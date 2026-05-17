import MIPStarRE.LDT.Pasting.BridgeLemmas.LineInterpolation.BadMass

/-!
# Line interpolation: tail lemmas

Non-eligible and false-mass tail lemmas completing the interpolation bridge.

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

lemma not_interpolationEligible_exists_none
    (params : Parameters) [FieldModel params.q]
    {k : ℕ}
    (gs : GHatTupleOutcome params k)
    (hk : params.d + 1 ≤ k)
    (hNot : ¬ InterpolationEligible params gs) :
    ∃ i : Fin k, (gs i).isSome = false := by
  by_contra hnone
  push Not at hnone
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
