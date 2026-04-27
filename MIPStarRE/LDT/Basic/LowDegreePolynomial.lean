import Mathlib.Algebra.MvPolynomial.Polynomial
import MIPStarRE.LDT.Basic.LinePolynomials

/-!
# Low-individual-degree polynomials for the low individual degree test

Multivariate low-degree polynomial objects and their restrictions.
-/

namespace MIPStarRE.LDT

/-- Global low-individual-degree polynomial outcomes. -/
structure Polynomial (params : Parameters) [FieldModel params.q] where
  poly : PolynomialModel params
  lowIndividualDegree : ∀ i, MvPolynomial.degreeOf i poly ≤ params.d

namespace Polynomial

/-- Evaluation of the stored multivariate polynomial on a coded point. -/
noncomputable def toFun {params : Parameters} [FieldModel params.q] (g : Polynomial params) :
    Point params → Fq params :=
  evalPolynomialModel params g.poly

noncomputable instance {params : Parameters} [FieldModel params.q] :
    CoeFun (Polynomial params) (fun _ => Point params → Fq params) :=
  ⟨Polynomial.toFun⟩

/-- The stored polynomial indeed certifies low individual degree. -/
theorem hasLowIndividualDegree {params : Parameters} [FieldModel params.q]
    (g : Polynomial params) :
    HasLowIndividualDegree params g := by
  refine ⟨g.poly, g.lowIndividualDegree, ?_⟩
  funext u
  rfl

/-- Extend a global polynomial to the slice at height `x` by ignoring the new variable. -/
noncomputable def appendAtHeight (params : Parameters) [FieldModel params.q]
    (g : Polynomial params) (_x : Fq params) : Polynomial params.next where
  poly := MvPolynomial.rename (embedCoord params) g.poly
  lowIndividualDegree := by
    intro i
    have hinj : Function.Injective (embedCoord params) := by
      intro a b h
      simp only [embedCoord, Fin.mk.injEq] at h
      exact Fin.ext h
    by_cases h : i.val < params.m
    · -- i is in the range of embedCoord: transfer the degree bound
      have hi : embedCoord params ⟨i.val, h⟩ = i := by
        ext; simp [embedCoord]
      rw [← hi, MvPolynomial.degreeOf_rename_of_injective hinj]
      exact g.lowIndividualDegree _
    · -- i is not in range: degreeOf = 0
      suffices MvPolynomial.degreeOf i (MvPolynomial.rename (embedCoord params) g.poly) = 0 by
        exact (le_of_eq this).trans (Nat.zero_le _)
      rw [MvPolynomial.degreeOf, MvPolynomial.degrees_rename_of_injective hinj]
      simp only [Multiset.count_eq_zero, Multiset.mem_map]
      rintro ⟨b, _, hb⟩
      simp only [embedCoord, Fin.ext_iff] at hb
      omega

/-- Coordinate map for restricting a polynomial in `m+1` variables to the slice `X_m = x`. -/
noncomputable def restrictAtHeightCoordinateMap (params : Parameters) [FieldModel params.q]
    (x : Fq params) :
    Fin params.next.m → PolynomialModel params :=
  fun i =>
    if h : i.1 < params.m then
      MvPolynomial.X ⟨i.1, h⟩
    else
      MvPolynomial.C (decodeScalar x)

private theorem degreeOf_restrictAtHeightCoordinateMap_le
    (params : Parameters) [FieldModel params.q] (x : Fq params)
    (i : Fin params.m) (j : Fin params.next.m) :
    MvPolynomial.degreeOf i (restrictAtHeightCoordinateMap params x j) ≤
      if j = embedCoord params i then 1 else 0 := by
  classical
  by_cases hji : j = embedCoord params i
  · subst hji
    rcases subsingleton_or_nontrivial (Scalar params) with hsub | hnontriv
    · letI := hsub
      have hX : (MvPolynomial.X i : PolynomialModel params) = 0 := Subsingleton.elim _ _
      simp [restrictAtHeightCoordinateMap, embedCoord, hX]
    · letI := hnontriv
      simpa [restrictAtHeightCoordinateMap, embedCoord] using
        (show MvPolynomial.degreeOf i (MvPolynomial.X i : PolynomialModel params) ≤ 1 by
          rw [MvPolynomial.degreeOf_X]
          simp)
  · by_cases hj : j.1 < params.m
    · have hne : (⟨j.1, hj⟩ : Fin params.m) ≠ i := by
        intro h
        apply hji
        ext
        simpa [embedCoord] using congrArg Fin.val h
      rcases subsingleton_or_nontrivial (Scalar params) with hsub | hnontriv
      · letI := hsub
        have hX : (MvPolynomial.X ⟨j.1, hj⟩ : PolynomialModel params) = 0 := Subsingleton.elim _ _
        simp [restrictAtHeightCoordinateMap, hj, hji, hX]
      · letI := hnontriv
        have hne' : i ≠ ⟨j.1, hj⟩ := by
          simpa [eq_comm] using hne
        rw [restrictAtHeightCoordinateMap, dif_pos hj, MvPolynomial.degreeOf_X]
        simp [hne', hji]
    · simp [restrictAtHeightCoordinateMap, hj, MvPolynomial.degreeOf_C, hji]

/-- Restrict a global polynomial in `m + 1` variables to the slice at height `x`. -/
noncomputable def restrictAtHeight (params : Parameters) [FieldModel params.q]
    (g : Polynomial params.next) (x : Fq params) : Polynomial params where
  poly := MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x) g.poly
  lowIndividualDegree := by
    intro i
    classical
    rw [g.poly.as_sum]
    have hmap :
        (MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x))
            (∑ n ∈ g.poly.support, MvPolynomial.monomial n (g.poly.coeff n)) =
          ∑ n ∈ g.poly.support,
            MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x)
              (MvPolynomial.monomial n (g.poly.coeff n)) := by
      exact map_sum
        (MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x))
        (fun n => MvPolynomial.monomial n (g.poly.coeff n)) g.poly.support
    calc
      MvPolynomial.degreeOf i
          ((MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x))
            (∑ n ∈ g.poly.support, MvPolynomial.monomial n (g.poly.coeff n))) =
          MvPolynomial.degreeOf i
            (∑ n ∈ g.poly.support,
              MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x)
                (MvPolynomial.monomial n (g.poly.coeff n))) := by
        rw [hmap]
      _ ≤ g.poly.support.sup fun n =>
            MvPolynomial.degreeOf i
              (MvPolynomial.eval₂Hom MvPolynomial.C (restrictAtHeightCoordinateMap params x)
                (MvPolynomial.monomial n (g.poly.coeff n))) :=
        MvPolynomial.degreeOf_sum_le i _ _
      _ ≤ params.d := by
        apply Finset.sup_le
        intro n hn
        rw [MvPolynomial.eval₂Hom_monomial]
        calc
          MvPolynomial.degreeOf i
              ((MvPolynomial.C (g.poly.coeff n) : PolynomialModel params) *
                ∏ j ∈ n.support, restrictAtHeightCoordinateMap params x j ^ n j) ≤
              MvPolynomial.degreeOf i (MvPolynomial.C (g.poly.coeff n)) +
                MvPolynomial.degreeOf i
                  (∏ j ∈ n.support, restrictAtHeightCoordinateMap params x j ^ n j) :=
            MvPolynomial.degreeOf_mul_le i _ _
          _ ≤ 0 +
                MvPolynomial.degreeOf i
                  (∏ j ∈ n.support, restrictAtHeightCoordinateMap params x j ^ n j) := by
            gcongr
            exact (MvPolynomial.degreeOf_C (g.poly.coeff n) i).le
          _ =
                MvPolynomial.degreeOf i
                  (∏ j ∈ n.support, restrictAtHeightCoordinateMap params x j ^ n j) := by
            simp
          _ ≤ ∑ j ∈ n.support,
                MvPolynomial.degreeOf i (restrictAtHeightCoordinateMap params x j ^ n j) :=
            MvPolynomial.degreeOf_prod_le i _ _
          _ ≤ ∑ j ∈ n.support, if j = embedCoord params i then n j else 0 := by
            apply Finset.sum_le_sum
            intro j hj
            calc
              MvPolynomial.degreeOf i (restrictAtHeightCoordinateMap params x j ^ n j) ≤
                  n j * MvPolynomial.degreeOf i (restrictAtHeightCoordinateMap params x j) :=
                MvPolynomial.degreeOf_pow_le i _ _
              _ ≤ n j * (if j = embedCoord params i then 1 else 0) := by
                exact Nat.mul_le_mul_left _ (degreeOf_restrictAtHeightCoordinateMap_le params x i j)
              _ = if j = embedCoord params i then n j else 0 := by
                split_ifs <;> simp
          _ = n (embedCoord params i) := by
            by_cases hmem : embedCoord params i ∈ n.support
            · rw [Finset.sum_eq_single (embedCoord params i)]
              · simp
              · intro j hj hne
                simp [hne]
              · intro hnot
                contradiction
            · rw [Finset.sum_eq_zero]
              · rw [Finsupp.notMem_support_iff.mp hmem]
              · intro j hj
                by_cases h : j = embedCoord params i
                · exact (hmem (h ▸ hj)).elim
                · simp [h]
          _ ≤ params.d := by
            exact
              (MvPolynomial.degreeOf_le_iff.mp
                (g.lowIndividualDegree (embedCoord params i))) n hn

/-- Coordinate polynomial for restricting to an axis-parallel affine line. -/
noncomputable def axisCoordinatePolynomial (params : Parameters) [FieldModel params.q]
    (ℓ : AxisParallelLine params) :
    Fin params.m → LinePolynomialModel params :=
  fun i =>
    if i = ℓ.direction then
      _root_.Polynomial.C (decodeScalar (ℓ.base i)) + _root_.Polynomial.X
    else
      _root_.Polynomial.C (decodeScalar (ℓ.base i))

private theorem natDegree_axisCoordinatePolynomial_le (params : Parameters) [FieldModel params.q]
    (ℓ : AxisParallelLine params) (i : Fin params.m) :
    (axisCoordinatePolynomial params ℓ i).natDegree ≤ if i = ℓ.direction then 1 else 0 := by
  classical
  by_cases hi : i = ℓ.direction
  · subst hi
    rcases subsingleton_or_nontrivial (Scalar params) with hsub | hnontriv
    · letI := hsub
      have hX : (_root_.Polynomial.X : LinePolynomialModel params) = 0 := Subsingleton.elim _ _
      simp [axisCoordinatePolynomial, hX]
    · letI := hnontriv
      simp [axisCoordinatePolynomial, add_comm]
  · simp [axisCoordinatePolynomial, hi, Polynomial.natDegree_C]

/-- Restrict a global polynomial to an axis-parallel line. -/
noncomputable def restrictToAxisParallelLine (params : Parameters) [FieldModel params.q]
    (g : Polynomial params) (ℓ : AxisParallelLine params) : AxisLinePolynomial params where
  poly := MvPolynomial.eval₂Hom _root_.Polynomial.C (axisCoordinatePolynomial params ℓ) g.poly
  degreeBounded := by
    classical
    rw [g.poly.as_sum, map_sum]
    refine Polynomial.natDegree_sum_le_of_forall_le
      (s := g.poly.support)
      (f := fun n =>
        MvPolynomial.eval₂Hom _root_.Polynomial.C (axisCoordinatePolynomial params ℓ)
          (MvPolynomial.monomial n (g.poly.coeff n)))
      (n := params.d) ?_
    intro n hn
    change
      (MvPolynomial.eval₂Hom _root_.Polynomial.C (axisCoordinatePolynomial params ℓ)
        (MvPolynomial.monomial n (g.poly.coeff n))).natDegree ≤ params.d
    rw [MvPolynomial.eval₂Hom_monomial]
    calc
      ((_root_.Polynomial.C (g.poly.coeff n) : LinePolynomialModel params) *
          ∏ j ∈ n.support, axisCoordinatePolynomial params ℓ j ^ n j).natDegree ≤
          (∏ j ∈ n.support, axisCoordinatePolynomial params ℓ j ^ n j).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ ≤ ∑ j ∈ n.support, (axisCoordinatePolynomial params ℓ j ^ n j).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ j ∈ n.support, if j = ℓ.direction then n j else 0 := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          (axisCoordinatePolynomial params ℓ j ^ n j).natDegree ≤
              n j * (axisCoordinatePolynomial params ℓ j).natDegree :=
            Polynomial.natDegree_pow_le
          _ ≤ n j * (if j = ℓ.direction then 1 else 0) := by
            exact Nat.mul_le_mul_left _ (natDegree_axisCoordinatePolynomial_le params ℓ j)
          _ = if j = ℓ.direction then n j else 0 := by
            split_ifs <;> simp
      _ = n ℓ.direction := by
        by_cases hmem : ℓ.direction ∈ n.support
        · rw [Finset.sum_eq_single ℓ.direction]
          · simp
          · intro j hj hne
            simp [hne]
          · intro hnot
            contradiction
        · rw [Finset.sum_eq_zero]
          · rw [Finsupp.notMem_support_iff.mp hmem]
          · intro j hj
            by_cases h : j = ℓ.direction
            · exact (hmem (h ▸ hj)).elim
            · simp [h]
      _ ≤ params.d := by
        exact (MvPolynomial.degreeOf_le_iff.mp (g.lowIndividualDegree ℓ.direction)) n hn

/-- Evaluating an axis-parallel restriction agrees with evaluating the original
polynomial at the corresponding point on the line. -/
@[simp] theorem restrictToAxisParallelLine_apply
    (params : Parameters) [FieldModel params.q]
    (g : Polynomial params) (ℓ : AxisParallelLine params) (t : Fq params) :
    restrictToAxisParallelLine params g ℓ t = g (ℓ.pointAt t) := by
  unfold restrictToAxisParallelLine Polynomial.toFun AxisLinePolynomial.toFun
    evalLinePolynomialModel evalPolynomialModel
  change encodeScalar
      (Polynomial.eval (decodeScalar t)
        (MvPolynomial.eval₂ Polynomial.C
          (axisCoordinatePolynomial params ℓ) g.poly)) = _
  rw [MvPolynomial.polynomial_eval_eval₂]
  change encodeScalar
      (MvPolynomial.eval₂
        ((Polynomial.evalRingHom (decodeScalar t)).comp Polynomial.C)
        (fun s => Polynomial.eval (decodeScalar t)
          (axisCoordinatePolynomial params ℓ s)) g.poly) =
    encodeScalar (MvPolynomial.eval₂ (RingHom.id _) (decodePoint (ℓ.pointAt t)) g.poly)
  have hcoeff :
      ((Polynomial.evalRingHom (decodeScalar t)).comp Polynomial.C) =
        RingHom.id _ := by
    ext a
    simp
  rw [hcoeff]
  have hvars :
      (fun s => Polynomial.eval (decodeScalar t)
        (axisCoordinatePolynomial params ℓ s)) =
        decodePoint (ℓ.pointAt t) := by
    funext i
    by_cases h : i = ℓ.direction
    · subst h
      simp [axisCoordinatePolynomial, AxisParallelLine.pointAt, decodePoint, addCoord]
    · simp [axisCoordinatePolynomial, AxisParallelLine.pointAt, decodePoint, h]
  rw [hvars]

/-- Coordinate polynomial for restricting to a diagonal affine line. -/
noncomputable def diagonalCoordinatePolynomial (params : Parameters) [FieldModel params.q]
    (ℓ : DiagonalLine params) :
    Fin params.m → LinePolynomialModel params :=
  fun i =>
    _root_.Polynomial.C (decodeScalar (ℓ.base i)) +
      _root_.Polynomial.C (decodeScalar (ℓ.direction i)) * _root_.Polynomial.X

private theorem natDegree_diagonalCoordinatePolynomial_le (params : Parameters)
    [FieldModel params.q]
    (ℓ : DiagonalLine params) (i : Fin params.m) :
    (diagonalCoordinatePolynomial params ℓ i).natDegree ≤ 1 := by
  rcases subsingleton_or_nontrivial (Scalar params) with hsub | hnontriv
  · letI := hsub
    have hX : (_root_.Polynomial.X : LinePolynomialModel params) = 0 := Subsingleton.elim _ _
    simp [diagonalCoordinatePolynomial, hX]
  · letI := hnontriv
    calc
      (diagonalCoordinatePolynomial params ℓ i).natDegree ≤
          max (_root_.Polynomial.C (decodeScalar (ℓ.base i))).natDegree
            ((_root_.Polynomial.C (decodeScalar (ℓ.direction i)) *
              _root_.Polynomial.X).natDegree) :=
        Polynomial.natDegree_add_le _ _
      _ ≤ max 0 1 := by
        gcongr
        · exact (Polynomial.natDegree_C _).le
        · exact
            (Polynomial.natDegree_C_mul_le
              _ (_root_.Polynomial.X : LinePolynomialModel params)).trans
            Polynomial.natDegree_X.le
      _ = 1 := by simp

/-- Restrict a global polynomial to a diagonal line. -/
noncomputable def restrictToDiagonalLine (params : Parameters) [FieldModel params.q]
    (g : Polynomial params) (ℓ : DiagonalLine params) : DiagonalLinePolynomial params where
  poly := MvPolynomial.eval₂Hom _root_.Polynomial.C (diagonalCoordinatePolynomial params ℓ) g.poly
  degreeBounded := by
    classical
    rw [g.poly.as_sum, map_sum]
    refine Polynomial.natDegree_sum_le_of_forall_le
      (s := g.poly.support)
      (f := fun n =>
        MvPolynomial.eval₂Hom _root_.Polynomial.C (diagonalCoordinatePolynomial params ℓ)
          (MvPolynomial.monomial n (g.poly.coeff n)))
      (n := params.m * params.d) ?_
    intro n hn
    change
      (MvPolynomial.eval₂Hom _root_.Polynomial.C (diagonalCoordinatePolynomial params ℓ)
        (MvPolynomial.monomial n (g.poly.coeff n))).natDegree ≤ params.m * params.d
    rw [MvPolynomial.eval₂Hom_monomial]
    calc
      ((_root_.Polynomial.C (g.poly.coeff n) : LinePolynomialModel params) *
          ∏ j ∈ n.support, diagonalCoordinatePolynomial params ℓ j ^ n j).natDegree ≤
          (∏ j ∈ n.support, diagonalCoordinatePolynomial params ℓ j ^ n j).natDegree :=
        Polynomial.natDegree_C_mul_le _ _
      _ ≤ ∑ j ∈ n.support, (diagonalCoordinatePolynomial params ℓ j ^ n j).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ j ∈ n.support, n j := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          (diagonalCoordinatePolynomial params ℓ j ^ n j).natDegree ≤
              n j * (diagonalCoordinatePolynomial params ℓ j).natDegree :=
            Polynomial.natDegree_pow_le
          _ ≤ n j * 1 := by
            exact Nat.mul_le_mul_left _ (natDegree_diagonalCoordinatePolynomial_le params ℓ j)
          _ = n j := by simp
      _ ≤ n.sum fun _ e => e := by
        simp [Finsupp.sum]
      _ ≤ ∑ j : Fin params.m, params.d := by
        simpa [Finsupp.sum_fintype] using
          (Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
            (MvPolynomial.degreeOf_le_iff.mp (g.lowIndividualDegree j)) n hn)
      _ = params.m * params.d := by
        simp [Fintype.card_fin]

end Polynomial


end MIPStarRE.LDT
