import MIPStarRE.LDT.Pasting.Sandwich.Switcheroo

/-!
# Section 12 — Sandwich constructions: `GHat` sandwich families

Completed-slice sandwich families and restriction helpers.
-/

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private lemma projSubMeas_outcome_mul_total_eq_outcome {α : Type*} [Fintype α]
    (A : ProjSubMeas α ι) (a : α) :
    A.outcome a * A.total = A.outcome a := by
  let P := A.outcome a
  let R := (1 : MIPStarRE.Quantum.Op ι) - A.total
  have hP_herm : Pᴴ = P := by
    simpa [P] using A.outcome_hermitian a
  have hR_nonneg : 0 ≤ R := by
    simpa [R] using sub_nonneg.mpr A.total_le_one
  have hR_le_self : R ≤ 1 - P := by
    simpa [R, P] using sub_le_sub_left (A.outcome_le_total a) (1 : MIPStarRE.Quantum.Op ι)
  have hPRP_nonneg : 0 ≤ P * R * P := by
    exact MIPStarRE.Quantum.sandwich_nonneg hR_nonneg hP_herm
  have hP_one_sub_P : P * (1 - P) * P = 0 := by
    calc
      P * (1 - P) * P = (P * 1 - P * P) * P := by rw [mul_sub]
      _ = 0 := by simp [P, A.proj a]
  have hPRP_eq_zero : P * R * P = 0 := by
    apply le_antisymm
    · calc
        P * R * P ≤ P * (1 - P) * P := by
          exact MIPStarRE.Quantum.sandwich_mono hP_herm hR_le_self
        _ = 0 := hP_one_sub_P
    · simpa using hPRP_nonneg
  have hA_total_herm : A.totalᴴ = A.total := by
    exact (Matrix.nonneg_iff_posSemidef.mp A.total_nonneg).isHermitian.eq
  have hR_herm : Rᴴ = R := by
    simp [R, hA_total_herm]
  have hR_sq_le : R * R ≤ R := by
    have hR_le_one : R ≤ 1 := by
      simpa [R] using sub_le_self (1 : MIPStarRE.Quantum.Op ι) A.total_nonneg
    exact MIPStarRE.Quantum.sq_le_self hR_nonneg hR_le_one
  have hRP_conj_mul : (R * P)ᴴ * (R * P) = P * (R * R) * P := by
    calc
      (R * P)ᴴ * (R * P) = (Pᴴ * Rᴴ) * (R * P) := by simp [Matrix.conjTranspose_mul]
      _ = P * (R * R) * P := by simp [hP_herm, hR_herm, mul_assoc]
  have hRP_eq_zero : R * P = 0 := by
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    rw [hRP_conj_mul]
    apply le_antisymm
    · calc
        P * (R * R) * P ≤ P * R * P := by
          exact MIPStarRE.Quantum.sandwich_mono hP_herm hR_sq_le
        _ = 0 := hPRP_eq_zero
    · have hnonneg : 0 ≤ P * (R * R) * P := by
        exact MIPStarRE.Quantum.sandwich_nonneg
          (show 0 ≤ R * R by
            exact Commute.mul_nonneg hR_nonneg hR_nonneg (Commute.refl R))
          hP_herm
      simpa using hnonneg
  calc
    A.outcome a * A.total = P * (1 - R) := by simp [P, R, sub_eq_add_neg, add_comm, add_left_comm]
    _ = P - P * R := by rw [mul_sub, mul_one]
    _ = P := by
          have : P * R = 0 := by
            simpa [hP_herm, hR_herm] using congrArg Matrix.conjTranspose hRP_eq_zero
          simp [this]
    _ = A.outcome a := by rfl

private lemma projSubMeas_total_proj {α : Type*} [Fintype α]
    (A : ProjSubMeas α ι) :
    A.total * A.total = A.total := by
  calc
    A.total * A.total = (∑ a : α, A.outcome a) * A.total := by rw [A.sum_eq_total]
    _ = ∑ a : α, A.outcome a * A.total := by rw [Matrix.sum_mul]
    _ = ∑ a : α, A.outcome a := by
          refine Finset.sum_congr rfl ?_
          intro a _ha
          exact projSubMeas_outcome_mul_total_eq_outcome A a
    _ = A.total := A.sum_eq_total

private lemma gHatIdxMeas_proj (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (x : Fq params) (g : GHatOutcome params) :
    (gHatIdxMeas params family x).outcome g * (gHatIdxMeas params family x).outcome g =
      (gHatIdxMeas params family x).outcome g := by
  cases g with
  | none =>
      let T := (family.meas x).total
      change (1 - T) * (1 - T) = 1 - T
      have hTT : T * T = T := by
        simpa [T] using projSubMeas_total_proj (family.meas x)
      calc
        (1 - T) * (1 - T) = 1 - T - T + T * T := by
          noncomm_ring
        _ = 1 - T := by
          rw [hTT]
          abel
  | some p =>
      simp [gHatIdxMeas, completeSubMeas, (family.meas x).proj p]

/-- Each binomial term in the Bernoulli tail operator is positive semidefinite. -/
lemma binomialOperatorTerm_nonneg {G : MIPStarRE.Quantum.Op ι} (n r : ℕ)
    (hG : 0 ≤ G) (hGle : G ≤ 1) :
    0 ≤ (Nat.choose n r : ℂ) • (G ^ r * (1 - G) ^ (n - r)) := by
  have hcomm : Commute G (1 - G) :=
    (Commute.one_right G).sub_right (Commute.refl G)
  refine smul_nonneg ?_ ?_
  · positivity
  · have hGr : 0 ≤ G ^ r := by
      exact (Matrix.PosSemidef.pow (Matrix.nonneg_iff_posSemidef.mp hG) r).nonneg
    have hIG : 0 ≤ (1 - G) ^ (n - r) := by
      exact
        (Matrix.PosSemidef.pow
          (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hGle)) (n - r)).nonneg
    have hcommPow : Commute (G ^ r) ((1 - G) ^ (n - r)) :=
      (hcomm.pow_left r).pow_right (n - r)
    exact Commute.mul_nonneg hGr hIG hcommPow

/-- Positivity of the Bernoulli tail operator for a PSD contraction. -/
theorem bernoulliTailOperator_nonneg
    (k degree : ℕ) (G : MIPStarRE.Quantum.Op ι)
    (hG : 0 ≤ G) (hGle : G ≤ 1) :
    0 ≤ bernoulliTailOperator k degree G := by
  unfold bernoulliTailOperator
  refine Finset.sum_nonneg fun r _ => ?_
  simpa using binomialOperatorTerm_nonneg (G := G) k r hG hGle

/-- The Bernoulli tail operator is bounded by the identity for a PSD contraction. -/
theorem bernoulliTailOperator_le_one
    (k degree : ℕ) (G : MIPStarRE.Quantum.Op ι)
    (hG : 0 ≤ G) (hGle : G ≤ 1) :
    bernoulliTailOperator k degree G ≤ 1 := by
  let term : ℕ → MIPStarRE.Quantum.Op ι := fun r =>
    (Nat.choose k r : ℂ) • (G ^ r * (1 - G) ^ (k - r))
  have hsubset : Finset.Icc (degree + 1) k ⊆ Finset.range (k + 1) := by
    intro r hr
    simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢
    exact Nat.lt_succ_of_le hr.2
  have htail_le_full :
      ∑ r ∈ Finset.Icc (degree + 1) k, term r ≤ ∑ r ∈ Finset.range (k + 1), term r := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro r hrange hrnot
    simpa [term] using binomialOperatorTerm_nonneg (G := G) k r hG hGle
  have hcomm : Commute G (1 - G) :=
    (Commute.one_right G).sub_right (Commute.refl G)
  have hfull :
      ∑ r ∈ Finset.range (k + 1), term r = 1 := by
    calc
      ∑ r ∈ Finset.range (k + 1), term r
          = ∑ r ∈ Finset.range (k + 1), G ^ r * (1 - G) ^ (k - r) * Nat.choose k r := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              let A := G ^ r * (1 - G) ^ (k - r)
              have hcast_comm : Commute (Nat.choose k r : MIPStarRE.Quantum.Op ι) A :=
                Nat.cast_commute (Nat.choose k r) A
              simpa [term, A, Algebra.smul_def] using hcast_comm.eq
      _ = (G + (1 - G)) ^ k := by
            symm
            exact Commute.add_pow hcomm k
      _ = 1 := by simp
  calc
    bernoulliTailOperator k degree G
        = ∑ r ∈ Finset.Icc (degree + 1) k, term r := by
            simp [bernoulliTailOperator, term]
    _ ≤ ∑ r ∈ Finset.range (k + 1), term r := htail_le_full
    _ = 1 := hfull

/-- Concrete family for the full sandwich
`\widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k} \cdots \widehat G^{x_1}_{g_1}`. -/
noncomputable def gHatSandwichFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (GHatTupleOutcome params k) ι :=
  fun xs =>
    { outcome := fun gs =>
        let half := gHatHalfProductOutcomeOperator params family k xs gs
        half * halfᴴ
      total :=
        let half := gHatHalfProductTotalOperator params family k xs
        half * halfᴴ
      outcome_pos := by
        intro gs
        simpa using
          (Matrix.posSemidef_self_mul_conjTranspose
            (gHatHalfProductOutcomeOperator params family k xs gs)).nonneg
      sum_eq_total := by
        induction k with
        | zero =>
            simp [gHatHalfProductOutcomeOperator, gHatHalfProductTotalOperator]
        | succ k ih =>
            let α : Fin (k + 1) → Type := fun _ => GHatOutcome params
            have hsplit :
                (∑ gs : GHatTupleOutcome params (k + 1),
                    let half := gHatHalfProductOutcomeOperator params family (k + 1) xs gs
                    half * halfᴴ) =
                  ∑ p : GHatOutcome params × GHatTupleOutcome params k,
                    (gHatIdxMeas params family (xs 0)).outcome p.1 *
                      (gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) p.2 *
                        (gHatHalfProductOutcomeOperator
                          params family k (pointTupleTail xs) p.2)ᴴ) *
                      (gHatIdxMeas params family (xs 0)).outcome p.1 := by
              symm
              exact Fintype.sum_equiv (Fin.consEquiv α)
                (fun p =>
                  (gHatIdxMeas params family (xs 0)).outcome p.1 *
                    (gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) p.2 *
                      (gHatHalfProductOutcomeOperator
                        params family k (pointTupleTail xs) p.2)ᴴ) *
                    (gHatIdxMeas params family (xs 0)).outcome p.1)
                (fun gs =>
                  let half := gHatHalfProductOutcomeOperator params family (k + 1) xs gs
                  half * halfᴴ)
                (by
                  intro p
                  have htail :
                      gHatTupleOutcomeTail ((Fin.consEquiv α) p) = p.2 := by
                    funext i
                    rfl
                  simp [gHatHalfProductOutcomeOperator, htail,
                    Matrix.conjTranspose_mul,
                    Matrix.mul_assoc, (gHatIdxMeas params family (xs 0)).outcome_hermitian])
            rw [hsplit]
            rw [← Finset.univ_product_univ, Finset.sum_product]
            calc
              ∑ g : GHatOutcome params,
                  ∑ gs : GHatTupleOutcome params k,
                    (gHatIdxMeas params family (xs 0)).outcome g *
                      (gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs *
                        (gHatHalfProductOutcomeOperator
                          params family k (pointTupleTail xs) gs)ᴴ) *
                      (gHatIdxMeas params family (xs 0)).outcome g
                = ∑ g : GHatOutcome params,
                    (gHatIdxMeas params family (xs 0)).outcome g *
                      (∑ gs : GHatTupleOutcome params k,
                        gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs *
                          (gHatHalfProductOutcomeOperator
                            params family k (pointTupleTail xs) gs)ᴴ) *
                      (gHatIdxMeas params family (xs 0)).outcome g := by
                    refine Finset.sum_congr rfl ?_
                    intro g _hg
                    calc
                      ∑ gs : GHatTupleOutcome params k,
                          (gHatIdxMeas params family (xs 0)).outcome g *
                            (gHatHalfProductOutcomeOperator
                              params family k (pointTupleTail xs) gs *
                              (gHatHalfProductOutcomeOperator
                                params family k (pointTupleTail xs) gs)ᴴ) *
                            (gHatIdxMeas params family (xs 0)).outcome g
                        = (∑ gs : GHatTupleOutcome params k,
                            (gHatIdxMeas params family (xs 0)).outcome g *
                              (gHatHalfProductOutcomeOperator
                                params family k (pointTupleTail xs) gs *
                                (gHatHalfProductOutcomeOperator
                                  params family k (pointTupleTail xs) gs)ᴴ)) *
                            (gHatIdxMeas params family (xs 0)).outcome g := by
                              rw [Finset.sum_mul]
                        _ = (gHatIdxMeas params family (xs 0)).outcome g *
                              (∑ gs : GHatTupleOutcome params k,
                                gHatHalfProductOutcomeOperator
                                  params family k (pointTupleTail xs) gs *
                                  (gHatHalfProductOutcomeOperator
                                    params family k (pointTupleTail xs) gs)ᴴ) *
                              (gHatIdxMeas params family (xs 0)).outcome g := by
                              rw [Matrix.mul_sum]
              _ = ∑ g : GHatOutcome params,
                    (gHatIdxMeas params family (xs 0)).outcome g *
                      (gHatHalfProductTotalOperator params family k (pointTupleTail xs) *
                        (gHatHalfProductTotalOperator
                          params family k (pointTupleTail xs))ᴴ) *
                      (gHatIdxMeas params family (xs 0)).outcome g := by
                    refine Finset.sum_congr rfl ?_
                    intro g _hg
                    rw [ih (pointTupleTail xs)]
              _ = ∑ g : GHatOutcome params,
                    (gHatIdxMeas params family (xs 0)).outcome g * 1 *
                      (gHatIdxMeas params family (xs 0)).outcome g := by
                    refine Finset.sum_congr rfl ?_
                    intro g _hg
                    simp [gHatHalfProductTotalOperator_eq_one]
              _ = ∑ g : GHatOutcome params,
                    (gHatIdxMeas params family (xs 0)).outcome g *
                      (gHatIdxMeas params family (xs 0)).outcome g := by
                    simp
              _ = ∑ g : GHatOutcome params, (gHatIdxMeas params family (xs 0)).outcome g := by
                    refine Finset.sum_congr rfl ?_
                    intro g _hg
                    exact gHatIdxMeas_proj params family (xs 0) g
              _ = (gHatIdxMeas params family (xs 0)).total := by
                    rw [(gHatIdxMeas params family (xs 0)).sum_eq_total]
              _ = (1 : MIPStarRE.Quantum.Op ι) := by
                    simp [gHatIdxMeas, completeSubMeas]
              _ =
                  gHatHalfProductTotalOperator params family (k + 1) xs *
                    (gHatHalfProductTotalOperator params family (k + 1) xs)ᴴ := by
                    simp [gHatHalfProductTotalOperator_eq_one]
      total_le_one := by
        simp [gHatHalfProductTotalOperator_eq_one] }

/-- Restrict a submeasurement to the outcomes satisfying `p`, dropping all other
mass from the total operator. -/
noncomputable def restrictSubMeas {α : Type*} [Fintype α]
    (A : SubMeas α ι) (p : α → Prop) [DecidablePred p] :
    SubMeas α ι :=
  { outcome := fun a => if p a then A.outcome a else 0
    total := ∑ a ∈ Finset.univ.filter p, A.outcome a
    outcome_pos := by
      intro a
      by_cases ha : p a <;> simp [ha, A.outcome_pos a]
    sum_eq_total := by
      simp [Finset.sum_filter]
    total_le_one := by
      calc
        ∑ a ∈ Finset.univ.filter p, A.outcome a ≤ ∑ a : α, A.outcome a := by
          exact Finset.sum_le_univ_sum_of_nonneg
            (s := Finset.univ.filter p)
            (w := fun a => A.outcome_pos a)
        _ = A.total := by
          rw [A.sum_eq_total]
        _ ≤ 1 := A.total_le_one }

/-- Restricting a submeasurement can only decrease its total operator. -/
lemma restrictSubMeas_total_le_total {α : Type*} [Fintype α]
    (A : SubMeas α ι) (p : α → Prop) [DecidablePred p] :
    (restrictSubMeas A p).total ≤ A.total := by
  calc
    (restrictSubMeas A p).total = ∑ a ∈ Finset.univ.filter p, A.outcome a := by
      rfl
    _ ≤ ∑ a : α, A.outcome a := by
      exact Finset.sum_le_univ_sum_of_nonneg
        (s := Finset.univ.filter p)
        (w := fun a => A.outcome_pos a)
    _ = A.total := A.sum_eq_total

/-- Restrict the sandwiched completed-slice family to tuples with support of size at
least `d + 1`, matching the `|τ| ≥ d+1` filter in the paper before interpolation. -/
noncomputable def interpolationEligibleSandwichFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (GHatTupleOutcome params k) ι :=
  fun xs =>
    restrictSubMeas
      (gHatSandwichFamily params family k xs)
      (InterpolationEligible params)

/-- Concrete family for the half-sandwich product of `k` completed slices. -/
noncomputable def gHatHalfSandwichLeft (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxOpFamily (PointTuple params k) (GHatTupleOutcome params k) (ι × ι) :=
  fun xs =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      { outcome := fun gs => gHatHalfProductOutcomeOperator params family k xs gs
        total := gHatHalfProductTotalOperator params family k xs
      }

/-- Concrete family for the cyclically permuted half-sandwich product. -/
noncomputable def gHatHalfSandwichRight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxOpFamily (PointTuple params k) (GHatTupleOutcome params k) (ι × ι) :=
  fun xs =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      { outcome := fun gs => gHatRotatedHalfProductOutcomeOperator params family k xs gs
        total := gHatRotatedHalfProductTotalOperator params family k xs
      }

end MIPStarRE.LDT.Pasting
