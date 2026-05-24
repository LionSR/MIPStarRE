import MIPStarRE.LDT.Pasting.BridgeLemmas.LdSandwichLineOnePoint.PrefixMoved

/-!
# Section 12 pasting: line one-point bridge — outcome lemmas

Internal helper module; part of the file-split for `#1127`.

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

/-- The postprocessed one-point right family has zero-operator `none` outcome,
because the selected slot satisfies `i < k` and is always postprocessed to `some`. -/
lemma ldSandwichLineOnePointRightFamily_outcome_none_eq_zero
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    ((ldSandwichLineOnePointRightFamily params strategy family k i) q).outcome none = 0 := by
  simp [ldSandwichLineOnePointRightFamily, postprocess, hi]

/-- The one-point right family is measurement-valued when the selected coordinate
exists.  This is the source of nonnegativity for the linear consistency defect. -/
lemma ldSandwichLineOnePointRightFamily_total_eq_one
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    ((ldSandwichLineOnePointRightFamily params strategy family k i) q).total = 1 := by
  let ℓ : AxisParallelLine params.next :=
    { base := appendPoint params q.1 zeroCoord
      direction := lastCoord params }
  simpa [ldSandwichLineOnePointRightFamily, verticalLineMeasurementFamily, hi,
    postprocess_total, ℓ] using (strategy.axisParallelMeasurement ℓ).total_eq_one

/-- The rotated prefix-only one-point left family has no `none` outcome. -/
lemma ldSandwichLineOnePointPrefixMovedFamily_outcome_none_eq_zero
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    (ldSandwichLineOnePointPrefixMovedFamily params family hi q).outcome none = 0 := by
  conv_lhs =>
    simp [ldSandwichLineOnePointPrefixMovedFamily, postprocess, restrictSubMeas,
      Finset.sum_filter]
  apply Finset.sum_eq_zero
  intro gs _hgs
  by_cases hsome : (gs 0).isSome = true
  · rcases Option.isSome_iff_exists.mp hsome with ⟨g, hg⟩
    simp [hg]
  · simp [hsome]

/-- Generic outcome expansion for evaluating a restricted completed-slice sandwich
family at a concrete field value. -/
lemma gHatSandwichFamily_restrict_eval_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {n : ℕ} (xs : PointTuple params n)
    (idx : Fin n) (u : Point params) (a : Fq params) :
    (postprocess
      (restrictSubMeas (gHatSandwichFamily params family n xs)
        (fun gs => (gs idx).isSome = true))
      (fun gs => Option.map (fun g : Polynomial params => g u) (gs idx))).outcome (some a) =
      ∑ gs : GHatTupleOutcome params n,
        if Option.map (fun g : Polynomial params => g u) (gs idx) = some a then
          let half := gHatHalfProductOutcomeOperator params family n xs gs
          half * halfᴴ
        else
          0 := by
  conv_lhs =>
    simp [postprocess, restrictSubMeas, gHatSandwichFamily, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro gs _hgs
  by_cases hmap : Option.map (fun g : Polynomial params => g u) (gs idx) = some a
  · rcases Option.map_eq_some_iff.mp hmap with ⟨g, hgs, hg⟩
    simp [hgs]
  · have hnone : ¬ ∃ g : Polynomial params, gs idx = some g ∧ g u = a := by
      rintro ⟨g, hgs, hg⟩
      exact hmap (Option.map_eq_some_iff.mpr ⟨g, hgs, hg⟩)
    simp [hnone]

/-- Outcome expansion for the original full one-point left family at a concrete field value. -/
lemma ldSandwichLineOnePointLeftFamily_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (a : Fq params) :
    ((ldSandwichLineOnePointLeftFamily params strategy family k i) q).outcome (some a) =
      ∑ gs : GHatTupleOutcome params k,
        if Option.map (fun g : Polynomial params => g q.1) (gs ⟨i, hi⟩) = some a then
          let half := gHatHalfProductOutcomeOperator params family k q.2 gs
          half * halfᴴ
        else
          0 := by
  simpa [ldSandwichLineOnePointLeftFamily, hi] using
    gHatSandwichFamily_restrict_eval_outcome_some
      params family q.2 ⟨i, hi⟩ q.1 a

/-- Outcome expansion for the original-order prefix family at a concrete field value. -/
lemma ldSandwichLineOnePointPrefixOriginalFamily_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (a : Fq params) :
    (ldSandwichLineOnePointPrefixOriginalFamily params family hi q).outcome (some a) =
      ∑ gs : GHatTupleOutcome params (i + 1),
        if Option.map (fun g : Polynomial params => g q.1)
            (gs ⟨i, Nat.lt_succ_self i⟩) = some a then
          let half := gHatHalfProductOutcomeOperator params family (i + 1)
            (fun j => q.2 ⟨j.1, by omega⟩) gs
          half * halfᴴ
        else
          0 := by
  simpa [ldSandwichLineOnePointPrefixOriginalFamily] using
    gHatSandwichFamily_restrict_eval_outcome_some
      params family (fun j => q.2 ⟨j.1, by omega⟩)
      ⟨i, Nat.lt_succ_self i⟩ q.1 a

/-- Outcome expansion for the selected-first prefix family at a concrete field value. -/
lemma ldSandwichLineOnePointPrefixMovedFamily_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k)
    (a : Fq params) :
    (ldSandwichLineOnePointPrefixMovedFamily params family hi q).outcome (some a) =
      ∑ gs : GHatTupleOutcome params (i + 1),
        if Option.map (fun g : Polynomial params => g q.1) (gs 0) = some a then
          let xsTail : PointTuple params i := fun j => q.2 ⟨j.1, by omega⟩
          let xs : PointTuple params (i + 1) := Fin.cons (q.2 ⟨i, hi⟩) xsTail
          let half := gHatHalfProductOutcomeOperator params family (i + 1) xs gs
          half * halfᴴ
        else
          0 := by
  simpa [ldSandwichLineOnePointPrefixMovedFamily] using
    gHatSandwichFamily_restrict_eval_outcome_some
      params family (Fin.cons (q.2 ⟨i, hi⟩) (fun j => q.2 ⟨j.1, by omega⟩))
      0 q.1 a

/-- The full one-point left family has no `none` outcome: the selected coordinate is
restricted to genuine completed polynomials before postprocessing by evaluation. -/
lemma ldSandwichLineOnePointLeftFamily_outcome_none_eq_zero
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    ((ldSandwichLineOnePointLeftFamily params strategy family k i) q).outcome none = 0 := by
  conv_lhs =>
    simp [ldSandwichLineOnePointLeftFamily, postprocess, restrictSubMeas, hi,
      Finset.sum_filter]
  apply Finset.sum_eq_zero
  intro gs _hgs
  cases hgs_i : gs ⟨i, hi⟩ with
  | none =>
      simp
  | some g =>
      simp

/-- The prefix-only one-point left family has no `none` outcome. -/
lemma ldSandwichLineOnePointPrefixOriginalFamily_outcome_none_eq_zero
    (params : Parameters)
    [FieldModel params.q]
    (family : IdxPolyFamily params ι)
    {k i : ℕ} (hi : i < k)
    (q : SandwichedLineQuestion params k) :
    (ldSandwichLineOnePointPrefixOriginalFamily params family hi q).outcome none = 0 := by
  conv_lhs =>
    simp [ldSandwichLineOnePointPrefixOriginalFamily, postprocess, restrictSubMeas,
      Finset.sum_filter]
  apply Finset.sum_eq_zero
  intro gs _hgs
  by_cases hsome : (gs ⟨i, Nat.lt_succ_self i⟩).isSome = true
  · rcases Option.isSome_iff_exists.mp hsome with ⟨g, hg⟩
    simp [hg]
  · simp [hsome]

/-- Delete one trailing sandwiched-line coordinate from the full one-point left
family, for a genuine field outcome.

This is the one-coordinate version of paper `ld-pasting.tex` lines 934--941:
summing over an extraneous completed-slice outcome collapses that measurement to
`I`, leaving the shorter sandwich. -/
lemma ldSandwichLineOnePointLeftFamily_drop_last_outcome_some
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    {n i : ℕ} (hi : i < n)
    (q : SandwichedLineQuestion params (n + 1))
    (a : Fq params) :
    ((ldSandwichLineOnePointLeftFamily params strategy family (n + 1) i) q).outcome
        (some a) =
      ((ldSandwichLineOnePointLeftFamily params strategy family n i)
        (q.1, fun j => q.2 ⟨j.1, by omega⟩)).outcome (some a) := by
  let qPrefix : SandwichedLineQuestion params n := (q.1, fun j => q.2 ⟨j.1, by omega⟩)
  have hiFull : i < n + 1 := by omega
  rw [ldSandwichLineOnePointLeftFamily_outcome_some params strategy family hiFull q a]
  rw [ldSandwichLineOnePointLeftFamily_outcome_some params strategy family hi qPrefix a]
  let e := gHatTupleOutcomePrefixLastEquiv params n
  have hsplit :
      (∑ gs : GHatTupleOutcome params (n + 1),
        if Option.map (fun g : Polynomial params => g q.1) (gs ⟨i, hiFull⟩) = some a then
          let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2 gs
          half * halfᴴ
        else
          0) =
      ∑ p : GHatTupleOutcome params n × GHatOutcome params,
        if Option.map (fun g : Polynomial params => g q.1) (p.1 ⟨i, hi⟩) = some a then
          let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2 (e.symm p)
          half * halfᴴ
        else
          0 := by
    exact Fintype.sum_equiv e
      (fun gs : GHatTupleOutcome params (n + 1) =>
        if Option.map (fun g : Polynomial params => g q.1) (gs ⟨i, hiFull⟩) = some a then
          let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2 gs
          half * halfᴴ
        else
          0)
      (fun p : GHatTupleOutcome params n × GHatOutcome params =>
        if Option.map (fun g : Polynomial params => g q.1) (p.1 ⟨i, hi⟩) = some a then
          let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2 (e.symm p)
          half * halfᴴ
        else
          0)
      (by
        intro gs
        change
          (if Option.map (fun g : Polynomial params => g q.1) (gs ⟨i, hiFull⟩) = some a then
            let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2 gs
            half * halfᴴ
          else
            0) =
          (if Option.map (fun g : Polynomial params => g q.1) ((e gs).1 ⟨i, hi⟩) = some a then
            let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2 (e.symm (e gs))
            half * halfᴴ
          else
            0)
        have hleft : e.symm (e gs) = gs := by
          exact e.left_inv gs
        rw [hleft]
        simp [e, gHatTupleOutcomePrefixLastEquiv])
  calc
    (∑ gs : GHatTupleOutcome params (n + 1),
        if Option.map (fun g : Polynomial params => g q.1) (gs ⟨i, hiFull⟩) = some a then
          let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2 gs
          half * halfᴴ
        else
          0)
        = ∑ p : GHatTupleOutcome params n × GHatOutcome params,
            if Option.map (fun g : Polynomial params => g q.1) (p.1 ⟨i, hi⟩) = some a then
              let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2 (e.symm p)
              half * halfᴴ
            else
              0 := hsplit
    _ = ∑ gsPrefix : GHatTupleOutcome params n,
          ∑ g : GHatOutcome params,
            if Option.map (fun g' : Polynomial params => g' q.1) (gsPrefix ⟨i, hi⟩) = some a then
              let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2
                (e.symm (gsPrefix, g))
              half * halfᴴ
            else
              0 := by
          rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ gsPrefix : GHatTupleOutcome params n,
          if Option.map (fun g : Polynomial params => g q.1) (gsPrefix ⟨i, hi⟩) = some a then
            let half := gHatHalfProductOutcomeOperator params family n qPrefix.2 gsPrefix
            half * halfᴴ
          else
            0 := by
          refine Finset.sum_congr rfl ?_
          intro gsPrefix _hgs
          by_cases hmatch : Option.map (fun g : Polynomial params => g q.1)
              (gsPrefix ⟨i, hi⟩) = some a
          · calc
              (∑ g : GHatOutcome params,
                if Option.map (fun g' : Polynomial params => g' q.1)
                    (gsPrefix ⟨i, hi⟩) = some a then
                  let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2
                    (e.symm (gsPrefix, g))
                  half * halfᴴ
                else
                  0)
                  = ∑ g : GHatOutcome params,
                      let half := gHatHalfProductOutcomeOperator params family (n + 1) q.2
                        (e.symm (gsPrefix, g))
                      half * halfᴴ := by
                    simp [hmatch]
              _ = gHatHalfProductOutcomeOperator params family n qPrefix.2 gsPrefix *
                    (gHatHalfProductOutcomeOperator params family n qPrefix.2 gsPrefix)ᴴ := by
                    simpa [qPrefix, e] using
                      gHatSandwich_sum_last_eq_prefix params family n q.2 gsPrefix
              _ = if Option.map (fun g : Polynomial params => g q.1)
                    (gsPrefix ⟨i, hi⟩) = some a then
                    let half := gHatHalfProductOutcomeOperator params family n qPrefix.2 gsPrefix
                    half * halfᴴ
                  else
                    0 := by
                    simp [hmatch]
          · simp [hmatch]

/-- Deleting all coordinates after `i` from the full one-point left family leaves
exactly the prefix family used in the Cauchy--Schwarz transport.

This closes the paper's exact marginalization step `ld-pasting.tex` lines
932--953; the remaining analytic residual starts after this deletion. -/
lemma ldSandwichLineOnePointLeftFamily_eq_prefixOriginal
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι) :
    ∀ {k i : ℕ} (hi : i < k),
      ldSandwichLineOnePointLeftFamily params strategy family k i =
        ldSandwichLineOnePointPrefixOriginalFamily params family hi
  | 0, i, hi => by cases hi
  | n + 1, i, hi => by
      by_cases hlast : i = n
      · subst i
        simpa using ldSandwichLineOnePointLeftFamily_self_eq_prefixOriginal
          params strategy family n
      · have hiPrefix : i < n := by omega
        have ih := ldSandwichLineOnePointLeftFamily_eq_prefixOriginal
          (params := params) (strategy := strategy) (family := family) hiPrefix
        funext q
        let qPrefix : SandwichedLineQuestion params n :=
          (q.1, fun j => q.2 ⟨j.1, by omega⟩)
        have hpref :
            ldSandwichLineOnePointPrefixOriginalFamily params family hiPrefix qPrefix =
              ldSandwichLineOnePointPrefixOriginalFamily params family hi q := by
          simp [ldSandwichLineOnePointPrefixOriginalFamily, qPrefix]
        have hout : ∀ o : Option (Fq params),
            ((ldSandwichLineOnePointLeftFamily params strategy family (n + 1) i) q).outcome o =
              (ldSandwichLineOnePointPrefixOriginalFamily params family hi q).outcome o := by
          intro o
          cases o with
          | none =>
              rw [ldSandwichLineOnePointLeftFamily_outcome_none_eq_zero
                params strategy family hi q]
              rw [ldSandwichLineOnePointPrefixOriginalFamily_outcome_none_eq_zero
                params family hi q]
          | some a =>
              calc
                ((ldSandwichLineOnePointLeftFamily params strategy family (n + 1) i) q).outcome
                    (some a)
                    = ((ldSandwichLineOnePointLeftFamily params strategy family n i)
                        qPrefix).outcome (some a) :=
                      ldSandwichLineOnePointLeftFamily_drop_last_outcome_some
                        params strategy family hiPrefix q a
                _ = (ldSandwichLineOnePointPrefixOriginalFamily params family hiPrefix
                        qPrefix).outcome (some a) := by
                      rw [congrFun ih qPrefix]
                _ = (ldSandwichLineOnePointPrefixOriginalFamily params family hi q).outcome
                        (some a) := by
                      rw [hpref]
        apply SubMeas.ext
        · exact hout
        · rw [← ((ldSandwichLineOnePointLeftFamily params strategy family (n + 1) i)
            q).sum_eq_total]
          rw [← (ldSandwichLineOnePointPrefixOriginalFamily params family hi q).sum_eq_total]
          exact Finset.sum_congr rfl fun o _ho => hout o

-- This arithmetic absorption proof expands several nested error estimates from the paper.
/-- Scalar absorption for the post-tail-deletion one-point estimate.

This is the arithmetic at `references/ldt-paper/ld-pasting.tex:1028--1033`,
with the endpoint error from `eq:ld-gbcon` and the two Cauchy--Schwarz losses
from `ld-pasting.tex:954--1024` kept separate.  The proof uses the paper's
`√426 ≤ 21` estimate and the square comparison
`√(γ^(1/16)+ζ^(1/16)+(d/q)^(1/16)) ≤ γ^(1/32)+ζ^(1/32)+(d/q)^(1/32)`. -/
lemma ldSandwichLineOnePoint_endpoint_comm_error_le
    (params : Parameters) [FieldModel params.q]
    (eps delta gamma zeta : Error) {j k : ℕ}
    (hj_pos : 1 ≤ j) (hjk : j ≤ k)
    (heps_nonneg : 0 ≤ eps)
    (hdelta_nonneg : 0 ≤ delta)
    (hgamma_nonneg : 0 ≤ gamma)
    (hzeta_nonneg : 0 ≤ zeta)
    (hzeta_le : zeta ≤ 1) :
    zeta + Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1) +
        2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta j) ≤
      ldSandwichLineOnePointError params eps delta gamma zeta k := by
  have hm_ge_one : (1 : Error) ≤ (params.m : Error) := by
    exact_mod_cast Nat.succ_le_of_lt params.hm
  have hk_ge_j : (j : Error) ≤ (k : Error) := by exact_mod_cast hjk
  have hratio_nonneg : 0 ≤ ((params.d : Error) / (params.q : Error)) := by
    positivity
  let E : Error := Real.rpow eps (1 / (32 : Error))
  let D : Error := Real.rpow delta (1 / (32 : Error))
  let Γ : Error := Real.rpow gamma (1 / (32 : Error))
  let Z : Error := Real.rpow zeta (1 / (32 : Error))
  let R : Error := Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))
  let S : Error := E + D + Γ + Z + R
  let T : Error := Γ + Z + R
  have hE_nonneg : 0 ≤ E := by dsimp [E]; exact Real.rpow_nonneg heps_nonneg _
  have hD_nonneg : 0 ≤ D := by dsimp [D]; exact Real.rpow_nonneg hdelta_nonneg _
  have hΓ_nonneg : 0 ≤ Γ := by dsimp [Γ]; exact Real.rpow_nonneg hgamma_nonneg _
  have hZ_nonneg : 0 ≤ Z := by dsimp [Z]; exact Real.rpow_nonneg hzeta_nonneg _
  have hR_nonneg : 0 ≤ R := by dsimp [R]; exact Real.rpow_nonneg hratio_nonneg _
  have hzeta_le_Z : zeta ≤ Z := by
    dsimp [Z]
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' hzeta_nonneg hzeta_le
        (by norm_num : 0 ≤ (1 / (32 : Error)))
        (by norm_num : (1 / (32 : Error)) ≤ (1 : Error)))
  have hzeta_bound : zeta ≤ (k : Error) * (params.m : Error) * Z := by
    calc
      zeta ≤ Z := hzeta_le_Z
      _ = 1 * Z := by ring
      _ ≤ ((k : Error) * (params.m : Error)) * Z := by
            have hkm_ge_one : (1 : Error) ≤ (k : Error) * (params.m : Error) := by
              have hk_ge_one : (1 : Error) ≤ (k : Error) := by
                calc
                  (1 : Error) ≤ (j : Error) := by exact_mod_cast hj_pos
                  _ ≤ (k : Error) := hk_ge_j
              calc
                (1 : Error) = 1 * 1 := by ring
                _ ≤ (k : Error) * (params.m : Error) := by
                  exact mul_le_mul hk_ge_one hm_ge_one (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_right hkm_ge_one hZ_nonneg
      _ = (k : Error) * (params.m : Error) * Z := by ring
  have hsqrt_endpoint :=
    ldSandwichLineOnePoint_endpoint_sqrt_bound params eps delta k
      (by
        calc
          1 ≤ j := hj_pos
          _ ≤ k := hjk)
      heps_nonneg hdelta_nonneg
  have hsqrt_bound :
      Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1) ≤
        3 * ((k : Error) * (params.m : Error) * (E + D)) := by
    calc
      Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1)
          ≤ 3 * (k : Error) * (params.m : Error) * (E + D) := by
            simpa [E, D, mul_assoc] using hsqrt_endpoint
      _ = 3 * ((k : Error) * (params.m : Error) * (E + D)) := by ring
  let sixteenthSum : Error :=
    Real.rpow gamma (1 / (16 : Error)) +
      Real.rpow zeta (1 / (16 : Error)) +
      Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error))
  let thirtysecondSum : Error := T
  have hgamma32_sq :
      Γ ^ (2 : ℕ) = Real.rpow gamma (1 / (16 : Error)) := by
    dsimp [Γ]
    calc
      (Real.rpow gamma (1 / (32 : Error))) ^ (2 : ℕ)
          = (Real.rpow gamma (1 / (32 : Error))) ^ (2 : Error) := by norm_num
      _ = Real.rpow gamma ((1 / (32 : Error)) * (2 : Error)) := by
            symm
            exact Real.rpow_mul hgamma_nonneg _ _
      _ = Real.rpow gamma (1 / (16 : Error)) := by norm_num
  have hzeta32_sq :
      Z ^ (2 : ℕ) = Real.rpow zeta (1 / (16 : Error)) := by
    dsimp [Z]
    calc
      (Real.rpow zeta (1 / (32 : Error))) ^ (2 : ℕ)
          = (Real.rpow zeta (1 / (32 : Error))) ^ (2 : Error) := by norm_num
      _ = Real.rpow zeta ((1 / (32 : Error)) * (2 : Error)) := by
            symm
            exact Real.rpow_mul hzeta_nonneg _ _
      _ = Real.rpow zeta (1 / (16 : Error)) := by norm_num
  have hratio32_sq :
      R ^ (2 : ℕ) =
        Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
    dsimp [R]
    calc
      (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) ^
          (2 : ℕ)
          = (Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (32 : Error))) ^
              (2 : Error) := by norm_num
      _ = Real.rpow (((params.d : Error) / (params.q : Error)))
            ((1 / (32 : Error)) * (2 : Error)) := by
            symm
            exact Real.rpow_mul hratio_nonneg _ _
      _ = Real.rpow (((params.d : Error) / (params.q : Error))) (1 / (16 : Error)) := by
            norm_num
  have hsixteenth_le_thirtysecond_sq : sixteenthSum ≤ thirtysecondSum ^ (2 : ℕ) := by
    have hsq : Γ ^ (2 : ℕ) + Z ^ (2 : ℕ) + R ^ (2 : ℕ) ≤ (Γ + Z + R) ^ (2 : ℕ) := by
      nlinarith [hΓ_nonneg, hZ_nonneg, hR_nonneg]
    rw [hgamma32_sq, hzeta32_sq, hratio32_sq] at hsq
    simpa [sixteenthSum, thirtysecondSum, T] using hsq
  have hsixteenth_nonneg : 0 ≤ sixteenthSum := by
    dsimp [sixteenthSum]
    positivity
  have hcomm_sqrt :
      Real.sqrt (commuteGHalfSandwichError params gamma zeta j) ≤
        21 * (j : Error) * (params.m : Error) * T := by
    have hright_nonneg : 0 ≤ 21 * (j : Error) * (params.m : Error) * T := by
      positivity
    refine (Real.sqrt_le_iff).2 ?_
    constructor
    · exact hright_nonneg
    · have hm_sq_ge : (params.m : Error) ≤ (params.m : Error) ^ (2 : ℕ) := by
        nlinarith [hm_ge_one]
      calc
        commuteGHalfSandwichError params gamma zeta j
            = 426 * ((j : Error) ^ (2 : ℕ)) * (params.m : Error) * sixteenthSum := by
              simp [commuteGHalfSandwichError, sixteenthSum]
        _ ≤ 441 * ((j : Error) ^ (2 : ℕ)) * (params.m : Error) * sixteenthSum := by
              have hcoef :
                  426 * ((j : Error) ^ (2 : ℕ)) * (params.m : Error) ≤
                    441 * ((j : Error) ^ (2 : ℕ)) * (params.m : Error) := by
                have hbase : (426 : Error) ≤ 441 := by norm_num
                have htail_nonneg : 0 ≤ ((j : Error) ^ (2 : ℕ)) * (params.m : Error) := by
                  positivity
                simpa [mul_assoc] using mul_le_mul_of_nonneg_right hbase htail_nonneg
              exact mul_le_mul_of_nonneg_right hcoef hsixteenth_nonneg
        _ ≤ 441 * ((j : Error) ^ (2 : ℕ)) * (params.m : Error) *
              (thirtysecondSum ^ (2 : ℕ)) := by
              have hcoef_nonneg : 0 ≤ 441 * ((j : Error) ^ (2 : ℕ)) * (params.m : Error) := by
                positivity
              exact mul_le_mul_of_nonneg_left hsixteenth_le_thirtysecond_sq hcoef_nonneg
        _ ≤ 441 * ((j : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
              (thirtysecondSum ^ (2 : ℕ)) := by
              gcongr
        _ = (21 * (j : Error) * (params.m : Error) * T) ^ (2 : ℕ) := by
              simp [thirtysecondSum]
              ring
  have hcomm_bound :
      2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta j) ≤
        42 * ((k : Error) * (params.m : Error) * T) := by
    have hjT_to_kT : (j : Error) * (params.m : Error) * T ≤
        (k : Error) * (params.m : Error) * T := by
      have hmT_nonneg : 0 ≤ (params.m : Error) * T := by positivity
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hk_ge_j hmT_nonneg
    calc
      2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta j)
          ≤ 2 * (21 * (j : Error) * (params.m : Error) * T) := by
            exact mul_le_mul_of_nonneg_left hcomm_sqrt (by norm_num)
      _ = 42 * ((j : Error) * (params.m : Error) * T) := by ring
      _ ≤ 42 * ((k : Error) * (params.m : Error) * T) := by
            exact mul_le_mul_of_nonneg_left hjT_to_kT (by norm_num)
  have hcomponent :
      (k : Error) * (params.m : Error) * Z +
          3 * ((k : Error) * (params.m : Error) * (E + D)) +
          42 * ((k : Error) * (params.m : Error) * T) ≤
        43 * ((k : Error) * (params.m : Error) * S) := by
    have hleft_nonneg : 0 ≤ (k : Error) * (params.m : Error) := by positivity
    dsimp [S, T]
    nlinarith [hleft_nonneg, hE_nonneg, hD_nonneg, hΓ_nonneg, hZ_nonneg, hR_nonneg]
  calc
    zeta + Real.sqrt (8 * (params.m : Error) * min eps 1 + 4 * min delta 1) +
        2 * Real.sqrt (commuteGHalfSandwichError params gamma zeta j)
        ≤ (k : Error) * (params.m : Error) * Z +
            3 * ((k : Error) * (params.m : Error) * (E + D)) +
            42 * ((k : Error) * (params.m : Error) * T) := by
          nlinarith [hzeta_bound, hsqrt_bound, hcomm_bound]
    _ ≤ 43 * ((k : Error) * (params.m : Error) * S) := hcomponent
    _ = ldSandwichLineOnePointError params eps delta gamma zeta k := by
          simp [ldSandwichLineOnePointError, S, E, D, Γ, Z, R]
          ring


end MIPStarRE.LDT.Pasting
