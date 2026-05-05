import MIPStarRE.LDT.SelfImprovement.Theorems.Results.AddInUStep12.Algebra

/-!
# Selected add-in-u Step 1/2 Cauchy--Schwarz bounds

Selected-family contraction inputs and raw `√(2δ)` estimates for the first
two add-in-u moves in the self-improvement chain.
-/

namespace MIPStarRE.LDT.SelfImprovement

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.GlobalVariance
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The selected fiber tensor mass is a contraction.

For fixed points `u, v` and a value `a`, the selected sum over pairs
`(o,h) ∈ S_u` with `h(v)=a` is bounded by the full product
`M^u_{\mathrm{tot}} ⊗ T_{\mathrm{tot}}`, hence by the identity. -/
private lemma addInU_selected_filtered_tensor_sum_le_one
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (u v : Point params)
    (a : Fq params) :
    ∑ ah ∈ (addInUSelectionPairs params S u).filter (fun ah => ah.2 v = a),
        opTensor ((M u).outcome ah.1) (T.outcome ah.2) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  calc
    ∑ ah ∈ (addInUSelectionPairs params S u).filter (fun ah => ah.2 v = a),
        opTensor ((M u).outcome ah.1) (T.outcome ah.2)
        ≤ ∑ ah : Outcome × Polynomial params,
            opTensor ((M u).outcome ah.1) (T.outcome ah.2) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (by
              intro ah hah
              exact Finset.mem_univ ah)
            (by
              intro ah _ _
              exact opTensor_nonneg ((M u).outcome_pos ah.1) (T.outcome_pos ah.2))
    _ = opTensor (M u).total T.total := by
          change (∑ oh ∈ (Finset.univ : Finset Outcome).product
                (Finset.univ : Finset (Polynomial params)),
              opTensor ((M u).outcome oh.1) (T.outcome oh.2)) =
            opTensor (M u).total T.total
          have hprod :
              (∑ oh ∈ (Finset.univ : Finset Outcome).product
                  (Finset.univ : Finset (Polynomial params)),
                opTensor ((M u).outcome oh.1) (T.outcome oh.2)) =
                ∑ o ∈ (Finset.univ : Finset Outcome),
                  ∑ h ∈ (Finset.univ : Finset (Polynomial params)),
                    opTensor ((M u).outcome o) (T.outcome h) := by
            simpa using
              (Finset.sum_product
                (s := (Finset.univ : Finset Outcome))
                (t := (Finset.univ : Finset (Polynomial params)))
                (f := fun oh : Outcome × Polynomial params =>
                  opTensor ((M u).outcome oh.1) (T.outcome oh.2)))
          rw [hprod]
          calc
            ∑ o : Outcome, ∑ h : Polynomial params,
                opTensor ((M u).outcome o) (T.outcome h)
                = ∑ o : Outcome, opTensor ((M u).outcome o) T.total := by
                  refine Finset.sum_congr rfl ?_
                  intro o _
                  rw [← T.sum_eq_total, opTensor_sum_right_univ]
            _ = opTensor (M u).total T.total := by
                  rw [← (M u).sum_eq_total, opTensor_sum_left_univ]
    _ ≤ leftTensor (ι₂ := ι) (M u).total := by
          exact opTensor_le_leftTensor (SubMeas.total_nonneg (M u)) T.total_le_one
    _ ≤ (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
          exact leftTensor_le_one (ι₂ := ι) (M u).total_le_one

/-- Cauchy--Schwarz contraction side condition for selected Step 1.

For a fixed `(u, v)`, the selected fiber sum
`K_a = ∑_{(o,h) ∈ S_u, h(v)=a} M^u_o ⊗ T_h` is a contraction.  Sandwiching
by the right-register point projector `A^v_a` and summing over `a` is therefore
bounded by the identity. -/
private lemma addInU_selected_step1_C_contraction
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (uv : Point params × Point params) :
    ∑ a : Fq params,
        (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ *
          (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)) ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  let K : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    ∑ ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a),
      opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)
  let Pa : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    rightTensor (ι₁ := ι) ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  have hsum_eq : ∀ a : Fq params,
      (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
          (fun ah => ah.2 uv.2 = a),
        opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            rightTensor (ι₁ := ι)
              ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)) =
        K a * Pa a := by
    intro a
    rw [← Finset.sum_mul]
  have hK_herm : ∀ a, (K a)ᴴ = K a := by
    intro a
    have hM_herm : ∀ o : Outcome, ((M uv.1).outcome o)ᴴ = (M uv.1).outcome o :=
      fun o =>
        (Matrix.nonneg_iff_posSemidef.mp ((M uv.1).outcome_pos o)).isHermitian.eq
    have hT_herm : ∀ h : Polynomial params, (T.outcome h)ᴴ = T.outcome h := fun h =>
      (Matrix.nonneg_iff_posSemidef.mp (T.outcome_pos h)).isHermitian.eq
    simp [K, Matrix.conjTranspose_sum, conjTranspose_opTensor, hM_herm, hT_herm]
  have hPa_herm : ∀ a, (Pa a)ᴴ = Pa a := by
    intro a
    have hOutcome_herm :
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)ᴴ =
          (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (Matrix.nonneg_iff_posSemidef.mp
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome_pos a)).isHermitian.eq
    simp [Pa, rightTensor_conjTranspose, hOutcome_herm]
  have hPa_proj : ∀ a, Pa a * Pa a = Pa a := by
    intro a
    have hproj : (strategy.pointMeasurement uv.2).toSubMeas.outcome a *
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a =
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (strategy.pointMeasurement uv.2).proj a
    change rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
        rightTensor (ι₁ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [rightTensor_mul_rightTensor, hproj]
  have hK_nonneg : ∀ a, 0 ≤ K a := by
    intro a
    refine Finset.sum_nonneg ?_
    intro ah _
    exact opTensor_nonneg ((M uv.1).outcome_pos ah.1) (T.outcome_pos ah.2)
  have hK_le_one : ∀ a, K a ≤ 1 := by
    intro a
    exact addInU_selected_filtered_tensor_sum_le_one params M T S uv.1 uv.2 a
  have hK_sq_le_one : ∀ a, K a * K a ≤ 1 := by
    intro a
    exact le_trans (MIPStarRE.Quantum.sq_le_self (hK_nonneg a) (hK_le_one a)) (hK_le_one a)
  have hterm_le : ∀ a : Fq params, (K a * Pa a)ᴴ * (K a * Pa a) ≤ Pa a := by
    intro a
    have hexpand : (K a * Pa a)ᴴ * (K a * Pa a) = Pa a * (K a * K a) * Pa a := by
      rw [Matrix.conjTranspose_mul, hK_herm a, hPa_herm a]
      ac_rfl
    rw [hexpand]
    calc
      Pa a * (K a * K a) * Pa a
          ≤ Pa a * 1 * Pa a := MIPStarRE.Quantum.sandwich_mono (hPa_herm a) (hK_sq_le_one a)
      _ = Pa a * Pa a := by simp
      _ = Pa a := hPa_proj a
  have hsum_Pa : ∑ a : Fq params, Pa a = (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    change ∑ a : Fq params,
        rightTensor (ι₁ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      (1 : MIPStarRE.Quantum.Op (ι × ι))
    rw [rightTensor_finset_sum]
    rw [(strategy.pointMeasurement uv.2).toSubMeas.sum_eq_total]
    have htotal : (strategy.pointMeasurement uv.2).toSubMeas.total = 1 :=
      (strategy.pointMeasurement uv.2).total_eq_one
    rw [htotal, rightTensor_one]
  calc
    ∑ a : Fq params,
        (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ *
          (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
                rightTensor (ι₁ := ι)
                  ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))
        = ∑ a : Fq params, (K a * Pa a)ᴴ * (K a * Pa a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hsum_eq a]
      _ ≤ ∑ a : Fq params, Pa a := Finset.sum_le_sum (fun a _ => hterm_le a)
      _ = 1 := hsum_Pa

/-- Cauchy--Schwarz contraction side condition for selected Step 2.

This is the left-register analogue of `addInU_selected_step1_C_contraction`:
for each fixed `(u,v)`, the operators
`C_a = A^v_a \otimes I · K_a`, with `K_a` the selected fiber tensor mass,
have `∑_a C_a C_aᴴ ≤ I`. -/
private lemma addInU_selected_step2_C_contraction
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (uv : Point params × Point params) :
    ∑ a : Fq params,
        (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            leftTensor (ι₂ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
              opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)) *
          (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            leftTensor (ι₂ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
              opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2))ᴴ ≤
      (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
  classical
  let K : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    ∑ ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a),
      opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)
  let Pa : Fq params → MIPStarRE.Quantum.Op (ι × ι) := fun a =>
    leftTensor (ι₂ := ι) ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  have hsum_eq : ∀ a : Fq params,
      (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
          (fun ah => ah.2 uv.2 = a),
        leftTensor (ι₂ := ι)
            ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
          opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)) =
        Pa a * K a := by
    intro a
    rw [← Finset.mul_sum]
  have hK_herm : ∀ a, (K a)ᴴ = K a := by
    intro a
    have hM_herm : ∀ o : Outcome, ((M uv.1).outcome o)ᴴ = (M uv.1).outcome o :=
      fun o =>
        (Matrix.nonneg_iff_posSemidef.mp ((M uv.1).outcome_pos o)).isHermitian.eq
    have hT_herm : ∀ h : Polynomial params, (T.outcome h)ᴴ = T.outcome h := fun h =>
      (Matrix.nonneg_iff_posSemidef.mp (T.outcome_pos h)).isHermitian.eq
    simp [K, Matrix.conjTranspose_sum, conjTranspose_opTensor, hM_herm, hT_herm]
  have hPa_herm : ∀ a, (Pa a)ᴴ = Pa a := by
    intro a
    have hOutcome_herm :
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)ᴴ =
          (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (Matrix.nonneg_iff_posSemidef.mp
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome_pos a)).isHermitian.eq
    simp [Pa, leftTensor_conjTranspose, hOutcome_herm]
  have hPa_proj : ∀ a, Pa a * Pa a = Pa a := by
    intro a
    have hproj : (strategy.pointMeasurement uv.2).toSubMeas.outcome a *
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a =
        (strategy.pointMeasurement uv.2).toSubMeas.outcome a :=
      (strategy.pointMeasurement uv.2).proj a
    change leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
        leftTensor (ι₂ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [leftTensor_mul_leftTensor, hproj]
  have hK_nonneg : ∀ a, 0 ≤ K a := by
    intro a
    refine Finset.sum_nonneg ?_
    intro ah _
    exact opTensor_nonneg ((M uv.1).outcome_pos ah.1) (T.outcome_pos ah.2)
  have hK_le_one : ∀ a, K a ≤ 1 := by
    intro a
    exact addInU_selected_filtered_tensor_sum_le_one params M T S uv.1 uv.2 a
  have hK_sq_le_one : ∀ a, K a * K a ≤ 1 := by
    intro a
    exact le_trans (MIPStarRE.Quantum.sq_le_self (hK_nonneg a) (hK_le_one a)) (hK_le_one a)
  have hterm_le : ∀ a : Fq params, (Pa a * K a) * (Pa a * K a)ᴴ ≤ Pa a := by
    intro a
    have hexpand : (Pa a * K a) * (Pa a * K a)ᴴ = Pa a * (K a * K a) * Pa a := by
      rw [Matrix.conjTranspose_mul, hK_herm a, hPa_herm a]
      ac_rfl
    rw [hexpand]
    calc
      Pa a * (K a * K a) * Pa a
          ≤ Pa a * 1 * Pa a := MIPStarRE.Quantum.sandwich_mono (hPa_herm a) (hK_sq_le_one a)
      _ = Pa a * Pa a := by simp
      _ = Pa a := hPa_proj a
  have hsum_Pa : ∑ a : Fq params, Pa a = (1 : MIPStarRE.Quantum.Op (ι × ι)) := by
    change ∑ a : Fq params,
        leftTensor (ι₂ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) =
      (1 : MIPStarRE.Quantum.Op (ι × ι))
    rw [leftTensor_finset_sum]
    rw [(strategy.pointMeasurement uv.2).toSubMeas.sum_eq_total]
    have htotal : (strategy.pointMeasurement uv.2).toSubMeas.total = 1 :=
      (strategy.pointMeasurement uv.2).total_eq_one
    rw [htotal, leftTensor_one]
  calc
    ∑ a : Fq params,
        (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            leftTensor (ι₂ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
              opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)) *
          (∑ ah ∈ (addInUSelectionPairs params S uv.1).filter
              (fun ah => ah.2 uv.2 = a),
            leftTensor (ι₂ := ι)
                ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
              opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2))ᴴ
        = ∑ a : Fq params, (Pa a * K a) * (Pa a * K a)ᴴ := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hsum_eq a]
      _ ≤ ∑ a : Fq params, Pa a := Finset.sum_le_sum (fun a _ => hterm_le a)
      _ = 1 := hsum_Pa

/-- Raw selected `|Q₀ - Q₁| ≤ √(2δ)` bound for the first add-in-u move.

This is the selection-parametrized form of
`addInU_cs_chain_step1_abs_le_sqrt_two_delta`.  It applies the weighted
Cauchy--Schwarz estimate to the selected pairs `(o,h) ∈ S_u`; the contraction
side condition is `addInU_selected_step1_C_contraction`. -/
lemma addInU_selected_cs_chain_step1_abs_le_sqrt_two_delta
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (delta : Error)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |addInUSelectedCSChainQ0 params strategy M T S -
        addInUSelectedCSChainQ1 params strategy M T S| ≤
      Real.sqrt (2 * delta) := by
  classical
  have hSDD := addInU_pointMeasurement_snd_selfConsistency params strategy delta hssc
  let Aop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => leftTensor (ι₂ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Bop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => rightTensor (ι₁ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Cop : Point params × Point params → Fq params → Outcome × Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a ah =>
      if ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a) then
        opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
          rightTensor (ι₁ := ι)
            ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
      else 0
  have hOutcome_herm : ∀ (v : Point params) (a : Fq params),
      ((strategy.pointMeasurement v).toSubMeas.outcome a)ᴴ =
        (strategy.pointMeasurement v).toSubMeas.outcome a := fun v a =>
    (Matrix.nonneg_iff_posSemidef.mp
      ((strategy.pointMeasurement v).toSubMeas.outcome_pos a)).isHermitian.eq
  have hAop_herm : ∀ uv a, (Aop uv a)ᴴ = Aop uv a := by
    intro uv a
    change (leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ =
      leftTensor (ι₂ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [leftTensor_conjTranspose, hOutcome_herm uv.2 a]
  have hBop_herm : ∀ uv a, (Bop uv a)ᴴ = Bop uv a := by
    intro uv a
    change (rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a))ᴴ =
      rightTensor (ι₁ := ι)
        ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    rw [rightTensor_conjTranspose, hOutcome_herm uv.2 a]
  have hfun_A : ∀ uv : Point params × Point params,
      (fun a : Fq params => (Aop uv a)ᴴ) = Aop uv := by
    intro uv
    funext a
    exact hAop_herm uv a
  have hfun_B : ∀ uv : Point params × Point params,
      (fun a : Fq params => (Bop uv a)ᴴ) = Bop uv := by
    intro uv
    funext a
    exact hBop_herm uv a
  have hAB :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        qSDDCore strategy.state
          (fun a : Fq params => (Aop uv a)ᴴ) (fun a : Fq params => (Bop uv a)ᴴ)) ≤
        2 * delta := by
    rcases hSDD with ⟨hsdd⟩
    refine le_trans ?_ hsdd
    refine le_of_eq ?_
    refine avgOver_congr _ _ _ ?_
    intro uv
    rw [hfun_A uv, hfun_B uv]
    rfl
  have hsum_C : ∀ (uv : Point params × Point params) (a : Fq params),
      (∑ ah : Outcome × Polynomial params, Cop uv a ah) =
        ∑ ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a),
          opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            rightTensor (ι₁ := ι)
              ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) := by
    intro uv a
    let s := (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a)
    let f : Outcome × Polynomial params → MIPStarRE.Quantum.Op (ι × ι) := fun ah =>
      opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
        rightTensor (ι₁ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
    have hfilter :
        (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0) =
          ∑ ah ∈ s, f ah := by
      calc
        (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0)
            = ∑ ah ∈ s, if ah ∈ s then f ah else 0 := by
                exact
                  (Finset.sum_subset (Finset.subset_univ s)
                    (fun ah _ hnot => by simp [hnot])).symm
        _ = ∑ ah ∈ s, f ah := by
              refine Finset.sum_congr rfl ?_
              intro ah hah
              simp [hah]
    simpa [Cop, s, f] using hfilter
  have hC : ∀ uv : Point params × Point params,
      (∑ a : Fq params,
          (∑ ah : Outcome × Polynomial params, Cop uv a ah)ᴴ *
            (∑ ah : Outcome × Polynomial params, Cop uv a ah)) ≤ 1 := by
    intro uv
    simpa [hsum_C uv] using addInU_selected_step1_C_contraction params strategy M T S uv
  have hcs := MIPStarRE.LDT.Preliminaries.closenessOfInnerProduct_right
    strategy.state strategy.isNormalized
    (uniformDistribution (Point params × Point params))
    (uniformDistribution_weight_sum_le_one (Point params × Point params))
    Aop Bop Cop (2 * delta) hAB hC
  have hcollapse :
      ∀ (uv : Point params × Point params)
        (D : (Point params × Point params) → Fq params →
          MIPStarRE.Quantum.Op (ι × ι)),
        (∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
            ev strategy.state (D uv a * Cop uv a ah)) =
          ∑ ah ∈ addInUSelectionPairs params S uv.1,
            ev strategy.state
              (D uv (ah.2 uv.2) *
                (opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
                  rightTensor (ι₁ := ι)
                    ((strategy.pointMeasurement uv.2).toSubMeas.outcome (ah.2 uv.2)))) := by
    intro uv D
    rw [Finset.sum_comm]
    let s := addInUSelectionPairs params S uv.1
    let f : Outcome × Polynomial params → Error := fun ah =>
      ev strategy.state
        (D uv (ah.2 uv.2) *
          (opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            rightTensor (ι₁ := ι)
              ((strategy.pointMeasurement uv.2).toSubMeas.outcome (ah.2 uv.2))))
    have hinner : ∀ ah : Outcome × Polynomial params,
        (∑ a : Fq params, ev strategy.state (D uv a * Cop uv a ah)) =
          if ah ∈ s then f ah else 0 := by
      intro ah
      by_cases hmem : ah ∈ s
      · rw [Finset.sum_eq_single (ah.2 uv.2)]
        · simp [Cop, s, f, hmem]
        · intro a _ ha
          have hnot : ah ∉ s.filter (fun bh => bh.2 uv.2 = a) := by
            intro hf
            exact ha (Eq.symm (Finset.mem_filter.mp hf).2)
          have hCop_zero : Cop uv a ah = 0 := by
            have hnot' :
                ¬ (ah ∈ addInUSelectionPairs params S uv.1 ∧ ah.2 uv.2 = a) := by
              intro hf
              exact hnot (Finset.mem_filter.mpr hf)
            simp [Cop, hnot']
          rw [hCop_zero, Matrix.mul_zero, ev_zero]
        · intro hmissing
          exact (hmissing (Finset.mem_univ _)).elim
      · have hzero : ∀ a : Fq params, ah ∉ s.filter (fun bh => bh.2 uv.2 = a) := by
          intro a hf
          exact hmem ((Finset.mem_filter.mp hf).1)
        calc
          ∑ a : Fq params, ev strategy.state (D uv a * Cop uv a ah)
              = ∑ a : Fq params, 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro a _
                  have hCop_zero : Cop uv a ah = 0 := by
                    have hnot' :
                        ¬ (ah ∈ addInUSelectionPairs params S uv.1 ∧ ah.2 uv.2 = a) := by
                      intro hf
                      exact hzero a (Finset.mem_filter.mpr hf)
                    simp [Cop, hnot']
                  rw [hCop_zero, Matrix.mul_zero, ev_zero]
          _ = if ah ∈ s then f ah else 0 := by simp [hmem]
    calc
      ∑ ah : Outcome × Polynomial params,
          ∑ a : Fq params, ev strategy.state (D uv a * Cop uv a ah)
          = ∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0 := by
              refine Finset.sum_congr rfl ?_
              intro ah _
              exact hinner ah
      _ = ∑ ah ∈ s, f ah := by
            have hfilter :
                (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0) =
                  ∑ ah ∈ s, f ah := by
              calc
                (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0)
                    = ∑ ah ∈ s, if ah ∈ s then f ah else 0 := by
                        exact
                          (Finset.sum_subset (Finset.subset_univ s)
                            (fun ah _ hnot => by simp [hnot])).symm
                _ = ∑ ah ∈ s, f ah := by
                      refine Finset.sum_congr rfl ?_
                      intro ah hah
                      simp [hah]
            exact hfilter
  have hmatch_pointwise : ∀ uv : Point params × Point params,
      (∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Aop uv a * Cop uv a ah)) -
        (∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Bop uv a * Cop uv a ah)) =
      ∑ ah ∈ addInUSelectionPairs params S uv.1,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state
          ((leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av) *
            (opTensor Moh (T.outcome ah.2) * rightTensor (ι₁ := ι) Av)) := by
    intro uv
    rw [hcollapse uv Aop, hcollapse uv Bop]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro ah _
    rw [← ev_sub]
    congr 1
    change
      leftTensor (ι₂ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) *
          (opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            rightTensor (ι₁ := ι)
              (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2)) -
        rightTensor (ι₁ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) *
          (opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            rightTensor (ι₁ := ι)
              (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2)) =
        (leftTensor (ι₂ := ι)
            (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) -
          rightTensor (ι₁ := ι)
            (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2)) *
          (opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            rightTensor (ι₁ := ι)
              (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2))
    noncomm_ring
  have hmatch :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Aop uv a * Cop uv a ah)) -
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Bop uv a * Cop uv a ah)) =
      addInUSelectedCSChainQ1 params strategy M T S -
        addInUSelectedCSChainQ0 params strategy M T S := by
    rw [addInU_selected_cs_chain_step1_diff_eq params strategy M T S]
    rw [← avgOver_sub]
    refine avgOver_congr _ _ _ ?_
    intro uv
    exact hmatch_pointwise uv
  rw [abs_sub_comm]
  rw [← hmatch]
  exact hcs

/-- Raw selected `|Q₁ - Q₂| ≤ √(2δ)` bound for the second add-in-u move.

This is the selection-parametrized form of
`addInU_cs_chain_step2_abs_le_sqrt_two_delta`.  It uses the left-action
Cauchy--Schwarz estimate with the selected Step 2 contraction side condition. -/
lemma addInU_selected_cs_chain_step2_abs_le_sqrt_two_delta
    {Outcome : Type*} [Fintype Outcome]
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params ι)
    (M : IdxSubMeas (Point params) Outcome ι)
    (T : SubMeas (Polynomial params) ι)
    (S : AddInUSelection params Outcome)
    (delta : Error)
    (hssc : BipartiteSSCRel strategy.state (uniformDistribution (Point params))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement) delta) :
    |addInUSelectedCSChainQ1 params strategy M T S -
        addInUSelectedCSChainQ2 params strategy M T S| ≤
      Real.sqrt (2 * delta) := by
  classical
  have hSDD := addInU_pointMeasurement_snd_selfConsistency params strategy delta hssc
  let Aop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => leftTensor (ι₂ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Bop : Point params × Point params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a => rightTensor (ι₁ := ι)
      ((strategy.pointMeasurement uv.2).toSubMeas.outcome a)
  let Cop : Point params × Point params → Fq params → Outcome × Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun uv a ah =>
      if ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a) then
        leftTensor (ι₂ := ι)
            ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
          opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)
      else 0
  have hAB :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        qSDDCore strategy.state (Aop uv) (Bop uv)) ≤ 2 * delta := by
    rcases hSDD with ⟨hsdd⟩
    refine le_trans ?_ hsdd
    refine le_of_eq ?_
    refine avgOver_congr _ _ _ ?_
    intro uv
    rfl
  have hsum_C : ∀ (uv : Point params × Point params) (a : Fq params),
      (∑ ah : Outcome × Polynomial params, Cop uv a ah) =
        ∑ ah ∈ (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a),
          leftTensor (ι₂ := ι)
              ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
            opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) := by
    intro uv a
    let s := (addInUSelectionPairs params S uv.1).filter (fun ah => ah.2 uv.2 = a)
    let f : Outcome × Polynomial params → MIPStarRE.Quantum.Op (ι × ι) := fun ah =>
      leftTensor (ι₂ := ι)
          ((strategy.pointMeasurement uv.2).toSubMeas.outcome a) *
        opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)
    have hfilter :
        (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0) =
          ∑ ah ∈ s, f ah := by
      calc
        (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0)
            = ∑ ah ∈ s, if ah ∈ s then f ah else 0 := by
                exact
                  (Finset.sum_subset (Finset.subset_univ s)
                    (fun ah _ hnot => by simp [hnot])).symm
        _ = ∑ ah ∈ s, f ah := by
              refine Finset.sum_congr rfl ?_
              intro ah hah
              simp [hah]
    simpa [Cop, s, f] using hfilter
  have hC : ∀ uv : Point params × Point params,
      (∑ a : Fq params,
          (∑ ah : Outcome × Polynomial params, Cop uv a ah) *
            (∑ ah : Outcome × Polynomial params, Cop uv a ah)ᴴ) ≤ 1 := by
    intro uv
    simpa [hsum_C uv] using addInU_selected_step2_C_contraction params strategy M T S uv
  have hcs := MIPStarRE.LDT.Preliminaries.closenessOfInnerProduct_left
    strategy.state strategy.isNormalized
    (uniformDistribution (Point params × Point params))
    (uniformDistribution_weight_sum_le_one (Point params × Point params))
    Aop Bop Cop (2 * delta) hAB hC
  have hcollapse :
      ∀ (uv : Point params × Point params)
        (D : (Point params × Point params) → Fq params →
          MIPStarRE.Quantum.Op (ι × ι)),
        (∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
            ev strategy.state (Cop uv a ah * D uv a)) =
          ∑ ah ∈ addInUSelectionPairs params S uv.1,
            ev strategy.state
              ((leftTensor (ι₂ := ι)
                    ((strategy.pointMeasurement uv.2).toSubMeas.outcome (ah.2 uv.2)) *
                  opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)) *
                D uv (ah.2 uv.2)) := by
    intro uv D
    rw [Finset.sum_comm]
    let s := addInUSelectionPairs params S uv.1
    let f : Outcome × Polynomial params → Error := fun ah =>
      ev strategy.state
        ((leftTensor (ι₂ := ι)
              ((strategy.pointMeasurement uv.2).toSubMeas.outcome (ah.2 uv.2)) *
            opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)) *
          D uv (ah.2 uv.2))
    have hinner : ∀ ah : Outcome × Polynomial params,
        (∑ a : Fq params, ev strategy.state (Cop uv a ah * D uv a)) =
          if ah ∈ s then f ah else 0 := by
      intro ah
      by_cases hmem : ah ∈ s
      · rw [Finset.sum_eq_single (ah.2 uv.2)]
        · simp [Cop, s, f, hmem]
        · intro a _ ha
          have hnot : ah ∉ s.filter (fun bh => bh.2 uv.2 = a) := by
            intro hf
            exact ha (Eq.symm (Finset.mem_filter.mp hf).2)
          have hCop_zero : Cop uv a ah = 0 := by
            have hnot' :
                ¬ (ah ∈ addInUSelectionPairs params S uv.1 ∧ ah.2 uv.2 = a) := by
              intro hf
              exact hnot (Finset.mem_filter.mpr hf)
            simp [Cop, hnot']
          rw [hCop_zero, Matrix.zero_mul, ev_zero]
        · intro hmissing
          exact (hmissing (Finset.mem_univ _)).elim
      · have hzero : ∀ a : Fq params, ah ∉ s.filter (fun bh => bh.2 uv.2 = a) := by
          intro a hf
          exact hmem ((Finset.mem_filter.mp hf).1)
        calc
          ∑ a : Fq params, ev strategy.state (Cop uv a ah * D uv a)
              = ∑ a : Fq params, 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro a _
                  have hCop_zero : Cop uv a ah = 0 := by
                    have hnot' :
                        ¬ (ah ∈ addInUSelectionPairs params S uv.1 ∧ ah.2 uv.2 = a) := by
                      intro hf
                      exact hzero a (Finset.mem_filter.mpr hf)
                    simp [Cop, hnot']
                  rw [hCop_zero, Matrix.zero_mul, ev_zero]
          _ = if ah ∈ s then f ah else 0 := by simp [hmem]
    calc
      ∑ ah : Outcome × Polynomial params,
          ∑ a : Fq params, ev strategy.state (Cop uv a ah * D uv a)
          = ∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0 := by
              refine Finset.sum_congr rfl ?_
              intro ah _
              exact hinner ah
      _ = ∑ ah ∈ s, f ah := by
            have hfilter :
                (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0) =
                  ∑ ah ∈ s, f ah := by
              calc
                (∑ ah : Outcome × Polynomial params, if ah ∈ s then f ah else 0)
                    = ∑ ah ∈ s, if ah ∈ s then f ah else 0 := by
                        exact
                          (Finset.sum_subset (Finset.subset_univ s)
                            (fun ah _ hnot => by simp [hnot])).symm
                _ = ∑ ah ∈ s, f ah := by
                      refine Finset.sum_congr rfl ?_
                      intro ah hah
                      simp [hah]
            exact hfilter
  have hmatch_pointwise : ∀ uv : Point params × Point params,
      (∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Cop uv a ah * Aop uv a)) -
        (∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Cop uv a ah * Bop uv a)) =
      ∑ ah ∈ addInUSelectionPairs params S uv.1,
        let Av := pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2
        let Moh := (M uv.1).outcome ah.1
        ev strategy.state
          (leftTensor (ι₂ := ι) Av *
            (opTensor Moh (T.outcome ah.2) *
              (leftTensor (ι₂ := ι) Av - rightTensor (ι₁ := ι) Av))) := by
    intro uv
    rw [hcollapse uv Aop, hcollapse uv Bop]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro ah _
    rw [← ev_sub]
    congr 1
    change
      (leftTensor (ι₂ := ι)
            (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) *
          opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)) *
          leftTensor (ι₂ := ι)
            (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) -
        (leftTensor (ι₂ := ι)
            (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) *
          opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2)) *
          rightTensor (ι₁ := ι)
            (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) =
        leftTensor (ι₂ := ι)
          (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) *
          (opTensor ((M uv.1).outcome ah.1) (T.outcome ah.2) *
            (leftTensor (ι₂ := ι)
                (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2) -
              rightTensor (ι₁ := ι)
                (pointConditionedOutcomeOperatorAtPolynomial params strategy ah.2 uv.2)))
    noncomm_ring
  have hmatch :
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Cop uv a ah * Aop uv a)) -
      avgOver (uniformDistribution (Point params × Point params)) (fun uv =>
        ∑ a : Fq params, ∑ ah : Outcome × Polynomial params,
          ev strategy.state (Cop uv a ah * Bop uv a)) =
      addInUSelectedCSChainQ2 params strategy M T S -
        addInUSelectedCSChainQ1 params strategy M T S := by
    rw [addInU_selected_cs_chain_step2_diff_eq params strategy M T S]
    rw [← avgOver_sub]
    refine avgOver_congr _ _ _ ?_
    intro uv
    exact hmatch_pointwise uv
  rw [abs_sub_comm]
  rw [← hmatch]
  exact hcs


end MIPStarRE.LDT.SelfImprovement
