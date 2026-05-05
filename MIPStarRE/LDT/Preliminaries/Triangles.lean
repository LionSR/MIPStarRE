import Mathlib.Algebra.Order.Chebyshev
import MIPStarRE.LDT.Preliminaries.CauchySchwarz

/-! # Triangle Inequalities for State-Dependent Distance

Formalizes the triangle inequality for vectors squared
(`prop:triangle-inequality-for-vectors-squared`), the substitution triangle
(`prop:triangle-sub`), and the consistency triangle inequality
(`prop:simeq-triangle-inequality`) from the LDT paper §3.

## References
- [arXiv:2009.12982] §3, Propositions at lines 596–684 of `preliminaries.tex`
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- Symmetry of the question-level state-dependent distance. -/
lemma qSDD_symm
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) :
    qSDD ψ A B = qSDD ψ B A := by
  let F : Outcome → MIPStarRE.Quantum.Op ι := fun a => A.outcome a - B.outcome a
  let G : Outcome → MIPStarRE.Quantum.Op ι := fun a => B.outcome a - A.outcome a
  have hFG : F = fun a => -G a := by
    funext a
    dsimp [F, G]
    abel
  unfold qSDD qSDDCore
  change ∑ a : Outcome, ev ψ ((F a)ᴴ * F a) = ∑ a : Outcome, ev ψ ((G a)ᴴ * G a)
  rw [hFG]
  refine Finset.sum_congr rfl ?_
  intro a _
  change
    ev ψ ((-G a)ᴴ * (-G a)) = ev ψ ((G a)ᴴ * G a)
  simp

/-- Symmetry of the state-dependent distance relation. -/
lemma sddRel_symm
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι) (δ : Error) :
    SDDRel ψ 𝒟 A B δ →
      SDDRel ψ 𝒟 B A δ := by
  intro ⟨h⟩
  constructor
  simpa [sddError, qSDD_symm] using h

/-- `prop:triangle-inequality-for-vectors-squared`.

For a finite family of operators `Dᵢ`, the squared norm of the summed vector
`(∑ᵢ Dᵢ) ψ` is controlled by the cardinality times the sum of the squared norms
of the individual vectors `Dᵢ ψ`. -/
theorem triangleInequalityForVectorsSquared
    {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (D : κ → MIPStarRE.Quantum.Op ι) :
    ev ψ ((∑ i, D i)ᴴ * (∑ i, D i)) ≤
      (Fintype.card κ : Error) * ∑ i, ev ψ ((D i)ᴴ * D i) := by
  simpa using ev_sum_conjTranspose_mul_sum_le ψ D

/-! ### Elementary max bound -/

/-- Adding `y` inside `max 0` changes the value by at most `|y|`. -/
lemma max_zero_add_le (x y : Error) :
    max 0 (x + y) ≤ max 0 x + |y| := by
  by_cases hxy : x + y < 0
  · rw [max_eq_left_of_lt hxy]
    positivity
  · have hxy' : 0 ≤ x + y := le_of_not_gt hxy
    rw [max_eq_right hxy']
    have hx : x ≤ max 0 x := le_max_right _ _
    have hy : y ≤ |y| := le_abs_self y
    linarith

private lemma avgOver_abs_le_sqrt_of_pointwise_nonneg
    {Question : Type*}
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (f g : Question → Error)
    (hfg : ∀ q, |f q| ≤ Real.sqrt (g q))
    (hg : ∀ q, 0 ≤ g q) :
    avgOver 𝒟 (fun q => |f q|) ≤ Real.sqrt (avgOver 𝒟 g) := by
  have havg_nonneg : 0 ≤ avgOver 𝒟 (fun q => |f q|) :=
    avgOver_nonneg 𝒟 (fun q => |f q|) (fun q => abs_nonneg (f q))
  have havg_abs :
      |avgOver 𝒟 (fun q => |f q|)| ≤ Real.sqrt (avgOver 𝒟 g) := by
    exact
      avgOver_abs_le_sqrt_of_pointwise 𝒟
        (fun q => |f q|)
        g
        (fun q => by
          simpa [abs_of_nonneg (abs_nonneg (f q))] using hfg q)
        hg
        h𝒟
  simpa [abs_of_nonneg havg_nonneg] using havg_abs

/-- `prop:triangle-sub`.

The proof rewrites both consistency errors as
`ev ψ (I ⊗ C.total) - Σₐ ev ψ (...)`, bound the overlap difference by
Cauchy-Schwarz using `ev_abs_mul_le_sqrt` and `subMeas_diagMass_le_one`, then
average with `avgOver_abs_le_sqrt_of_pointwise`.

This signature is the downstream API needed by Stream D. -/
theorem triangleSub
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : IdxMeas Question Outcome ι) (C : IdxSubMeas Question Outcome ι)
    (δ ε : Error)
    (hAC : ConsRel ψ 𝒟
      (IdxMeas.toIdxSubMeas A) C δ)
    (hAB : SDDRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A))
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas B)) ε) :
    ConsRel ψ 𝒟
      (IdxMeas.toIdxSubMeas B)
      C (δ + Real.sqrt ε) := by
  let AL : IdxSubMeas Question Outcome (ι × ι) :=
    IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A)
  let BL : IdxSubMeas Question Outcome (ι × ι) :=
    IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas B)
  let CR : IdxSubMeas Question Outcome (ι × ι) :=
    IdxSubMeas.liftRight C
  let matchA : Question → Error := fun q =>
    ∑ a : Outcome, ev ψ ((AL q).outcome a * (CR q).outcome a)
  let matchB : Question → Error := fun q =>
    ∑ a : Outcome, ev ψ ((BL q).outcome a * (CR q).outcome a)
  let overlap : Question → Error := fun q =>
    ev ψ (rightTensor (ι₁ := ι) ((C q).total))
  let sdd : Question → Error := fun q =>
    qSDD ψ (AL q) (BL q)
  let gap : Question → Error := fun q => matchA q - matchB q
  rcases hAC with ⟨hAC⟩
  rw [bipartiteConsError_eq_consError_placed] at hAC
  rcases hAB with ⟨hAB⟩
  have hgap_pointwise : ∀ q, |gap q| ≤ Real.sqrt (sdd q) := by
    intro q
    let diagC : Error := ∑ a : Outcome, ev ψ ((CR q).outcome a * (CR q).outcome a)
    have hdiagC_le_one : diagC ≤ 1 := by
      simpa [diagC] using subMeas_diagMass_le_one ψ hψ (CR q)
    have haux :
        |∑ a : Outcome, ev ψ (((AL q).outcome a - (BL q).outcome a) * (CR q).outcome a)| ≤
          Real.sqrt (sdd q) * Real.sqrt diagC := by
      calc
        |∑ a : Outcome, ev ψ (((AL q).outcome a - (BL q).outcome a) * (CR q).outcome a)|
          ≤ Real.sqrt
              (∑ a : Outcome,
                ev ψ
                  (((AL q).outcome a - (BL q).outcome a) *
                    ((AL q).outcome a - (BL q).outcome a)ᴴ)) *
              Real.sqrt
                (∑ a : Outcome, ev ψ (((CR q).outcome a)ᴴ * (CR q).outcome a)) := by
                  simpa using
                    sum_ev_mul_le_sqrt ψ
                      (fun a => (AL q).outcome a - (BL q).outcome a)
                      (fun a => (CR q).outcome a)
        _ = Real.sqrt (sdd q) * Real.sqrt diagC := by
              simp [sdd, qSDD, qSDDCore, diagC, SubMeas.outcome_hermitian]
    have hsqrtC : Real.sqrt diagC ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hdiagC_le_one
    have haux' :
        |∑ a : Outcome, ev ψ (((AL q).outcome a - (BL q).outcome a) * (CR q).outcome a)| ≤
          Real.sqrt (sdd q) := by
      calc
        |∑ a : Outcome, ev ψ (((AL q).outcome a - (BL q).outcome a) * (CR q).outcome a)|
          ≤ Real.sqrt (sdd q) * Real.sqrt diagC := haux
        _ ≤ Real.sqrt (sdd q) * 1 := by
              exact mul_le_mul_of_nonneg_left hsqrtC (Real.sqrt_nonneg _)
        _ = Real.sqrt (sdd q) := by ring
    convert haux' using 1
    dsimp [gap, matchA, matchB]
    refine congrArg abs ?_
    calc
      ∑ a : Outcome, ev ψ ((AL q).outcome a * (CR q).outcome a) -
          ∑ a : Outcome, ev ψ ((BL q).outcome a * (CR q).outcome a)
        = ∑ a : Outcome,
            (ev ψ ((AL q).outcome a * (CR q).outcome a) -
              ev ψ ((BL q).outcome a * (CR q).outcome a)) := by
                rw [← Finset.sum_sub_distrib]
      _ = ∑ a : Outcome, ev ψ (((AL q).outcome a - (BL q).outcome a) * (CR q).outcome a) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [(ev_sub ψ ((AL q).outcome a * (CR q).outcome a)
              ((BL q).outcome a * (CR q).outcome a)).symm]
            simp [sub_mul]
  have hgap_avg_abs :
      avgOver 𝒟 (fun q => |gap q|) ≤ Real.sqrt (avgOver 𝒟 sdd) := by
    exact
      avgOver_abs_le_sqrt_of_pointwise_nonneg 𝒟 h𝒟 gap sdd
        hgap_pointwise
        (fun q => qSDD_nonneg ψ (AL q) (BL q))
  have hdefect_pointwise :
      ∀ q, qConsDefect ψ (BL q) (CR q) ≤ qConsDefect ψ (AL q) (CR q) + |gap q| := by
    intro q
    have hdefA :
        qConsDefect ψ (AL q) (CR q) = max 0 (overlap q - matchA q) := by
      unfold qConsDefect qMatchMass
      dsimp [overlap, matchA, AL, CR]
      rw [show
        ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A) q).total) *
            ((IdxSubMeas.liftRight C q).total) =
          leftTensor (ι₂ := ι) ((A q).total) *
            rightTensor (ι₁ := ι) ((C q).total) by rfl]
      rw [(A q).total_eq_one]
      simp [IdxSubMeas.liftLeft, IdxSubMeas.liftRight, IdxMeas.toIdxSubMeas,
        leftTensor, rightTensor]
    have hdefB :
        qConsDefect ψ (BL q) (CR q) = max 0 (overlap q - matchB q) := by
      unfold qConsDefect qMatchMass
      dsimp [overlap, matchB, BL, CR]
      rw [show
        ((IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas B) q).total) *
            ((IdxSubMeas.liftRight C q).total) =
          leftTensor (ι₂ := ι) ((B q).total) *
            rightTensor (ι₁ := ι) ((C q).total) by rfl]
      rw [(B q).total_eq_one]
      simp [IdxSubMeas.liftLeft, IdxSubMeas.liftRight, IdxMeas.toIdxSubMeas,
        leftTensor, rightTensor]
    calc
      qConsDefect ψ (BL q) (CR q)
        = max 0 ((overlap q - matchA q) + gap q) := by
            rw [hdefB]
            dsimp [gap]
            ring_nf
      _ ≤ max 0 (overlap q - matchA q) + |gap q| := max_zero_add_le _ _
      _ = qConsDefect ψ (AL q) (CR q) + |gap q| := by
            rw [hdefA]
  constructor
  rw [bipartiteConsError_eq_consError_placed]
  unfold consError sddError at *
  calc
    avgOver 𝒟 (fun q => qConsDefect ψ (BL q) (CR q))
      ≤ avgOver 𝒟 (fun q => qConsDefect ψ (AL q) (CR q) + |gap q|) := by
          apply avgOver_mono
          intro q
          exact hdefect_pointwise q
    _ = avgOver 𝒟 (fun q => qConsDefect ψ (AL q) (CR q)) +
          avgOver 𝒟 (fun q => |gap q|) := by
            rw [avgOver_add]
    _ ≤ δ + Real.sqrt (avgOver 𝒟 sdd) := by
          exact add_le_add hAC hgap_avg_abs
    _ ≤ δ + Real.sqrt ε := by
          simpa [add_comm] using add_le_add_right (Real.sqrt_le_sqrt hAB) δ

/-! ### Right-register variant of `triangleSub` -/

private lemma right_match_gap_abs_le_sqrt_qSDD
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (A B D : SubMeas Outcome ι) :
    |(∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)) -
        ∑ a : Outcome, ev ψ (A.outcome a * D.outcome a)| ≤
      Real.sqrt (qSDD ψ B D) := by
  let diagA : Error := ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
  have hdiagA_le_one : diagA ≤ 1 := by
    simpa [diagA] using subMeas_diagMass_le_one ψ hψ A
  have haux :
      |∑ a : Outcome, ev ψ (A.outcome a * (B.outcome a - D.outcome a))| ≤
        Real.sqrt diagA * Real.sqrt (qSDD ψ B D) := by
    calc
      |∑ a : Outcome, ev ψ (A.outcome a * (B.outcome a - D.outcome a))|
        ≤ Real.sqrt
            (∑ a : Outcome, ev ψ (A.outcome a * (A.outcome a)ᴴ)) *
            Real.sqrt
              (∑ a : Outcome,
                ev ψ ((B.outcome a - D.outcome a)ᴴ *
                  (B.outcome a - D.outcome a))) := by
              simpa using
                sum_ev_mul_le_sqrt ψ
                  (fun a => A.outcome a)
                  (fun a => B.outcome a - D.outcome a)
      _ = Real.sqrt diagA * Real.sqrt (qSDD ψ B D) := by
            simp [diagA, qSDD, qSDDCore, SubMeas.outcome_hermitian]
  have hsqrtA : Real.sqrt diagA ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hdiagA_le_one
  have haux' :
      |∑ a : Outcome, ev ψ (A.outcome a * (B.outcome a - D.outcome a))| ≤
        Real.sqrt (qSDD ψ B D) := by
    calc
      |∑ a : Outcome, ev ψ (A.outcome a * (B.outcome a - D.outcome a))|
        ≤ Real.sqrt diagA * Real.sqrt (qSDD ψ B D) := haux
      _ ≤ 1 * Real.sqrt (qSDD ψ B D) := by
            exact mul_le_mul_of_nonneg_right hsqrtA (Real.sqrt_nonneg _)
      _ = Real.sqrt (qSDD ψ B D) := by ring
  convert haux' using 1
  refine congrArg abs ?_
  calc
    (∑ a : Outcome, ev ψ (A.outcome a * B.outcome a)) -
        ∑ a : Outcome, ev ψ (A.outcome a * D.outcome a)
      = ∑ a : Outcome,
          (ev ψ (A.outcome a * B.outcome a) -
            ev ψ (A.outcome a * D.outcome a)) := by
              rw [← Finset.sum_sub_distrib]
    _ = ∑ a : Outcome, ev ψ (A.outcome a * (B.outcome a - D.outcome a)) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [(ev_sub ψ (A.outcome a * B.outcome a)
            (A.outcome a * D.outcome a)).symm]
          simp [mul_sub]

theorem triangleSub_right
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question Outcome ι)
    (B D : IdxMeas Question Outcome ι) (δ ε : Error)
    (hAB : ConsRel ψ 𝒟
      A (IdxMeas.toIdxSubMeas B) δ)
    (hBD : SDDRel ψ 𝒟
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D)) ε) :
    ConsRel ψ 𝒟
      A
      (IdxMeas.toIdxSubMeas D) (δ + Real.sqrt ε) := by
  let AL : IdxSubMeas Question Outcome (ι × ι) := IdxSubMeas.liftLeft A
  let BR : IdxSubMeas Question Outcome (ι × ι) :=
    IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)
  let DR : IdxSubMeas Question Outcome (ι × ι) :=
    IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D)
  let matchB : Question → Error := fun q =>
    ∑ a : Outcome, ev ψ ((AL q).outcome a * (BR q).outcome a)
  let matchD : Question → Error := fun q =>
    ∑ a : Outcome, ev ψ ((AL q).outcome a * (DR q).outcome a)
  let overlap : Question → Error := fun q =>
    ev ψ (leftTensor (ι₂ := ι) ((A q).total))
  let sdd : Question → Error := fun q =>
    qSDD ψ (BR q) (DR q)
  let gap : Question → Error := fun q => matchB q - matchD q
  rcases hAB with ⟨hAB⟩
  rw [bipartiteConsError_eq_consError_placed] at hAB
  rcases hBD with ⟨hBD⟩
  have hgap_pointwise : ∀ q, |gap q| ≤ Real.sqrt (sdd q) := by
    intro q
    simpa [gap, matchB, matchD, sdd] using
      right_match_gap_abs_le_sqrt_qSDD ψ hψ (AL q) (BR q) (DR q)
  have hgap_avg_abs :
      avgOver 𝒟 (fun q => |gap q|) ≤ Real.sqrt (avgOver 𝒟 sdd) := by
    exact
      avgOver_abs_le_sqrt_of_pointwise_nonneg 𝒟 h𝒟 gap sdd
        hgap_pointwise
        (fun q => qSDD_nonneg ψ (BR q) (DR q))
  have hdefect_pointwise :
      ∀ q, qConsDefect ψ (AL q) (DR q) ≤ qConsDefect ψ (AL q) (BR q) + |gap q| := by
    intro q
    have hdefB :
        qConsDefect ψ (AL q) (BR q) = max 0 (overlap q - matchB q) := by
      unfold qConsDefect qMatchMass
      dsimp [overlap, matchB, AL, BR]
      rw [show
        ((IdxSubMeas.liftLeft A q).total) *
            ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B) q).total) =
          leftTensor (ι₂ := ι) ((A q).total) *
            rightTensor (ι₁ := ι) ((B q).total) by rfl]
      rw [(B q).total_eq_one]
      simp [IdxSubMeas.liftLeft, IdxSubMeas.liftRight, IdxMeas.toIdxSubMeas,
        leftTensor, rightTensor]
    have hdefD :
        qConsDefect ψ (AL q) (DR q) = max 0 (overlap q - matchD q) := by
      unfold qConsDefect qMatchMass
      dsimp [overlap, matchD, AL, DR]
      rw [show
        ((IdxSubMeas.liftLeft A q).total) *
            ((IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D) q).total) =
          leftTensor (ι₂ := ι) ((A q).total) *
            rightTensor (ι₁ := ι) ((D q).total) by rfl]
      rw [(D q).total_eq_one]
      simp [IdxSubMeas.liftLeft, IdxSubMeas.liftRight, IdxMeas.toIdxSubMeas,
        leftTensor, rightTensor]
    calc
      qConsDefect ψ (AL q) (DR q)
        = max 0 ((overlap q - matchB q) + gap q) := by
            rw [hdefD]
            dsimp [gap]
            ring_nf
      _ ≤ max 0 (overlap q - matchB q) + |gap q| := max_zero_add_le _ _
      _ = qConsDefect ψ (AL q) (BR q) + |gap q| := by
            rw [hdefB]
  constructor
  rw [bipartiteConsError_eq_consError_placed]
  unfold consError sddError at *
  calc
    avgOver 𝒟 (fun q => qConsDefect ψ (AL q) (DR q))
      ≤ avgOver 𝒟 (fun q => qConsDefect ψ (AL q) (BR q) + |gap q|) := by
          apply avgOver_mono
          intro q
          exact hdefect_pointwise q
    _ = avgOver 𝒟 (fun q => qConsDefect ψ (AL q) (BR q)) +
          avgOver 𝒟 (fun q => |gap q|) := by
            rw [avgOver_add]
    _ ≤ δ + Real.sqrt (avgOver 𝒟 sdd) := by
          exact add_le_add hAB hgap_avg_abs
    _ ≤ δ + Real.sqrt ε := by
          simpa [add_comm] using add_le_add_right (Real.sqrt_le_sqrt hBD) δ

/-- Right-register substitution for submeasurements, with the total-overlap
displacement stated explicitly.

For complete right-register measurements the total-overlap term
`ev ψ (A_total ⊗ B_total)` is independent of the right family.  For general
submeasurements this term may change.  The lemma therefore separates the usual
state-dependent-distance contribution from the averaged displacement of the
right total operator. -/
theorem triangleSub_right_subMeas_totalGap
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B D : IdxSubMeas Question Outcome ι) (δ ε η : Error)
    (hAB : ConsRel ψ 𝒟 A B δ)
    (hBD : SDDRel ψ 𝒟
      (IdxSubMeas.liftRight B)
      (IdxSubMeas.liftRight D) ε)
    (hTotal :
      avgOver 𝒟 (fun q =>
        |ev ψ (leftTensor (ι₂ := ι) ((A q).total) *
            rightTensor (ι₁ := ι) ((D q).total)) -
          ev ψ (leftTensor (ι₂ := ι) ((A q).total) *
            rightTensor (ι₁ := ι) ((B q).total))|) ≤ η) :
    ConsRel ψ 𝒟 A D (δ + Real.sqrt ε + η) := by
  let AL : IdxSubMeas Question Outcome (ι × ι) := IdxSubMeas.liftLeft A
  let BR : IdxSubMeas Question Outcome (ι × ι) := IdxSubMeas.liftRight B
  let DR : IdxSubMeas Question Outcome (ι × ι) := IdxSubMeas.liftRight D
  let matchB : Question → Error := fun q =>
    ∑ a : Outcome, ev ψ ((AL q).outcome a * (BR q).outcome a)
  let matchD : Question → Error := fun q =>
    ∑ a : Outcome, ev ψ ((AL q).outcome a * (DR q).outcome a)
  let totalB : Question → Error := fun q =>
    ev ψ ((AL q).total * (BR q).total)
  let totalD : Question → Error := fun q =>
    ev ψ ((AL q).total * (DR q).total)
  let sdd : Question → Error := fun q =>
    qSDD ψ (BR q) (DR q)
  let matchGap : Question → Error := fun q => matchB q - matchD q
  let totalGap : Question → Error := fun q => totalD q - totalB q
  rcases hAB with ⟨hAB⟩
  rw [bipartiteConsError_eq_consError_placed] at hAB
  rcases hBD with ⟨hBD⟩
  have hmatchGap_pointwise : ∀ q, |matchGap q| ≤ Real.sqrt (sdd q) := by
    intro q
    simpa [matchGap, matchB, matchD, sdd] using
      right_match_gap_abs_le_sqrt_qSDD ψ hψ (AL q) (BR q) (DR q)
  have hmatchGap_avg_abs :
      avgOver 𝒟 (fun q => |matchGap q|) ≤ Real.sqrt (avgOver 𝒟 sdd) := by
    exact
      avgOver_abs_le_sqrt_of_pointwise_nonneg 𝒟 h𝒟 matchGap sdd
        hmatchGap_pointwise
        (fun q => qSDD_nonneg ψ (BR q) (DR q))
  have htotalGap_avg_abs :
      avgOver 𝒟 (fun q => |totalGap q|) ≤ η := by
    simpa [totalGap, totalD, totalB, AL, BR, DR, IdxSubMeas.liftLeft,
      IdxSubMeas.liftRight] using hTotal
  have hdefect_pointwise :
      ∀ q, qConsDefect ψ (AL q) (DR q) ≤
        qConsDefect ψ (AL q) (BR q) + |matchGap q| + |totalGap q| := by
    intro q
    have hdefB :
        qConsDefect ψ (AL q) (BR q) = max 0 (totalB q - matchB q) := by
      unfold qConsDefect qMatchMass
      dsimp [totalB, matchB]
    have hdefD :
        qConsDefect ψ (AL q) (DR q) = max 0 (totalD q - matchD q) := by
      unfold qConsDefect qMatchMass
      dsimp [totalD, matchD]
    calc
      qConsDefect ψ (AL q) (DR q)
        = max 0 (((totalB q - matchB q) + matchGap q) + totalGap q) := by
            rw [hdefD]
            dsimp [matchGap, totalGap]
            ring_nf
      _ ≤ max 0 ((totalB q - matchB q) + matchGap q) + |totalGap q| := by
            exact max_zero_add_le _ _
      _ ≤ (max 0 (totalB q - matchB q) + |matchGap q|) + |totalGap q| := by
            linarith [max_zero_add_le (totalB q - matchB q) (matchGap q)]
      _ = qConsDefect ψ (AL q) (BR q) + |matchGap q| + |totalGap q| := by
            rw [hdefB]
  constructor
  rw [bipartiteConsError_eq_consError_placed]
  unfold consError sddError at *
  calc
    avgOver 𝒟 (fun q => qConsDefect ψ (AL q) (DR q))
      ≤ avgOver 𝒟
          (fun q => qConsDefect ψ (AL q) (BR q) + |matchGap q| + |totalGap q|) := by
          apply avgOver_mono
          intro q
          exact hdefect_pointwise q
    _ = (avgOver 𝒟 (fun q => qConsDefect ψ (AL q) (BR q)) +
          avgOver 𝒟 (fun q => |matchGap q|)) +
          avgOver 𝒟 (fun q => |totalGap q|) := by
            rw [avgOver_add, avgOver_add]
    _ ≤ (δ + Real.sqrt (avgOver 𝒟 sdd)) + η := by
          exact add_le_add (add_le_add hAB hmatchGap_avg_abs) htotalGap_avg_abs
    _ ≤ (δ + Real.sqrt ε) + η := by
          have hsqrt_sdd_le :
              Real.sqrt (avgOver 𝒟 sdd) ≤ Real.sqrt ε := by
            exact Real.sqrt_le_sqrt (by simpa [sdd, BR, DR] using hBD)
          linarith
    _ = δ + Real.sqrt ε + η := by ring

/-- `prop:simeq-triangle-inequality`.

Apply `simeqToApprox` to the two hypotheses through the middle
measurement `B`, use the `SDDRel` triangle inequality to compare the induced
right-side families, and finish with `triangleSub`. Quantitatively this gives
`ε + sqrt (4 * (δ + γ)) = ε + 2 * sqrt (δ + γ)`.

This is stated here with the exact paper-style API needed by downstream files. -/
theorem simeqTriangleInequality
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B C D : IdxMeas Question Outcome ι)
    (ε δ γ : Error)
    (hAB : ConsRel ψ 𝒟
      (IdxMeas.toIdxSubMeas A)
      (IdxMeas.toIdxSubMeas B) ε)
    (hCB : ConsRel ψ 𝒟
      (IdxMeas.toIdxSubMeas C)
      (IdxMeas.toIdxSubMeas B) δ)
    (hCD : ConsRel ψ 𝒟
      (IdxMeas.toIdxSubMeas C)
      (IdxMeas.toIdxSubMeas D) γ) :
    ConsRel ψ 𝒟
      (IdxMeas.toIdxSubMeas A)
      (IdxMeas.toIdxSubMeas D)
      (ε + 2 * Real.sqrt (δ + γ)) := by
  have hCB_bip : BipartiteSDDRel ψ 𝒟
      (IdxMeas.toIdxSubMeas C)
      (IdxMeas.toIdxSubMeas B)
      (2 * δ) :=
    simeqToApprox ψ 𝒟 C B δ hCB
  have hCD_bip : BipartiteSDDRel ψ 𝒟
      (IdxMeas.toIdxSubMeas C)
      (IdxMeas.toIdxSubMeas D)
      (2 * γ) :=
    simeqToApprox ψ 𝒟 C D γ hCD
  have hCB_sdd : SDDRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas C))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B))
      (2 * δ) := by
    exact ⟨hCB_bip.leftRightSquaredDistanceBound⟩
  have hCD_sdd : SDDRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas C))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D))
      (2 * γ) := by
    exact ⟨hCD_bip.leftRightSquaredDistanceBound⟩
  have hBC_sdd : SDDRel ψ 𝒟
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B))
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas C))
      (2 * δ) := by
    exact sddRel_symm ψ 𝒟 _ _ _ hCB_sdd
  have hBD_sdd_raw : SDDRel ψ 𝒟
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D))
      (2 * ((2 * δ) + (2 * γ))) := by
    exact
      stateDependentDistanceRel_triangle ψ 𝒟
        (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B))
        (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas C))
        (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D))
        (2 * δ) (2 * γ) hBC_sdd hCD_sdd
  have hBD_sdd : SDDRel ψ 𝒟
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D))
      (4 * (δ + γ)) := by
    exact
      stateDependentDistanceRel_mono ψ 𝒟
        (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B))
        (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D))
        (2 * ((2 * δ) + (2 * γ))) (4 * (δ + γ))
        (by
          -- Normalizing both sides turns each expression into `4 * δ + 4 * γ`.
          ring_nf
          linarith)
        hBD_sdd_raw
  have hδ_nonneg : 0 ≤ δ := by
    rcases hCB with ⟨hδ⟩
    exact le_trans (bipartiteConsError_nonneg ψ 𝒟 _ _) hδ
  have hγ_nonneg : 0 ≤ γ := by
    rcases hCD with ⟨hγ⟩
    exact le_trans (bipartiteConsError_nonneg ψ 𝒟 _ _) hγ
  have hsqrt_four :
      Real.sqrt (4 * (δ + γ)) = 2 * Real.sqrt (δ + γ) := by
    have hδγ_nonneg : 0 ≤ δ + γ := add_nonneg hδ_nonneg hγ_nonneg
    calc
      Real.sqrt (4 * (δ + γ))
        = Real.sqrt (4 : Error) * Real.sqrt (δ + γ) := by
            rw [Real.sqrt_mul (show 0 ≤ (4 : Error) by positivity)]
      _ = 2 * Real.sqrt (δ + γ) := by norm_num
  have hfinal :
      ConsRel ψ 𝒟
        (IdxMeas.toIdxSubMeas A)
        (IdxMeas.toIdxSubMeas D)
        (ε + Real.sqrt (4 * (δ + γ))) := by
    exact
      triangleSub_right ψ 𝒟 hψ h𝒟
        (IdxMeas.toIdxSubMeas A) B D ε (4 * (δ + γ))
        hAB hBD_sdd
  exact
    (by
      simpa [hsqrt_four] using hfinal)

/-- `prop:triangle-inequality-for-approx_delta`.

The paper states the iterated telescoping version for an arbitrary chain of
approximations. The current API records the binary composition step used
throughout the repository; the full iterated form follows by induction on the
length of the chain. -/
theorem triangleInequalityForApproxDelta
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B C : IdxSubMeas Question Outcome ι) (δ₁ δ₂ : Error) :
    SDDRel ψ 𝒟 A B δ₁ →
    SDDRel ψ 𝒟 B C δ₂ →
    SDDRel ψ 𝒟 A C (2 * (δ₁ + δ₂)) :=
  stateDependentDistanceRel_triangle ψ 𝒟 A B C δ₁ δ₂

end MIPStarRE.LDT.Preliminaries
