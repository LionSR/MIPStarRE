import MIPStarRE.LDT.MakingMeasurementsProjective.Statements
-- `Mathlib` is imported transitively through the dependency chain above.

/-!
# Section 5 — Q/X/XHat/P intermediate layer

Paper-faithful proof infrastructure for the internal orthonormalization chain in
`references/ldt-paper/orthonormalization.tex`.

This file adds the intermediate `Q/X/XHat/P` objects and the 15 helper-lemma
stubs tracked in issue #197. The actual proofs are deferred, but the signatures
are intended to match the paper's decomposition of the argument.

## References

- `references/ldt-paper/orthonormalization.tex`, Section 6.2, for the
  `Q/X/XHat/P` intermediate layer and its helper lemmas.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.MakingMeasurementsProjective

open MIPStarRE.LDT

noncomputable section

-- NOTE: sorry stubs are intentional scaffolding for issue #197. See PROOF_INTEGRITY.md.

/-- The quarter-root error term `ζ^(1/4)` used throughout the paper's late-stage
orthonormalization estimates. -/
noncomputable def zetaQuarterRoot (ζ : Error) : Error :=
  Real.rpow ζ (1 / (4 : Error))

/-- A raw operator family viewed as a constant indexed family on the trivial
question set. -/
def constOpFamily {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A : OpFamily Outcome ι) :
    IdxOpFamily Unit Outcome ι :=
  fun _ => A

/-- Data for the paper's intermediate `Q`-layer: the rank-reduced family
`Q_a`, its total operator `Q`, and the auxiliary projective measurement `T_a`
used to define `X_a`, `XHat_a`, and `P_a`. -/
structure QLayerData (Outcome : Type*) [Fintype Outcome]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  auxSpace : FiniteHilbertSpace
  q : OpFamily Outcome ι
  t : ProjMeas Outcome auxSpace.carrier

/-- The paper's operator `Q_a`. -/
def Qa {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QLayerData Outcome ι) (a : Outcome) :
    MIPStarRE.Quantum.Op ι :=
  data.q.outcome a

/-- The paper's total operator `Q = ∑_a Q_a`. -/
def QTotal {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QLayerData Outcome ι) :
    MIPStarRE.Quantum.Op ι :=
  data.q.total

/-- The paper's auxiliary projector `T_a`. -/
def Ta {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QLayerData Outcome ι) (a : Outcome) :
    MIPStarRE.Quantum.Op data.auxSpace.carrier :=
  data.t.outcome a

/-- Witness package for `lem:projective-non-measurement`. -/
structure RoundingToProjectorsWitness {Outcome : Type*}
    [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι)
    (ζ : Error) (R : OpFamily Outcome ι) : Prop where
  projective :
    ∀ a : Outcome, MIPStarRE.Quantum.IsProj (R.outcome a)
  closeness :
    SDDOpRel ψ (uniformDistribution Unit)
      (constOpFamily (A.toSubMeas : OpFamily Outcome ι))
      (constOpFamily R)
      (2 * spectralTruncationError ζ)
  total_le :
    R.total ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
      (1 : MIPStarRE.Quantum.Op ι)

/-- Witness package for `lem:projective-low-rank-sum`. -/
structure RankReductionWitness {Outcome : Type*}
    [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (A : Measurement Outcome ι)
    (ζ : Error) (data : QLayerData Outcome ι) : Prop where
  projective :
    ∀ a : Outcome, MIPStarRE.Quantum.IsProj (Qa data a)
  closeness :
    SDDOpRel ψ (uniformDistribution Unit)
      (constOpFamily (A.toSubMeas : OpFamily Outcome ι))
      (constOpFamily data.q)
      (roundingToProjectiveError ζ)
  total_le :
    QTotal data ≤ (((1 : Error) + 2 * spectralTruncationError ζ) : ℂ) •
      (1 : MIPStarRE.Quantum.Op ι)
  auxDim_le :
    Fintype.card data.auxSpace.carrier ≤ Fintype.card ι

/-- Data for the paper's `X/XHat/P` layer built on top of `Q_a` and the
auxiliary projectors `T_a`.  The square matrices `u`, `v`, `sigmaLeft`,
and `sigmaRight` are placeholders for the SVD objects appearing in the paper's
formulas. -/
structure QXPLayerData (Outcome : Type*) [Fintype Outcome]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where
  qLayer : QLayerData Outcome ι
  x : Matrix qLayer.auxSpace.carrier ι ℂ
  xHat : Matrix qLayer.auxSpace.carrier ι ℂ
  u : MatrixOperator qLayer.auxSpace
  v : MIPStarRE.Quantum.Op ι
  sigmaLeft : MatrixOperator qLayer.auxSpace
  sigmaRight : MIPStarRE.Quantum.Op ι
  qa_eq : ∀ a : Outcome, qLayer.q.outcome a = xᴴ * Ta qLayer a * x
  qa_projective : ∀ a : Outcome, MIPStarRE.Quantum.IsProj (qLayer.q.outcome a)
  xHat_coisometry : xHat * xHatᴴ = 1
  x_gram_right : xᴴ * x = QTotal qLayer
  x_gram_left_svd : x * xᴴ = u * (sigmaLeft * sigmaLeft) * uᴴ
  q_total_svd : QTotal qLayer = v * (sigmaRight * sigmaRight) * vᴴ
  xHat_mixed : xᴴ * xHat = CFC.sqrt (QTotal qLayer)

/-- The paper's matrix `X_a = T_a · X`. -/
def Xa {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Matrix data.qLayer.auxSpace.carrier ι ℂ :=
  Ta data.qLayer a * data.x

/-- The paper's matrix `XHat_a = T_a · XHat`. -/
def XHatA {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Matrix data.qLayer.auxSpace.carrier ι ℂ :=
  Ta data.qLayer a * data.xHat

/-- The paper's operator `P_a = XHat† · T_a · XHat`. -/
def Pa {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    MIPStarRE.Quantum.Op ι :=
  data.xHatᴴ * Ta data.qLayer a * data.xHat

/-- The raw operator family `P = {P_a}`. -/
noncomputable def PFamily {Outcome : Type*} [Fintype Outcome]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (data : QXPLayerData Outcome ι) :
    OpFamily Outcome ι where
  outcome := Pa data
  total := ∑ a, Pa data a

/-- **Almost-projective estimate** (`eq:A-looks-projective`).

This is the opening inequality in the proof of
`lem:orthonormalization-main-lemma`, extracted as an explicit Lean lemma so the
later `Q/X/XHat/P` layer can depend on it directly. -/
lemma aLooksProjective {Outcome : Type*}
    {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB))
    (A : Measurement Outcome ιA) (B : ProjMeas Outcome ιB) (ζ : Error) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily A.toSubMeas)
      (constSubMeasFamily B.toSubMeas) ζ →
      ∑ a, ev ψ (leftTensor (ι₂ := ιB) (A.outcome a - A.outcome a * A.outcome a)) ≤
        2 * ζ := by
  intro hCons
  rcases hCons with ⟨hCons⟩
  let defect : Error :=
    ∑ a : Outcome,
      ev ψ (leftTensor (ι₂ := ιB) (A.outcome a - A.outcome a * A.outcome a))
  let diagA : Error :=
    ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a))
  let overlap : Error :=
    ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a))
  let totalMass : Error := ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB))
  have hCons' : qBipartiteConsDefect ψ A.toSubMeas B.toSubMeas ≤ ζ := by
    simpa [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily] using hCons
  have hgap : totalMass - overlap ≤ ζ := by
    have hq :
        max 0 (totalMass - overlap) ≤ ζ := by
      simpa [qBipartiteConsDefect, qBipartiteMatchMass, totalMass, overlap,
        A.total_eq_one, B.total_eq_one, opTensor] using hCons'
    exact le_trans (le_max_right 0 (totalMass - overlap)) hq
  have h_expand :
      ∀ a : Outcome,
        ev ψ
            (((leftTensor (ι₂ := ιB) (A.outcome a) -
                  rightTensor (ι₁ := ιA) (B.outcome a))ᴴ) *
              (leftTensor (ι₂ := ιB) (A.outcome a) -
                rightTensor (ι₁ := ιA) (B.outcome a))) =
          ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a)) +
            ev ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a)) -
            2 * ev ψ (opTensor (A.outcome a) (B.outcome a)) := by
    intro a
    have hLherm :
        (leftTensor (ι₂ := ιB) (A.outcome a))ᴴ =
          leftTensor (ι₂ := ιB) (A.outcome a) := by
      exact
        (Matrix.nonneg_iff_posSemidef.mp
          (leftTensor_nonneg (ι₂ := ιB) (A.outcome_pos a))).isHermitian.eq
    have hRherm :
        (rightTensor (ι₁ := ιA) (B.outcome a))ᴴ =
          rightTensor (ι₁ := ιA) (B.outcome a) := by
      exact
        (Matrix.nonneg_iff_posSemidef.mp
          (rightTensor_nonneg (ι₁ := ιA) (B.outcome_pos a))).isHermitian.eq
    calc
      ev ψ
          (((leftTensor (ι₂ := ιB) (A.outcome a) -
                rightTensor (ι₁ := ιA) (B.outcome a))ᴴ) *
            (leftTensor (ι₂ := ιB) (A.outcome a) -
              rightTensor (ι₁ := ιA) (B.outcome a)))
        =
          ev ψ
            (((leftTensor (ι₂ := ιB) (A.outcome a) *
                  leftTensor (ι₂ := ιB) (A.outcome a) -
                leftTensor (ι₂ := ιB) (A.outcome a) *
                  rightTensor (ι₁ := ιA) (B.outcome a)) -
              (rightTensor (ι₁ := ιA) (B.outcome a) *
                  leftTensor (ι₂ := ιB) (A.outcome a) -
                rightTensor (ι₁ := ιA) (B.outcome a) *
                  rightTensor (ι₁ := ιA) (B.outcome a)))) := by
            congr 1
            simp [hLherm, hRherm, sub_mul, mul_sub]
            abel
      _ =
          ev ψ
            (leftTensor (ι₂ := ιB) (A.outcome a) *
              leftTensor (ι₂ := ιB) (A.outcome a)) -
            ev ψ
              (leftTensor (ι₂ := ιB) (A.outcome a) *
                rightTensor (ι₁ := ιA) (B.outcome a)) -
            (ev ψ
                (rightTensor (ι₁ := ιA) (B.outcome a) *
                  leftTensor (ι₂ := ιB) (A.outcome a)) -
              ev ψ
                (rightTensor (ι₁ := ιA) (B.outcome a) *
                  rightTensor (ι₁ := ιA) (B.outcome a))) := by
            rw [ev_sub, ev_sub, ev_sub]
      _ =
          ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a)) +
            ev ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a)) -
            2 * ev ψ (opTensor (A.outcome a) (B.outcome a)) := by
            rw [leftTensor_mul_leftTensor, leftTensor_mul_rightTensor_eq_opTensor,
              rightTensor_mul_leftTensor_eq_opTensor, rightTensor_mul_rightTensor]
            simp [B.proj a]
            ring
  have hsdd_nonneg :
      0 ≤ qSDD ψ
        (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
        (rightPlacedSubMeas (ιA := ιA) B.toSubMeas) := by
    exact qSDD_nonneg ψ
      (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
      (rightPlacedSubMeas (ιA := ιA) B.toSubMeas)
  have hdiag_lower : 2 * overlap - totalMass ≤ diagA := by
    have hright_one :
        ev ψ (rightTensor (ι₁ := ιA) (1 : MIPStarRE.Quantum.Op ιB)) =
          ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
      congr 1
      ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
        simp [rightTensor, Matrix.one_apply, h₁, h₂]
    have hright :
        ∑ a : Outcome, ev ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a)) =
          ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
      calc
        ∑ a : Outcome, ev ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a))
          = ∑ a : Outcome, ev ψ (rightTensor (ι₁ := ιA) (B.outcome a)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              simp [B.proj a]
        _ = ev ψ (rightTensor (ι₁ := ιA) (∑ a : Outcome, B.outcome a)) := by
              rw [← ev_sum ψ (fun a : Outcome => rightTensor (ι₁ := ιA) (B.outcome a))]
              rw [rightTensor_finset_sum (ι₁ := ιA) Finset.univ B.outcome]
        _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
              simpa [B.sum_eq] using hright_one
    have hsdd_eq :
        qSDD ψ
          (leftPlacedSubMeas (ιB := ιB) A.toSubMeas)
          (rightPlacedSubMeas (ιA := ιA) B.toSubMeas) =
          diagA + totalMass - 2 * overlap := by
      unfold qSDD qSDDCore diagA overlap totalMass
      calc
        ∑ a : Outcome,
            ev ψ
              ((((leftPlacedSubMeas (ιB := ιB) A.toSubMeas).outcome a -
                    (rightPlacedSubMeas (ιA := ιA) B.toSubMeas).outcome a)ᴴ) *
                ((leftPlacedSubMeas (ιB := ιB) A.toSubMeas).outcome a -
                  (rightPlacedSubMeas (ιA := ιA) B.toSubMeas).outcome a))
          =
            ∑ a : Outcome,
              (ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a)) +
                ev ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a)) -
                2 * ev ψ (opTensor (A.outcome a) (B.outcome a))) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              simpa [leftPlacedSubMeas, rightPlacedSubMeas] using h_expand a
        _ =
            (∑ a : Outcome,
              ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a))) +
              (∑ a : Outcome,
                ev ψ (rightTensor (ι₁ := ιA) (B.outcome a * B.outcome a))) -
              2 * ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a)) := by
              rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
        _ =
            (∑ a : Outcome,
              ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a))) +
              ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
              2 * ∑ a : Outcome, ev ψ (opTensor (A.outcome a) (B.outcome a)) := by
              rw [hright]
    linarith
  have hdefect_eq : defect = totalMass - diagA := by
    unfold defect diagA totalMass
    have hleft_one :
        ev ψ (leftTensor (ι₂ := ιB) (1 : MIPStarRE.Quantum.Op ιA)) =
          ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) := by
      congr 1
      ext i j
      rcases i with ⟨i₁, i₂⟩
      rcases j with ⟨j₁, j₂⟩
      by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
        simp [leftTensor, Matrix.one_apply, h₁, h₂]
    have hleft_sub :
        ∀ X Y : MIPStarRE.Quantum.Op ιA,
          leftTensor (ι₂ := ιB) (X - Y) =
            leftTensor (ι₂ := ιB) X - leftTensor (ι₂ := ιB) Y := by
      intro X Y
      have hneg :
          Matrix.kronecker (-Y) (1 : MIPStarRE.Quantum.Op ιB) =
            -Matrix.kronecker Y (1 : MIPStarRE.Quantum.Op ιB) := by
        simpa using (Matrix.smul_kronecker (-1 : ℂ) Y (1 : MIPStarRE.Quantum.Op ιB))
      calc
        leftTensor (ι₂ := ιB) (X - Y)
          = Matrix.kronecker X (1 : MIPStarRE.Quantum.Op ιB) +
              Matrix.kronecker (-Y) (1 : MIPStarRE.Quantum.Op ιB) := by
                simpa [leftTensor, sub_eq_add_neg] using
                  (Matrix.add_kronecker X (-Y) (1 : MIPStarRE.Quantum.Op ιB))
        _ = leftTensor (ι₂ := ιB) X - leftTensor (ι₂ := ιB) Y := by
              rw [hneg]
              simp [leftTensor, sub_eq_add_neg]
    calc
      ∑ a : Outcome,
          ev ψ (leftTensor (ι₂ := ιB) (A.outcome a - A.outcome a * A.outcome a))
        =
          ∑ a : Outcome,
            (ev ψ (leftTensor (ι₂ := ιB) (A.outcome a)) -
              ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a))) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            rw [hleft_sub, ev_sub]
      _ =
          (∑ a : Outcome, ev ψ (leftTensor (ι₂ := ιB) (A.outcome a))) -
            ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a)) := by
            rw [Finset.sum_sub_distrib]
      _ = ev ψ (1 : MIPStarRE.Quantum.Op (ιA × ιB)) -
            ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ιB) (A.outcome a * A.outcome a)) := by
            rw [← ev_sum ψ (fun a : Outcome => leftTensor (ι₂ := ιB) (A.outcome a))]
            rw [leftTensor_finset_sum (ι₂ := ιB) Finset.univ A.outcome]
            simpa [A.sum_eq] using hleft_one
  calc
    ∑ a : Outcome,
        ev ψ (leftTensor (ι₂ := ιB) (A.outcome a - A.outcome a * A.outcome a))
      = totalMass - diagA := hdefect_eq
    _ ≤ 2 * (totalMass - overlap) := by
          linarith
    _ ≤ 2 * ζ := by
          linarith

/-- **Scalar truncation inequality** (`lem:trunc-inequality`).

For `x ∈ [0,1]`, truncating at threshold `1 - δ` changes `x` by at most
`(1 / δ) * (x - x^2)` in squared distance. -/
lemma truncationInequality (δ x : Error) :
    0 < δ →
      δ ≤ 1 / 2 →
      0 ≤ x →
      x ≤ 1 →
      let trunc : Error := if 1 - δ ≤ x then 1 else 0
      (x - trunc) ^ (2 : Nat) ≤ (1 / δ) * (x - x ^ (2 : Nat)) := by
  intro hδ hδ_half hx_nonneg hx_le_one
  dsimp
  by_cases h : 1 - δ ≤ x
  · simp [h]
    have hδ_le_x : δ ≤ x := by
      linarith
    have hmain : (x - 1) ^ (2 : Nat) * δ ≤ x - x ^ (2 : Nat) := by
      nlinarith
    have hdiv : (x - 1) ^ (2 : Nat) ≤ (x - x ^ (2 : Nat)) / δ := by
      exact (le_div_iff₀ hδ).2 hmain
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
  · simp [h]
    push_neg at h
    have hδ_le_one_sub_x : δ ≤ 1 - x := by
      linarith
    have hmain : x ^ (2 : Nat) * δ ≤ x - x ^ (2 : Nat) := by
      have hx_sq_le_x : x ^ (2 : Nat) ≤ x := by
        nlinarith
      have hmul₁ : x ^ (2 : Nat) * δ ≤ x * δ := by
        exact mul_le_mul_of_nonneg_right hx_sq_le_x (le_of_lt hδ)
      have hmul₂ : x * δ ≤ x * (1 - x) := by
        exact mul_le_mul_of_nonneg_left hδ_le_one_sub_x hx_nonneg
      have hmul : x ^ (2 : Nat) * δ ≤ x * (1 - x) := by
        exact le_trans hmul₁ hmul₂
      nlinarith
    have hdiv : x ^ (2 : Nat) ≤ (x - x ^ (2 : Nat)) / δ := by
      exact (le_div_iff₀ hδ).2 hmain
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

/-- **Rounding to projectors** (`lem:projective-non-measurement`).

From the estimate `eq:A-looks-projective`, construct a family `R_a` of
projectors close to `A_a` whose total is bounded by `(1 + 2√ζ)I`. -/
lemma projectiveNonMeasurement {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error) :
    (∑ a, ev ψ (A.outcome a - A.outcome a * A.outcome a) ≤ 2 * ζ) →
      ∃ R : OpFamily Outcome ι,
        RoundingToProjectorsWitness ψ A ζ R := by
  -- TODO: prove (issue #197)
  sorry

/-- **Rank reduction** (`lem:projective-low-rank-sum`).

Construct the paper's rank-reduced family `Q_a`, together with the auxiliary
projective measurement `T_a`, so that `Q_a` remains close to `A_a`, its total
stays bounded by `(1 + 2√ζ)I`, and the auxiliary dimension is at most the
original ambient dimension. -/
lemma projectiveLowRankSum {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error) :
    ∃ data : QLayerData Outcome ι,
      RankReductionWitness ψ A ζ data := by
  -- TODO: prove (issue #197)
  sorry

/-- **Completeness of `Q`** (`lem:Q-completeness`).

If `Q_a` is the rank-reduced family from `lem:projective-low-rank-sum`, then
its total operator `Q` has expectation at least `1 - 11 ζ^(1/4)`. -/
lemma qCompleteness {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QLayerData Outcome ι) :
    RankReductionWitness ψ A ζ data →
      ev ψ (QTotal data) ≥ 1 - 11 * zetaQuarterRoot ζ := by
  -- TODO: prove (issue #197)
  sorry

/-- **Completeness of `sqrt Q`** (`lem:sqrt-Q-completeness`).

The square root of the total operator `Q` remains almost complete on `ψ`. -/
lemma sqrtQCompleteness {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QLayerData Outcome ι) :
    RankReductionWitness ψ A ζ data →
      ev ψ (CFC.sqrt (QTotal data)) ≥ 1 - 12 * zetaQuarterRoot ζ := by
  -- TODO: prove (issue #197)
  sorry

/-- **`Q` is almost projective** (`lem:q-almost-projective`).

The rank-reduced family satisfies the operator inequality
`∑_a (Q_a Q Q_a - Q_a) ≤ 4√ζ · I`. -/
lemma qAlmostProjective {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QLayerData Outcome ι) :
    RankReductionWitness ψ A ζ data →
      (∑ a, (Qa data a * QTotal data * Qa data a - Qa data a)) ≤
        (((4 : Error) * spectralTruncationError ζ) : ℂ) • (1 : MIPStarRE.Quantum.Op ι) := by
  -- TODO: prove (issue #197)
  sorry

/-- **`X_a = T_a X`** (`lem:xa-t`). -/
lemma xa_t {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Xa data a = Ta data.qLayer a * data.x := by
  rfl

/-- **`Q_a` restated** (`lem:qa-restated`).

Rewrites the paper's operator `Q_a` in terms of `X_a`, `X`, and `T_a`. -/
lemma qaRestated {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    Qa data.qLayer a = (Xa data a)ᴴ * Xa data a ∧
      Qa data.qLayer a = data.xᴴ * Ta data.qLayer a * data.x ∧
      Qa data.qLayer a = (Xa data a)ᴴ * data.x := by
  have hTa : (Ta data.qLayer a)ᴴ = Ta data.qLayer a := by
    simpa [Ta] using ProjMeas.outcome_hermitian data.qLayer.t a
  constructor
  · calc
      Qa data.qLayer a = data.xᴴ * Ta data.qLayer a * data.x := data.qa_eq a
      _ = (Xa data a)ᴴ * Xa data a := by
        symm
        calc
          (Xa data a)ᴴ * Xa data a =
              data.xᴴ * Ta data.qLayer a * (Ta data.qLayer a * data.x) := by
                simp [Xa, Matrix.conjTranspose_mul, hTa, Matrix.mul_assoc]
          _ = data.xᴴ * Ta data.qLayer a * data.x := by
                simpa [Matrix.mul_assoc] using
                  congrArg (fun M => data.xᴴ * (M * data.x)) (data.qLayer.t.proj a)
  · constructor
    · exact data.qa_eq a
    · calc
        Qa data.qLayer a = data.xᴴ * Ta data.qLayer a * data.x := data.qa_eq a
        _ = (Xa data a)ᴴ * data.x := by
          simp [Xa, Matrix.conjTranspose_mul, hTa]

/-- **`X` squared** (`lem:X-squared`).

Identifies both Gram matrices of `X` with the paper's SVD data and the total
operator `Q`. -/
lemma xSquared {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    data.x * data.xᴴ = data.u * (data.sigmaLeft * data.sigmaLeft) * data.uᴴ ∧
      data.xᴴ * data.x = QTotal data.qLayer ∧
      QTotal data.qLayer = data.v * (data.sigmaRight * data.sigmaRight) * data.vᴴ := by
  exact ⟨data.x_gram_left_svd, data.x_gram_right, data.q_total_svd⟩

/-- **`X`-expression to `Q`-expression** (`lem:X-expression-to-Q-expression`).

Converts the quadratic error term in `X X† - I` to the corresponding
`Q_a Q Q_a - Q_a` expression. -/
lemma xExpressionToQExpression {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
    (Xa data a)ᴴ *
        ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1)) *
        Xa data a =
      Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
        Qa data.qLayer a := by
  have hQaSq : Qa data.qLayer a * Qa data.qLayer a = Qa data.qLayer a := by
    exact (data.qa_projective a).idempotent
  have hQaXa : (Xa data a)ᴴ * Xa data a = Qa data.qLayer a := by
    exact (qaRestated data a).1.symm
  have hQaLeft : (Xa data a)ᴴ * data.x = Qa data.qLayer a := by
    exact (qaRestated data a).2.2.symm
  have hQaRight : data.xᴴ * Xa data a = Qa data.qLayer a := by
    simpa [Xa, Matrix.mul_assoc] using (data.qa_eq a).symm
  calc
    (Xa data a)ᴴ *
        ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1)) *
        Xa data a =
      ((Xa data a)ᴴ * ((data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1))) *
        Xa data a := by
          rw [Matrix.mul_assoc]
    _ = ((Xa data a)ᴴ *
          (data.x * data.xᴴ * (data.x * data.xᴴ) + (-2 • (data.x * data.xᴴ) + 1))) *
        Xa data a := by
          congr 1
          noncomm_ring
    _ = (Xa data a)ᴴ * data.x * (data.xᴴ * data.x * (data.xᴴ * Xa data a)) +
        (-2 • ((Xa data a)ᴴ * data.x * (data.xᴴ * Xa data a)) + (Xa data a)ᴴ * Xa data a) := by
          rw [Matrix.mul_assoc]
          rw [Matrix.add_mul, Matrix.add_mul]
          rw [Matrix.mul_add, Matrix.mul_add]
          have hneg :
              (Xa data a)ᴴ * ((-(data.x * data.xᴴ) + -(data.x * data.xᴴ)) * Xa data a) =
                -((Xa data a)ᴴ * (data.x * (data.xᴴ * Xa data a))) +
                  -((Xa data a)ᴴ * (data.x * (data.xᴴ * Xa data a))) := by
            rw [Matrix.add_mul]
            rw [Matrix.mul_add]
            simp [Matrix.mul_assoc]
          simp [Matrix.mul_assoc, two_smul, hneg]
    _ = Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
        Qa data.qLayer a := by
      simp [Matrix.mul_assoc, hQaXa, hQaLeft, hQaRight, data.x_gram_right, hQaSq]
      noncomm_ring
    _ = Qa data.qLayer a * QTotal data.qLayer * Qa data.qLayer a -
        Qa data.qLayer a := by
      noncomm_ring

/-- **`P_a` restated** (`lem:pa-restated`).

Rewrites `P_a` in terms of `XHat`, `XHat_a`, and `T_a`. -/
lemma paRestated {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) (a : Outcome) :
      Pa data a = data.xHatᴴ * Ta data.qLayer a * data.xHat ∧
      Pa data a = (XHatA data a)ᴴ * data.xHat := by
  constructor
  · -- The first conjunct is definitional from `Pa`.
    rfl
  · have hTa : (Ta data.qLayer a)ᴴ = Ta data.qLayer a := by
      simpa [Ta] using ProjMeas.outcome_hermitian data.qLayer.t a
    have hXHatA : (XHatA data a)ᴴ = data.xHatᴴ * Ta data.qLayer a := by
      calc
        (XHatA data a)ᴴ = (Ta data.qLayer a * data.xHat)ᴴ := by rfl
        _ = data.xHatᴴ * (Ta data.qLayer a)ᴴ := by
              simp [Matrix.conjTranspose_mul]
        _ = data.xHatᴴ * Ta data.qLayer a := by rw [hTa]
    calc
      Pa data a = data.xHatᴴ * Ta data.qLayer a * data.xHat := by rfl
      _ = (XHatA data a)ᴴ * data.xHat := by rw [hXHatA]

/-- **`XHat` squared** (`lem:X-hat-squared`).

The unitary-part matrix `XHat` has `XHat XHat† = I` on the auxiliary space. -/
lemma xHatSquared {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    data.xHat * data.xHatᴴ =
      (1 : MIPStarRE.Quantum.Op data.qLayer.auxSpace.carrier) := by
  simpa using data.xHat_coisometry

/-- **`X` times `XHat`** (`lem:X-times-X-hat`).

Relates the mixed products `X XHat†` and `X† XHat` to the SVD data and to
`sqrt Q`. -/
lemma xTimesXHat {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    data.x * data.xHatᴴ = data.u * data.sigmaLeft * data.uᴴ ∧
      data.xᴴ * data.xHat = CFC.sqrt (QTotal data.qLayer) := by
  -- TODO: prove (issue #197)
  sorry

private lemma xHat_mixed_adjoint {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    data.xHatᴴ * data.x = CFC.sqrt (QTotal data.qLayer) := by
  calc
    data.xHatᴴ * data.x = (data.xᴴ * data.xHat)ᴴ := by
      simp [Matrix.conjTranspose_mul]
    _ = (CFC.sqrt (QTotal data.qLayer))ᴴ := by rw [data.xHat_mixed]
    _ = CFC.sqrt (QTotal data.qLayer) := by
      simpa using (CFC.sqrt_nonneg (QTotal data.qLayer)).isHermitian.eq

private lemma xxHat_isHermitian {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (data.x * data.xHatᴴ)ᴴ = data.x * data.xHatᴴ := by
  calc
    (data.x * data.xHatᴴ)ᴴ = data.xHat * data.xᴴ := by
      simp [Matrix.conjTranspose_mul]
    _ = data.xHat * data.xᴴ * (data.xHat * data.xHatᴴ) := by
      simp [data.xHat_coisometry]
    _ = data.xHat * (data.xᴴ * data.xHat) * data.xHatᴴ := by
      simp [Matrix.mul_assoc]
    _ = data.xHat * (data.xHatᴴ * data.x) * data.xHatᴴ := by
      rw [xHat_mixed_adjoint data, data.xHat_mixed]
    _ = (data.xHat * data.xHatᴴ) * data.x * data.xHatᴴ := by
      simp [Matrix.mul_assoc]
    _ = data.x * data.xHatᴴ := by
      simp [data.xHat_coisometry, Matrix.mul_assoc]

private lemma xxHat_sq {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (data.x * data.xHatᴴ) * (data.x * data.xHatᴴ) = data.x * data.xᴴ := by
  calc
    (data.x * data.xHatᴴ) * (data.x * data.xHatᴴ)
        = data.x * (data.xHatᴴ * data.x) * data.xHatᴴ := by
            simp [Matrix.mul_assoc]
    _ = data.x * (data.xᴴ * data.xHat) * data.xHatᴴ := by
          rw [xHat_mixed_adjoint data, data.xHat_mixed]
    _ = data.x * data.xᴴ := by
          simp [Matrix.mul_assoc, data.xHat_coisometry]

private lemma xxHat_nonneg {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    0 ≤ data.x * data.xHatᴴ := by
  have hsqrt_nonneg : 0 ≤ CFC.sqrt (QTotal data.qLayer) := CFC.sqrt_nonneg (QTotal data.qLayer)
  calc
    0 ≤ data.xHat * CFC.sqrt (QTotal data.qLayer) * data.xHatᴴ := by
      exact
        (Matrix.PosSemidef.mul_mul_conjTranspose_same
          (Matrix.nonneg_iff_posSemidef.mp hsqrt_nonneg)
          data.xHat).nonneg
    _ = data.x * data.xHatᴴ := by
      calc
        data.xHat * CFC.sqrt (QTotal data.qLayer) * data.xHatᴴ
            = data.xHat * (data.xHatᴴ * data.x) * data.xHatᴴ := by
                rw [← xHat_mixed_adjoint data]
        _ = (data.xHat * data.xHatᴴ) * data.x * data.xHatᴴ := by
              simp [Matrix.mul_assoc]
        _ = data.x * data.xHatᴴ := by
              simp [data.xHat_coisometry, Matrix.mul_assoc]

/-- **Squared difference** (`lem:squared-difference`).

Bounds the defect between `X` and `XHat` by the squared defect of `X X†`
from the auxiliary identity. -/
lemma squaredDifference {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    (data.x - data.xHat) * (data.x - data.xHat)ᴴ ≤
      (data.x * data.xᴴ - 1) * (data.x * data.xᴴ - 1) := by
  sorry

/-- **Projectivity of `P`** (`lem:P-projectivity`).

The family `P_a` built from `XHat` and `T_a` is a projective
submeasurement. -/
lemma pProjectivity {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (data : QXPLayerData Outcome ι) :
    ∃ P : ProjSubMeas Outcome ι,
      ∀ a : Outcome, P.outcome a = Pa data a := by
  sorry

/-- **`P` is close to `Q`** (`lem:P-Q-approx`).

The final internal comparison in the paper's repair step shows that `P_a`
is `30 ζ^(1/4)`-close to `Q_a` in the project's `≈`-style raw-family metric. -/
lemma pQApprox {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι)
    (A : Measurement Outcome ι) (ζ : Error)
    (data : QXPLayerData Outcome ι) :
    RankReductionWitness ψ A ζ data.qLayer →
      SDDOpRel ψ (uniformDistribution Unit)
        (constOpFamily data.qLayer.q)
        (constOpFamily (PFamily data))
        (30 * zetaQuarterRoot ζ) := by
  -- TODO: prove (issue #197)
  sorry

end

end MIPStarRE.LDT.MakingMeasurementsProjective
