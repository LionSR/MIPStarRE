import MIPStarRE.LDT.Test.Defs
import MIPStarRE.LDT.Preliminaries.PolynomialAgreement

/-!
# `mainFormal` Step 5 — Schwartz--Zippel self-consistency handoff

This file isolates the paper's Step 5 bridge in
`references/ldt-paper/inductive_step.tex`, lines 119--133.  The algebraic
expansion/reindexing from evaluated consistency to the full-polynomial
consistency defect is proved here, and the genuinely Schwartz--Zippel part is
provided by the shared tensor bound
`Preliminaries.polynomialCollisionMass_le_mdq`.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

namespace Test

open Classical in
private lemma postprocess_match_summand_expand
    {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (A B : SubMeas α ι) (f : α → β) (b : β) :
    ev ψ (opTensor ((postprocess A f).outcome b) ((postprocess B f).outcome b)) =
      ∑ aa : α × α,
        if f aa.1 = b ∧ f aa.2 = b then
          ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2))
        else 0 := by
  classical
  simp only [postprocess, Finset.sum_filter, opTensor_sum_left_univ, opTensor_sum_right_univ,
    ev_sum]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro a _
  refine Finset.sum_congr rfl ?_
  intro x _
  by_cases ha : f a = b <;> by_cases hx : f x = b <;> simp [ha, hx, opTensor, ev_zero]

open Classical in
private lemma qBipartiteMatchMass_postprocess_eq_pair_sum
    {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (A B : SubMeas α ι) (f : α → β) :
    qBipartiteMatchMass ψ (postprocess A f) (postprocess B f) =
      ∑ aa : α × α,
        if f aa.1 = f aa.2 then
          ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2))
        else 0 := by
  classical
  unfold qBipartiteMatchMass
  calc
    ∑ b : β, ev ψ (opTensor ((postprocess A f).outcome b) ((postprocess B f).outcome b))
      = ∑ b : β, ∑ aa : α × α,
          if f aa.1 = b ∧ f aa.2 = b then
            ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2))
          else 0 := by
            refine Finset.sum_congr rfl ?_
            intro b _
            exact postprocess_match_summand_expand ψ A B f b
    _ = ∑ aa : α × α, ∑ b : β,
          if f aa.1 = b ∧ f aa.2 = b then
            ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2))
          else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ aa : α × α,
        if f aa.1 = f aa.2 then
          ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2))
        else 0 := by
            refine Finset.sum_congr rfl ?_
            intro aa _
            by_cases h : f aa.1 = f aa.2
            · rw [Finset.sum_eq_single (f aa.1)]
              · simp [h]
              · intro b _ hb
                have hb1 : f aa.1 ≠ b := by
                  intro hEq
                  exact hb hEq.symm
                by_cases h1 : f aa.1 = b
                · exact (hb1 h1).elim
                · simp [h1]
              · simp
            · have hzero : (∑ b : β,
                  if f aa.1 = b ∧ f aa.2 = b then
                    ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2)) else 0) = 0 := by
                refine Finset.sum_eq_zero ?_
                intro b _
                by_cases h1 : f aa.1 = b
                · have h2 : f aa.2 ≠ b := by
                    intro h2
                    exact h (h1.trans h2.symm)
                  simp [h1, h2]
                · simp [h1]
              simp [h, hzero]

open Classical in
private lemma qBipartiteMatchMass_eq_pair_diag
    {α ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (A B : SubMeas α ι) :
    qBipartiteMatchMass ψ A B =
      ∑ aa : α × α,
        if aa.1 = aa.2 then
          ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2))
        else 0 := by
  classical
  unfold qBipartiteMatchMass
  symm
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro a _
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    have hb' : ¬ a = b := by
      intro hEq
      exact hb hEq.symm
    simp [hb']
  · simp

open Classical in
private noncomputable def localCollisionMass
    {α β ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (A B : SubMeas α ι) (f : α → β) : Error :=
  ∑ aa : α × α,
    (if aa.1 = aa.2 then 0 else if f aa.1 = f aa.2 then (1 : Error) else 0) *
      ev ψ (opTensor (A.outcome aa.1) (B.outcome aa.2))

private lemma localCollisionMass_nonneg
    {α β ι : Type*} [Fintype α] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (A B : SubMeas α ι) (f : α → β) :
    0 ≤ localCollisionMass ψ A B f := by
  classical
  unfold localCollisionMass
  refine Finset.sum_nonneg ?_
  intro aa _
  apply mul_nonneg
  · by_cases hEq : aa.1 = aa.2
    · simp [hEq]
    · by_cases hf : f aa.1 = f aa.2
      · simp [hEq, hf]
      · simp [hEq, hf]
  · exact ev_nonneg_of_psd ψ _ (opTensor_nonneg (A.outcome_pos aa.1) (B.outcome_pos aa.2))

private lemma qBipartiteMatchMass_postprocess_eq_add_localCollision
    {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (A B : SubMeas α ι) (f : α → β) :
    qBipartiteMatchMass ψ (postprocess A f) (postprocess B f) =
      qBipartiteMatchMass ψ A B + localCollisionMass ψ A B f := by
  classical
  rw [qBipartiteMatchMass_postprocess_eq_pair_sum]
  rw [qBipartiteMatchMass_eq_pair_diag]
  unfold localCollisionMass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro aa _
  by_cases hEq : aa.1 = aa.2
  · simp [hEq]
  · by_cases hf : f aa.1 = f aa.2 <;> simp [hEq, hf]

private lemma max_sub_le_max_sub_add_of_nonneg (x c : Error) (hc : 0 ≤ c) :
    max 0 x ≤ max 0 (x - c) + c := by
  apply max_le
  · exact add_nonneg (le_max_left 0 (x - c)) hc
  · have hx : x - c ≤ max 0 (x - c) := le_max_right 0 (x - c)
    linarith

private lemma qBipartiteConsDefect_le_postprocess_add_localCollision
    {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState (ι × ι)) (A B : SubMeas α ι) (f : α → β) :
    qBipartiteConsDefect ψ A B ≤
      qBipartiteConsDefect ψ (postprocess A f) (postprocess B f) +
        localCollisionMass ψ A B f := by
  classical
  let c := localCollisionMass ψ A B f
  have hc : 0 ≤ c := localCollisionMass_nonneg ψ A B f
  have hmatch := qBipartiteMatchMass_postprocess_eq_add_localCollision ψ A B f
  unfold qBipartiteConsDefect
  simp only [postprocess_total]
  rw [hmatch]
  change max 0 (ev ψ (opTensor A.total B.total) - qBipartiteMatchMass ψ A B) ≤
    max 0 (ev ψ (opTensor A.total B.total) -
      (qBipartiteMatchMass ψ A B + c)) + c
  convert
    (max_sub_le_max_sub_add_of_nonneg
      (ev ψ (opTensor A.total B.total) - qBipartiteMatchMass ψ A B) c hc) using 1
  ring_nf

private lemma avg_localCollisionMass_eval_eq_polynomialCollisionMass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (Left Right : SubMeas (Polynomial params) ι) :
    avgOver (uniformDistribution (Point params))
      (fun u => localCollisionMass ψ Left Right (fun g : Polynomial params => g u)) =
      Preliminaries.polynomialCollisionMass params ψ Left Right := by
  classical
  unfold localCollisionMass Preliminaries.polynomialCollisionMass
  rw [avgOver_sum]
  refine Finset.sum_congr rfl ?_
  intro gg _
  by_cases hEq : gg.1 = gg.2
  · simp [hEq, avgOver_zero]
  · simp only [hEq, if_false]
    rw [avgOver_mul_const]
    congr 1
    apply avgOver_congr
    intro u
    by_cases h : gg.1 u = gg.2 u <;> simp [h]

/-- The exact algebraic expansion/reindexing statement used in `mainFormal` Step 5.

Paper origin: `references/ldt-paper/inductive_step.tex:119-130`
(`\label{eq:G-self-consistency}`), with the collision estimate supplied by the
Schwartz--Zippel lemma.

Paper lines 119--128 compare the evaluated consistency defect

`E_u ∑_{a ≠ b} ⟨ψ| G^A_[g(u)=a] ⊗ G^B_[h(u)=b] |ψ⟩`

with the full-polynomial consistency defect

`∑_{g ≠ h} ⟨ψ| G^A_g ⊗ G^B_h |ψ⟩`.

The paper reuses `g` as the bound name in the Alice and Bob sums; Lean writes
these independently-bound polynomial outcomes as `g` and `h` to make the
independence explicit.

After expanding the postprocessed outcomes and separating the colliding pairs
`g(u)=h(u)`, the only extra term is the collision mass bounded by
Schwartz--Zippel in `Preliminaries.polynomialCollisionMass_le_mdq`.  This
predicate records precisely that expansion step, without bundling the
Schwartz--Zippel estimate itself into an unproved hypothesis. -/
def MainFormalStep5ExpansionBound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (Left Right : SubMeas (Polynomial params) ι) : Prop :=
  bipartiteConsError ψ (uniformDistribution Unit)
      (constSubMeasFamily Left) (constSubMeasFamily Right) ≤
    bipartiteConsError ψ (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Left)
      (polynomialEvaluationFamily params Right) +
    Preliminaries.polynomialCollisionMass params ψ Left Right

/-- The algebraic Step 5 expansion bound: the full-polynomial consistency
error is bounded by the evaluated consistency error plus the collision mass. -/
theorem mainFormalStep5_expansionBound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι))
    (Left Right : SubMeas (Polynomial params) ι) :
    MainFormalStep5ExpansionBound params ψ Left Right := by
  classical
  unfold MainFormalStep5ExpansionBound
  calc
    bipartiteConsError ψ (uniformDistribution Unit)
        (constSubMeasFamily Left) (constSubMeasFamily Right)
      = qBipartiteConsDefect ψ Left Right := by
          simp [bipartiteConsError, avgOver, uniformDistribution, constSubMeasFamily]
    _ = avgOver (uniformDistribution (Point params))
          (fun _ : Point params => qBipartiteConsDefect ψ Left Right) := by
          exact (avgOver_uniform_const (α := Point params)
            (c := qBipartiteConsDefect ψ Left Right)).symm
    _ ≤ avgOver (uniformDistribution (Point params))
          (fun u =>
            qBipartiteConsDefect ψ (evaluateAt params u Left) (evaluateAt params u Right) +
              localCollisionMass ψ Left Right (fun g : Polynomial params => g u)) := by
          apply avgOver_mono
          intro u
          exact qBipartiteConsDefect_le_postprocess_add_localCollision ψ Left Right
            (fun g : Polynomial params => g u)
    _ = bipartiteConsError ψ (uniformDistribution (Point params))
          (polynomialEvaluationFamily params Left)
          (polynomialEvaluationFamily params Right) +
        Preliminaries.polynomialCollisionMass params ψ Left Right := by
          rw [avgOver_add]
          change bipartiteConsError ψ (uniformDistribution (Point params))
              (polynomialEvaluationFamily params Left)
              (polynomialEvaluationFamily params Right) +
            avgOver (uniformDistribution (Point params))
              (fun u => localCollisionMass ψ Left Right (fun g : Polynomial params => g u)) =
            bipartiteConsError ψ (uniformDistribution (Point params))
              (polynomialEvaluationFamily params Left)
              (polynomialEvaluationFamily params Right) +
            Preliminaries.polynomialCollisionMass params ψ Left Right
          rw [avg_localCollisionMass_eval_eq_polynomialCollisionMass]

/-- Step 5 packaging for `mainFormal` using the proved algebraic expansion bound.

Given evaluated consistency at error `ζ` (paper line 116) and the exact
line-122--125 expansion recorded by `MainFormalStep5ExpansionBound`, the
proved tensor Schwartz--Zippel bound contributes the paper's `md/q` loss and
returns full-polynomial consistency at error `ζ + md/q` (paper lines 126--133). -/
theorem mainFormalStep5_selfConsistency_ofExpansionBound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (params : Parameters) [FieldModel params.q]
    (ψ : QuantumState (ι × ι)) (hnorm : ψ.IsNormalized)
    (Left Right : SubMeas (Polynomial params) ι) (ζ : Error)
    (hevaluated : ConsRel ψ (uniformDistribution (Point params))
      (polynomialEvaluationFamily params Left)
      (polynomialEvaluationFamily params Right) ζ) :
    ConsRel ψ (uniformDistribution Unit)
      (constSubMeasFamily Left) (constSubMeasFamily Right)
      (ζ + (params.m * params.d : Error) / params.q) := by
  constructor
  calc
    bipartiteConsError ψ (uniformDistribution Unit)
        (constSubMeasFamily Left) (constSubMeasFamily Right)
      ≤ bipartiteConsError ψ (uniformDistribution (Point params))
          (polynomialEvaluationFamily params Left)
          (polynomialEvaluationFamily params Right) +
        Preliminaries.polynomialCollisionMass params ψ Left Right :=
        mainFormalStep5_expansionBound params ψ Left Right
    _ ≤ ζ + (params.m * params.d : Error) / params.q := by
        have hcollision :=
          Preliminaries.polynomialCollisionMass_le_mdq params ψ hnorm Left Right
        linarith [hevaluated.offDiagonalBound, hcollision]

end Test

end MIPStarRE.LDT
