import Mathlib.Algebra.Order.Chebyshev
import MIPStarRE.LDT.Preliminaries.Theorems

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
  let x : κ → Error := fun i => Real.sqrt (ev ψ ((D i)ᴴ * D i))
  calc
    ev ψ ((∑ i, D i)ᴴ * (∑ i, D i))
      = ∑ i, ∑ j, ev ψ ((D i)ᴴ * D j) := by
          rw [Matrix.conjTranspose_sum, Finset.sum_mul, ev_sum]
          simp_rw [Matrix.mul_sum, ev_sum]
    _ ≤ ∑ i, ∑ j, |ev ψ ((D i)ᴴ * D j)| := by
          refine Finset.sum_le_sum ?_
          intro i _
          refine Finset.sum_le_sum ?_
          intro j _
          exact le_abs_self _
    _ ≤ ∑ i, ∑ j, x i * x j := by
          refine Finset.sum_le_sum ?_
          intro i _
          refine Finset.sum_le_sum ?_
          intro j _
          dsimp [x]
          simpa using ev_abs_mul_le_sqrt ψ ((D i)ᴴ) (D j)
    _ = (∑ i, x i) ^ 2 := by
          rw [sq]
          calc
            ∑ i, ∑ j, x i * x j = ∑ i, x i * ∑ j, x j := by
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [Finset.mul_sum]
            _ = (∑ i, x i) * ∑ j, x j := by
              rw [Finset.sum_mul]
    _ ≤ (Fintype.card κ : Error) * ∑ i, x i ^ 2 := by
          simpa using
            (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x))
    _ = (Fintype.card κ : Error) * ∑ i, ev ψ ((D i)ᴴ * D i) := by
          refine congrArg ((Fintype.card κ : Error) * ·) ?_
          refine Finset.sum_congr rfl ?_
          intro i _
          dsimp [x]
          rw [Real.sq_sqrt]
          exact ev_adjoint_self_nonneg ψ (D i)

/-- `prop:triangle-sub`.

Proof sketch: rewrite both consistency errors as
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
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A))
      (IdxSubMeas.liftRight C) δ)
    (hAB : SDDRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A))
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas B)) ε) :
    ConsRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas B))
      (IdxSubMeas.liftRight C) (δ + Real.sqrt ε) := by
    -- TODO(#176): replace with the proof sketched in the docstring
    sorry

/-- `prop:simeq-triangle-inequality`.

Proof sketch: apply `simeqToApprox` to the two hypotheses through the middle
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
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) ε)
    (hCB : ConsRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas C))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas B)) δ)
    (hCD : ConsRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas C))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D)) γ) :
    ConsRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A))
      (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas D))
      (ε + 2 * Real.sqrt (δ + γ)) := by
    -- TODO(#176): complete using simeqToApprox + SDDRel triangle + triangleSub
    sorry

end MIPStarRE.LDT.Preliminaries
