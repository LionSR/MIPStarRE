import MIPStarRE.LDT.Preliminaries.Triangles.Core

/-!
# Triangle Inequalities for State-Dependent Distance: Simultaneous Equivalence

This module contains the simultaneous-equivalence triangle inequalities and the
final approximate-delta triangle estimate.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

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

/-- Heterogeneous form of `prop:simeq-triangle-inequality`.

This is the paper's triangle step for a general bipartite strategy: the first
and third measurements act on Alice's space, while the second and fourth act on
Bob's space.  No same-space identification or swap symmetry is used. -/
theorem simeqTriangleInequality_heterogeneous
    {Question Outcome : Type*} {ιA ιB : Type*}
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB] [Fintype Outcome]
    (ψ : QuantumState (ιA × ιB)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized) (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A C : IdxMeas Question Outcome ιA)
    (B D : IdxMeas Question Outcome ιB)
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
  have hCB_sdd : SDDRel ψ 𝒟
      (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas C))
      (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas B))
      (2 * δ) :=
    simeqToApprox_heterogeneous ψ 𝒟 C B δ hCB
  have hCD_sdd : SDDRel ψ 𝒟
      (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas C))
      (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas D))
      (2 * γ) :=
    simeqToApprox_heterogeneous ψ 𝒟 C D γ hCD
  have hBC_sdd : SDDRel ψ 𝒟
      (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas B))
      (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas C))
      (2 * δ) := by
    exact sddRel_symm ψ 𝒟 _ _ _ hCB_sdd
  have hBD_sdd_raw : SDDRel ψ 𝒟
      (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas B))
      (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas D))
      (2 * ((2 * δ) + (2 * γ))) := by
    exact
      stateDependentDistanceRel_triangle ψ 𝒟
        (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas B))
        (IdxSubMeas.placeLeft (ιB := ιB) (IdxMeas.toIdxSubMeas C))
        (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas D))
        (2 * δ) (2 * γ) hBC_sdd hCD_sdd
  have hBD_sdd : SDDRel ψ 𝒟
      (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas B))
      (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas D))
      (4 * (δ + γ)) := by
    exact
      stateDependentDistanceRel_mono ψ 𝒟
        (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas B))
        (IdxSubMeas.placeRight (ιA := ιA) (IdxMeas.toIdxSubMeas D))
        (2 * ((2 * δ) + (2 * γ))) (4 * (δ + γ))
        (by
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
      triangleSub_right_heterogeneous ψ 𝒟 hψ h𝒟
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
