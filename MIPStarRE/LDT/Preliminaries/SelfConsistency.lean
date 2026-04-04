import MIPStarRE.LDT.Preliminaries.Theorems

/-!
# Self-Consistency Extensions

Additional proposition statements from
`references/ldt-paper/preliminaries.tex`.

The long paper-faithful Lean proofs for these extensions are still pending.
This file records the exact signatures together with proof-sketch comments
as statement stubs; the theorem bodies use `sorry` placeholders until the
full proofs are formalized.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

/-- `prop:cool-prop` — Squared mass lower bound from bipartite SSC.

Proof sketch:
1. Apply Cauchy-Schwarz to the families `A_a ⊗ I` and `I ⊗ A_a`.
2. Use permutation invariance to identify the two square-mass factors.
3. Conclude `∑ₐ ⟨ψ|(A_a)^2 ⊗ I|ψ⟩ ≥ ∑ₐ ⟨ψ|A_a ⊗ A_a|ψ⟩`.
4. Combine with `BipartiteSSCRel` on the constant `Unit`-indexed family. -/
theorem bipartiteSSCSquaredMass {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (A : SubMeas Outcome ι) (ζ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit) (constSubMeasFamily A) ζ →
      ∑ a : Outcome, ev ψ (leftTensor (ι₂ := ι) (A.outcome a * A.outcome a)) ≥
        ev ψ (leftTensor (ι₂ := ι) A.total) - ζ := by
    sorry -- TODO(sorry)

/-- `prop:other-two-notions-of-self-consistency`.

Proof sketch:
1. Expand `qConsDefect` for the left/right lifts.
2. Bound the total-overlap term `⟨ψ|A ⊗ A|ψ⟩` by `⟨ψ|A ⊗ I|ψ⟩`
   using `A.total ≤ I`.
3. The remaining expression is exactly the bipartite SSC defect.
4. Average over questions and use the hypothesis. -/
theorem otherTwoNotionsOfSelfConsistency {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) (δ : Error) :
    BipartiteSSCRel ψ 𝒟 A δ →
      ConsRel ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftRight A) δ := by
    sorry -- TODO(sorry)

/-- `prop:two-notions-of-self-consistency-after-evaluation`.

Proof sketch:
1. Postprocessing preserves the total mass and can only increase the diagonal
   overlap term `∑_b ⟨ψ|A_[f(a)=b] ⊗ A_[f(a)=b]|ψ⟩`.
2. Hence bipartite SSC transfers from `A` to the postprocessed family.
3. Apply `twoNotionsOfSelfConsistency` to the postprocessed family. -/
theorem twoNotionsOfSelfConsistencyAfterEvaluation
    {Question α β : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (𝒟 : Distribution Question)
    (A : IdxSubMeas Question α ι) (δ : Error) (f : α → β) :
    BipartiteSSCRel ψ 𝒟 A δ →
      SDDRel ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess (A q) f))
        (IdxSubMeas.liftRight (fun q => postprocess (A q) f))
        (2 * δ) := by
    sorry -- TODO(sorry)

/-- `prop:completeness-transfer-self-consistent-A`.

Proof sketch:
1. Lower-bound `⟨ψ|B ⊗ I|ψ⟩` by the mixed overlap
   `∑ₐ ⟨ψ|B_a ⊗ A_a|ψ⟩` using `A_a ≤ I`.
2. Compare `∑ₐ ⟨ψ|B_a ⊗ A_a|ψ⟩` with
   `∑ₐ ⟨ψ|A_a ⊗ A_a|ψ⟩` by a Cauchy-Schwarz overlap estimate from
   the hypothesis `A ⊗ I ≈_ε B ⊗ I`.
3. Use bipartite SSC to replace the latter by
   `⟨ψ|A ⊗ I|ψ⟩ - δ`.
4. Relax the resulting bound to the requested `δ + 2√ε` form. -/
theorem completenessTransferSelfConsistentA
    {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : IdxSubMeas Question Outcome ι) (δ ε : Error) :
    BipartiteSSCRel ψ 𝒟 A δ →
    SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftLeft B) ε →
      idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft B) ≥
        idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) - δ - 2 * Real.sqrt ε := by
    sorry -- TODO(sorry)

/-- `prop:self-consistency-implies-data-processing`.

Proof sketch:
1. First prove the “wrong-side” estimate
   `P_[f] ⊗ I ≈_{2δ + 4√ε} I ⊗ A_[f]` by:
   - expanding the `qSDD` square,
   - bounding the mass of `P` via `completenessTransferProjectiveP`,
   - comparing the mixed overlap with the diagonal overlap of `A`,
   - and using SSC plus postprocessing monotonicity.
2. Apply `twoNotionsOfSelfConsistencyAfterEvaluation` to obtain
   `A_[f] ⊗ I ≈_{2δ} I ⊗ A_[f]`.
3. Use the `SDDRel` triangle inequality to conclude
   `P_[f] ⊗ I ≈_{8δ + 8√ε} A_[f] ⊗ I`. -/
theorem selfConsistencyImpliesDataProcessing
    {Question α β : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]
    (ψ : QuantumState (ι × ι))
    (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question α ι)
    (P : IdxProjSubMeas Question α ι)
    (δ ε : Error) (f : α → β) :
    BipartiteSSCRel ψ 𝒟 A δ →
    SDDRel ψ 𝒟
      (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas P))
      (IdxSubMeas.liftLeft A) ε →
      SDDRel ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess ((P q).toSubMeas) f))
        (IdxSubMeas.liftLeft (fun q => postprocess (A q) f))
        (8 * δ + 8 * Real.sqrt ε) := by
    sorry -- TODO(sorry)

end MIPStarRE.LDT.Preliminaries
