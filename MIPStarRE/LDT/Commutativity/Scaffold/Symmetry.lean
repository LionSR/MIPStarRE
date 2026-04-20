import MIPStarRE.LDT.Commutativity.Scaffold.Core

/-!
# Section 11 commutativity: scaffold symmetry

Symmetry transport between coded `F_q` points and the underlying scalar model,
packaging the scaffold theorem statements used by the Section 11 commutativity
argument.

## References

- arXiv:2009.12982, Section 11 (commutativity of the Pauli-`X` and `Z` players).
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-! ## Scaffold theorem statements -/

/-- Package the point-consistency field using the local evaluated-point-family
notation. -/
private lemma evaluatedPointFamily_pointConsistency
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      (evaluatedPointFamily params family)
      zeta := by
  simpa [evaluatedPointFamily] using hcons.pointConsistency

private lemma qMatchMass_symm
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) :
    qMatchMass ψ A B = qMatchMass ψ B A := by
  unfold qMatchMass
  refine Finset.sum_congr rfl ?_
  intro a _
  exact ev_mul_comm_of_psd ψ _ _ (A.outcome_pos a) (B.outcome_pos a)

private lemma qConsDefect_symm
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState ι) (A B : SubMeas Outcome ι) :
    qConsDefect ψ A B = qConsDefect ψ B A := by
  simp [qConsDefect, qMatchMass_symm,
    ev_mul_comm_of_psd ψ _ _ A.total_nonneg B.total_nonneg]

omit [Fintype ι] [DecidableEq ι] in
private lemma swapDensity_eq_reindex
    (X : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity X = Matrix.reindex (Equiv.prodComm ι ι) (Equiv.prodComm ι ι) X := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  rfl

private lemma normalizedTrace_reindex
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (X : MIPStarRE.Quantum.Op α) :
    MIPStarRE.Quantum.normalizedTrace (Matrix.reindex e e X) =
      MIPStarRE.Quantum.normalizedTrace X := by
  have hcard : Fintype.card β = Fintype.card α := Fintype.card_congr e.symm
  unfold MIPStarRE.Quantum.normalizedTrace Matrix.trace
  simp_rw [Matrix.diag_apply, Matrix.reindex_apply]
  rw [← e.symm.sum_comp (fun i : α => X i i)]
  simp [hcard]

private lemma swapDensity_mul
    (X Y : MIPStarRE.Quantum.Op (ι × ι)) :
    swapDensity (X * Y) = swapDensity X * swapDensity Y := by
  simpa [swapDensity_eq_reindex] using
    (Matrix.reindexAlgEquiv_mul ℂ ℂ (Equiv.prodComm ι ι) X Y)

private lemma normalizedTrace_swapDensity
    (X : MIPStarRE.Quantum.Op (ι × ι)) :
    MIPStarRE.Quantum.normalizedTrace (swapDensity X) =
      MIPStarRE.Quantum.normalizedTrace X := by
  simpa [swapDensity_eq_reindex] using
    normalizedTrace_reindex (Equiv.prodComm ι ι) X

private lemma swapDensity_opTensor
    (X Y : MIPStarRE.Quantum.Op ι) :
    swapDensity (opTensor X Y) = opTensor Y X := by
  ext x y
  rcases x with ⟨i₁, i₂⟩
  rcases y with ⟨j₁, j₂⟩
  simp [swapDensity, opTensor, mul_comm]

private lemma ev_swapDensity_of_density_fixed
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (Z : MIPStarRE.Quantum.Op (ι × ι)) :
    ev ψ (swapDensity Z) = ev ψ Z := by
  unfold ev
  apply congrArg Complex.re
  calc
    MIPStarRE.Quantum.normalizedTrace (ψ.density * swapDensity Z)
      = MIPStarRE.Quantum.normalizedTrace (swapDensity (ψ.density * Z)) := by
          rw [swapDensity_mul]
          simp [hfix]
    _ = MIPStarRE.Quantum.normalizedTrace (ψ.density * Z) :=
          normalizedTrace_swapDensity _

private lemma ev_opTensor_swap_of_density_fixed
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (X Y : MIPStarRE.Quantum.Op ι) :
    ev ψ (opTensor X Y) = ev ψ (opTensor Y X) := by
  rw [show opTensor Y X = swapDensity (opTensor X Y) by
    rw [swapDensity_opTensor]]
  exact (ev_swapDensity_of_density_fixed ψ hfix (opTensor X Y)).symm

private lemma qBipartiteMatchMass_symm_of_density_fixed
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (A B : SubMeas Outcome ι) :
    qBipartiteMatchMass ψ A B = qBipartiteMatchMass ψ B A := by
  unfold qBipartiteMatchMass
  refine Finset.sum_congr rfl ?_
  intro a _
  exact ev_opTensor_swap_of_density_fixed ψ hfix (A.outcome a) (B.outcome a)

private lemma qBipartiteConsDefect_symm_of_density_fixed
    {Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (A B : SubMeas Outcome ι) :
    qBipartiteConsDefect ψ A B = qBipartiteConsDefect ψ B A := by
  simp [qBipartiteConsDefect, qBipartiteMatchMass_symm_of_density_fixed,
    ev_opTensor_swap_of_density_fixed, hfix]

private lemma consRel_symm_of_density_fixed
    {Question Outcome : Type*} [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (hfix : swapDensity ψ.density = ψ.density)
    (𝒟 : Distribution Question)
    (A B : IdxSubMeas Question Outcome ι)
    (δ : Error) :
    ConsRel ψ 𝒟 A B δ → ConsRel ψ 𝒟 B A δ := by
  intro ⟨h⟩
  constructor
  unfold bipartiteConsError at *
  calc
    avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (B q) (A q))
      = avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q) (B q)) := by
          apply avgOver_congr
          intro q
          symm
          exact qBipartiteConsDefect_symm_of_density_fixed ψ hfix (A q) (B q)
    _ ≤ δ := h

private lemma evaluatedPointFamily_pointConsistency_swapped_of_density_fixed
    (params : Parameters)
    [FieldModel params.q]
    (strategy : SymStrat params.next ι)
    (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hfix : swapDensity strategy.state.density = strategy.state.density)
    (hcons : family.ConsistentWithPoints strategy zeta) :
    ConsRel strategy.state
      (uniformDistribution (Point params.next))
      (evaluatedPointFamily params family)
      (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
      zeta := by
  exact consRel_symm_of_density_fixed
    strategy.state hfix
    (uniformDistribution (Point params.next))
    (IdxProjMeas.toIdxSubMeas strategy.pointMeasurement)
    (evaluatedPointFamily params family)
    zeta
    (by simpa [evaluatedPointFamily] using hcons.pointConsistency)


end MIPStarRE.LDT.Commutativity
