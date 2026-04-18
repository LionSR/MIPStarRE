import MIPStarRE.LDT.Preliminaries.Triangles.Consistency

/-!
# Triangle inequalities: binary `approx_δ` composition

Records the binary composition step of `prop:triangle-inequality-for-approx_delta`
from the paper; the iterated chain version follows by induction on chain length.

## References

- arXiv:2009.12982, Section 7 (triangle inequalities for state-dependent distance).
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

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
