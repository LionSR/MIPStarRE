import MIPStarRE.LDT.Basic.Distribution
import MIPStarRE.LDT.MakingMeasurementsProjective.Defs

/-!
# Section 7 hypercube graph: core definitions

Vertex-set cardinality and base-`q` digit encoding for points in `F_q^m`,
used to index the hypercube graph operators.

## References

- arXiv:2009.12982, Section 7 (expansion of the hypercube graph).
-/

namespace MIPStarRE.LDT.ExpansionHypercubeGraph

open MIPStarRE.LDT
open MIPStarRE.LDT.MakingMeasurementsProjective
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The number of vertices in the hypercube graph `C`. -/
def hypercubeVertexCount (params : Parameters) : ℕ :=
  params.q ^ params.m

/-- Encode a point `u ∈ F_q^m` by its base-`q` digit expansion. -/
def pointCode (params : Parameters) (u : Point params) : ℕ :=
  ∑ i : Fin params.m, (u i).1 * params.q ^ i.1

/-- The set of coordinates on which two points disagree. -/
def coordinateDisagreementSet (params : Parameters)
    (u v : Point params) : Finset (Fin params.m) :=
  Finset.univ.filter (fun i => u i ≠ v i)

/-- The number of coordinates on which two points disagree. -/
def coordinateDisagreementCount (params : Parameters)
    (u v : Point params) : ℕ :=
  (coordinateDisagreementSet params u v).card

/-- The hypercube edge relation: two points differ in at most one coordinate. -/
def IsHypercubeEdge (params : Parameters) (u v : Point params) : Prop :=
  coordinateDisagreementCount params u v ≤ 1

instance instDecidableIsHypercubeEdge (params : Parameters) (u v : Point params) :
    Decidable (IsHypercubeEdge params u v) := by
  unfold IsHypercubeEdge
  infer_instance

instance instDecidablePredHypercubeEdgePair (params : Parameters) :
    DecidablePred (fun uv : Point params × Point params => IsHypercubeEdge params uv.1 uv.2) := by
  intro uv
  infer_instance

/-- Edge sampling by rerandomizing a single coordinate.
This is the Section 7.1 distribution:
pick `u ∈ F_q^m`, `i ∈ {1, ..., m}`, and `x ∈ F_q` uniformly,
then set `v = u[i ↦ x]`. -/
noncomputable def rerandomizeCoordWeight (params : Parameters)
    (u v : Point params) : Error :=
  (((∑ p : Fin params.m × Fq params,
      if Function.update u p.1 p.2 = v then (1 : ℕ) else 0) : ℕ) : Error) /
    (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error)

noncomputable def rerandomizeCoord (params : Parameters) :
    Distribution (Point params × Point params) :=
  { support := Finset.univ
    weight := fun uv => rerandomizeCoordWeight params uv.1 uv.2
    -- Normalization: `∑ uv, weight uv = 1`. Each triple `(u, i, x)`
    -- contributes to exactly one pair `(u, Function.update u i x)`, so the
    -- total count is `q^m * m * q = hypercubeVertexCount * m * q`, matching
    -- the denominator. `Distribution` doesn't carry a mass field; the
    -- normalization should be proved as a standalone lemma when needed.
    nonnegative := by
      intro uv
      have hden :
          0 ≤ (((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error) := by
        positivity
      exact div_nonneg (by positivity) hden
    outsideSupport := by
      intro uv huv
      exact False.elim (huv (Finset.mem_univ uv)) }

theorem rerandomizeCoord_mass_eq_one (params : Parameters) :
    ∑ uv ∈ (rerandomizeCoord params).support, (rerandomizeCoord params).weight uv = 1 := by
  classical
  have hvertex_pos : 0 < hypercubeVertexCount params := by
    simp [hypercubeVertexCount, pow_pos params.hq]
  have hden_ne :
      ((((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos hvertex_pos params.hm) params.hq))
  have hcount :
      (∑ uv : Point params × Point params,
        ∑ p : Fin params.m × Fq params,
          if Function.update uv.1 p.1 p.2 = uv.2 then (1 : ℕ) else 0) =
        hypercubeVertexCount params * params.m * params.q := by
    calc
      (∑ uv : Point params × Point params,
          ∑ p : Fin params.m × Fq params,
            if Function.update uv.1 p.1 p.2 = uv.2 then (1 : ℕ) else 0)
        = ∑ p : Fin params.m × Fq params,
            ∑ uv : Point params × Point params,
              if Function.update uv.1 p.1 p.2 = uv.2 then (1 : ℕ) else 0 := by
                rw [Finset.sum_comm]
      _ = ∑ p : Fin params.m × Fq params, hypercubeVertexCount params := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            rw [Fintype.sum_prod_type]
            simp [hypercubeVertexCount, Fintype.card_fin]
      _ = hypercubeVertexCount params * params.m * params.q := by
            simp [hypercubeVertexCount, Fintype.card_fin]
            ring_nf
  have hcount_cast :
      (∑ uv : Point params × Point params,
        (((∑ p : Fin params.m × Fq params,
            if Function.update uv.1 p.1 p.2 = uv.2 then (1 : ℕ) else 0) : ℕ) : Error)) =
        ((((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error)) := by
    simpa using congrArg (fun n : ℕ => (n : Error)) hcount
  simp only [rerandomizeCoord, rerandomizeCoordWeight]
  simp_rw [div_eq_mul_inv]
  calc
    ∑ uv : Point params × Point params,
        (((∑ p : Fin params.m × Fq params,
            if Function.update uv.1 p.1 p.2 = uv.2 then (1 : ℕ) else 0) : ℕ) : Error) *
          ((((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error)⁻¹)
      = (∑ uv : Point params × Point params,
          (((∑ p : Fin params.m × Fq params,
              if Function.update uv.1 p.1 p.2 = uv.2 then (1 : ℕ) else 0) : ℕ) : Error)) *
            ((((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) : Error)⁻¹) := by
              simpa using
                (Finset.sum_mul
                  (s := (Finset.univ : Finset (Point params × Point params)))
                  (f := fun uv =>
                    (((∑ p : Fin params.m × Fq params,
                        if Function.update uv.1 p.1 p.2 = uv.2 then (1 : ℕ) else 0) : ℕ) :
                      Error))
                  (a := ((((hypercubeVertexCount params : ℕ) * params.m * params.q : ℕ) :
                    Error)⁻¹))).symm
    _ = 1 := by
          rw [hcount_cast]
          exact mul_inv_cancel₀ hden_ne

/-- Independent sampling of two uniformly random points. -/
noncomputable def independentPointPairWeight (params : Parameters)
    (_uv : Point params × Point params) : Error :=
  ((hypercubeVertexCount params : Error)⁻¹) * ((hypercubeVertexCount params : Error)⁻¹)

noncomputable def independentPointPair (params : Parameters) :
    Distribution (Point params × Point params) :=
  { support := Finset.univ
    weight := independentPointPairWeight params
    nonnegative := by
      intro uv
      simp only [independentPointPairWeight]
      apply mul_nonneg <;> exact inv_nonneg.mpr (Nat.cast_nonneg _)
    outsideSupport := by
      intro uv huv
      exact False.elim (huv (Finset.mem_univ uv)) }

/-- An honest finite matrix register for the hypercube vertices. -/
def pointHilbertSpace (params : Parameters) : FiniteHilbertSpace where
  carrier := Point params
  instFintype := inferInstance
  instDecidableEq := inferInstance
  instNonempty := inferInstance

/-- The paper's normalized adjacency weight for an ordered pair of vertices.
This update-sum is equivalent to the older case-split via
`coordinateDisagreementCount`: when `u ≠ v`, each differing coordinate
contributes the unique update sending `u i` to `v i`, while when `u = v`
the `q` self-loop updates contribute once for each coordinate. -/
noncomputable def hypercubeAdjacencyWeight (params : Parameters)
    (u v : Point params) : ℂ :=
  (((params.m : ℂ) * (params.q : ℂ) * (hypercubeVertexCount params : ℂ))⁻¹) *
    ∑ p : Fin params.m × Fq params,
      if Function.update u p.1 p.2 = v then (1 : ℂ) else 0

/-- The actual adjacency matrix of the edge-graph on `F_q^m`. -/
noncomputable def matrixAdjacencyOperator (params : Parameters) :
    MatrixOperator (pointHilbertSpace params) :=
  fun u v => hypercubeAdjacencyWeight params u v

/-- The actual Laplacian matrix `(1 / M) I - K` on the vertex register. -/
noncomputable def matrixLaplacianOperator (params : Parameters) :
    MatrixOperator (pointHilbertSpace params) :=
  ((hypercubeVertexCount params : ℂ)⁻¹) • (1 : MatrixOperator (pointHilbertSpace params)) -
    matrixAdjacencyOperator params

/-- The normalized adjacency matrix `K` of the hypercube graph on `F_q^m`,
as a matrix indexed by `Point params` directly. -/
noncomputable def adjacency (params : Parameters) : MIPStarRE.Quantum.Op (Point params) :=
  matrixAdjacencyOperator params

/-- The Laplacian `L = (1/M) I - K` on the hypercube vertex space,
as a matrix indexed by `Point params` directly. -/
noncomputable def laplacian (params : Parameters) : MIPStarRE.Quantum.Op (Point params) :=
  matrixLaplacianOperator params

/-- The edge-difference form of the Laplacian from `prop:laplacian-rewrite`:
`L = (1/2) · 𝔼_{(u,v)∼C} (|u⟩-|v⟩)(⟨u|-⟨v|)`.

Defined entrywise via the `rerandomizeCoordWeight` distribution on ordered
vertex pairs.  The equality with `laplacian` is proved in
`MIPStarRE.LDT.ExpansionHypercubeGraph.laplacian_eq_edgeDifferenceForm`. -/
noncomputable def laplacianDifferenceForm (params : Parameters) :
    MIPStarRE.Quantum.Op (Point params) :=
  fun a b => (1/2 : ℂ) *
    ∑ uv : Point params × Point params,
      ((rerandomizeCoordWeight params uv.1 uv.2 : ℂ)) *
        (((if a = uv.1 then (1 : ℂ) else 0) - (if a = uv.2 then (1 : ℂ) else 0)) *
         ((if uv.1 = b then (1 : ℂ) else 0) - (if uv.2 = b then (1 : ℂ) else 0)))

/-- The squared difference operator `(A^u - A^v)ᴴ(A^u - A^v)`. -/
noncomputable def pointDifferenceSquaredOperator {params : Parameters}
    (A : Point params → MIPStarRE.Quantum.Op ι) (u v : Point params) : MIPStarRE.Quantum.Op ι :=
  (A u - A v)ᴴ * (A u - A v)

/-- The local variance from `def:local-and-variance`. -/
noncomputable def localVariance (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : Error :=
  (1 / (2 : Error)) *
    avgOver (rerandomizeCoord params)
      (fun uv => ev ψ (pointDifferenceSquaredOperator A uv.1 uv.2))

/-- The global variance from `def:local-and-variance`. -/
noncomputable def globalVariance (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : Error :=
  (1 / (2 : Error)) *
    avgOver (independentPointPair params)
      (fun uv => ev ψ (pointDifferenceSquaredOperator A uv.1 uv.2))

/-- Combined accessor for the local and global variances. -/
noncomputable def localAndVariance (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) (ψ : QuantumState ι) : Error × Error :=
  (localVariance params A ψ, globalVariance params A ψ)

/-- The column-space indices for `A_combine`. -/
abbrev combinedColumnIndex (params : Parameters) (ι : Type*) := Point params × ι

/-- The combined column operator used for the trace rewrites.
Its `u`-th block is `(A^u)ᴴ`, so that the resulting trace expands to
`τ(ρ · (A^u - A^v)ᴴ (A^u - A^v))` for arbitrary operator families. -/
noncomputable def combinedOperator (params : Parameters)
    (A : Point params → MIPStarRE.Quantum.Op ι) :
    Matrix (combinedColumnIndex params ι) ι ℂ :=
  fun ui j => star (A ui.1 j ui.2)

end MIPStarRE.LDT.ExpansionHypercubeGraph
