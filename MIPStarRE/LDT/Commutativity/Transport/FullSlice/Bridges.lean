import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Averages
import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Machinery
import MIPStarRE.LDT.Commutativity.Transport.Pullback
import MIPStarRE.LDT.Commutativity.Scaffold.Products
import MIPStarRE.LDT.Commutativity.EvaluatedSliceCommutation.Averages
import MIPStarRE.LDT.Preliminaries.PolynomialAgreement

/-!
# Full-slice scalar-to-tensor bridges and main result

`closenessOfIP` bridges transforming scalar quartic averages into
manifestly positive tensor-form partners, the tensor-marginalization
assembly, and the main identity `fullSliceCommutation_qSDDOp_avg_eq`
expressing the pulled-back `sddErrorOp` as
2(`fullSliceABAAvg` - `fullSliceABABAvg`).

## References

- arXiv:2009.12982, Section 11.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Expand the averaged full-slice `qSDDOp` into the four projector terms
`BAB + ABA - BABA - ABAB`. -/
private lemma fullSliceCommutation_qSDDOp_avg_expand_full
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q =>
          qSDDOp strategy.state
            (fullSliceProductLeft params strategy family q)
            (fullSliceProductRight params strategy family q)) =
      avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q =>
          ∑ gh : FullSliceOutcome params,
            (fullSliceBABTerm params strategy family q gh +
              fullSliceABATerm params strategy family q gh -
              fullSliceBABATerm params strategy family q gh -
              fullSliceABABTerm params strategy family q gh)) := by
  apply avgOver_congr
  intro q
  unfold qSDDOp qSDDCore
  refine Finset.sum_congr rfl ?_
  intro gh _
  rcases gh with ⟨g, h⟩
  let A : MIPStarRE.Quantum.Op ι := (fullSliceFirstFactor params family q).outcome g
  let B : MIPStarRE.Quantum.Op ι := (fullSliceSecondFactor params family q).outcome h
  let LA : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) A
  let LB : MIPStarRE.Quantum.Op (ι × ι) := leftTensor (ι₂ := ι) B
  have hA_proj : A * A = A := by
    simpa [A, fullSliceFirstFactor] using (family.meas q.1).proj g
  have hB_proj : B * B = B := by
    simpa [B, fullSliceSecondFactor] using (family.meas q.2).proj h
  have hLA_herm : LAᴴ = LA := by
    let hLA_nonneg :=
      Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) ((family.meas q.1).outcome_pos g))
    exact hLA_nonneg.isHermitian.eq
  have hLB_herm : LBᴴ = LB := by
    let hLB_nonneg :=
      Matrix.nonneg_iff_posSemidef.mp
        (leftTensor_nonneg (ι₂ := ι) ((family.meas q.2).outcome_pos h))
    exact hLB_nonneg.isHermitian.eq
  have hLA_proj : LA * LA = LA := by
    simpa [LA, leftTensor_mul_leftTensor] using congrArg (leftTensor (ι₂ := ι)) hA_proj
  have hLB_proj : LB * LB = LB := by
    simpa [LB, leftTensor_mul_leftTensor] using congrArg (leftTensor (ι₂ := ι)) hB_proj
  have hmain :
      (((LA * LB - LB * LA)ᴴ) * (LA * LB - LB * LA)) =
        LB * LA * LB + LA * LB * LA - LB * LA * LB * LA - LA * LB * LA * LB := by
    rw [show (LA * LB - LB * LA)ᴴ = LB * LA - LA * LB by
      simp [Matrix.conjTranspose_mul, hLA_herm, hLB_herm]]
    calc
      (LB * LA - LA * LB) * (LA * LB - LB * LA)
          = LB * LA * LA * LB - LB * LA * LB * LA - LA * LB * LA * LB +
              LA * LB * LB * LA := by
              noncomm_ring
      _ = LB * LA * LB - LB * LA * LB * LA - LA * LB * LA * LB + LA * LB * LA := by
            simp [mul_assoc, hLA_proj, hLB_proj]
      _ = LB * LA * LB + LA * LB * LA - LB * LA * LB * LA - LA * LB * LA * LB := by
            abel
  calc
    ev strategy.state
        (((fullSliceProductLeft params strategy family q).outcome (g, h) -
            (fullSliceProductRight params strategy family q).outcome (g, h))ᴴ *
          ((fullSliceProductLeft params strategy family q).outcome (g, h) -
            (fullSliceProductRight params strategy family q).outcome (g, h)))
      = ev strategy.state (((LA * LB - LB * LA)ᴴ) * (LA * LB - LB * LA)) := by
          simp [A, B, LA, LB, fullSliceProductLeft, fullSliceProductRight,
            fullSliceFirstFactor, fullSliceSecondFactor, leftOrderedProductOpFamily,
            OpFamily.leftPlacedOpFamily, orderedProductOpFamily, reversedProductOpFamily,
            leftTensor_mul_leftTensor]
    _ = ev strategy.state
          (LB * LA * LB + LA * LB * LA - LB * LA * LB * LA - LA * LB * LA * LB) := by
            rw [hmain]
    _ = ev strategy.state (LB * LA * LB) + ev strategy.state (LA * LB * LA) -
          ev strategy.state (LB * LA * LB * LA) -
            ev strategy.state (LA * LB * LA * LB) := by
          rw [ev_sub, ev_sub, ev_add]
    _ = ev strategy.state (leftTensor (ι₂ := ι) (B * A * B)) +
          ev strategy.state (leftTensor (ι₂ := ι) (A * B * A)) -
          ev strategy.state (leftTensor (ι₂ := ι) (B * A * B * A)) -
            ev strategy.state (leftTensor (ι₂ := ι) (A * B * A * B)) := by
          simp [LA, LB, leftTensor_mul_leftTensor, mul_assoc]
    _ = fullSliceBABTerm params strategy family q (g, h) +
          fullSliceABATerm params strategy family q (g, h) -
          fullSliceBABATerm params strategy family q (g, h) -
            fullSliceABABTerm params strategy family q (g, h) := by
          simp [fullSliceBABTerm, fullSliceABATerm,
            fullSliceBABATerm, fullSliceABABTerm, A, B]

/-- Swapping the full-slice question and outcome identifies the averaged
`BAB`/`ABA` terms and the averaged `BABA`/`ABAB` terms. -/
private lemma fullSliceCommutation_avg_swap_terms
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q => ∑ gh : FullSliceOutcome params,
          fullSliceBABTerm params strategy family q gh) =
      avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q => ∑ gh : FullSliceOutcome params,
          fullSliceABATerm params strategy family q gh) ∧
    avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q => ∑ gh : FullSliceOutcome params,
          fullSliceBABATerm params strategy family q gh) =
      avgOver (uniformDistribution (FullSliceQuestion params))
        (fun q => ∑ gh : FullSliceOutcome params,
          fullSliceABABTerm params strategy family q gh) := by
  let Q := FullSliceQuestion params
  let O := FullSliceOutcome params
  let e : (Q × O) ≃ (Q × O) :=
    { toFun := fun z => ((z.1.2, z.1.1), (z.2.2, z.2.1))
      invFun := fun z => ((z.1.2, z.1.1), (z.2.2, z.2.1))
      left_inv := by
        rintro ⟨⟨x, y⟩, ⟨g, h⟩⟩
        rfl
      right_inv := by
        rintro ⟨⟨x, y⟩, ⟨g, h⟩⟩
        rfl }
  have hpairBAB :
      avgOver (uniformDistribution (Q × O))
          (fun z => fullSliceBABTerm params strategy family z.1 z.2) =
        avgOver (uniformDistribution (Q × O))
          (fun z => fullSliceABATerm params strategy family z.1 z.2) := by
    calc
      avgOver (uniformDistribution (Q × O))
          (fun z => fullSliceBABTerm params strategy family z.1 z.2)
        = avgOver (uniformDistribution (Q × O))
            (fun z => fullSliceBABTerm params strategy family (e.symm z).1 (e.symm z).2) := by
              simpa using
                (avgOver_uniform_equiv e
                  (fun z : Q × O => fullSliceBABTerm params strategy family z.1 z.2))
      _ = avgOver (uniformDistribution (Q × O))
            (fun z => fullSliceABATerm params strategy family z.1 z.2) := by
              apply avgOver_congr
              rintro ⟨⟨x, y⟩, ⟨g, h⟩⟩
              simp [e, fullSliceBABTerm, fullSliceABATerm,
                fullSliceFirstFactor, fullSliceSecondFactor]
  have hpairBABA :
      avgOver (uniformDistribution (Q × O))
          (fun z => fullSliceBABATerm params strategy family z.1 z.2) =
        avgOver (uniformDistribution (Q × O))
          (fun z => fullSliceABABTerm params strategy family z.1 z.2) := by
    calc
      avgOver (uniformDistribution (Q × O))
          (fun z => fullSliceBABATerm params strategy family z.1 z.2)
        = avgOver (uniformDistribution (Q × O))
            (fun z => fullSliceBABATerm params strategy family (e.symm z).1 (e.symm z).2) := by
              simpa using
                (avgOver_uniform_equiv e
                  (fun z : Q × O => fullSliceBABATerm params strategy family z.1 z.2))
      _ = avgOver (uniformDistribution (Q × O))
            (fun z => fullSliceABABTerm params strategy family z.1 z.2) := by
              apply avgOver_congr
              rintro ⟨⟨x, y⟩, ⟨g, h⟩⟩
              simp [e, fullSliceBABATerm, fullSliceABABTerm,
                fullSliceFirstFactor, fullSliceSecondFactor]
  constructor
  · calc
      avgOver (uniformDistribution Q)
          (fun q => ∑ gh : O, fullSliceBABTerm params strategy family q gh)
        = (Fintype.card O : Error) * avgOver (uniformDistribution (Q × O))
            (fun z => fullSliceBABTerm params strategy family z.1 z.2) := by
              exact avgOver_sum_eq_card_mul_avgOver_prod
                (fun q gh => fullSliceBABTerm params strategy family q gh)
      _ = (Fintype.card O : Error) * avgOver (uniformDistribution (Q × O))
            (fun z => fullSliceABATerm params strategy family z.1 z.2) := by
              rw [hpairBAB]
      _ = avgOver (uniformDistribution Q)
            (fun q => ∑ gh : O, fullSliceABATerm params strategy family q gh) := by
              symm
              exact avgOver_sum_eq_card_mul_avgOver_prod
                (fun q gh => fullSliceABATerm params strategy family q gh)
  · calc
      avgOver (uniformDistribution Q)
          (fun q => ∑ gh : O, fullSliceBABATerm params strategy family q gh)
        = (Fintype.card O : Error) * avgOver (uniformDistribution (Q × O))
            (fun z => fullSliceBABATerm params strategy family z.1 z.2) := by
              exact avgOver_sum_eq_card_mul_avgOver_prod
                (fun q gh => fullSliceBABATerm params strategy family q gh)
      _ = (Fintype.card O : Error) * avgOver (uniformDistribution (Q × O))
            (fun z => fullSliceABABTerm params strategy family z.1 z.2) := by
              rw [hpairBABA]
      _ = avgOver (uniformDistribution Q)
            (fun q => ∑ gh : O, fullSliceABABTerm params strategy family q gh) := by
              symm
              exact avgOver_sum_eq_card_mul_avgOver_prod
                (fun q gh => fullSliceABABTerm params strategy family q gh)

/-- Scalar-to-tensor bridge for paper `eq:gcom4`
(`commutativity-G.tex` lines 332-337).

One `closenessOfIP` application moves the trailing `G^x_g` in the scalar quartic
`G^y_h G^x_g G^y_h G^x_g ⊗ I` to the right register, producing the manifestly
PSD tensor form `G^y_h G^x_g G^y_h ⊗ G^x_g`.  The scalar side is stated as
`fullSliceABABAvg`; the proof first uses the `(x,g) ↔ (y,h)` swap symmetry above
to identify the averaged `BABA` scalar with the averaged `ABAB` scalar. -/
private lemma fullSliceABAB_scalar_to_BABAtensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |fullSliceABABAvg params strategy family -
        fullSliceBABAtensorAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 : Distribution (FullSliceQuestion params) :=
    uniformDistribution (FullSliceQuestion params)
  let A : FullSliceQuestion params → Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun xy g => leftTensor (ι₂ := ι) ((family.meas xy.1).toSubMeas.outcome g)
  let B : FullSliceQuestion params → Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun xy g => rightTensor (ι₁ := ι) ((family.meas xy.1).toSubMeas.outcome g)
  let C : FullSliceQuestion params → Polynomial params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun xy g h =>
      leftTensor (ι₂ := ι)
        ((family.meas xy.2).toSubMeas.outcome h *
          (family.meas xy.1).toSubMeas.outcome g *
          (family.meas xy.2).toSubMeas.outcome h)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using uniformDistribution_weight_sum_le_one (FullSliceQuestion params)
  have hAB : avgOver 𝒟 (fun xy => qSDDCore strategy.state (A xy) (B xy)) ≤ zeta := by
    simpa [𝒟, A, B] using fullSlice_selfConsistency_fst_bound params strategy family zeta hself
  have hC :
      ∀ xy,
        ∑ g : Polynomial params,
            (∑ h : Polynomial params, C xy g h) * (∑ h : Polynomial params, C xy g h)ᴴ ≤
          1 := by
    intro xy
    simpa [C, fullSliceFirstFactor, fullSliceSecondProj] using
      (leftTensor_normalizationCondition_sandwich_bound
        (P := fullSliceFirstFactor params family xy)
        (Q := fullSliceSecondProj params family xy))
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 A B C zeta hAB hC
  have hBABA_to_ABAB := (fullSliceCommutation_avg_swap_terms params strategy family).2
  have hScalar :
      avgOver 𝒟
          (fun xy => ∑ g : Polynomial params, ∑ h : Polynomial params,
            ev strategy.state (C xy g h * A xy g)) =
        fullSliceABABAvg params strategy family := by
    calc
      avgOver 𝒟
          (fun xy => ∑ g : Polynomial params, ∑ h : Polynomial params,
            ev strategy.state (C xy g h * A xy g))
        = avgOver 𝒟
            (fun xy => ∑ gh : FullSliceOutcome params,
              fullSliceBABATerm params strategy family xy gh) := by
            apply avgOver_congr
            intro xy
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro g _
            refine Finset.sum_congr rfl ?_
            intro h _
            simp [C, A, fullSliceBABATerm, fullSliceFirstFactor, fullSliceSecondFactor,
              leftTensor_mul_leftTensor, mul_assoc]
      _ = avgOver 𝒟
            (fun xy => ∑ gh : FullSliceOutcome params,
              fullSliceABABTerm params strategy family xy gh) := by
            simpa [𝒟] using hBABA_to_ABAB
      _ = fullSliceABABAvg params strategy family := by
            rfl
  have hTensor :
      avgOver 𝒟
          (fun xy => ∑ g : Polynomial params, ∑ h : Polynomial params,
            ev strategy.state (C xy g h * B xy g)) =
        fullSliceBABAtensorAvg params strategy family := by
    unfold fullSliceBABAtensorAvg
    apply avgOver_congr
    intro xy
    simpa [C, B] using
      (Fintype.sum_prod_type' (f := fun g : Polynomial params => fun h : Polynomial params =>
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((family.meas xy.2).toSubMeas.outcome h *
                (family.meas xy.1).toSubMeas.outcome g *
                (family.meas xy.2).toSubMeas.outcome h) *
            rightTensor (ι₁ := ι)
              ((family.meas xy.1).toSubMeas.outcome g)))).symm
  calc
    |fullSliceABABAvg params strategy family - fullSliceBABAtensorAvg params strategy family|
      = |avgOver 𝒟
            (fun xy => ∑ g : Polynomial params, ∑ h : Polynomial params,
              ev strategy.state (C xy g h * A xy g)) -
          avgOver 𝒟
            (fun xy => ∑ g : Polynomial params, ∑ h : Polynomial params,
              ev strategy.state (C xy g h * B xy g))| := by
            rw [hScalar, hTensor]
    _ ≤ Real.sqrt zeta := hclose

/-- Y-side scalar-to-tensor bridge: move the trailing `G^y_h` in
`G^x_g G^y_h G^x_g G^y_h ⊗ I` to the right register, giving
`G^x_g G^y_h G^x_g ⊗ G^y_h`.  This is the full-slice analogue of the second
approximation in `commutativity-G.tex` lines 356-360. -/
private lemma fullSliceABAB_scalar_to_ABABtensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |fullSliceABABAvg params strategy family -
        fullSliceABABtensorAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 : Distribution (FullSliceQuestion params) :=
    uniformDistribution (FullSliceQuestion params)
  let A : FullSliceQuestion params → Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun xy h => leftTensor (ι₂ := ι) ((family.meas xy.2).toSubMeas.outcome h)
  let B : FullSliceQuestion params → Polynomial params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun xy h => rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)
  let C : FullSliceQuestion params → Polynomial params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun xy h g =>
      leftTensor (ι₂ := ι)
        ((family.meas xy.1).toSubMeas.outcome g *
          (family.meas xy.2).toSubMeas.outcome h *
          (family.meas xy.1).toSubMeas.outcome g)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using uniformDistribution_weight_sum_le_one (FullSliceQuestion params)
  have hAB : avgOver 𝒟 (fun xy => qSDDCore strategy.state (A xy) (B xy)) ≤ zeta := by
    simpa [𝒟, A, B] using fullSlice_selfConsistency_snd_bound params strategy family zeta hself
  have hC :
      ∀ xy,
        ∑ h : Polynomial params,
            (∑ g : Polynomial params, C xy h g) * (∑ g : Polynomial params, C xy h g)ᴴ ≤
          1 := by
    intro xy
    simpa [C, fullSliceSecondFactor, fullSliceFirstProj] using
      (leftTensor_normalizationCondition_sandwich_bound
        (P := fullSliceSecondFactor params family xy)
        (Q := fullSliceFirstProj params family xy))
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 A B C zeta hAB hC
  have hScalar :
      avgOver 𝒟
          (fun xy => ∑ h : Polynomial params, ∑ g : Polynomial params,
            ev strategy.state (C xy h g * A xy h)) =
        fullSliceABABAvg params strategy family := by
    unfold fullSliceABABAvg
    apply avgOver_congr
    intro xy
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro h _
    refine Finset.sum_congr rfl ?_
    intro g _
    simp [C, A, leftTensor_mul_leftTensor, mul_assoc]
  have hTensor :
      avgOver 𝒟
          (fun xy => ∑ h : Polynomial params, ∑ g : Polynomial params,
            ev strategy.state (C xy h g * B xy h)) =
        fullSliceABABtensorAvg params strategy family := by
    unfold fullSliceABABtensorAvg
    apply avgOver_congr
    intro xy
    calc
      ∑ h : Polynomial params, ∑ g : Polynomial params,
          ev strategy.state (C xy h g * B xy h)
        = ∑ g : Polynomial params, ∑ h : Polynomial params,
            ev strategy.state (C xy h g * B xy h) := by
            rw [Finset.sum_comm]
      _ = ∑ gh : FullSliceOutcome params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((family.meas xy.1).toSubMeas.outcome gh.1 *
                    (family.meas xy.2).toSubMeas.outcome gh.2 *
                    (family.meas xy.1).toSubMeas.outcome gh.1) *
                rightTensor (ι₁ := ι)
                  ((family.meas xy.2).toSubMeas.outcome gh.2)) := by
            simpa [C, B] using
              (Fintype.sum_prod_type' (f := fun g : Polynomial params =>
                fun h : Polynomial params =>
                  ev strategy.state
                    (leftTensor (ι₂ := ι)
                        ((family.meas xy.1).toSubMeas.outcome g *
                          (family.meas xy.2).toSubMeas.outcome h *
                          (family.meas xy.1).toSubMeas.outcome g) *
                      rightTensor (ι₁ := ι)
                        ((family.meas xy.2).toSubMeas.outcome h)))).symm
  calc
    |fullSliceABABAvg params strategy family - fullSliceABABtensorAvg params strategy family|
      = |avgOver 𝒟
            (fun xy => ∑ h : Polynomial params, ∑ g : Polynomial params,
              ev strategy.state (C xy h g * A xy h)) -
          avgOver 𝒟
            (fun xy => ∑ h : Polynomial params, ∑ g : Polynomial params,
              ev strategy.state (C xy h g * B xy h))| := by
            rw [hScalar, hTensor]
    _ ≤ Real.sqrt zeta := hclose

/-- X-evaluated/full-y scalar-to-tensor bridge for paper line 360.

After the x-side Schwartz--Zippel step, the first family has already been
postprocessed at `u`, while the y-family is still full-polynomial.  This lemma
proves the second `closenessOfIP` move in `commutativity-G.tex` lines 356--360:
move the trailing `G^y_h` in
`G^x_[g(u)=a] G^y_h G^x_[g(u)=a] G^y_h ⊗ I` to the right register, yielding
`G^x_[g(u)=a] G^y_h G^x_[g(u)=a] ⊗ G^y_h`.

The preceding line-359 bridge from the `BAB ⊗ A` tensor endpoint to this scalar
endpoint remains separate because it follows a different `closenessOfIP` leg. -/
lemma xEvaluatedFullSliceABABAvg_to_xEvaluatedFullSliceABABtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |xEvaluatedFullSliceABABAvg params strategy family -
        xEvaluatedFullSliceABABtensorAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 : Distribution (Point params × FullSliceQuestion params) :=
    uniformDistribution (Point params × FullSliceQuestion params)
  let A : Point params × FullSliceQuestion params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux h => leftTensor (ι₂ := ι) ((family.meas ux.2.2).toSubMeas.outcome h)
  let B : Point params × FullSliceQuestion params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux h => rightTensor (ι₁ := ι) ((family.meas ux.2.2).toSubMeas.outcome h)
  let C : Point params × FullSliceQuestion params → Polynomial params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux h a =>
      leftTensor (ι₂ := ι)
        ((evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a *
          (family.meas ux.2.2).toSubMeas.outcome h *
          (evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)).outcome a)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using uniformDistribution_weight_sum_le_one
      (Point params × FullSliceQuestion params)
  have hAB : avgOver 𝒟 (fun ux => qSDDCore strategy.state (A ux) (B ux)) ≤ zeta := by
    have hsnd :=
      avgOver_uniform_snd (α := Point params) (β := FullSliceQuestion params)
        (f := fun xy =>
          qSDDCore strategy.state
            (fun h : Polynomial params =>
              leftTensor (ι₂ := ι) ((family.meas xy.2).toSubMeas.outcome h))
            (fun h : Polynomial params =>
              rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)))
    calc
      avgOver 𝒟 (fun ux => qSDDCore strategy.state (A ux) (B ux))
        = avgOver (uniformDistribution (FullSliceQuestion params))
            (fun xy =>
              qSDDCore strategy.state
                (fun h : Polynomial params =>
                  leftTensor (ι₂ := ι) ((family.meas xy.2).toSubMeas.outcome h))
                (fun h : Polynomial params =>
                  rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h))) := by
            simpa [𝒟, A, B] using hsnd
      _ ≤ zeta := fullSlice_selfConsistency_snd_bound params strategy family zeta hself
  have hC :
      ∀ ux,
        ∑ h : Polynomial params,
            (∑ a : Fq params, C ux h a) * (∑ a : Fq params, C ux h a)ᴴ ≤ 1 := by
    intro ux
    let P : SubMeas (Polynomial params) ι := fullSliceSecondFactor params family ux.2
    let Q : ProjSubMeas (Fq params) ι :=
      evaluateAtProjSubMeas params ux.1 (fullSliceFirstProj params family ux.2)
    simpa [C, P, Q, evaluateAtProjSubMeas, evaluateAt, fullSliceFirstProj,
      fullSliceSecondFactor] using
      (leftTensor_normalizationCondition_sandwich_bound (P := P) (Q := Q))
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 A B C zeta hAB hC
  have hScalar :
      avgOver 𝒟
          (fun ux => ∑ h : Polynomial params, ∑ a : Fq params,
            ev strategy.state (C ux h a * A ux h)) =
        xEvaluatedFullSliceABABAvg params strategy family := by
    unfold xEvaluatedFullSliceABABAvg
    apply avgOver_congr
    rintro ⟨u, xy⟩
    calc
      ∑ h : Polynomial params, ∑ a : Fq params,
          ev strategy.state (C (u, xy) h a * A (u, xy) h)
        = ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                  (family.meas xy.2).toSubMeas.outcome h *
                  (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                  (family.meas xy.2).toSubMeas.outcome h)) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro h _
            simp [C, A, leftTensor_mul_leftTensor, mul_assoc]
      _ = ∑ ah : Fq params × Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome ah.1 *
                  (family.meas xy.2).toSubMeas.outcome ah.2 *
                  (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome ah.1 *
                  (family.meas xy.2).toSubMeas.outcome ah.2)) := by
            exact (Fintype.sum_prod_type' (f := fun a : Fq params =>
              fun h : Polynomial params =>
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                    ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                      (family.meas xy.2).toSubMeas.outcome h *
                      (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                      (family.meas xy.2).toSubMeas.outcome h)))).symm
  have hTensor :
      avgOver 𝒟
          (fun ux => ∑ h : Polynomial params, ∑ a : Fq params,
            ev strategy.state (C ux h a * B ux h)) =
        xEvaluatedFullSliceABABtensorAvg params strategy family := by
    unfold xEvaluatedFullSliceABABtensorAvg
    apply avgOver_congr
    rintro ⟨u, xy⟩
    calc
      ∑ h : Polynomial params, ∑ a : Fq params,
          ev strategy.state (C (u, xy) h a * B (u, xy) h)
        = ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                    (family.meas xy.2).toSubMeas.outcome h *
                    (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a) *
                rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)) := by
            rw [Finset.sum_comm]
      _ = ∑ ah : Fq params × Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome ah.1 *
                    (family.meas xy.2).toSubMeas.outcome ah.2 *
                    (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome ah.1) *
                rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome ah.2)) := by
            exact (Fintype.sum_prod_type' (f := fun a : Fq params =>
              fun h : Polynomial params =>
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      ((evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a *
                        (family.meas xy.2).toSubMeas.outcome h *
                        (evaluateAt params u ((family.meas xy.1).toSubMeas)).outcome a) *
                    rightTensor (ι₁ := ι) ((family.meas xy.2).toSubMeas.outcome h)))).symm
  calc
    |xEvaluatedFullSliceABABAvg params strategy family -
        xEvaluatedFullSliceABABtensorAvg params strategy family|
      = |avgOver 𝒟
            (fun ux => ∑ h : Polynomial params, ∑ a : Fq params,
              ev strategy.state (C ux h a * A ux h)) -
          avgOver 𝒟
            (fun ux => ∑ h : Polynomial params, ∑ a : Fq params,
              ev strategy.state (C ux h a * B ux h))| := by
            rw [hScalar, hTensor]
    _ ≤ Real.sqrt zeta := hclose

/-- Evaluated-slice scalar-to-tensor bridge for the first approximation after
`eq:evaluate-gcom-at-points` (`commutativity-G.tex` lines 356-365).

This is the evaluated analogue of `fullSliceABAB_scalar_to_BABAtensor`.  The
point-level self-consistency for the already evaluated/postprocessed family is
now derived from slice strong self-consistency by
`evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent`. -/
private lemma evaluatedSliceABAB_scalar_to_BABAtensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |evaluatedSliceABABAvg params strategy family -
        evaluatedSliceBABAtensorAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 : Distribution (EvaluatedSliceQuestion params) :=
    uniformDistribution (EvaluatedSliceQuestion params)
  let A : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a => leftTensor (ι₂ := ι) ((evaluatedSliceFirstFactor params family q).outcome a)
  let B : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a => rightTensor (ι₁ := ι) ((evaluatedSliceFirstFactor params family q).outcome a)
  let C : EvaluatedSliceQuestion params → Fq params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q a b =>
      leftTensor (ι₂ := ι)
        ((evaluatedSliceSecondFactor params family q).outcome b *
          (evaluatedSliceFirstFactor params family q).outcome a *
          (evaluatedSliceSecondFactor params family q).outcome b)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)
  have hAB : avgOver 𝒟 (fun q => qSDDCore strategy.state (A q) (B q)) ≤ zeta := by
    simpa [𝒟, A, B] using
      evaluatedSlice_selfConsistency_fst_bound params strategy family zeta hself
  have hC :
      ∀ q,
        ∑ a : Fq params,
            (∑ b : Fq params, C q a b) * (∑ b : Fq params, C q a b)ᴴ ≤ 1 := by
    intro q
    simpa [C, evaluatedSliceFirstFactor, evaluatedSliceSecondProj] using
      (leftTensor_normalizationCondition_sandwich_bound
        (P := evaluatedSliceFirstFactor params family q)
        (Q := evaluatedSliceSecondProj params family q))
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 A B C zeta hAB hC
  have hBABA_to_ABAB := (evaluatedSliceCommutation_avg_swap_terms params strategy family).2
  have hScalar :
      avgOver 𝒟
          (fun q => ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state (C q a b * A q a)) =
        evaluatedSliceABABAvg params strategy family := by
    calc
      avgOver 𝒟
          (fun q => ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state (C q a b * A q a))
        = avgOver 𝒟
            (fun q => ∑ ab : EvaluatedSliceOutcome params,
              evaluatedSliceBABATerm params strategy family q ab) := by
            apply avgOver_congr
            intro q
            rw [Fintype.sum_prod_type]
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro b _
            simp [C, A, evaluatedSliceBABATerm, evaluatedSliceFirstFactor,
              evaluatedSliceSecondFactor, leftTensor_mul_leftTensor, mul_assoc]
      _ = avgOver 𝒟
            (fun q => ∑ ab : EvaluatedSliceOutcome params,
              evaluatedSliceABABTerm params strategy family q ab) := by
            simpa [𝒟] using hBABA_to_ABAB
      _ = evaluatedSliceABABAvg params strategy family := by
            rfl
  have hTensor :
      avgOver 𝒟
          (fun q => ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state (C q a b * B q a)) =
        evaluatedSliceBABAtensorAvg params strategy family := by
    unfold evaluatedSliceBABAtensorAvg
    apply avgOver_congr
    intro q
    simpa [C, B, evaluatedSliceFirstFactor, evaluatedSliceSecondFactor] using
      (Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
        ev strategy.state
          (leftTensor (ι₂ := ι)
              ((evaluatedSliceSecondFactor params family q).outcome b *
                (evaluatedSliceFirstFactor params family q).outcome a *
                (evaluatedSliceSecondFactor params family q).outcome b) *
            rightTensor (ι₁ := ι)
              ((evaluatedSliceFirstFactor params family q).outcome a)))).symm
  calc
    |evaluatedSliceABABAvg params strategy family -
        evaluatedSliceBABAtensorAvg params strategy family|
      = |avgOver 𝒟
            (fun q => ∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state (C q a b * A q a)) -
          avgOver 𝒟
            (fun q => ∑ a : Fq params, ∑ b : Fq params,
              ev strategy.state (C q a b * B q a))| := by
            rw [hScalar, hTensor]
    _ ≤ Real.sqrt zeta := hclose

/-- First mixed bridge in paper lines 356--360: move the already x-evaluated
outcome from the right tensor register back to the left register. -/
private lemma xEvaluatedSliceBABAtensor_to_BABAScalar
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |xEvaluatedSliceBABAtensorAvg params strategy family -
        xEvaluatedSliceBABAScalarAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 : Distribution (Point params × FullSliceQuestion params) :=
    uniformDistribution (Point params × FullSliceQuestion params)
  let X : Point params × FullSliceQuestion params → SubMeas (Fq params) ι :=
    fun ux => evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
  let Y : Point params × FullSliceQuestion params → SubMeas (Polynomial params) ι :=
    fun ux => (family.meas ux.2.2).toSubMeas
  let A : Point params × FullSliceQuestion params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux a => leftTensor (ι₂ := ι) ((X ux).outcome a)
  let B : Point params × FullSliceQuestion params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux a => rightTensor (ι₁ := ι) ((X ux).outcome a)
  let C : Point params × FullSliceQuestion params → Fq params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux a h => leftTensor (ι₂ := ι)
      ((Y ux).outcome h * (X ux).outcome a * (Y ux).outcome h)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using uniformDistribution_weight_sum_le_one
      (Point params × FullSliceQuestion params)
  have hAB : avgOver 𝒟 (fun ux => qSDDCore strategy.state (A ux) (B ux)) ≤ zeta := by
    simpa [𝒟, A, B, X] using
      xEvaluated_selfConsistency_fst_bound params strategy family zeta hself
  have hC :
      ∀ ux,
        ∑ a : Fq params,
            (∑ h : Polynomial params, C ux a h) *
              (∑ h : Polynomial params, C ux a h)ᴴ ≤ 1 := by
    intro ux
    simpa [C, X, Y] using
      leftTensor_normalizationCondition_sandwich_bound
        (ι := ι) (P := X ux) (Q := family.meas ux.2.2)
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 A B C zeta hAB hC
  have hScalar :
      avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
        ev strategy.state (C ux a h * A ux a)) =
        xEvaluatedSliceBABAScalarAvg params strategy family := by
    unfold xEvaluatedSliceBABAScalarAvg
    apply avgOver_congr
    intro ux
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro h _
    simp [A, C, X, Y, leftTensor_mul_leftTensor, mul_assoc]
  have hTensor :
      avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
        ev strategy.state (C ux a h * B ux a)) =
        xEvaluatedSliceBABAtensorAvg params strategy family := by
    rw [xEvaluatedSliceBABAtensorAvg_eq_xFullData params strategy family]
  calc
    |xEvaluatedSliceBABAtensorAvg params strategy family -
        xEvaluatedSliceBABAScalarAvg params strategy family|
      = |avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state (C ux a h * B ux a)) -
          avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state (C ux a h * A ux a))| := by
          rw [hTensor, hScalar]
    _ = |avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state (C ux a h * A ux a)) -
          avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state (C ux a h * B ux a))| := by
          rw [abs_sub_comm]
    _ ≤ Real.sqrt zeta := hclose

/-- First mixed bridge in paper line 359: move the already x-evaluated outcome
from the right tensor register back to the left register, yielding the public
`xEvaluatedFullSliceABABAvg` scalar endpoint. -/
lemma xEvaluatedSliceBABAtensor_to_xEvaluatedFullSliceABABAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |xEvaluatedSliceBABAtensorAvg params strategy family -
        xEvaluatedFullSliceABABAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 : Distribution (Point params × FullSliceQuestion params) :=
    uniformDistribution (Point params × FullSliceQuestion params)
  let X : Point params × FullSliceQuestion params → SubMeas (Fq params) ι :=
    fun ux => evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
  let Y : Point params × FullSliceQuestion params → SubMeas (Polynomial params) ι :=
    fun ux => (family.meas ux.2.2).toSubMeas
  let A : Point params × FullSliceQuestion params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux a => leftTensor (ι₂ := ι) ((X ux).outcome a)
  let B : Point params × FullSliceQuestion params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux a => rightTensor (ι₁ := ι) ((X ux).outcome a)
  let C : Point params × FullSliceQuestion params → Fq params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux a h => leftTensor (ι₂ := ι)
      ((Y ux).outcome h * (X ux).outcome a * (Y ux).outcome h)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using uniformDistribution_weight_sum_le_one
      (Point params × FullSliceQuestion params)
  have hAB :
      avgOver 𝒟
        (fun ux => qSDDCore strategy.state (fun a => (A ux a)ᴴ) (fun a => (B ux a)ᴴ)) ≤
        zeta := by
    calc
      avgOver 𝒟
          (fun ux => qSDDCore strategy.state (fun a => (A ux a)ᴴ) (fun a => (B ux a)ᴴ))
        = avgOver 𝒟 (fun ux => qSDDCore strategy.state (A ux) (B ux)) := by
            apply avgOver_congr
            intro ux
            unfold qSDDCore
            apply Finset.sum_congr rfl
            intro a _
            have hX : ((X ux).outcome a)ᴴ = (X ux).outcome a := (X ux).outcome_hermitian a
            simp [A, B, hX]
      _ ≤ zeta := by
            simpa [𝒟, A, B, X] using
              xEvaluated_selfConsistency_fst_bound params strategy family zeta hself
  have hC :
      ∀ ux,
        ∑ a : Fq params,
            (∑ h : Polynomial params, C ux a h)ᴴ *
              (∑ h : Polynomial params, C ux a h) ≤ 1 := by
    intro ux
    simpa [C, X, Y] using
      leftTensor_normalizationCondition_sandwich_adjoint_bound
        (ι := ι) (P := X ux) (Q := family.meas ux.2.2)
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIPAdjoint
      strategy.state hnorm 𝒟 h𝒟 A B C zeta hAB hC
  have hScalar :
      avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
        ev strategy.state (A ux a * C ux a h)) =
        xEvaluatedFullSliceABABAvg params strategy family := by
    unfold xEvaluatedFullSliceABABAvg
    apply avgOver_congr
    intro ux
    calc
      ∑ a : Fq params, ∑ h : Polynomial params,
          ev strategy.state (A ux a * C ux a h)
        = ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                ((X ux).outcome a * (Y ux).outcome h * (X ux).outcome a *
                  (Y ux).outcome h)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro h _
            simp [A, C, X, Y, leftTensor_mul_leftTensor, mul_assoc]
      _ = ∑ ah : Fq params × Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                ((X ux).outcome ah.1 * (Y ux).outcome ah.2 * (X ux).outcome ah.1 *
                  (Y ux).outcome ah.2)) := by
            exact (Fintype.sum_prod_type' (f := fun a : Fq params =>
              fun h : Polynomial params =>
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                    ((X ux).outcome a * (Y ux).outcome h * (X ux).outcome a *
                      (Y ux).outcome h)))).symm
  have hTensor :
      avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
        ev strategy.state (B ux a * C ux a h)) =
        xEvaluatedSliceBABAtensorAvg params strategy family := by
    rw [xEvaluatedSliceBABAtensorAvg_eq_xFullData params strategy family]
    apply avgOver_congr
    intro ux
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro h _
    rw [rightTensor_mul_leftTensor_eq_opTensor,
      ← leftTensor_mul_rightTensor_eq_opTensor]
  calc
    |xEvaluatedSliceBABAtensorAvg params strategy family -
        xEvaluatedFullSliceABABAvg params strategy family|
      = |avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state (B ux a * C ux a h)) -
          avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state (A ux a * C ux a h))| := by
          rw [hTensor, hScalar]
    _ = |avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state (A ux a * C ux a h)) -
          avgOver 𝒟 (fun ux => ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state (B ux a * C ux a h))| := by
          rw [abs_sub_comm]
    _ ≤ Real.sqrt zeta := hclose

/-- Second mixed bridge in paper lines 356--360: move the full-y outcome to the
right tensor register. -/
private lemma xEvaluatedSliceBABAScalar_to_xEvaluatedFullSliceABABtensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |xEvaluatedSliceBABAScalarAvg params strategy family -
        xEvaluatedFullSliceABABtensorAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 : Distribution (Point params × FullSliceQuestion params) :=
    uniformDistribution (Point params × FullSliceQuestion params)
  let X : Point params × FullSliceQuestion params → SubMeas (Fq params) ι :=
    fun ux => evaluateAt params ux.1 ((family.meas ux.2.1).toSubMeas)
  let Y : Point params × FullSliceQuestion params → SubMeas (Polynomial params) ι :=
    fun ux => (family.meas ux.2.2).toSubMeas
  let A : Point params × FullSliceQuestion params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux h => leftTensor (ι₂ := ι) ((Y ux).outcome h)
  let B : Point params × FullSliceQuestion params → Polynomial params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux h => rightTensor (ι₁ := ι) ((Y ux).outcome h)
  let C : Point params × FullSliceQuestion params → Polynomial params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun ux h a => leftTensor (ι₂ := ι)
      ((X ux).outcome a * (Y ux).outcome h * (X ux).outcome a)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using uniformDistribution_weight_sum_le_one
      (Point params × FullSliceQuestion params)
  have hAB :
      avgOver 𝒟
        (fun ux => qSDDCore strategy.state (fun h => (A ux h)ᴴ) (fun h => (B ux h)ᴴ)) ≤
        zeta := by
    simpa [𝒟, A, B, Y] using
      xEvaluated_selfConsistency_snd_adjoint_bound params strategy family zeta hself
  have hC :
      ∀ ux,
        ∑ h : Polynomial params,
            (∑ a : Fq params, C ux h a)ᴴ *
              (∑ a : Fq params, C ux h a) ≤ 1 := by
    intro ux
    simpa [C, X, Y, xEvaluatedFirstProj] using
      leftTensor_normalizationCondition_sandwich_adjoint_bound
        (ι := ι) (P := Y ux) (Q := xEvaluatedFirstProj params family ux)
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIPAdjoint
      strategy.state hnorm 𝒟 h𝒟 A B C zeta hAB hC
  have hScalar :
      avgOver 𝒟 (fun ux => ∑ h : Polynomial params, ∑ a : Fq params,
        ev strategy.state (A ux h * C ux h a)) =
        xEvaluatedSliceBABAScalarAvg params strategy family := by
    unfold xEvaluatedSliceBABAScalarAvg
    apply avgOver_congr
    intro ux
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro h _
    simp [A, C, X, Y, leftTensor_mul_leftTensor, mul_assoc]
  have hTensor :
      avgOver 𝒟 (fun ux => ∑ h : Polynomial params, ∑ a : Fq params,
        ev strategy.state (B ux h * C ux h a)) =
        xEvaluatedFullSliceABABtensorAvg params strategy family := by
    unfold xEvaluatedFullSliceABABtensorAvg
    apply avgOver_congr
    intro ux
    calc
      ∑ h : Polynomial params, ∑ a : Fq params, ev strategy.state (B ux h * C ux h a)
        = ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state (B ux h * C ux h a) := by
            rw [Finset.sum_comm]
      _ = ∑ a : Fq params, ∑ h : Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) ((X ux).outcome a * (Y ux).outcome h *
                  (X ux).outcome a) *
                rightTensor (ι₁ := ι) ((Y ux).outcome h)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            refine Finset.sum_congr rfl ?_
            intro h _
            rw [rightTensor_mul_leftTensor_eq_opTensor,
              ← leftTensor_mul_rightTensor_eq_opTensor]
      _ = ∑ ah : Fq params × Polynomial params,
            ev strategy.state
              (leftTensor (ι₂ := ι) ((X ux).outcome ah.1 * (Y ux).outcome ah.2 *
                  (X ux).outcome ah.1) *
                rightTensor (ι₁ := ι) ((Y ux).outcome ah.2)) := by
            exact (Fintype.sum_prod_type' (f := fun a : Fq params =>
              fun h : Polynomial params =>
                ev strategy.state
                  (leftTensor (ι₂ := ι) ((X ux).outcome a * (Y ux).outcome h *
                      (X ux).outcome a) *
                    rightTensor (ι₁ := ι) ((Y ux).outcome h)))).symm
  calc
    |xEvaluatedSliceBABAScalarAvg params strategy family -
        xEvaluatedFullSliceABABtensorAvg params strategy family|
      = |avgOver 𝒟 (fun ux => ∑ h : Polynomial params, ∑ a : Fq params,
            ev strategy.state (A ux h * C ux h a)) -
          avgOver 𝒟 (fun ux => ∑ h : Polynomial params, ∑ a : Fq params,
            ev strategy.state (B ux h * C ux h a))| := by
          rw [hScalar, hTensor]
    _ ≤ Real.sqrt zeta := hclose

/-- Mixed bridge from the x-evaluated `BAB ⊗ A` tensor endpoint to the
x-evaluated/y-full `ABA ⊗ B` tensor endpoint. -/
private lemma xEvaluatedSliceBABAtensor_to_xEvaluatedFullSliceABABtensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |xEvaluatedSliceBABAtensorAvg params strategy family -
        xEvaluatedFullSliceABABtensorAvg params strategy family| ≤
      2 * Real.sqrt zeta := by
  have h1 := xEvaluatedSliceBABAtensor_to_BABAScalar
    params strategy family zeta hnorm hself
  have h2 := xEvaluatedSliceBABAScalar_to_xEvaluatedFullSliceABABtensor
    params strategy family zeta hnorm hself
  have htri := abs_sub_le
    (xEvaluatedSliceBABAtensorAvg params strategy family)
    (xEvaluatedSliceBABAScalarAvg params strategy family)
    (xEvaluatedFullSliceABABtensorAvg params strategy family)
  linarith

/-- Full-slice prefix bound for the y-side scalar quartic.

This packages the paper's first three y-prefix steps: the scalar-to-tensor
`√ζ` bridge, the x-marginalization `md/q` step, and the mixed x-evaluated
bridge to the `xEvaluatedFullSliceABABtensorAvg` endpoint. -/
lemma fullSliceABAB_to_xEvaluatedFullSliceABABtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |fullSliceABABAvg params strategy family -
        xEvaluatedFullSliceABABtensorAvg params strategy family| ≤
      (↑params.m : Error) * ↑params.d / ↑params.q + 3 * Real.sqrt zeta := by
  have h1 := fullSliceABAB_scalar_to_BABAtensor params strategy family zeta hnorm hself
  have h2 := fullSliceBABA_tensor_marginalize_x params strategy family hnorm
  have h3 := xEvaluatedSliceBABAtensor_to_xEvaluatedFullSliceABABtensor
    params strategy family zeta hnorm hself
  have htri := abs_sub_le
    (fullSliceABABAvg params strategy family)
    (fullSliceBABAtensorAvg params strategy family)
    (xEvaluatedFullSliceABABtensorAvg params strategy family)
  have hmid := abs_sub_le
    (fullSliceBABAtensorAvg params strategy family)
    (xEvaluatedSliceBABAtensorAvg params strategy family)
    (xEvaluatedFullSliceABABtensorAvg params strategy family)
  linarith

/-- Evaluated-slice y-side scalar-to-tensor bridge: move the trailing
`G^y_[h(v)=b]` in the scalar quartic to the right register, producing the tensor
form in paper `commutativity-G.tex` line 360. -/
private lemma evaluatedSliceABAB_scalar_to_ABABtensor
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |evaluatedSliceABABAvg params strategy family -
        evaluatedSliceABABtensorAvg params strategy family| ≤ Real.sqrt zeta := by
  let 𝒟 : Distribution (EvaluatedSliceQuestion params) :=
    uniformDistribution (EvaluatedSliceQuestion params)
  let A : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q b => leftTensor (ι₂ := ι) ((evaluatedSliceSecondFactor params family q).outcome b)
  let B : EvaluatedSliceQuestion params → Fq params → MIPStarRE.Quantum.Op (ι × ι) :=
    fun q b => rightTensor (ι₁ := ι) ((evaluatedSliceSecondFactor params family q).outcome b)
  let C : EvaluatedSliceQuestion params → Fq params → Fq params →
      MIPStarRE.Quantum.Op (ι × ι) :=
    fun q b a =>
      leftTensor (ι₂ := ι)
        ((evaluatedSliceFirstFactor params family q).outcome a *
          (evaluatedSliceSecondFactor params family q).outcome b *
          (evaluatedSliceFirstFactor params family q).outcome a)
  have h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1 := by
    simpa [𝒟] using uniformDistribution_weight_sum_le_one (EvaluatedSliceQuestion params)
  have hAB : avgOver 𝒟 (fun q => qSDDCore strategy.state (A q) (B q)) ≤ zeta := by
    simpa [𝒟, A, B] using
      evaluatedSlice_selfConsistency_snd_bound params strategy family zeta hself
  have hC :
      ∀ q,
        ∑ b : Fq params,
            (∑ a : Fq params, C q b a) * (∑ a : Fq params, C q b a)ᴴ ≤ 1 := by
    intro q
    simpa [C, evaluatedSliceSecondFactor, evaluatedSliceFirstProj] using
      (leftTensor_normalizationCondition_sandwich_bound
        (P := evaluatedSliceSecondFactor params family q)
        (Q := evaluatedSliceFirstProj params family q))
  have hclose :=
    MIPStarRE.LDT.Preliminaries.closenessOfIP
      strategy.state hnorm 𝒟 h𝒟 A B C zeta hAB hC
  have hScalar :
      avgOver 𝒟
          (fun q => ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state (C q b a * A q b)) =
        evaluatedSliceABABAvg params strategy family := by
    unfold evaluatedSliceABABAvg
    apply avgOver_congr
    intro q
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro b _
    refine Finset.sum_congr rfl ?_
    intro a _
    simp [C, A, evaluatedSliceABABTerm, evaluatedSliceFirstFactor,
      evaluatedSliceSecondFactor, leftTensor_mul_leftTensor, mul_assoc]
  have hTensor :
      avgOver 𝒟
          (fun q => ∑ b : Fq params, ∑ a : Fq params,
            ev strategy.state (C q b a * B q b)) =
        evaluatedSliceABABtensorAvg params strategy family := by
    unfold evaluatedSliceABABtensorAvg
    apply avgOver_congr
    intro q
    calc
      ∑ b : Fq params, ∑ a : Fq params,
          ev strategy.state (C q b a * B q b)
        = ∑ a : Fq params, ∑ b : Fq params,
            ev strategy.state (C q b a * B q b) := by
            rw [Finset.sum_comm]
      _ = ∑ ab : EvaluatedSliceOutcome params,
            ev strategy.state
              (leftTensor (ι₂ := ι)
                  ((evaluatedSliceFirstFactor params family q).outcome ab.1 *
                    (evaluatedSliceSecondFactor params family q).outcome ab.2 *
                    (evaluatedSliceFirstFactor params family q).outcome ab.1) *
                rightTensor (ι₁ := ι)
                  ((evaluatedSliceSecondFactor params family q).outcome ab.2)) := by
            simpa [C, B, evaluatedSliceFirstFactor, evaluatedSliceSecondFactor] using
              (Fintype.sum_prod_type' (f := fun a : Fq params => fun b : Fq params =>
                ev strategy.state
                  (leftTensor (ι₂ := ι)
                      ((evaluatedSliceFirstFactor params family q).outcome a *
                        (evaluatedSliceSecondFactor params family q).outcome b *
                        (evaluatedSliceFirstFactor params family q).outcome a) *
                    rightTensor (ι₁ := ι)
                      ((evaluatedSliceSecondFactor params family q).outcome b)))).symm
  calc
    |evaluatedSliceABABAvg params strategy family -
        evaluatedSliceABABtensorAvg params strategy family|
      = |avgOver 𝒟
            (fun q => ∑ b : Fq params, ∑ a : Fq params,
              ev strategy.state (C q b a * A q b)) -
          avgOver 𝒟
            (fun q => ∑ b : Fq params, ∑ a : Fq params,
              ev strategy.state (C q b a * B q b))| := by
            rw [hScalar, hTensor]
    _ ≤ Real.sqrt zeta := hclose

/-- Proved x-prefix from the full scalar quartic to the x-evaluated `BAB ⊗ A`
tensor endpoint.

This packages the first two paper steps for the second term in
`commutativity-G.tex` lines 332--354: the `eq:gcom4` scalar-to-`BAB ⊗ A`
bridge costs `√ζ`, and the `eq:gcom4-diff` Schwartz--Zippel
postprocessing of the `x` polynomial outcome costs `md/q`. The remaining
paper lines 356--360 are intentionally not included here; they are the two
`closenessOfIP` legs from `xEvaluatedSliceBABAtensorAvg` to
`xEvaluatedFullSliceABABtensorAvg`. -/
lemma fullSliceABAB_to_xEvaluatedSliceBABAtensorAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |fullSliceABABAvg params strategy family -
        xEvaluatedSliceBABAtensorAvg params strategy family| ≤
      (↑params.m : Error) * ↑params.d / ↑params.q + Real.sqrt zeta := by
  have hbridge := fullSliceABAB_scalar_to_BABAtensor params strategy family zeta hnorm hself
  have hx := fullSliceBABA_tensor_marginalize_x params strategy family hnorm
  have hx' :
      |fullSliceBABAtensorAvg params strategy family -
          xEvaluatedSliceBABAtensorAvg params strategy family| ≤
        (↑params.m : Error) * ↑params.d / ↑params.q := by
    simpa [Nat.cast_mul] using hx
  have htri :=
    abs_sub_le
      (fullSliceABABAvg params strategy family)
      (fullSliceBABAtensorAvg params strategy family)
      (xEvaluatedSliceBABAtensorAvg params strategy family)
  linarith

/-- Proved y-tail from the mixed `ABA ⊗ B` tensor endpoint to the evaluated
scalar quartic.

This packages the paper steps after the x-stage has already reached
`xEvaluatedFullSliceABABtensorAvg`: y-Schwartz-Zippel marginalization
(`commutativity-G.tex` lines 369--385) followed by the `√ζ`
`closenessOfIP` move that swaps a trailing `G^y_{[h(v)=b]}` between the
scalar quartic and the `ABA ⊗ B` tensor -- the doubly-evaluated analogue
of paper line 360, exposed via `evaluatedSliceABAB_scalar_to_ABABtensor`. -/
lemma xEvaluatedFullSliceABABtensor_to_evaluatedSliceABABAvg
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (zeta : Error)
    (hnorm : strategy.state.IsNormalized)
    (hself : family.StronglySelfConsistent strategy.state zeta) :
    |xEvaluatedFullSliceABABtensorAvg params strategy family -
        evaluatedSliceABABAvg params strategy family| ≤
      (↑params.m : Error) * ↑params.d / ↑params.q + Real.sqrt zeta := by
  have hyTensor :=
    fullSliceABAB_tensor_marginalize_y params strategy family hnorm
  have hevalBridge :=
    evaluatedSliceABAB_scalar_to_ABABtensor params strategy family zeta hnorm hself
  have hevalBridge' :
      |evaluatedSliceABABtensorAvg params strategy family -
          evaluatedSliceABABAvg params strategy family| ≤ Real.sqrt zeta := by
    rwa [abs_sub_comm] at hevalBridge
  have htri :=
    abs_sub_le
      (xEvaluatedFullSliceABABtensorAvg params strategy family)
      (evaluatedSliceABABtensorAvg params strategy family)
      (evaluatedSliceABABAvg params strategy family)
  linarith

/-- Paper `eq:gcomterms` (`commutativity-G.tex` lines 286-290).

Full-slice analog of `evaluatedSliceCommutation_qSDDOp_avg_eq` (line 878): the
pulled-back `sddErrorOp` on the full-slice product equals `2·(ABAAvg − ABABAvg)`
after using projectivity and the `(x,g) ↔ (y,h)` symmetry to collapse
`BAB + ABA − BABA − ABAB` into the two surviving scalar quartic terms. -/
lemma fullSliceCommutation_qSDDOp_avg_eq
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    sddErrorOp strategy.state
        (uniformDistribution (EvaluatedSliceQuestion params))
        (fun q => fullSliceProductLeft params strategy family
          (fullSliceQuestionOfEvaluatedSlice params q))
        (fun q => fullSliceProductRight params strategy family
          (fullSliceQuestionOfEvaluatedSlice params q)) =
      2 * (fullSliceABAAvg params strategy family -
        fullSliceABABAvg params strategy family) := by
  have hswap := fullSliceCommutation_avg_swap_terms params strategy family
  let D := uniformDistribution (FullSliceQuestion params)
  rw [sddErrorOp_pullback_fullSliceQuestion_eq params strategy.state
    (fullSliceProductLeft params strategy family)
    (fullSliceProductRight params strategy family)]
  unfold sddErrorOp
  rw [fullSliceCommutation_qSDDOp_avg_expand_full params strategy family]
  rcases hswap with ⟨hBAB, hBABA⟩
  let BAB : FullSliceQuestion params → Error := fun q =>
    ∑ gh : FullSliceOutcome params, fullSliceBABTerm params strategy family q gh
  let ABA : FullSliceQuestion params → Error := fun q =>
    ∑ gh : FullSliceOutcome params, fullSliceABATerm params strategy family q gh
  let BABA : FullSliceQuestion params → Error := fun q =>
    ∑ gh : FullSliceOutcome params, fullSliceBABATerm params strategy family q gh
  let ABAB : FullSliceQuestion params → Error := fun q =>
    ∑ gh : FullSliceOutcome params, fullSliceABABTerm params strategy family q gh
  calc
    avgOver D
        (fun q =>
          ∑ gh : FullSliceOutcome params,
            (fullSliceBABTerm params strategy family q gh +
              fullSliceABATerm params strategy family q gh -
              fullSliceBABATerm params strategy family q gh -
              fullSliceABABTerm params strategy family q gh))
      = avgOver D (fun q => (BAB q + ABA q) - (BABA q + ABAB q)) := by
          apply avgOver_congr
          intro q
          dsimp [BAB, ABA, BABA, ABAB]
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
          ring
    _ = avgOver D (fun q => BAB q + ABA q) -
          avgOver D (fun q => BABA q + ABAB q) := by
          simp [avgOver, Finset.sum_sub_distrib, mul_sub]
    _ = (avgOver D BAB + avgOver D ABA) -
          (avgOver D BABA + avgOver D ABAB) := by
          rw [avgOver_add, avgOver_add]
    _ = (avgOver D ABA + avgOver D ABA) -
          (avgOver D ABAB + avgOver D ABAB) := by
          rw [hBAB, hBABA]
    _ = 2 * (avgOver D ABA - avgOver D ABAB) := by
          ring
    _ = 2 * (fullSliceABAAvg params strategy family -
          fullSliceABABAvg params strategy family) := by
          rfl

end MIPStarRE.LDT.Commutativity
