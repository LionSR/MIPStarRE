import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Averages
import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Machinery.Marginalization
import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Machinery.Normalization

/-!
# X-evaluated full-slice closeness bridge

Single `closenessOfIP` bridge for the x-evaluated/full-y scalar-to-tensor
transition; extracted from `Closeness.lean` per #1127.

## References

- arXiv:2009.12982, Section 11.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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

end MIPStarRE.LDT.Commutativity
