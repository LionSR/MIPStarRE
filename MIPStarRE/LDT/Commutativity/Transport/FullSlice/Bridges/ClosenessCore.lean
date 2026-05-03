import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Averages
import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Machinery.Marginalization
import MIPStarRE.LDT.Commutativity.Transport.FullSlice.Machinery.Normalization

/-!
# Core full-slice closeness-of-inner-product bridges

Standalone `closenessOfIP` scalar↔tensor bridges extracted from
`Closeness.lean` per #1127.  These four lemmas are the core
tensor-form machinery that moves a trailing measurement outcome between
the scalar quartic and a manifestly positive tensor register.

Ex-private definitions are tensor-form machinery per architecture decision
#713; downstream code should use the scalar public API exposed by
`Closeness.lean` and `ClosenessXEval.lean`.

## References

- arXiv:2009.12982, Section 11.
-/

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Scalar-to-tensor bridge for paper `eq:gcom4`
(`commutativity-G.tex` lines 332-337).

One `closenessOfIP` application moves the trailing `G^x_g` in the scalar quartic
`G^y_h G^x_g G^y_h G^x_g ⊗ I` to the right register, producing the manifestly
PSD tensor form `G^y_h G^x_g G^y_h ⊗ G^x_g`.  The scalar side is stated as
`fullSliceABABAvg`; the proof first uses the `(x,g) ↔ (y,h)` swap symmetry above
to identify the averaged `BABA` scalar with the averaged `ABAB` scalar. -/
lemma fullSliceABAB_scalar_to_BABAtensor
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
lemma fullSliceABAB_scalar_to_ABABtensor
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

/-- Evaluated-slice scalar-to-tensor bridge for the first approximation after
`eq:evaluate-gcom-at-points` (`commutativity-G.tex` lines 356-365).

This is the evaluated analogue of `fullSliceABAB_scalar_to_BABAtensor`.  The
point-level self-consistency for the already evaluated/postprocessed family is
now derived from slice strong self-consistency by
`evaluatedPointFamily_selfConsistency_of_stronglySelfConsistent`. -/
lemma evaluatedSliceABAB_scalar_to_BABAtensor
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
lemma xEvaluatedSliceBABAtensor_to_BABAScalar
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

end MIPStarRE.LDT.Commutativity
