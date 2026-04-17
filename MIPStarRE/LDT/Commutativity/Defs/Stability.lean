import MIPStarRE.LDT.Commutativity.Defs.Core

namespace MIPStarRE.LDT.Commutativity

open MIPStarRE.LDT
open MIPStarRE.Quantum
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (params : Parameters) [FieldModel params.q]
/-- Reindex a raw operator family and append an explicit weight.

The outcome type `β` must retain every coordinate that still appears in
`weight`; otherwise any later postprocessing would sum over an irrelevant fiber
and change the operator by a multiplicity factor. -/
private noncomputable def weightedReindexOpFamily
    {α β : Type*} [Fintype α] [Fintype β]
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (base : OpFamily α κ)
    (reindex : β → α)
    (weight : β → MIPStarRE.Quantum.Op κ) :
    OpFamily β κ :=
  let body := fun b => base.outcome (reindex b) * weight b
  { outcome := body
    total := ∑ b : β, body b }

/-- Postprocess the full-slice ordered product at sampled points.
On the bipartite space `d * d`. -/
noncomputable def evaluatedFromFullSliceProductLeft (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxOpFamily (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    OpFamily.postprocess (fullSliceProductLeft params strategy family xy)
      (evaluateFullSliceOutcomeAtQuestion params q)

/-- Postprocess the full-slice reversed product at sampled points.
On the bipartite space `d * d`. -/
noncomputable def evaluatedFromFullSliceProductRight (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι) :
    IdxOpFamily (EvaluatedSliceQuestion params) (EvaluatedSliceOutcome params) (ι × ι) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    OpFamily.postprocess (fullSliceProductRight params strategy family xy)
      (evaluateFullSliceOutcomeAtQuestion params q)

/-- Internal overlap family from the `G^y` insertion/removal step.

The paper writes the extra factor as the left-register total `G^y = ∑_h G^y_h`.
For the `SDDOpRel` packaging we keep the polynomial `h` explicit and attach the
right-register weight `(G_h^y)^{1/2}` to each outcome. Summing the squared
differences over `h` then recovers the total `G^y` without introducing a fiber
multiplicity from unrelated `g` values.

This is deliberately an overlap estimate family, not the scalar
`clm:g-comm-stability` expression from the paper.  The paper claim keeps the
right-register factor `A_b^{v,y}` and is driven by the boundedness witness
`Z^y`; the overlap family below instead measures a stronger-looking SDD package
against `G_h^y` weights. On the bipartite space `d * d`. -/
noncomputable def commDataProcessedGStabilityOneLeft (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι) :
    IdxOpFamily (EvaluatedSliceQuestion params) (StabilityOneOutcome params) (ι × ι) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    weightedReindexOpFamily
      (appendRightTotalOpFamily
        ((evaluatedSliceSandwichFirstFactor params strategy family q) :
          OpFamily (EvaluatedSliceOutcome params) (ι × ι))
        (leftTensor (ι₂ := ι) ((fullSliceSecondFactor params family xy).total)))
      (evaluateStabilityOneOutcomeAtQuestion params q)
      (fun ah => rightTensor (ι₁ := ι)
        (CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2)))

/-- Internal overlap family after removing the trailing `G^y`, while keeping
the `G_h^y` right-register square-root weight used by the SDD package.
On the bipartite space `d * d`. -/
noncomputable def commDataProcessedGStabilityOneRight (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι) :
    IdxOpFamily (EvaluatedSliceQuestion params) (StabilityOneOutcome params) (ι × ι) :=
  fun q =>
    weightedReindexOpFamily
      ((evaluatedSliceSandwichFirstFactor params strategy family q) :
        OpFamily (EvaluatedSliceOutcome params) (ι × ι))
      (evaluateStabilityOneOutcomeAtQuestion params q)
      (fun ah => rightTensor (ι₁ := ι)
        (CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2)))

/-- Internal overlap family from the `G^x` insertion/removal step.

As for `commDataProcessedGStabilityOneLeft`, this packages an overlap-style SDD
comparison.  The paper's `clm:g-comm-stability2` is a scalar boundedness argument
with right-register factor `A_a^{u,x} A_b^{v,y}` and an internal
`commutativityPoints` transport step.
On the bipartite space `d * d`. -/
noncomputable def commDataProcessedGStabilityTwoLeft (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι) :
    IdxOpFamily (EvaluatedSliceQuestion params) (StabilityTwoOutcome params) (ι × ι) :=
  fun q =>
    let xy := fullSliceQuestionOfEvaluatedSlice params q
    weightedReindexOpFamily
      (appendRightTotalOpFamily
        (evaluatedSliceProductLeft params strategy family q)
        (leftTensor (ι₂ := ι) ((fullSliceFirstFactor params family xy).total)))
      (evaluateStabilityTwoOutcomeAtQuestion params q)
      (fun gb => rightTensor (ι₁ := ι)
        (CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1)))

/-- Internal overlap family after removing the trailing `G^x`, while keeping
the `G_g^x` right-register square-root weight used by the SDD package.
On the bipartite space `d * d`. -/
noncomputable def commDataProcessedGStabilityTwoRight (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι) :
    IdxOpFamily (EvaluatedSliceQuestion params) (StabilityTwoOutcome params) (ι × ι) :=
  fun q =>
    weightedReindexOpFamily
      (evaluatedSliceProductLeft params strategy family q)
      (evaluateStabilityTwoOutcomeAtQuestion params q)
      (fun gb => rightTensor (ι₁ := ι)
        (CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1)))

/-- Expand one outcome of the first `G^y` stability family. -/
lemma commDataProcessedGStabilityOneLeft_outcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (q : EvaluatedSliceQuestion params)
    (ah : StabilityOneOutcome params) :
    (commDataProcessedGStabilityOneLeft params strategy family G q).outcome ah =
      (leftPlacedSubMeas (ιB := ι)
          (evaluatedSliceSandwichRaw params strategy family q)).outcome
          (ah.1, ah.2 (truncatePoint params q.2)) *
        leftTensor (ι₂ := ι)
          ((fullSliceSecondFactor params family
            (fullSliceQuestionOfEvaluatedSlice params q)).total) *
        rightTensor (ι₁ := ι)
          (CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2)) := by
  rfl

/-- Expand one outcome of the second `G^y` stability family. -/
lemma commDataProcessedGStabilityOneRight_outcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (q : EvaluatedSliceQuestion params)
    (ah : StabilityOneOutcome params) :
    (commDataProcessedGStabilityOneRight params strategy family G q).outcome ah =
      leftTensor (ι₂ := ι)
          ((evaluatedSliceSandwichRaw params strategy family q).outcome
              (ah.1, ah.2 (truncatePoint params q.2))) *
        rightTensor (ι₁ := ι)
          (CFC.sqrt ((G (pointHeight params q.2)).outcome ah.2)) := by
  rfl

/-- Expand one outcome of the first `G^x` stability family. -/
lemma commDataProcessedGStabilityTwoLeft_outcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (q : EvaluatedSliceQuestion params)
    (gb : StabilityTwoOutcome params) :
    (commDataProcessedGStabilityTwoLeft params strategy family G q).outcome gb =
      (evaluatedSliceProductLeft params strategy family q).outcome
          (gb.1 (truncatePoint params q.1), gb.2) *
        leftTensor (ι₂ := ι)
          ((fullSliceFirstFactor params family
            (fullSliceQuestionOfEvaluatedSlice params q)).total) *
        rightTensor (ι₁ := ι)
          (CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1)) := by
  rfl

/-- Expand one outcome of the second `G^x` stability family. -/
lemma commDataProcessedGStabilityTwoRight_outcome
    (params : Parameters) [FieldModel params.q]
    (strategy : SymStrat params.next ι) (family : IdxPolyFamily params ι)
    (G : Fq params → SubMeas (Polynomial params) ι)
    (q : EvaluatedSliceQuestion params)
    (gb : StabilityTwoOutcome params) :
    (commDataProcessedGStabilityTwoRight params strategy family G q).outcome gb =
      leftTensor (ι₂ := ι)
          ((orderedProductOpFamily
              (evaluatedSliceFirstFactor params family q)
              (evaluatedSliceSecondFactor params family q)).outcome
              (gb.1 (truncatePoint params q.1), gb.2)) *
        rightTensor (ι₁ := ι)
          (CFC.sqrt ((G (pointHeight params q.1)).outcome gb.1)) := by
  rfl


end MIPStarRE.LDT.Commutativity
