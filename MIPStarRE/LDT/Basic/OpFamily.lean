import MIPStarRE.LDT.Basic.SubMeasurement

/-!
# Raw operator families for the low individual degree test

This file introduces the paper-level notion of an indexed family of operators
without positivity or boundedness requirements. These are used for `≈_δ`
chains whose intermediate objects are arbitrary matrix families rather than
honest submeasurements.
-/

open scoped BigOperators MatrixOrder Matrix ComplexOrder

namespace MIPStarRE.LDT

/-- A raw operator family: outcome operators indexed by `α`, without PSD or bound
requirements. This matches the paper's use of arbitrary matrix families in
`≈_δ` chains. -/
structure OpFamily (α : Type*) (ι : Type*) [Fintype ι] [DecidableEq ι] where
  outcome : α → MIPStarRE.Quantum.Op ι
  total : MIPStarRE.Quantum.Op ι

/-- Indexed raw operator family (question → outcome → operator). -/
def IdxOpFamily (Question Outcome : Type*) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :=
  Question → OpFamily Outcome ι

namespace SubMeas

/-- Forget the PSD and boundedness structure of a submeasurement. -/
def toOpFamily {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι]
    (A : SubMeas α ι) : OpFamily α ι where
  outcome := A.outcome
  total := A.total

end SubMeas

instance {α : Type*} {ι : Type*}
    [Fintype α] [Fintype ι] [DecidableEq ι] :
    Coe (SubMeas α ι) (OpFamily α ι) where
  coe := SubMeas.toOpFamily

namespace IdxSubMeas

/-- Forget the PSD and boundedness structure of an indexed submeasurement family. -/
def toIdxOpFamily {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxSubMeas Question Outcome ι) :
    IdxOpFamily Question Outcome ι :=
  fun q => (A q).toOpFamily

end IdxSubMeas

namespace OpFamily

/-- Lift a raw operator family to the left tensor factor of `ι × ι`. -/
def liftLeft {α : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : OpFamily α ι) : OpFamily α (ι × ι) where
  outcome := fun a => leftTensor (ι₂ := ι) (A.outcome a)
  total := leftTensor (ι₂ := ι) A.total

/-- Place a raw operator family on the left tensor factor of `ιA × ιB`. -/
def leftPlacedOpFamily {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : OpFamily α ιA) :
    OpFamily α (ιA × ιB) where
  outcome := fun a => leftTensor (ι₂ := ιB) (A.outcome a)
  total := leftTensor (ι₂ := ιB) A.total

/-- Place a raw operator family on the right tensor factor of `ιA × ιB`. -/
def rightPlacedOpFamily {α : Type*}
    {ιA ιB : Type*} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : OpFamily α ιB) :
    OpFamily α (ιA × ιB) where
  outcome := fun a => rightTensor (ι₁ := ιA) (A.outcome a)
  total := rightTensor (ι₁ := ιA) A.total

/-- Post-process the outcomes of a raw operator family. -/
noncomputable def postprocess {α β : Type*} {ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι] [DecidableEq ι]
    (A : OpFamily α ι) (f : α → β) :
    OpFamily β ι := by
  classical
  exact
    { outcome := fun b =>
        ∑ a ∈ Finset.univ.filter (fun a => f a = b), A.outcome a
      total := A.total }

end OpFamily

namespace IdxOpFamily

/-- Lift an indexed raw operator family to the left tensor factor. -/
def liftLeft {Question Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (A : IdxOpFamily Question Outcome ι) :
    IdxOpFamily Question Outcome (ι × ι) :=
  fun q => (A q).liftLeft

/-- Forget the extra structure on an indexed submeasurement family after left placement. -/
def ofIdxSubMeasLeft {Question Outcome : Type*} {ι : Type*}
    [Fintype Outcome] [Fintype ι] [DecidableEq ι]
    (A : IdxSubMeas Question Outcome ι) :
    IdxOpFamily Question Outcome (ι × ι) :=
  (IdxSubMeas.toIdxOpFamily A).liftLeft

end IdxOpFamily

end MIPStarRE.LDT
