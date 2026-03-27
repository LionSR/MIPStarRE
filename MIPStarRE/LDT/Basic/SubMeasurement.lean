import MIPStarRE.LDT.Basic.Operator

/-!
# SubMeas infrastructure for the low individual degree test

Shared measurement definitions: submeasurements, measurements, projective variants,
indexed families, postprocessing, and completion.
-/

noncomputable section

namespace MIPStarRE.LDT

/-- A paper-local submeasurement with outcomes in `α` and Hilbert space dimension `d`. -/
structure SubMeas (α : Type*) (d : ℕ) where
  name : String := ""
  outcome : α → Operator d := fun _ => default
  total : Operator d := default

instance : Inhabited (SubMeas α d) where
  default := {}

/-- A paper-local measurement. -/
structure Measurement (α : Type*) (d : ℕ) extends SubMeas α d where
  completePlaceholder : True := trivial

instance : Inhabited (Measurement α d) where
  default := { toSubMeas := default }

/-- A paper-local projective submeasurement. -/
structure ProjSubMeas (α : Type*) (d : ℕ) extends SubMeas α d where
  projPlaceholder : True := trivial

instance : Inhabited (ProjSubMeas α d) where
  default := { toSubMeas := default }

/-- A paper-local projective measurement. -/
structure ProjMeas (α : Type*) (d : ℕ) extends Measurement α d where
  projPlaceholder : True := trivial

instance : Inhabited (ProjMeas α d) where
  default := { toMeasurement := default }

abbrev IdxSubMeas (Question Outcome : Type*) (d : ℕ) :=
  Question → SubMeas Outcome d
abbrev IdxMeas (Question Outcome : Type*) (d : ℕ) :=
  Question → Measurement Outcome d
abbrev IdxProjSubMeas (Question Outcome : Type*) (d : ℕ) :=
  Question → ProjSubMeas Outcome d
abbrev IdxProjMeas (Question Outcome : Type*) (d : ℕ) :=
  Question → ProjMeas Outcome d

namespace IdxMeas

def toIdxSubMeas {Question Outcome : Type*} {d : ℕ}
    (A : IdxMeas Question Outcome d) :
    IdxSubMeas Question Outcome d :=
  fun q => (A q).toSubMeas

end IdxMeas

namespace IdxProjSubMeas

def toIdxSubMeas {Question Outcome : Type*} {d : ℕ}
    (A : IdxProjSubMeas Question Outcome d) :
    IdxSubMeas Question Outcome d :=
  fun q => (A q).toSubMeas

end IdxProjSubMeas

namespace IdxProjMeas

def toIdxMeas {Question Outcome : Type*} {d : ℕ}
    (A : IdxProjMeas Question Outcome d) :
    IdxMeas Question Outcome d :=
  fun q => (A q).toMeasurement

def toIdxSubMeas {Question Outcome : Type*} {d : ℕ}
    (A : IdxProjMeas Question Outcome d) :
    IdxSubMeas Question Outcome d :=
  fun q => (A q).toSubMeas

end IdxProjMeas

/-- Post-process the outcomes of a submeasurement. The processed operator at `b` is the
sum of the operators of all `a` with `f a = b`. -/
noncomputable def postprocess {α β : Type*} {d : ℕ} [Fintype α]
    (A : SubMeas α d) (f : α → β) :
    SubMeas β d := by
  classical
  exact {
    name := s!"{A.name}.post"
    outcome := fun b =>
      sumOpList
        (((Finset.univ.filter fun a => f a = b).toList).map A.outcome)
    total := A.total
  }

/-- Complete a submeasurement by adjoining a distinguished failure outcome. -/
def completeSubMeas {α : Type*} {d : ℕ}
    (A : SubMeas α d) : Measurement (Option α) d where
  toSubMeas := {
    name := s!"{A.name}.completion"
    outcome := fun
      | some a => A.outcome a
      | none =>
          { name := s!"{A.name}.failure"
            matrix := 1 - A.total.matrix }
    total :=
      { name := s!"{A.name}.completion.total"
        matrix := 1 }
  }

/-- Constant indexed family taking the same submeasurement on every question. -/
def constSubMeasFamily {α : Type*} {d : ℕ}
    (A : SubMeas α d) :
    IdxSubMeas Unit α d :=
  fun _ => A

end MIPStarRE.LDT
