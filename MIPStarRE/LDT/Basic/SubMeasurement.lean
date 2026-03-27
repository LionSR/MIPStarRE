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
  outcomeOperator : α → Operator d := fun _ => default
  totalOperator : Operator d := default

instance : Inhabited (SubMeas α d) where
  default := {}

/-- A paper-local measurement. -/
structure Measurement (α : Type*) (d : ℕ) extends SubMeas α d where
  completeWitness : True := trivial

instance : Inhabited (Measurement α d) where
  default := { toSubMeas := default }

/-- A paper-local projective submeasurement. -/
structure ProjSubMeas (α : Type*) (d : ℕ) extends SubMeas α d where
  projectiveWitness : True := trivial

instance : Inhabited (ProjSubMeas α d) where
  default := { toSubMeas := default }

/-- A paper-local projective measurement. -/
structure ProjMeas (α : Type*) (d : ℕ) extends Measurement α d where
  projectiveWitness : True := trivial

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

/-- Post-process the outcomes of a submeasurement. When the outcome space is enumerable,
the processed operator at `b` is the sum of the operators of all `a` with `f a = b`.
Otherwise we fall back to the zero operator in the ambient space until the relevant
bounded-answer enumeration is made explicit. -/
noncomputable def postprocess {α β : Type*} {d : ℕ}
    (A : SubMeas α d) (f : α → β) :
    SubMeas β d := by
  classical
  if h : Nonempty (Fintype α) then
    letI : Fintype α := Classical.choice h
    exact {
      name := s!"{A.name}.post"
      outcomeOperator := fun b =>
        sumOpList
          (((Finset.univ.filter fun a => f a = b).toList).map A.outcomeOperator)
      totalOperator := A.totalOperator
    }
  else
    exact {
      name := s!"{A.name}.post"
      outcomeOperator := fun _ => (0 : Operator d)
      totalOperator := A.totalOperator
    }

/-- Complete a submeasurement by adjoining a distinguished failure outcome. -/
def completeSubMeas {α : Type*} {d : ℕ}
    (A : SubMeas α d) : Measurement (Option α) d where
  toSubMeas := {
    name := s!"{A.name}.completion"
    outcomeOperator := fun
      | some a => A.outcomeOperator a
      | none =>
          { name := s!"{A.name}.failure"
            matrix := 1 - A.totalOperator.matrix }
    totalOperator :=
      { name := s!"{A.name}.completion.total"
        matrix := 1 }
  }

/-- Constant indexed family taking the same submeasurement on every question. -/
def constSubMeasFamily {α : Type*} {d : ℕ}
    (A : SubMeas α d) :
    IdxSubMeas Unit α d :=
  fun _ => A

end MIPStarRE.LDT
