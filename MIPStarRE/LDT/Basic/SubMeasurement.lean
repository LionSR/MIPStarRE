import MIPStarRE.LDT.Basic.Operator

/-!
# SubMeasurement infrastructure for the low individual degree test

Shared measurement definitions: submeasurements, measurements, projective variants,
indexed families, postprocessing, and completion.
-/

noncomputable section

namespace MIPStarRE.LDT

/-- A paper-local submeasurement with outcomes in `α` and Hilbert space dimension `d`. -/
structure SubMeasurement (α : Type*) (d : ℕ) where
  name : String := ""
  outcomeOperator : α → Operator d := fun _ => default
  totalOperator : Operator d := default

instance : Inhabited (SubMeasurement α d) where
  default := {}

/-- A paper-local measurement. -/
structure Measurement (α : Type*) (d : ℕ) extends SubMeasurement α d where
  completeWitness : True := trivial

instance : Inhabited (Measurement α d) where
  default := { toSubMeasurement := default }

/-- A paper-local projective submeasurement. -/
structure ProjectiveSubMeasurement (α : Type*) (d : ℕ) extends SubMeasurement α d where
  projectiveWitness : True := trivial

instance : Inhabited (ProjectiveSubMeasurement α d) where
  default := { toSubMeasurement := default }

/-- A paper-local projective measurement. -/
structure ProjectiveMeasurement (α : Type*) (d : ℕ) extends Measurement α d where
  projectiveWitness : True := trivial

instance : Inhabited (ProjectiveMeasurement α d) where
  default := { toMeasurement := default }

abbrev IndexedSubMeasurement (Question Outcome : Type*) (d : ℕ) :=
  Question → SubMeasurement Outcome d
abbrev IndexedMeasurement (Question Outcome : Type*) (d : ℕ) :=
  Question → Measurement Outcome d
abbrev IndexedProjectiveSubMeasurement (Question Outcome : Type*) (d : ℕ) :=
  Question → ProjectiveSubMeasurement Outcome d
abbrev IndexedProjectiveMeasurement (Question Outcome : Type*) (d : ℕ) :=
  Question → ProjectiveMeasurement Outcome d

namespace IndexedMeasurement

def toIndexedSubMeasurement {Question Outcome : Type*} {d : ℕ}
    (A : IndexedMeasurement Question Outcome d) :
    IndexedSubMeasurement Question Outcome d :=
  fun q => (A q).toSubMeasurement

end IndexedMeasurement

namespace IndexedProjectiveSubMeasurement

def toIndexedSubMeasurement {Question Outcome : Type*} {d : ℕ}
    (A : IndexedProjectiveSubMeasurement Question Outcome d) :
    IndexedSubMeasurement Question Outcome d :=
  fun q => (A q).toSubMeasurement

end IndexedProjectiveSubMeasurement

namespace IndexedProjectiveMeasurement

def toIndexedMeasurement {Question Outcome : Type*} {d : ℕ}
    (A : IndexedProjectiveMeasurement Question Outcome d) :
    IndexedMeasurement Question Outcome d :=
  fun q => (A q).toMeasurement

def toIndexedSubMeasurement {Question Outcome : Type*} {d : ℕ}
    (A : IndexedProjectiveMeasurement Question Outcome d) :
    IndexedSubMeasurement Question Outcome d :=
  fun q => (A q).toSubMeasurement

end IndexedProjectiveMeasurement

/-- Post-process the outcomes of a submeasurement. When the outcome space is enumerable,
the processed operator at `b` is the sum of the operators of all `a` with `f a = b`.
Otherwise we fall back to the zero operator in the ambient space until the relevant
bounded-answer enumeration is made explicit. -/
noncomputable def postprocess {α β : Type*} {d : ℕ}
    (A : SubMeasurement α d) (f : α → β) :
    SubMeasurement β d := by
  classical
  if h : Nonempty (Fintype α) then
    letI : Fintype α := Classical.choice h
    exact {
      name := s!"{A.name}.post"
      outcomeOperator := fun b =>
        sumOperatorList
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
def completeSubMeasurement {α : Type*} {d : ℕ}
    (A : SubMeasurement α d) : Measurement (Option α) d where
  toSubMeasurement := {
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
def constantSubMeasurementFamily {α : Type*} {d : ℕ}
    (A : SubMeasurement α d) :
    IndexedSubMeasurement Unit α d :=
  fun _ => A

end MIPStarRE.LDT
