import MIPStarRE.Paper2009LDT.Basic.Operator
import MIPStarRE.Paper2009LDT.Basic.Distribution

/-!
# SubMeasurement infrastructure for the low individual degree test

Shared measurement definitions: submeasurements, measurements, projective variants,
indexed families, postprocessing, and completion.
-/

noncomputable section

namespace MIPStarRE.Paper2009LDT

/-- A paper-local submeasurement with outcomes in `α`. -/
structure SubMeasurement (α : Type _) where
  name : String := ""
  outcomeOperator : α → Operator := fun _ => default
  totalOperator : Operator := default
  deriving Inhabited

/-- A paper-local measurement. -/
structure Measurement (α : Type _) extends SubMeasurement α where
  completeWitness : True := trivial
  deriving Inhabited

/-- A paper-local projective submeasurement. -/
structure ProjectiveSubMeasurement (α : Type _) extends SubMeasurement α where
  projectiveWitness : True := trivial
  deriving Inhabited

/-- A paper-local projective measurement. -/
structure ProjectiveMeasurement (α : Type _) extends Measurement α where
  projectiveWitness : True := trivial
  deriving Inhabited

abbrev IndexedSubMeasurement (Question Outcome : Type _) := Question → SubMeasurement Outcome
abbrev IndexedMeasurement (Question Outcome : Type _) := Question → Measurement Outcome
abbrev IndexedProjectiveSubMeasurement (Question Outcome : Type _) :=
  Question → ProjectiveSubMeasurement Outcome
abbrev IndexedProjectiveMeasurement (Question Outcome : Type _) :=
  Question → ProjectiveMeasurement Outcome

namespace IndexedMeasurement

def toIndexedSubMeasurement {Question Outcome : Type _}
    (A : IndexedMeasurement Question Outcome) : IndexedSubMeasurement Question Outcome :=
  fun q => (A q).toSubMeasurement

end IndexedMeasurement

namespace IndexedProjectiveSubMeasurement

def toIndexedSubMeasurement {Question Outcome : Type _}
    (A : IndexedProjectiveSubMeasurement Question Outcome) :
    IndexedSubMeasurement Question Outcome :=
  fun q => (A q).toSubMeasurement

end IndexedProjectiveSubMeasurement

namespace IndexedProjectiveMeasurement

def toIndexedMeasurement {Question Outcome : Type _}
    (A : IndexedProjectiveMeasurement Question Outcome) :
    IndexedMeasurement Question Outcome :=
  fun q => (A q).toMeasurement

def toIndexedSubMeasurement {Question Outcome : Type _}
    (A : IndexedProjectiveMeasurement Question Outcome) :
    IndexedSubMeasurement Question Outcome :=
  fun q => (A q).toSubMeasurement

end IndexedProjectiveMeasurement

/-- Post-process the outcomes of a submeasurement. When the outcome space is enumerable,
the processed operator at `b` is the sum of the operators of all `a` with `f a = b`.
Otherwise we fall back to the zero operator in the ambient space until the relevant
bounded-answer enumeration is made explicit. -/
noncomputable def postprocess {α β : Type _} (A : SubMeasurement α) (f : α → β) :
    SubMeasurement β := by
  classical
  if h : Nonempty (Fintype α) then
    letI : Fintype α := Classical.choice h
    exact {
      name := s!"{A.name}.post"
      outcomeOperator := fun b =>
        sumOperatorList A.totalOperator
          (((Finset.univ.filter fun a => f a = b).toList).map A.outcomeOperator)
      totalOperator := A.totalOperator
    }
  else
    exact {
      name := s!"{A.name}.post"
      outcomeOperator := fun _ => zeroLike A.totalOperator
      totalOperator := A.totalOperator
    }

/-- Complete a submeasurement by adjoining a distinguished failure outcome. -/
def completeSubMeasurement {α : Type _} (A : SubMeasurement α) : Measurement (Option α) where
  toSubMeasurement := {
    name := s!"{A.name}.completion"
    outcomeOperator := fun
      | some a => A.outcomeOperator a
      | none =>
          { name := s!"{A.name}.failure"
            dim := A.totalOperator.dim
            matrix := 1 - A.totalOperator.matrix }
    totalOperator :=
      { name := s!"{A.name}.completion.total"
        dim := A.totalOperator.dim
        matrix := 1 }
  }

/-- Constant indexed family taking the same submeasurement on every question. -/
def constantSubMeasurementFamily {α : Type _} (A : SubMeasurement α) :
    IndexedSubMeasurement Unit α :=
  fun _ => A

end MIPStarRE.Paper2009LDT
