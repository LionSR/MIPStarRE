import MIPStarRE.Codes.LinearCode

/-!
Interfaces for the tensor code test from arXiv:2111.08131.

This file provides the combinatorial question/answer layer for the test while
staying independent of the eventual operator-algebraic semantics of strategies.
The resulting structures are lightweight, but they already capture the basic
objects from Sections 2--3: points of a tensor grid, axis-parallel lines, and
the point/line/pair question types of the game.
-/

namespace MIPStarRE.Games

/-- A point of the `m`-dimensional grid with coordinate set `ι`. -/
abbrev GridPoint (m : ℕ) (ι : Type*) := Fin m → ι

/--
A lightweight representation of an axis-parallel line in `ι^m`.

We store a distinguished axis together with a base point. Varying the base point
along the chosen axis traverses the line. This representation is intentionally
not quotiented by the irrelevant value of `base axis`; it is designed for a
small, easy-to-use scaffold rather than a canonical set-theoretic encoding.
-/
structure AxisParallelLine (m : ℕ) (ι : Type*) where
  axis : Fin m
  base : GridPoint m ι

namespace AxisParallelLine

variable {m : ℕ} {ι : Type*}

/-- The point on the line obtained by inserting `value` in the varying coordinate. -/
def point (ℓ : AxisParallelLine m ι) (value : ι) : GridPoint m ι :=
  Function.update ℓ.base ℓ.axis value

/-- The set of grid points lying on the line. -/
def carrier (ℓ : AxisParallelLine m ι) : Set (GridPoint m ι) :=
  Set.range ℓ.point

@[simp] theorem point_axis (ℓ : AxisParallelLine m ι) (value : ι) :
    ℓ.point value ℓ.axis = value := by
  simp [point]

@[simp] theorem point_ne_axis (ℓ : AxisParallelLine m ι) (value : ι) {i : Fin m}
    (h : i ≠ ℓ.axis) :
    ℓ.point value i = ℓ.base i := by
  simp [point, h]

@[simp] theorem point_mem_carrier (ℓ : AxisParallelLine m ι) (value : ι) :
    ℓ.point value ∈ ℓ.carrier :=
  ⟨value, rfl⟩

/-- The axis-parallel line through `u` in direction `axis`. -/
def through (u : GridPoint m ι) (axis : Fin m) : AxisParallelLine m ι where
  axis := axis
  base := u

@[simp] theorem through_base_mem_carrier (u : GridPoint m ι) (axis : Fin m) :
    u ∈ (through u axis).carrier := by
  refine ⟨u axis, ?_⟩
  ext i
  by_cases h : i = axis
  · subst h
    simp [through, point]
  · simp [through, point, h]

end AxisParallelLine

namespace TensorCodeTest

/-- Parameters for the tensor code test associated with a base code. -/
structure Params (R ι : Type*) [Semiring R] [Fintype ι] [DecidableEq ι] [DecidableEq R] where
  baseCode : MIPStarRE.Codes.LinearCode R ι
  tensorPower : ℕ
  tensorPower_ge_two : 2 ≤ tensorPower

section Basic

variable {R ι : Type*} [Semiring R] [Fintype ι] [DecidableEq ι] [DecidableEq R]

/-- Points queried in the tensor-power domain `ι^m`. -/
abbrev Point (params : Params R ι) := GridPoint params.tensorPower ι

/-- Line questions queried in the axis-parallel consistency part of the test. -/
abbrev LineQuestion (params : Params R ι) := AxisParallelLine params.tensorPower ι

/-- A line answer is a codeword of the base code. -/
abbrev LineAnswer (params : Params R ι) := params.baseCode.words

/--
Pair questions from the subcube-commutation part of the test.

At this stage we record only the two queried points. The additional bookkeeping
for the supporting subcube distribution can be added later without changing the
rest of the interface.
-/
structure PairQuestion (params : Params R ι) where
  left : Point params
  right : Point params

/-- The three question types that appear in the tensor code test. -/
inductive Question (params : Params R ι) where
  | point (u : Point params)
  | line (ℓ : LineQuestion params)
  | pair (q : PairQuestion params)

/-- The corresponding answer types for point, line, and pair questions. -/
inductive Answer (params : Params R ι) where
  | point (a : R)
  | line (g : LineAnswer params)
  | pair (a b : R)

/-- The line through `u` in the chosen direction. -/
def lineThrough (params : Params R ι) (u : Point params)
    (axis : Fin params.tensorPower) : LineQuestion params :=
  AxisParallelLine.through u axis

/-- Read the base-code answer at the coordinate specified by a grid point on a line. -/
def lineAnswerAt (params : Params R ι) (ℓ : LineQuestion params)
    (u : Point params) (g : LineAnswer params) : R :=
  (g : ι → R) (u ℓ.axis)

/-- The acceptance condition of the line-vs-point part of the tensor code test. -/
def LineVsPointAccepts (params : Params R ι) (ℓ : LineQuestion params)
    (u : Point params) (g : LineAnswer params) (a : R) : Prop :=
  u ∈ ℓ.carrier ∧ lineAnswerAt params ℓ u g = a

end Basic

end TensorCodeTest

end MIPStarRE.Games
