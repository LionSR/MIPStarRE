import MIPStarRE.LDT.Basic.ParametersBase

/-!
# Axis-parallel lines for the low individual degree test

Axis-parallel line geometry on top of the core parameter infrastructure.
-/

namespace MIPStarRE.LDT

/-- A genuinely axis-parallel affine line in `F_q^m`. -/
structure AxisParallelLine (params : Parameters) where
  base : Point params
  direction : Fin params.m
  deriving DecidableEq, Inhabited

namespace AxisParallelLine

/-- The canonical affine parameterization `t ↦ base + t e_i`. -/
def pointAt {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) : Fq params → Point params :=
  fun t i =>
    if i = ℓ.direction then
      addCoord (ℓ.base i) t
    else
      ℓ.base i

/-- Canonical geometric axis-parallel line through `u` in direction `i`.

The representative stores zero in the moving coordinate, so all points on the
same geometric line map to the same `AxisParallelLine`. -/
def throughPoint {params : Parameters} [FieldModel params.q]
    (u : Point params) (i : Fin params.m) : AxisParallelLine params where
  base := fun j => if j = i then zeroCoord else u j
  direction := i

/-- Affine parameter of the sampled point on the canonical axis-parallel line
through `u` in direction `i`. -/
def sampleParameter {params : Parameters} [FieldModel params.q]
    (u : Point params) (i : Fin params.m) : Fq params :=
  u i

/-- Rebase an axis-parallel line so that the old point `ℓ.pointAt t` becomes the new base point. -/
def rebaseAt {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) (t : Fq params) : AxisParallelLine params where
  base := ℓ.pointAt t
  direction := ℓ.direction

@[simp] theorem rebaseAt_pointAt_zero {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) (t : Fq params) :
    (rebaseAt ℓ t).pointAt zeroCoord = ℓ.pointAt t := by
  ext i
  simp [rebaseAt, pointAt, addCoord, zeroCoord]

@[simp] theorem rebaseAt_zero {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) :
    rebaseAt ℓ zeroCoord = ℓ := by
  cases ℓ with
  | mk base direction =>
      change
        ({ base :=
             ({ base := base, direction := direction } : AxisParallelLine params).pointAt zeroCoord,
           direction := direction } : AxisParallelLine params) =
        ({ base := base, direction := direction } : AxisParallelLine params)
      congr
      funext i
      simp [pointAt, addCoord, zeroCoord]

@[simp] theorem rebaseAt_direction {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) (t : Fq params) :
    (rebaseAt ℓ t).direction = ℓ.direction :=
  rfl

/-- Embed an axis-parallel line into the slice at height `x`. -/
def appendAtHeight (params : Parameters)
    (ℓ : AxisParallelLine params) (x : Fq params) : AxisParallelLine params.next where
  base := appendPoint params ℓ.base x
  direction := embedCoord params ℓ.direction

@[simp] theorem appendAtHeight_rebaseAt {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) (t x : Fq params) :
    appendAtHeight params (rebaseAt ℓ t) x =
      rebaseAt (appendAtHeight params ℓ x) t := by
  cases ℓ with
  | mk base direction =>
      change
        ({ base :=
             appendPoint params
               (({ base := base, direction := direction } : AxisParallelLine params).pointAt t) x,
           direction := embedCoord params direction } : AxisParallelLine params.next) =
        ({ base :=
             ({ base := appendPoint params base x,
                direction := embedCoord params direction } :
                AxisParallelLine params.next).pointAt t,
           direction := embedCoord params direction } : AxisParallelLine params.next)
      congr
      funext i
      by_cases hdir : i = embedCoord params direction
      · subst i
        simp [appendPoint, pointAt, embedCoord]
        rfl
      · by_cases hi : i.1 < params.m
        · have hdir' : (⟨i.1, hi⟩ : Fin params.m) ≠ direction := by
            intro h
            apply hdir
            apply Fin.ext
            simpa [embedCoord] using congrArg Fin.val h
          simp [appendPoint, pointAt, hi, hdir, hdir']
        · simp [appendPoint, pointAt, hi, hdir]

end AxisParallelLine

end MIPStarRE.LDT
