import MIPStarRE.LDT.Basic.AxisParallelLine

/-!
# Diagonal lines for the low individual degree test

Diagonal-line geometry and rebasing operations.

## References

- arXiv:2009.12982, Section 3 (low individual degree test, diagonal line
  questions).
-/

namespace MIPStarRE.LDT

/-- A genuinely affine diagonal line in `F_q^m`. -/
structure DiagonalLine (params : Parameters) where
  base : Point params
  direction : Point params
  deriving DecidableEq, Inhabited

namespace DiagonalLine

/-- The canonical affine parameterization `t ↦ base + t · direction`. -/
def pointAt {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) : Fq params → Point params :=
  fun t => addPoint ℓ.base (smulPoint t ℓ.direction)

/-- The support of the nonzero coordinates of a direction vector. -/
noncomputable def nonzeroDirectionSupport {params : Parameters} [FieldModel params.q]
    (v : Point params) : Finset (Fin params.m) :=
  Finset.univ.filter fun i => v i ≠ zeroCoord

/-- The least nonzero coordinate of a direction vector, when one exists. -/
noncomputable def firstNonzeroCoord? {params : Parameters} [FieldModel params.q]
    (v : Point params) : Option (Fin params.m) :=
  open Classical in
  let s := nonzeroDirectionSupport (params := params) v
  if hs : s.Nonempty then some (s.min' hs) else none

/-- Normalize a direction vector so its first nonzero coordinate becomes `1`. -/
noncomputable def normalizeDirection {params : Parameters} [FieldModel params.q]
    (v : Point params) : Point params :=
  open Classical in
  match firstNonzeroCoord? (params := params) v with
    | none => zeroPoint
    | some i => smulPoint (invCoord (v i)) v

/-- Canonical geometric diagonal line through `u` in direction `v`.

For nonzero `v`, we normalize by the first nonzero coordinate and shift the
base point so that this pivot coordinate is `0`. The degenerate `v = 0` case is
kept as the singleton line through `u`. -/
noncomputable def throughPointDirection {params : Parameters} [FieldModel params.q]
    (u v : Point params) : DiagonalLine params :=
  open Classical in
  match firstNonzeroCoord? (params := params) v with
    | none => { base := u, direction := zeroPoint }
    | some i =>
        let w := normalizeDirection (params := params) v
        let t := u i
        { base := fun j => subCoord (u j) (mulCoord t (w j))
          direction := w }

/-- Affine parameter of the sampled point on the canonical diagonal line through
`u` in direction `v`. -/
noncomputable def sampleParameter {params : Parameters} [FieldModel params.q]
    (u v : Point params) : Fq params :=
  open Classical in
  match firstNonzeroCoord? (params := params) v with
    | none => zeroCoord
    | some i => u i

@[simp] theorem throughPoint_pointAt_sampleParameter {params : Parameters}
    [FieldModel params.q] (u : Point params) (i : Fin params.m) :
    (AxisParallelLine.throughPoint (params := params) u i).pointAt
        (AxisParallelLine.sampleParameter (params := params) u i) = u := by
  funext j
  by_cases h : j = i
  · subst h
    unfold AxisParallelLine.pointAt AxisParallelLine.throughPoint
    simp [AxisParallelLine.sampleParameter, addCoord, zeroCoord]
  · simp [AxisParallelLine.throughPoint, AxisParallelLine.pointAt, h]

@[simp] theorem throughPointDirection_pointAt_sampleParameter {params : Parameters}
    [FieldModel params.q] (u v : Point params) :
    (DiagonalLine.throughPointDirection (params := params) u v).pointAt
        (DiagonalLine.sampleParameter (params := params) u v) = u := by
  classical
  unfold DiagonalLine.throughPointDirection DiagonalLine.sampleParameter
  split
  · funext j
    simp [DiagonalLine.pointAt, addPoint, smulPoint, zeroPoint,
      zeroCoord, addCoord, mulCoord]
  · rename_i i
    funext j
    simp [DiagonalLine.pointAt, addPoint, smulPoint, subCoord, addCoord, mulCoord]

/-- Rebase a diagonal line so that the old point `ℓ.pointAt t` becomes the new base point. -/
def rebaseAt {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t : Fq params) : DiagonalLine params where
  base := ℓ.pointAt t
  direction := ℓ.direction

@[simp] theorem rebaseAt_pointAt_zero {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t : Fq params) :
    (rebaseAt ℓ t).pointAt zeroCoord = ℓ.pointAt t := by
  ext i
  simp [rebaseAt, pointAt, addPoint, smulPoint, addCoord, mulCoord, zeroCoord]

theorem rebaseAt_pointAt {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t s : Fq params) :
    (rebaseAt ℓ t).pointAt s = ℓ.pointAt (addCoord t s) := by
  funext i
  suffices
      addCoord (addCoord (ℓ.base i) (mulCoord t (ℓ.direction i)))
          (mulCoord s (ℓ.direction i)) =
        addCoord (ℓ.base i) (mulCoord (addCoord t s) (ℓ.direction i)) by
    simpa [rebaseAt, pointAt, addPoint, smulPoint] using this
  change
    encodeScalar
        (decodeScalar
            (encodeScalar
              (decodeScalar (ℓ.base i) +
                decodeScalar (encodeScalar (decodeScalar t * decodeScalar (ℓ.direction i))))) +
          decodeScalar (encodeScalar (decodeScalar s * decodeScalar (ℓ.direction i)))) =
      encodeScalar
        (decodeScalar (ℓ.base i) +
          decodeScalar
            (encodeScalar
              (decodeScalar (encodeScalar (decodeScalar t + decodeScalar s)) *
                decodeScalar (ℓ.direction i))))
  simp only [decode_encodeScalar]
  congr 1
  ring_nf

@[simp] theorem rebaseAt_zero {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) :
    rebaseAt ℓ zeroCoord = ℓ := by
  cases ℓ with
  | mk base direction =>
      change
        ({ base :=
             ({ base := base, direction := direction } : DiagonalLine params).pointAt zeroCoord,
           direction := direction } : DiagonalLine params) =
        ({ base := base, direction := direction } : DiagonalLine params)
      congr
      funext i
      simp [pointAt, addPoint, smulPoint, addCoord, mulCoord, zeroCoord]

theorem rebaseAt_rebase {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t s : Fq params) :
    rebaseAt (rebaseAt ℓ t) s = rebaseAt ℓ (addCoord t s) := by
  cases ℓ with
  | mk base direction =>
      change
        ({ base :=
             (rebaseAt
               ({ base := base, direction := direction } : DiagonalLine params) t).pointAt s,
           direction := direction } : DiagonalLine params) =
        ({ base :=
             ({ base := base, direction := direction } : DiagonalLine params).pointAt
               (addCoord t s),
           direction := direction } : DiagonalLine params)
      exact congrArg
        (fun b => ({ base := b, direction := direction } : DiagonalLine params))
        (rebaseAt_pointAt { base := base, direction := direction } t s)

/-- Embed a diagonal line into the slice at height `x`, keeping the new coordinate fixed. -/
def appendAtHeight (params : Parameters) [FieldModel params.q]
    (ℓ : DiagonalLine params) (x : Fq params) : DiagonalLine params.next where
  base := appendPoint params ℓ.base x
  direction := appendPoint params ℓ.direction zeroCoord

@[simp] theorem appendAtHeight_rebaseAt {params : Parameters} [FieldModel params.q]
    (ℓ : DiagonalLine params) (t x : Fq params) :
    appendAtHeight params (rebaseAt ℓ t) x =
      rebaseAt (appendAtHeight params ℓ x) t := by
  cases ℓ with
  | mk base direction =>
      change
        ({ base := appendPoint params (addPoint base (smulPoint t direction)) x,
           direction := appendPoint params direction zeroCoord } : DiagonalLine params.next) =
        ({ base := addPoint (appendPoint params base x)
             (smulPoint t (appendPoint params direction zeroCoord)),
           direction := appendPoint params direction zeroCoord } : DiagonalLine params.next)
      congr
      funext i
      by_cases hi : i.1 < params.m
      · have hleft :
            appendPoint params (addPoint base (smulPoint t direction)) x i =
              addCoord (base ⟨i.1, hi⟩) (mulCoord t (direction ⟨i.1, hi⟩)) := by
          simp [appendPoint, addPoint, smulPoint, hi]
        have hright :
            addPoint (appendPoint params base x)
                (smulPoint t (appendPoint params direction zeroCoord)) i =
              addCoord (base ⟨i.1, hi⟩) (mulCoord t (direction ⟨i.1, hi⟩)) := by
          simp [appendPoint, addPoint, smulPoint, hi]
          congr
        rw [hleft, hright]
      · have hleft :
            appendPoint params (addPoint base (smulPoint t direction)) x i = x := by
          simp [appendPoint, hi]
        have hright :
            addPoint (appendPoint params base x)
                (smulPoint t (appendPoint params direction zeroCoord)) i =
              addCoord x (mulCoord t zeroCoord) := by
          simp [appendPoint, addPoint, smulPoint, hi]
          rfl
        rw [hleft, hright]
        change x = addCoord x (mulCoord t zeroCoord)
        rw [← encode_decodeScalar x]
        unfold addCoord mulCoord zeroCoord
        simp only [decode_encodeScalar]
        congr 1
        ring_nf

end DiagonalLine

end MIPStarRE.LDT
