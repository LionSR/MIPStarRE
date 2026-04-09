# Issue #135: OpFamily Scoping Report

## Summary

I checked the requested files and the nearby `OpFamily` stack.

The core issue is real: [`SubMeas`](../../MIPStarRE/LDT/Basic/SubMeasurement.lean) requires
PSD outcomes and a total bounded by the identity, so an ordered product
`A_a * B_b` cannot in general be packaged as a `SubMeas` without extra
commutation or positivity hypotheses. In the current codebase, though, the raw
family infrastructure for this has already been introduced:

- [`MIPStarRE/LDT/Basic/OpFamily.lean`](../../MIPStarRE/LDT/Basic/OpFamily.lean)
  defines `OpFamily`, `IdxOpFamily`, `SubMeas.toOpFamily`,
  `IdxSubMeas.toIdxOpFamily`, `OpFamily.leftPlacedOpFamily`,
  `OpFamily.rightPlacedOpFamily`, and `OpFamily.postprocess`.
- [`MIPStarRE/LDT/Test/Defs.lean`](../../MIPStarRE/LDT/Test/Defs.lean)
  already provides the raw-metric layer `qSDDOp`, `sddErrorOp`, and
  `SDDOpRel`.
- [`MIPStarRE/LDT/CommutativityPoints/Defs.lean`](../../MIPStarRE/LDT/CommutativityPoints/Defs.lean)
  already defines `orderedProductOpFamily` and `reversedProductOpFamily` as
  raw families, and the downstream Section 10 constructions already return
  `IdxOpFamily` where appropriate.

So issue #135 is not blocked on inventing `OpFamily`. The real remaining work is
to finish centralizing and using the raw-family layer consistently.

## Findings

### 1. `SubMeas` is genuinely too strong for raw ordered products

[`MIPStarRE/LDT/Basic/SubMeasurement.lean:18`](../../MIPStarRE/LDT/Basic/SubMeasurement.lean#L18)
defines `SubMeas` with fields:

- `outcome_pos : ∀ a, 0 ≤ outcome a`
- `sum_eq_total : ∑ a, outcome a = total`
- `total_le_one : total ≤ 1`

This means any constructor returning `SubMeas` must prove PSD and `≤ 1`.
For ordered products `A_a * B_b`, that is false in general unless extra
hypotheses are added. This matches the problem description.

### 2. `OpFamily` already exists as the right raw layer

[`MIPStarRE/LDT/Basic/OpFamily.lean:24`](../../MIPStarRE/LDT/Basic/OpFamily.lean#L24)
defines the raw family:

- `structure OpFamily (α : Type*) (ι : Type*)`

and immediately provides the needed forgetful bridges:

- [`SubMeas.toOpFamily`](../../MIPStarRE/LDT/Basic/OpFamily.lean#L36)
- [`IdxSubMeas.toIdxOpFamily`](../../MIPStarRE/LDT/Basic/OpFamily.lean#L52)

It also already contains the tensor-placement and postprocessing helpers used by
the commutativity development.

### 3. The active ordered/reversed product defs are already raw, not `SubMeas`

[`MIPStarRE/LDT/CommutativityPoints/Defs.lean:66`](../../MIPStarRE/LDT/CommutativityPoints/Defs.lean#L66)
and
[`MIPStarRE/LDT/CommutativityPoints/Defs.lean:88`](../../MIPStarRE/LDT/CommutativityPoints/Defs.lean#L88)
define:

- `orderedProductOpFamily`
- `reversedProductOpFamily`

Both return `OpFamily`, not `SubMeas`. Their only theorem is the algebraic
identity `sum outcome = total`, which is exactly the right level.

I did not find any surviving `orderedProductSubMeas` or `reversedProductSubMeas`
in the requested files or nearby commutativity files.

### 4. `CommutativityPoints/Defs.lean` does not contain the feared PSD `sorry`s

I checked the places the task called out. In
[`MIPStarRE/LDT/CommutativityPoints/Defs.lean`](../../MIPStarRE/LDT/CommutativityPoints/Defs.lean),
the ordered/reversed product constructions are already raw and have no `sorry`
proofs.

The `SubMeas`-valued constructions that remain there are the ones that are
actually mathematically valid as submeasurements:

- `tensorProductSubMeas`
- `pointDiagonalLineMixedProductLeft`
- `pointDiagonalLineMixedProductRight`

Those use tensor products of PSD effects, so they are not the problematic part
of issue #135.

### 5. Section 11 defs are already mostly migrated to `IdxOpFamily`

[`MIPStarRE/LDT/Commutativity/Defs.lean`](../../MIPStarRE/LDT/Commutativity/Defs.lean)
already returns `IdxOpFamily` for the raw ordered/reversed product objects:

- `evaluatedSliceProductLeft` at
  [`:169`](../../MIPStarRE/LDT/Commutativity/Defs.lean#L169)
- `evaluatedSliceProductRight` at
  [`:179`](../../MIPStarRE/LDT/Commutativity/Defs.lean#L179)
- `evaluatedSlicePointMeasurementProduct` at
  [`:220`](../../MIPStarRE/LDT/Commutativity/Defs.lean#L220)
- `fullSliceProductLeft` at
  [`:243`](../../MIPStarRE/LDT/Commutativity/Defs.lean#L243)
- `fullSliceProductRight` at
  [`:253`](../../MIPStarRE/LDT/Commutativity/Defs.lean#L253)
- all four `commDataProcessedGStability*` families at
  [`:330`](../../MIPStarRE/LDT/Commutativity/Defs.lean#L330),
  [`:348`](../../MIPStarRE/LDT/Commutativity/Defs.lean#L348),
  [`:362`](../../MIPStarRE/LDT/Commutativity/Defs.lean#L362),
  [`:379`](../../MIPStarRE/LDT/Commutativity/Defs.lean#L379)

This is already the correct direction for issue #135.

### 6. The remaining `sorry`s are theorem-layer bridge gaps, not bad raw defs

The current `sorry`s in
[`MIPStarRE/LDT/Commutativity/Theorems.lean`](../../MIPStarRE/LDT/Commutativity/Theorems.lean)
are at:

- [`:153`](../../MIPStarRE/LDT/Commutativity/Theorems.lean#L153)
- [`:159`](../../MIPStarRE/LDT/Commutativity/Theorems.lean#L159)
- [`:165`](../../MIPStarRE/LDT/Commutativity/Theorems.lean#L165)
- [`:171`](../../MIPStarRE/LDT/Commutativity/Theorems.lean#L171)
- [`:350`](../../MIPStarRE/LDT/Commutativity/Theorems.lean#L350)

These are not PSD-proof holes for ordered products. They are missing bridge
proofs that should compare `IdxOpFamily` objects via `SDDOpRel`, then transport
those comparisons through postprocessing and reindexing.

### 7. Section 10 already contains the bridge pattern Section 11 needs

[`MIPStarRE/LDT/CommutativityPoints/Theorem.lean`](../../MIPStarRE/LDT/CommutativityPoints/Theorem.lean)
already develops exactly the sort of raw-family machinery that Section 11 still
needs to reuse:

- direct `SDDOpRel` comparisons between raw placed families at
  [`:698`](../../MIPStarRE/LDT/CommutativityPoints/Theorem.lean#L698)
- a bridge from a raw ordered product to a genuine `IdxSubMeas` object via
  `IdxSubMeas.toIdxOpFamily` at
  [`:810`](../../MIPStarRE/LDT/CommutativityPoints/Theorem.lean#L810)
- triangle-inequality chaining on raw families at
  [`:1390`](../../MIPStarRE/LDT/CommutativityPoints/Theorem.lean#L1390)

This is a strong signal that Section 11 should be finished by reusing the raw
comparison style already established in Section 10, not by trying to upgrade the
ordered products back to `SubMeas`.

### 8. The main structural smell is location, not absence

The generic raw ordered-product helpers currently live in
[`MIPStarRE/LDT/CommutativityPoints/Defs.lean`](../../MIPStarRE/LDT/CommutativityPoints/Defs.lean),
while
[`MIPStarRE/LDT/Commutativity/Defs.lean`](../../MIPStarRE/LDT/Commutativity/Defs.lean)
imports `MIPStarRE.LDT.CommutativityPoints.Theorem` at the top to reach them.

That is backwards for infrastructure:

- Section 11 defs should not depend on a Section 10 theorem file.
- `orderedProductOpFamily` and `reversedProductOpFamily` are generic raw-family
  utilities, not point-commutativity-specific content.

## Recommendations

### Recommended scope for issue #135

1. Treat `Basic/OpFamily.lean` as the canonical raw-family layer.
2. Move `orderedProductOpFamily` and `reversedProductOpFamily` out of
   `CommutativityPoints/Defs.lean` into a basic infrastructure file.
   The best target is probably `MIPStarRE/LDT/Basic/OpFamily.lean`, unless you
   want to keep the file small and create a sibling like
   `MIPStarRE/LDT/Basic/OpFamilyProduct.lean`.
3. Move the purely generic algebraic lemmas
   `orderedProductOpFamily_sum_eq_total` and
   `reversedProductOpFamily_sum_eq_total` with them.
4. Update `Commutativity/Defs.lean`, `CommutativityPoints/Defs.lean`, and
   `Pasting/Sandwich.lean` to import the new infrastructure location directly.
5. Do not introduce any new `SubMeas` wrappers for ordered or reversed products.
   The raw `OpFamily` return type is already the mathematically honest one.

### Downstream API guidance

Use `IdxOpFamily` and `SDDOpRel` whenever the paper compares raw operator
expressions such as:

- `A_a B_b`
- `B_b A_a`
- weighted / postprocessed families with explicit square-root factors
- intermediate bridge families whose `total` is only a bookkeeping operator

Keep `SubMeas` only when the construction really preserves PSD and the
submeasurement bound, such as:

- tensor-placed POVMs
- tensor products of PSD effects
- sandwiched products `A_a B_b A_a`

### Concrete proof work implied by this scoping

After the helper move, the likely next proof steps are:

1. Add Section 11 bridge lemmas that mirror the successful Section 10 pattern in
   `CommutativityPoints/Theorem.lean`, but for
   `evaluatedSliceProductLeft/Right`,
   `commDataProcessedGStabilityOneLeft/Right`, and
   `commDataProcessedGStabilityTwoLeft/Right`.
2. Keep `postprocessedSelfConsistency` in
   `CommDataProcessedGConclusion` as `SDDRel`, since
   `evaluatedPointFamilyLeft/Right` are honest placed submeasurements.
3. Keep the other commutativity/stability theorem fields as `SDDOpRel`; they
   already have the right type.
4. Reuse `IdxSubMeas.toIdxOpFamily` at the exact bridge points where a valid
   `SubMeas` construction is compared against a raw ordered-product family.

## Bottom line

Issue #135 is already partially implemented.

The missing work is not "introduce `OpFamily` from scratch" and not "repair PSD
proofs for ordered products." The right scope is:

- promote the raw ordered-product helpers into basic infrastructure, and
- finish the theorem-level migration so Section 11 uses the existing
  `IdxOpFamily` / `SDDOpRel` bridge style consistently.
