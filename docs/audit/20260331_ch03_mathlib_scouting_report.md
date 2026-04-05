# 2026-03-31 — Chapter 3 Mathlib Scouting Report

## Scope and method

This memo scouts the Chapter 3 proposition list from PR issue context and classifies each item as:

- **found in Mathlib**
- **partially available**
- **needs ground-up local development**

I checked two surfaces:

1. **Mathlib-facing API already vendored in this repo**, especially additive-character and polynomial toolchains.
2. **Current local LDT preliminaries scaffold** (`MIPStarRE/LDT/Preliminaries/Theorems.lean`, plus operator inequalities in `MIPStarRE/LDT/Basic/Operator.lean`).

---

## Classification by proposition

## A) Fourier / finite field facts

### `prop:fourier-fact-scalar` (Prop 4.30)
**Claim sketch:** `E[ω^{tr[x*a]}] = δ_{a,0}` over finite field.

**Classification:** **partially available**.

**What is available now:**
- `AddChar.sum_eq_zero_of_ne_one`
- `AddChar.sum_eq_card_of_eq_one`
- `AddChar.sum_mulShift`
- `AddChar.FiniteField.primitiveChar_to_Complex`

These give exactly the finite additive-character sum vanishing/non-vanishing primitives needed for the scalar orthogonality argument. The repo does **not** yet expose the paper-shaped expectation/delta corollary as a named theorem.

**Mathlib declarations and import path:**
- Declarations: in namespace `AddChar`
- Module: `Mathlib.NumberTheory.LegendreSymbol.AddCharacter`
- Add import:
  ```lean
  import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
  ```

---

### `prop:fourier-fact-vector` (Prop 4.65)
**Claim sketch:** vector-space Fourier orthogonality over `F_q^m`.

**Classification:** **partially available**.

**What is available now:**
- Same additive-character sum infrastructure as above (`sum_mulShift`, primitive chars, trace-to-complex setup).

**Gap:**
- No ready-made theorem in Mathlib with the exact `F_q^m` “delta under averaging over vectors” formulation under paper notation/normalization.
- Need a local wrapper converting vector indexing conventions into the reusable `AddChar` sum identities.

**Mathlib declarations and import path:**
- Use `Mathlib.NumberTheory.LegendreSymbol.AddCharacter` (same import as scalar fact).

---

### `lem:schwartz-zippel-total-degree`
**Claim sketch:** Schwartz–Zippel style bound by total degree.

**Classification:** **partially available**.

**What is available now:**
- `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset` (Combinatorial Nullstellensatz direction).
- Homogeneous/evaluation machinery in `Mathlib.RingTheory.MvPolynomial.Homogeneous` (`exists_eval_ne_zero_of_totalDegree_le_card_aux`, etc.).

**Gap:**
- No direct theorem named/packaged as “Schwartz–Zippel with explicit probability bound” in current API.
- Need local theorem layer translating finite-set cardinal estimates into the exact paper inequality statement.

**Mathlib declarations and import paths:**
- `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset`
  ```lean
  import Mathlib.Combinatorics.Nullstellensatz
  ```
- Supporting total-degree infrastructure:
  ```lean
  import Mathlib.RingTheory.MvPolynomial.Homogeneous
  ```

---

## B) Distance / consistency toolbox

### `prop:triangle-sub` (Prop 4.370)
**Classification:** **partially available**.

**Available local ingredients:**
- `stateDependentDistanceRel_triangle` (currently private)
- `ev_diff_triangle`
- `normalizedTrace_triangle`

These are the correct quantitative shape but still need a public paper-level theorem for the specific `simeq/approx` transfer statement.

---

### `prop:easy-approx-from-approx-delta` (Prop 4.547)
**Classification:** **needs ground-up local development**.

**Reasoning:**
- No theorem with this label or obvious equivalent currently appears in local preliminaries; only nearby bridge lemmas are present.

---

### `prop:Cab-approx-delta` (Prop 4.570)
**Classification:** **needs ground-up local development**.

**Reasoning:**
- No local theorem appears for this `C_{a,b}`-specific stability statement.

---

### `prop:triangle-inequality-for-vectors-squared` (Prop 4.596)
**Classification:** **partially available**.

**Available now:**
- Operator-level squared-distance triangle inequality: `ev_diff_triangle`.

**Gap:**
- Need explicit vector/family-averaged specialization in the exact chapter notation.

---

### `prop:triangle-inequality-for-approx_delta` (Prop 4.622)
**Classification:** **partially available**.

**Available now:**
- `stateDependentDistanceRel_triangle` proves the right structural inequality for `SDDRel`.

**Gap:**
- The lemma is private and not exported as the paper proposition statement (`approx_delta`-named public theorem).

---

### `prop:simeq-triangle-inequality` (Prop 4.653)
**Classification:** **needs ground-up local development**.

**Reasoning:**
- No direct theorem with this proposition label in `Preliminaries/Theorems.lean`.
- Existing triangle infrastructure is for `SDDRel`; conversion back to `simeq` chain still needs formalization.

---

## C) Self-consistency toolbox

### `prop:cons-sub-meas-details` (Prop 4.709)
**Classification:** **partially available**.

**Available now:**
- `theorem consSubMeas` already exists and packages diagonal/sandwich/combined control.

**Gap:**
- May still require proposition-specific “details” corollaries in paper notation.

---

### `prop:other-two-notions-of-self-consistency`
**Classification:** **partially available**.

**Available now:**
- `theorem twoNotionsOfSelfConsistency` directly matches “strong SC implies self-closeness (`A` vs `A`) up to constants”.

---

### `prop:two-notions-of-self-consistency-after-evaluation`
**Classification:** **needs ground-up local development**.

**Reasoning:**
- No explicit “after evaluation” theorem currently visible in preliminaries scaffolding.

---

### `prop:completeness-transfer-self-consistent-A`
**Classification:** **partially available**.

**Available now:**
- `theorem completenessTransferProjectiveP`
- `theorem completingToMeasurement`

**Gap:**
- Need dedicated “self-consistent A” transfer statement wiring these pieces in the exact chapter form.

---

### `prop:self-consistency-implies-data-processing`
**Classification:** **partially available**.

**Available now:**
- `theorem simeqDataProcessing` (consistency relation form).

**Gap:**
- If chapter statement is on the self-consistency object/notation directly, a wrapper theorem is still needed.

---

### `prop:cool-prop` (Prop 4.1115)
**Classification:** **needs ground-up local development**.

**Reasoning:**
- No theorem in current local files appears to target the sum-of-squares lower bound under self-consistency with `zeta`-loss.

---

## Recommended next 3 formalization sub-issues / code bundles

### Bundle 1 — Finite-field Fourier wrappers + scalar/vector orthogonality
**Target declarations to add (proposed names):**
- `fourierFactScalar_delta`
- `fourierFactVector_delta`
- helper `addChar_expectation_eq_delta`

**Primary file target:**
- `MIPStarRE/LDT/Preliminaries/FourierFacts.lean` (new)

**Main imports:**
```lean
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.FieldTheory.Finite.Basic
```

**Deliverables:** close `prop:fourier-fact-scalar` and `prop:fourier-fact-vector` with paper-shaped wrappers.

---

### Bundle 2 — Schwartz–Zippel local theorem layer
**Target declarations to add (proposed names):**
- `schwartzZippel_totalDegree_bound`
- `schwartzZippel_nonzero_eval_exists`

**Primary file target:**
- `MIPStarRE/LDT/Preliminaries/SchwartzZippel.lean` (new)

**Main imports:**
```lean
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.RingTheory.MvPolynomial.Homogeneous
```

**Deliverables:** close `lem:schwartz-zippel-total-degree` with explicit finite probability/cardinality corollaries used downstream.

---

### Bundle 3 — Public distance/self-consistency triangle & transfer API
**Target declarations to add/refactor:**
- make/export public theorem replacing private `stateDependentDistanceRel_triangle`
- `triangleInequalityForApproxDelta`
- `simeqTriangleInequality`
- `twoNotionsOfSelfConsistencyAfterEvaluation`
- `selfConsistencyImpliesDataProcessing` (wrapper over existing `simeqDataProcessing` if needed)

**Primary file target:**
- `MIPStarRE/LDT/Preliminaries/Theorems.lean` (extend)
- optional split: `MIPStarRE/LDT/Preliminaries/TriangleAndTransfer.lean` (new)

**Deliverables:** close most of the Chapter-3 distance/self-consistency proposition cluster with stable public names.

---

## Quick import shortlist for Chapter 3 work

```lean
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.RingTheory.MvPolynomial.Homogeneous
```

(Additional linear-algebra/analysis imports can be deferred until individual proof files are created.)
