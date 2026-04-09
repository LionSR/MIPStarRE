# ConsRel Check Against the Paper

Issue: #238

## Scope

This report compares the Lean definition of `ConsRel` with Definition 4.8 (`def:simeq`) in the LDT paper, checks the helper definitions it depends on, and audits the codebase for uses of `ConsRel` that may not respect the paper's left/right convention.

Main paper references:

- `references/ldt-paper/preliminaries.tex`, Definition 4.8, lines 255-268
- `blueprint/src/chapter/ch03_preliminaries.tex`, lines 156-166

Main Lean references:

- `MIPStarRE/LDT/Test/Defs.lean`, lines 140-212
- `MIPStarRE/LDT/Basic/Operator.lean`, lines 44-67
- `MIPStarRE/LDT/Basic/SubMeasurement.lean`, lines 515-537

## Executive Summary

The core Lean definition of `ConsRel` matches the paper's Definition 4.8.

- `qBipartiteMatchMass` computes the diagonal term `∑_a ⟨ψ|A_a ⊗ B_a|ψ⟩`.
- `qBipartiteConsDefect` computes the off-diagonal mass
  `∑_{a ≠ b} ⟨ψ|A_a ⊗ B_b|ψ⟩`,
  written as
  `max 0 (⟨ψ|A_total ⊗ B_total|ψ⟩ - ∑_a ⟨ψ|A_a ⊗ B_a|ψ⟩)`.
- The tensor placement is correct: the first argument is on the left tensor factor and the second argument is on the right tensor factor.
- Most downstream uses follow this convention.

However, I found one important downstream mismatch:

- `MIPStarRE/LDT/Test/MainTheorem.lean`, lines 44-46, does not literally encode the paper's second consistency clause from `thm:main-formal`.

## 1. Paper Definition vs Lean Definition

The paper says:

> `A_a^x ⊗ I ≃_δ I ⊗ B_a^x` iff
> `E_{x~D} Σ_{a≠b} ⟨ψ| A_a^x ⊗ B_b^x |ψ⟩ ≤ δ`.

Source:

- `references/ldt-paper/preliminaries.tex`, lines 255-268
- `blueprint/src/chapter/ch03_preliminaries.tex`, lines 156-166

The Lean definition is:

- `qBipartiteMatchMass` in `MIPStarRE/LDT/Test/Defs.lean`, lines 140-145
- `qBipartiteConsDefect` in `MIPStarRE/LDT/Test/Defs.lean`, lines 154-160
- `bipartiteConsError` in `MIPStarRE/LDT/Test/Defs.lean`, lines 163-169
- `ConsRel` in `MIPStarRE/LDT/Test/Defs.lean`, lines 205-212

So Lean defines:

```lean
qBipartiteMatchMass ψ A B := ∑ a, ev ψ (opTensor (A.outcome a) (B.outcome a))

qBipartiteConsDefect ψ A B :=
  let totalOverlap := ev ψ (opTensor A.total B.total)
  max 0 (totalOverlap - qBipartiteMatchMass ψ A B)

bipartiteConsError ψ 𝒟 A B :=
  avgOver 𝒟 (fun q => qBipartiteConsDefect ψ (A q) (B q))

ConsRel ψ 𝒟 A B δ :=
  bipartiteConsError ψ 𝒟 A B ≤ δ
```

This is the right shape for the paper definition.

## 2. Does `bipartiteConsError` Compute the Paper's Off-Diagonal Sum?

Yes.

For a fixed question `x`, Lean computes

```text
qBipartiteConsDefect ψ (A x) (B x)
  = max 0 (⟨ψ|A^x_total ⊗ B^x_total|ψ⟩ - ∑_a ⟨ψ|A^x_a ⊗ B^x_a|ψ⟩).
```

Since `A.total = ∑_a A_a` and `B.total = ∑_b B_b`, this expands to

```text
⟨ψ|(∑_a A_a) ⊗ (∑_b B_b)|ψ⟩ - ∑_a ⟨ψ|A_a ⊗ B_a|ψ⟩
= ∑_{a,b} ⟨ψ|A_a ⊗ B_b|ψ⟩ - ∑_a ⟨ψ|A_a ⊗ B_a|ψ⟩
= ∑_{a≠b} ⟨ψ|A_a ⊗ B_b|ψ⟩.
```

Why the `max 0` does not change the intended value:

- each `A_a` and `B_b` is PSD by the `SubMeas` structure
- `opTensor A_a B_b` is PSD
- hence each term `ev ψ (A_a ⊗ B_b)` is nonnegative
- so the off-diagonal sum is already nonnegative

This means the Lean formula is mathematically the same quantity as the paper's `Σ_{a≠b}` expression.

Conclusion:

- `qBipartiteConsDefect` is the paper's off-diagonal consistency error
- `bipartiteConsError` is its expectation over questions
- `ConsRel` is exactly the corresponding `≤ δ` relation

## 3. Is the Tensor Placement Correct?

Yes.

The tensor primitives are:

- `opTensor A B = Matrix.kronecker A B`
  in `MIPStarRE/LDT/Basic/Operator.lean`, lines 44-48
- `leftTensor A = A ⊗ I`
  in `MIPStarRE/LDT/Basic/Operator.lean`, lines 50-53
- `rightTensor B = I ⊗ B`
  in `MIPStarRE/LDT/Basic/Operator.lean`, lines 55-58
- `leftTensor_mul_rightTensor_eq_opTensor`
  in `MIPStarRE/LDT/Basic/Operator.lean`, lines 61-67

The placement wrappers are:

- `leftPlacedSubMeas`
  in `MIPStarRE/LDT/Basic/SubMeasurement.lean`, lines 515-528
- `rightPlacedSubMeas`
  in `MIPStarRE/LDT/Basic/SubMeasurement.lean`, lines 531-537

And the bridge theorem states:

```lean
qBipartiteConsDefect ψ A B =
  qConsDefect ψ (leftPlacedSubMeas A) (rightPlacedSubMeas B)
```

Source:

- `MIPStarRE/LDT/Test/Defs.lean`, lines 173-182

Likewise for the averaged error:

```lean
bipartiteConsError ψ 𝒟 A B =
  consError ψ 𝒟
    (fun q => leftPlacedSubMeas (A q))
    (fun q => rightPlacedSubMeas (B q))
```

Source:

- `MIPStarRE/LDT/Test/Defs.lean`, lines 186-198

So the argument order is unambiguous:

- first family = left tensor factor
- second family = right tensor factor

This matches the paper's notation
`A_a^x ⊗ I ≃_δ I ⊗ B_a^x`.

## 4. Usage Audit

I checked all `ConsRel` uses returned by ripgrep across `MIPStarRE/LDT`.

### 4.1 Clearly consistent uses

These files use `ConsRel` or `bipartiteConsError` in a way that matches the paper convention:

- `MIPStarRE/LDT/Test/Strategy.lean`, lines 112-142 and 177-195
  The comments explicitly say the first family acts on the left register and the second on the right. The definitions match that commentary.
- `MIPStarRE/LDT/MainInductionStep/Defs.lean`, lines 48-118
  Same left/right convention for point-vs-line families.
- `MIPStarRE/LDT/CommutativityPoints/Theorem.lean`, especially lines 61-64 and 106-109
  The proof uses `bipartiteConsError_eq_consError_placed`, which preserves left/right order explicitly.
- `MIPStarRE/LDT/Preliminaries/Theorems.lean`
  The bridge from `ConsRel` to `BipartiteSDDRel` is always via left-placement for the first family and right-placement for the second.
- `MIPStarRE/LDT/Preliminaries/Triangles.lean`
  Both triangle lemmas keep the first family on the left and the second on the right; they rewrite through the placement bridge rather than silently swapping arguments.
- `MIPStarRE/LDT/Preliminaries/SelfConsistency.lean`, lines 74-158
  `otherTwoNotionsOfSelfConsistency` uses `ConsRel ψ 𝒟 A A` and rewrites it to left/right placements of the same family, which is consistent with the bipartite reading.
- `MIPStarRE/LDT/Pasting/Statements.lean`, lines 282-299
  The statements for `h-b-consistency` and `h-a-consistency` put the pasted family in the first slot and the line/point family in the second slot, matching the paper's displayed formulas `H ⊗ I ≃ I ⊗ B` and `H ⊗ I ≃ I ⊗ A`.
- `MIPStarRE/LDT/Pasting/Theorems.lean`, lines 944-959
  `hAConsistency` follows the same `H ⊗ I ≃ I ⊗ A` orientation as the paper.

### 4.2 No hidden swap inside the helper APIs

I did not find any helper theorem redefining `ConsRel` as a symmetric relation.

In particular:

- the bridge theorem in `Test/Defs.lean` preserves order
- the strategy failure probabilities in `Test/Strategy.lean` preserve order
- the triangle and approximation theorems in `Preliminaries` preserve order

So if a theorem uses `ConsRel ψ 𝒟 X Y δ`, it really means:

```text
X on the left register, Y on the right register.
```

That directionality matters.

## 5. Concrete Mismatch Found

### `Test.mainFormal` does not literally match the paper's second clause

Paper statement:

- `references/ldt-paper/test_definition.tex`, lines 190-199
- `blueprint/src/chapter/ch02_test.tex`, lines 96-113

The paper says the two point-consistency conclusions are:

```text
A^{A,u}_a ⊗ I ≃_ν I ⊗ G^B_[g(u)=a]
I ⊗ A^{B,u}_a ≃_ν G^A_[g(u)=a] ⊗ I
```

But the Lean theorem `MIPStarRE/LDT/Test/MainTheorem.lean`, lines 40-50, states:

```lean
ConsRel ... strategy.pointMeasurementA ... (polynomialEvaluationFamily ... G_B)
∧ ConsRel ... strategy.pointMeasurementB ... (polynomialEvaluationFamily ... G_A)
∧ ConsRel ... G_A ... G_B
```

Using the established meaning of `ConsRel`, the second conjunct denotes

```text
A^{B,u}_a ⊗ I ≃_ν I ⊗ G^A_[g(u)=a],
```

not the paper's

```text
I ⊗ A^{B,u}_a ≃_ν G^A_[g(u)=a] ⊗ I.
```

Why this is a real mismatch:

- `ConsRel` is directional in Lean
- the bridge lemmas preserve that direction
- there is no general symmetry lemma turning `ConsRel ψ 𝒟 A B` into `ConsRel ψ 𝒟 B A`
- the doc comment immediately above the theorem already describes the paper's mirror-oriented clause, so the prose and theorem statement disagree locally

This is the only clear use-site mismatch I found.

## 6. Answers to the Key Questions

### Does `bipartiteConsError` compute `E_x Σ_{a≠b} ⟨ψ|A^x_a ⊗ B^x_b|ψ⟩`?

Yes.

It computes that quantity via

```text
E_x max 0 (⟨ψ|A^x_total ⊗ B^x_total|ψ⟩ - ∑_a ⟨ψ|A^x_a ⊗ B^x_a|ψ⟩),
```

which equals the off-diagonal sum because the outcomes are PSD submeasurement effects.

### Is the tensor placement correct?

Yes.

The code consistently uses:

- first argument on the left tensor factor
- second argument on the right tensor factor

This is backed by `opTensor`, `leftTensor`, `rightTensor`, `leftPlacedSubMeas`, `rightPlacedSubMeas`, and `bipartiteConsError_eq_consError_placed`.

### Are there any uses where the arguments are swapped?

I found one clear mismatch:

- `MIPStarRE/LDT/Test/MainTheorem.lean`, lines 44-46

The second conjunct of `mainFormal` is written in the opposite direction from the paper's displayed formula.

Aside from that theorem statement, the audited uses I checked respect the intended convention.

## 7. Bottom Line

`ConsRel` itself is paper-faithful.

The definition-level implementation is correct:

- correct tensor order
- correct diagonal term
- correct off-diagonal defect
- correct averaging over questions

The main follow-up item is not to change `ConsRel`, but to revisit the theorem statement of:

- `MIPStarRE/LDT/Test/MainTheorem.lean`, `mainFormal`

Its second consistency clause should be checked and likely rewritten if the goal is literal agreement with the paper's `I ⊗ A^{B,u}_a ≃ G^A_[g(u)=a] ⊗ I` statement.
