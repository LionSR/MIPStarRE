---
title: "Stream E faithfulness scouting"
date: 2026-04-05
author: AI research assistant
purpose: >
  Faithfulness scouting for self-consistency extension propositions and their paper-level hypotheses.
status: snapshot
track: paper2009ldt
kind: scouting-report
---

# Stream E Faithfulness: Self-Consistency Extensions

## Executive take

The paper's SSC definition in `def:strong-self-consistency` is the bipartite overlap condition

`E_x Σ_a ⟨ψ, A_a^x ⊗ A_a^x ψ⟩ ≥ ⟨ψ, A ⊗ I ψ⟩ - δ`.

So for these five propositions, the faithful top-level hypothesis is almost always `BipartiteSSCRel`, not `SSCRel`.
`SSCRel` is the local square-based notion and is best treated as an internal bridge when a proof really needs `Σ_a ⟨ψ, A_a^2 ⊗ I ψ⟩`.

The paper states "permutation-invariant state" in all five propositions, but that assumption is only operationally needed for:

- `prop:two-notions-of-self-consistency-after-evaluation`
- `prop:self-consistency-implies-data-processing`

It is not genuinely used in the paper proofs of:

- `prop:other-two-notions-of-self-consistency`
- `prop:completeness-transfer-self-consistent-A`
- `prop:cool-prop`

For Lean API design, I would therefore keep `BipartiteSSCRel` everywhere, add `PermInvState` only where the proof actually needs it, and use `uniformDistribution Unit` plus `constSubMeasFamily` for the single-question proposition `prop:cool-prop`.

## Summary table

| Proposition | Paper SSC hypothesis | Best Lean hypothesis | Best Lean conclusion | Questioned? | `PermInvState` needed? |
| --- | --- | --- | --- | --- | --- |
| `other-two-notions` | overlap SSC | `BipartiteSSCRel` | `ConsRel` on left/right lifts | yes | no |
| `after-evaluation` | overlap SSC | `BipartiteSSCRel` | `SDDRel` on postprocessed left/right lifts | yes | yes |
| `completeness-transfer-self-consistent-A` | overlap SSC on `A` | `BipartiteSSCRel` on `A` plus same-side `SDDRel` between `A` and `B` | raw mass inequality | yes | no |
| `self-consistency-implies-data-processing` | overlap SSC on `A` | `BipartiteSSCRel` on `A` plus same-side `SDDRel` between `A` and projective `P` | `SDDRel` on postprocessed same-side lifts | yes | yes |
| `cool-prop` | overlap SSC | `BipartiteSSCRel` on a `Unit`-constant family | raw scalar inequality | no | no |

## 1. `prop:other-two-notions-of-self-consistency`

1. Paper SSC hypothesis form:
   Bipartite overlap SSC. It is exactly the paper's `E_x Σ_a ⟨ψ, A_a^x ⊗ A_a^x ψ⟩ ≥ ⟨ψ, A ⊗ I ψ⟩ - δ`.

2. Paper conclusion form:
   `≃_δ`, not `≈_δ`. So the target notion is consistency/off-diagonal mass, hence `ConsRel`, not `SDDRel`.

3. Paper state assumption:
   The proposition states permutation-invariance, but the proof itself does not use it. No `swap_ev` step appears.

4. Paper distribution:
   Question-indexed. The hypothesis is averaged over `x`, so this should use a general `Distribution Question`.

5. Best Lean hypothesis:
   `BipartiteSSCRel ψ 𝒟 A δ`.
   Reason: this is the exact wrapper for the paper's overlap-based SSC definition. `SSCRel` would already have replaced the paper's hypothesis by the stronger local square-based one.

6. Best Lean conclusion:
   `ConsRel ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftRight A) δ`.
   Reason: the paper conclusion is opposite-side consistency `A_a^x ⊗ I ≃_δ I ⊗ A_a^x`.

7. Proposed Lean signature:

```lean
theorem otherTwoNotionsOfSelfConsistency {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxSubMeas Question Outcome ι) (δ : Error) :
    BipartiteSSCRel ψ 𝒟 A δ →
      ConsRel ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftRight A) δ
```

8. Relation to existing theorems:
   This does not duplicate `twoNotionsOfSelfConsistency`. It is the sibling theorem with the weaker `≃_δ` conclusion instead of the already-formalized `≈_{2δ}` conclusion.

### Measurement converse

The paper says this is an iff for measurements. The clean Lean handling is:

- keep the submeasurement theorem above as the main theorem
- add a measurement-specialized iff corollary

```lean
theorem otherTwoNotionsOfSelfConsistency_iff_measurement {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (A : IdxMeas Question Outcome ι) (δ : Error) :
    BipartiteSSCRel ψ 𝒟 (IdxMeas.toIdxSubMeas A) δ ↔
      ConsRel ψ 𝒟
        (IdxSubMeas.liftLeft (IdxMeas.toIdxSubMeas A))
        (IdxSubMeas.liftRight (IdxMeas.toIdxSubMeas A))
        δ
```

That matches the paper without forcing the main theorem into an awkward "iff under extra completeness hypotheses" shape.

## 2. `prop:two-notions-of-self-consistency-after-evaluation`

1. Paper SSC hypothesis form:
   Again the bipartite overlap SSC hypothesis. It is still the definition from `def:strong-self-consistency`, before postprocessing.

2. Paper conclusion form:
   `≈_{2δ}` after postprocessing, so the target is `SDDRel`.

3. Paper state assumption:
   Permutation-invariance is genuinely used here. The proof rewrites the square expansion into `2 * (...)`, which is exactly the same `swap_ev` move used by the existing `twoNotionsOfSelfConsistency`.

4. Paper distribution:
   Question-indexed.

5. Best Lean hypothesis:
   `PermInvState ψ ∧ BipartiteSSCRel ψ 𝒟 A δ`, or equivalently separate arguments `hperm : PermInvState ψ` and `hssc : BipartiteSSCRel ψ 𝒟 A δ`.
   `SSCRel` is not the right public hypothesis because the paper starts from overlap SSC.

6. Best Lean conclusion:
   `SDDRel ψ 𝒟` between the postprocessed left and right lifts.

7. Proposed Lean signature:

```lean
theorem twoNotionsOfSelfConsistencyAfterEvaluation
    {Question α β : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hperm : PermInvState ψ)
    (A : IdxSubMeas Question α ι) (δ : Error) (f : α → β) :
    BipartiteSSCRel ψ 𝒟 A δ →
      SDDRel ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess (A q) f))
        (IdxSubMeas.liftRight (fun q => postprocess (A q) f))
        (2 * δ)
```

8. Relation to existing theorems:
   This extends `twoNotionsOfSelfConsistency`; it is not a duplicate. The likely proof is:
   first prove a postprocessing monotonicity lemma for `BipartiteSSCRel`, then apply the existing `twoNotionsOfSelfConsistency` to the postprocessed family.

## 3. `prop:completeness-transfer-self-consistent-A`

1. Paper SSC hypothesis form:
   Overlap SSC on `A`, not local square SSC.

2. Paper conclusion form:
   Raw scalar inequality
   `⟨ψ, B ⊗ I ψ⟩ ≥ ⟨ψ, A ⊗ I ψ⟩ - δ - 2√ε`.
   This is not a `ConsRel` or `SDDRel` conclusion.

3. Paper state assumption:
   The proposition states permutation-invariance, but the proof does not need it. It only uses the overlap term `Σ_a ⟨ψ, A_a ⊗ A_a ψ⟩` directly.

4. Paper distribution:
   Question-indexed. Both families `A` and `B` are indexed by question.

5. Best Lean hypothesis:
   `BipartiteSSCRel ψ 𝒟 A δ` plus same-side approximation
   `SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftLeft B) ε`.
   Reason: the paper compares `A_a^x ⊗ I` and `B_a^x ⊗ I`, so same-side left lifts are the faithful encoding.

6. Best Lean conclusion:
   A raw inequality on `idxSubMeasMass`, not a relation wrapper.

7. Proposed Lean signature:

```lean
theorem completenessTransferSelfConsistentA {Question Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : IdxSubMeas Question Outcome ι)
    (δ ε : Error) :
    BipartiteSSCRel ψ 𝒟 A δ →
    SDDRel ψ 𝒟 (IdxSubMeas.liftLeft A) (IdxSubMeas.liftLeft B) ε →
      idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft B) ≥
        idxSubMeasMass ψ 𝒟 (IdxSubMeas.liftLeft A) -
          δ - 2 * Real.sqrt ε
```

8. Relation to existing theorems:
   This is genuinely new. It is closest in spirit to `completenessTransferProjectiveP`, but it is not a duplicate because:
   `B` is arbitrary, not projective, and the hypothesis includes SSC on `A`.

## 4. `prop:self-consistency-implies-data-processing`

1. Paper SSC hypothesis form:
   Overlap SSC on `A`.

2. Paper conclusion form:
   Same-side postprocessed `≈` statement:
   `P^x_[f(a)=b] ⊗ I ≈_{8δ + 8√ε} A^x_[f(a)=b] ⊗ I`.
   So the target is `SDDRel` on left lifts of postprocessed families.

3. Paper state assumption:
   Permutation-invariance is genuinely needed overall, because the proof uses `prop:two-notions-of-self-consistency-after-evaluation`, and that step needs the left/right square-term symmetry.

4. Paper distribution:
   Question-indexed.

5. Best Lean hypothesis:
   `BipartiteSSCRel ψ 𝒟 A δ` plus same-side approximation between `A` and projective `P`.
   Here the most faithful comparison is still on left lifts. `SSCRel` is not the right public hypothesis.

6. Best Lean conclusion:
   `SDDRel` between the postprocessed left lifts of `P` and `A`.

7. Proposed Lean signature:

```lean
theorem selfConsistencyImpliesDataProcessing
    {Question α β : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype α] [Fintype β]
    (ψ : QuantumState (ι × ι)) (𝒟 : Distribution Question)
    (hperm : PermInvState ψ)
    (hψ : ψ.IsNormalized)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A : IdxSubMeas Question α ι)
    (P : IdxProjSubMeas Question α ι)
    (δ ε : Error) (f : α → β) :
    BipartiteSSCRel ψ 𝒟 A δ →
    SDDRel ψ 𝒟
      (IdxSubMeas.liftLeft A)
      (IdxSubMeas.liftLeft (IdxProjSubMeas.toIdxSubMeas P))
      ε →
      SDDRel ψ 𝒟
        (IdxSubMeas.liftLeft (fun q => postprocess ((P q).toSubMeas) f))
        (IdxSubMeas.liftLeft (fun q => postprocess (A q) f))
        (8 * δ + 8 * Real.sqrt ε)
```

I wrote the approximation hypothesis in `A`-then-`P` order because that composes more directly with `completenessTransferProjectiveP`. If paper-order syntax is preferred, add a small symmetry lemma for `SDDRel` first.

8. Relation to existing theorems:
   This is a composite extension, not a duplicate. It should be built from:

   - `completenessTransferProjectiveP`: already formalized, but a small API helper such as `IdxProjSubMeas.liftLeft` would make instantiation cleaner
   - `easy-approx-from-approx-delta`: not present as a single public theorem under that name; the repo currently has the underlying overlap-gap ingredients `question_overlap_gap_left` and `question_overlap_gap_right`
   - `twoNotionsOfSelfConsistencyAfterEvaluation`: not yet formalized
   - triangle inequality for `≈_δ`: present only as private `stateDependentDistanceRel_triangle`
   - `simeqDataProcessing`: already formalized, but it is the wrong theorem here because it is about `≃` for opposite-side full measurements rather than `≈` for same-side postprocessed submeasurements

### Proof-chain status for the paper's cited ingredients

- `prop:completeness-transfer-projective-P`
  Already formalized as `completenessTransferProjectiveP`.

- `prop:easy-approx-from-approx-delta`
  Not formalized under that paper name as a public theorem. The repo instead exposes lower-level overlap-gap lemmas and uses them inside later proofs.

- `prop:two-notions-of-self-consistency-after-evaluation`
  Not yet formalized.

- `prop:triangle-inequality-for-approx_delta`
  Exists only as private `stateDependentDistanceRel_triangle`, with the expected `2 * (δ₁ + δ₂)` degradation.

## 5. `prop:cool-prop`

1. Paper SSC hypothesis form:
   Single-question overlap SSC, with no `x`-indexing.

2. Paper conclusion form:
   Raw scalar inequality involving the local square mass on one side:
   `Σ_a ⟨ψ, A_a^2 ⊗ I ψ⟩ ≥ Σ_a ⟨ψ, A_a ⊗ I ψ⟩ - ζ`.

3. Paper state assumption:
   The proposition states permutation-invariance, but the proof does not use it. The argument is Cauchy-Schwarz plus the overlap SSC lower bound.

4. Paper distribution:
   No question distribution. In Lean this should be represented by `uniformDistribution Unit` and `constSubMeasFamily`.

5. Best Lean hypothesis:
   `BipartiteSSCRel ψ (uniformDistribution Unit) (constSubMeasFamily A) ζ`.
   This is exactly the single-question version of the paper's SSC hypothesis.

6. Best Lean conclusion:
   Raw scalar inequality. Do not force this into `SSCRel`; the paper statement is a concrete estimate used as a helper.

7. Proposed Lean signature:

```lean
theorem coolProp {Outcome : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState (ι × ι))
    (A : SubMeas Outcome ι) (ζ : Error) :
    BipartiteSSCRel ψ (uniformDistribution Unit) (constSubMeasFamily A) ζ →
      ∑ a, ev ψ (leftTensor (ι₂ := ι) (A.outcome a * A.outcome a)) ≥
        ∑ a, ev ψ (leftTensor (ι₂ := ι) (A.outcome a)) - ζ
```

8. Relation to existing theorems:
   This is not a duplicate of `completingToMeasurement`, but it is the right standalone helper to factor out from the completion proof. The current file proves an equivalent local estimate only indirectly inside the private completion argument.

## Overall recommendation

For faithfulness to the paper statements in `preliminaries.tex`, the public theorems in this cluster should use the following pattern:

- top-level SSC assumptions: `BipartiteSSCRel`
- opposite-side `≃`: `ConsRel` on `liftLeft`/`liftRight`
- opposite-side or same-side `≈`: `SDDRel`
- single-question statements: `uniformDistribution Unit` plus `constSubMeasFamily`
- scalar completeness bounds: raw inequalities on `idxSubMeasMass`

The only place where `SSCRel` should surface in this cluster is as an internal bridge for the already-formalized completion argument, not as the user-facing hypothesis for the five paper propositions above.
