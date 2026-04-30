import MIPStarRE.LDT.Preliminaries.SwitchSandwichMain.LeftTransfer
import MIPStarRE.LDT.Preliminaries.SwitchSandwichMain.RightTransfer
import MIPStarRE.LDT.Preliminaries.SwitchSandwichMain.Completeness

/-!
# Preliminary comparison theorems: switch-sandwich main estimates

Barrel module re-exporting the concrete switch-sandwich main submodules.

## Paper alignment

The main theorem `switchSandwich` (in `Completeness.lean`) assembles the paper's
`prop:switch-sandwich`:

```
E_x Σ_a ⟨ψ| A_a B A_a ⊗ I |ψ⟩
  ≈_{2√δ} E_x Σ_a ⟨ψ| B ⊗ A_a |ψ⟩
  ≈_{√δ} E_x Σ_a ⟨ψ| B A_a ⊗ I |ψ⟩
```

where:
* `leftSandwichExpectation`  = `leftTensor(A_a) * leftTensor(B) * leftTensor(A_a)` = `A_a B A_a ⊗ I`
* `middleSandwichExpectation` = `leftTensor(B) * rightTensor(A_a)` = `B ⊗ A_a`
* `rightSandwichExpectation`  = `leftTensor(B * A_a)` = `B A_a ⊗ I`

The hypothesis `BipartiteSDDRel ψ 𝒟 (toSubMeas A) (toSubMeas A) δ` encodes
`A_a^x ⊗ I ≈_δ I ⊗ A_a^x` — exactly the paper's `eq:Aapproxd`.
-/
