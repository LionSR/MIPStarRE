# Section 6 Companion Helpers Audit (#653)

Date: 2026-04-24

## Scope

Audited the public Section 6 interface on:

- `main` at `2ae82c5d`
- `origin/gpt54/issue-633-session24` (PR #649)

Files inspected:

- `MIPStarRE/LDT/MainInductionStep.lean`
- `MIPStarRE/LDT/MainInductionStep/Statements.lean`
- `MIPStarRE/LDT/MainInductionStep/Theorems.lean`

## Executive summary

No additional promotion is warranted.

The companion helpers named in issue #653 are already public, already named, and already re-exported by the barrel module `MIPStarRE.LDT.MainInductionStep`. The follow-up audit therefore concludes that PR #649 does **not** need extra `abbrev`/`def`/theorem wrappers for the restriction or recursion packagers.

The only wrapper that is still PR-local is `mainInductionPublicWrapper` itself; its proposed signature on `origin/gpt54/issue-633-session24` already refers to the companion helpers through their existing public names.

## Findings

### 1. The Section 6 barrel already exports the helper declarations

`MIPStarRE/LDT/MainInductionStep.lean` imports and re-exports:

- `Defs`
- `Statements`
- `Theorems`

So any non-`private` declaration in `MainInductionStep/Theorems.lean` is already part of the public Section 6 interface.

### 2. The restriction and recursion packagers are already public on `main`

All three relevant constructors live in `MIPStarRE/LDT/MainInductionStep/Theorems.lean` as top-level declarations inside the public namespace `MIPStarRE.LDT.MainInductionStep`:

- `RestrictedProbabilitiesStatement.ofWeightedBounds`
  - proposition-valued packaging lemma
  - correctly declared as a `lemma`
- `SliceRestrictionPackage.ofRestrictedProbabilities`
  - data-bearing package constructor
  - correctly declared as a `noncomputable def`
- `PerSliceInductionPackage.ofRecursion`
  - data-bearing package constructor
  - correctly declared as a `noncomputable def`

These are exactly the names suggested by issue #653, so there is no missing export to add.

### 3. `SelfImprovementPackage.ofSelfImprovementInInductionSection` already received the same promotion

The analogous self-improvement constructor from PR #659 is also already public on `main`:

- `SelfImprovementPackage.ofSelfImprovementInInductionSection`
  - data-bearing package constructor
  - correctly declared as a `noncomputable def`

So the natural “third companion helper” has already been promoted in the same style.

### 4. Naming and declaration kinds are consistent

The current naming scheme is internally coherent:

- package-producing propositions use `.of...` lemmas/theorems when the codomain is a proposition;
- package-producing data constructors use `.of...` `noncomputable def`s when the codomain is a structure with data.

That means:

- `RestrictedProbabilitiesStatement.ofWeightedBounds` being a lemma is appropriate because `RestrictedProbabilitiesStatement ...` is a proposition;
- `SliceRestrictionPackage.ofRestrictedProbabilities`, `PerSliceInductionPackage.ofRecursion`, and `SelfImprovementPackage.ofSelfImprovementInInductionSection` being `noncomputable def`s is appropriate because they return structures carrying data.

No renaming is recommended.

### 5. PR #649 already uses the public helper names directly

On `origin/gpt54/issue-633-session24`, `mainInductionPublicWrapper` is the only new public boundary theorem. Its statement introduces

- `let hrestrict := SliceRestrictionPackage.ofRestrictedProbabilities ...`

inside the types of `hrec` and `hselfProducer`, and its proof body reuses the same public constructor name.

So, after the review fix that removed the private helper mentioned in the original PR description, the wrapper no longer hides the restriction package behind a private declaration. Downstream users can already reference the companion helper names directly.

## Conclusion

Issue #653 is a **no-action API audit**:

- `SliceRestrictionPackage.ofRestrictedProbabilities` is already public;
- `PerSliceInductionPackage.ofRecursion` is already public;
- `SelfImprovementPackage.ofSelfImprovementInInductionSection` is already public;
- `RestrictedProbabilitiesStatement.ofWeightedBounds` is already public and correctly theorem-valued;
- `mainInductionPublicWrapper` on PR #649 already leans on those public names rather than on a private bridge helper.

Adding further aliases or duplicate wrappers would not expose any new functionality and would risk creating redundant API surface.

## Recommended closing note for #653

No code change is needed beyond documenting the audit result: the Section 6 companion helpers were already promoted publicly before this follow-up landed, and PR #649's wrapper signature is already aligned with that public surface.
