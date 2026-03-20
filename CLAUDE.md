# Lean repository instructions

## Commands
- Build: `lake build`
- Optional Mathlib cache refresh: `lake exe cache get`
- Find sorrys: `grep -R "sorry" . --include="*.lean"`

## Rules
- Prefer minimal diffs.
- Do not change theorem statements unless the issue explicitly asks for it.
- Reuse existing Mathlib lemmas before adding local helper lemmas.
- Do not introduce new axioms.
- Do not add unrelated `sorry`s.
- If a proof is hard, first reduce it to helper lemmas with clear names.

## Done when
- `lake build` passes
- target theorem or fix is implemented
- no unrelated files were changed
