# Challenge.lean generation

This directory generates the self-contained statement file `Challenge.lean`
used by the companion repository
[MIPStarRE-comparator](https://github.com/LionSR/MIPStarRE-comparator) to
verify, with the official
[leanprover/comparator](https://github.com/leanprover/comparator), that this
library proves the main theorem `MIPStarRE.LDT.Test.mainFormal`.  Background
and trust model: `docs/comparator.md`.

The generated file imports only Mathlib and re-declares, verbatim and in
dependency order, every declaration in the kernel closure of the statement of
`mainFormal`, each with a provenance comment; the theorem itself is stated
with `sorry`.

## Regenerating

Run from the repository root (requires a built library):

```sh
# 1. extract the closure of the statement of mainFormal
#    (a Lean metaprogram mirroring comparator's runForUsedConsts traversal)
lake env lean scripts/comparator/extract_closure.lean > closure.tsv
awk -F'\t' 'NF==4' closure.tsv > closure.clean.tsv

# 2. assemble the challenge file (topological order, namespace handling)
python3 scripts/comparator/assemble_challenge.py closure.clean.tsv > draft.lean
cat scripts/comparator/challenge_header.lean draft.lean \
    scripts/comparator/challenge_footer.lean > Challenge.lean
```

Then copy `Challenge.lean` into the MIPStarRE-comparator repository, bump the
`rev` pin in its `lakefile.toml` to the library commit it was generated from,
and run its `./verify.sh` (its CI also runs on every push).

## Maintenance notes

- The assembler's `EXTRAS`/`MODULE_PRELUDES` tables carry elaboration context
  (attribute commands, `CoeFun` instances, `variable`/`open` blocks) that the
  kernel closure cannot see.  Extend them if regeneration produces compile
  errors in `Challenge.lean`; the script fails loudly if a table key no
  longer matches any extracted declaration.
- The `mainFormal` statement in `challenge_footer.lean` is a manual copy of
  the theorem in `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean`.  If the
  library statement changes, update the footer too — comparator fails with
  "theorem statement do not match" until the two agree.
- Declarations without a source range (compiler-generated congruence lemmas
  and `autoParam` helpers) are emitted as explanatory comments; they
  regenerate identically during elaboration of the challenge file.
