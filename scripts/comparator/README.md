# Challenge.lean regeneration

`Challenge.lean` (repo root) is generated from the library:

```sh
# 1. extract the comparator-relevant closure of the statement of mainFormal
lake env lean scripts/comparator/extract_closure.lean > closure.tsv
awk -F'\t' 'NF==4' closure.tsv > closure.clean.tsv  # keep NORANGE rows: they surface as visible placeholders

# 2. assemble the challenge file (topological order, namespace/context handling)
python3 scripts/comparator/assemble_challenge.py closure.clean.tsv > draft.lean
cat scripts/comparator/challenge_header.lean draft.lean \
    scripts/comparator/challenge_footer.lean > Challenge.lean

# 3. verify (see docs/comparator.md for the comparator invocation)
```

The assembler's `EXTRAS`/`MODULE_PRELUDES` tables carry elaboration context
(attribute commands, CoeFun instances, `variable`/`open` blocks) that the
kernel closure cannot see; extend them if regeneration produces compile
errors in `Challenge.lean`.

Note: the `mainFormal` statement in `challenge_footer.lean` is a manual copy of
the theorem in `MIPStarRE/LDT/Test/MainTheorem/MainFormal.lean`.  If the
library statement changes, update the footer too — comparator fails with
"theorem statement do not match" until the two agree, and CI runs comparator
on every PR that touches `MIPStarRE/**.lean`.
