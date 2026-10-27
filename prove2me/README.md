# Private LIDT Prove2Me Upload

This directory contains the mechanically extracted, generated, validated, and uploaded private
Prove2Me graph for the LIDT formalization at source commit
`f382c801026f53a9efc260fdee707cb35e0adb15`.

All generated Lean declarations are wrapped in `namespace LIDT`. Every platform entry is tagged
`LIDT` and was submitted with `private: true`.

## Contents

- `extracted/`: declaration graph and declaration-level sketch facts from Lean meta-programs.
- `generated/`: upload plan, payload manifest, rename map, type audit, QPBT import check, and
  validation receipt.
- `platform/`: exact generated definition bundles, theorem stubs, and proof files submitted to
  Prove2Me.
- `records/upload_state.json`: resumable publish and verification state, including platform IDs and
  the final census.
- `tools/`: extraction, planning, generation, validation, and idempotent private-upload scripts.

## Verified Result

- 231 private definition bundles.
- 449 private theorem nodes.
- 449 accepted proofs; every theorem is `Proved` and zero are `Open`.
- 445 declarations requested by the QPBT session are mapped in
  `/home/drx/p2m/status/lidt-names.tsv` and compile-checked through the generated import audit.
- The main theorem is `LIDT.MIPStarRE.LDT.Test.mainFormal`, platform ID
  `b2e0f20e-0ffa-46f6-b8a9-3853a661b399`.

Run the local validation gate with:

```bash
python3 prove2me/tools/validate_upload.py
```

The uploader is resumable and private-only:

```bash
python3 prove2me/tools/upload_private.py --phase all --concurrency 8
```

Do not run any platform make-public operation without explicit owner approval. Publication is
permanent and recursively publishes a theorem's private dependency closure.
