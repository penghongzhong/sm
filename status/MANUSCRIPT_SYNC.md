# Manuscript sync record

Public verification repository: `penghongzhong/sm`.

This repository contains Lean verification material only. The manuscript source and PDF remain in the user's ChatGPT Library and are intentionally not committed here.

## Current synchronized manuscript snapshot

- TeX filename: `stereo_scalar_scattering_v20_W20_LeanSync_v1.tex`
- TeX SHA-256: `be83fe09b191016005a0e2d20ff58528b8c97366e3d50412bc19e31eccf3d946`
- PDF filename: `stereo_scalar_scattering_v20_W20_LeanSync_v1.pdf`
- PDF SHA-256: `6d852a4b157c851cf57465c66a7de5fb504d59d21c541ce8e69250726c7a1e99`
- PDF pages: 133
- Sync date: 2026-09-28

## Authority hierarchy — user reconfirmed 2026-09-28

1. **Verification target:** the full W20 manuscript, using the synchronized 133-page edition identified above.
2. **Master baseline:** `stereo_scalar_scattering_v20_W20`.
3. **Auxiliary Lean-min reference only:** `SM_Lean_Min_v4_SYNC_T025_T027_20260918`.
4. **Lean migration material:** `SM_V21_N001_N033_MEGA_RESYNC_20260920.lean`.

The previous instruction treating the 36-page compressed manuscript as the verification target is superseded. The compressed manuscript is not a substitute for the full W20 proof. Its T001–T094 inventory is an auxiliary index, not evidence of exhaustive W20 coverage.

The page count describes the current edition. Later corrections may change pagination; identify those editions by versioned filenames and hashes rather than forcing 133 pages.

## Artifact identity check

On 2026-09-28, SHA-256 was recomputed from both mounted private artifacts and matched the two digests above exactly. This check confirms artifact identity only: it is not a proof that Lean covers every manuscript statement. No TeX/PDF modification or new Lean compilation was performed as part of this authority correction.

## Synchronization rule

A mathematically substantive Lean failure is handled in this order:

1. identify the exact W20 theorem/equation and all relevant hypotheses;
2. determine whether each dependency is standard/published or internal;
3. repair the ChatGPT-Library TeX proof if needed;
4. compile and inspect the matching Library PDF;
5. update the corresponding Lean theorem and concrete-object bridges;
6. rerun Lean/CI and record the actual result;
7. update the file hashes and coverage mapping.

No manuscript body, TeX source, PDF, or private manuscript build artifact may be committed or uploaded to this public repository. The original private repository remains unchanged by this authority correction.
