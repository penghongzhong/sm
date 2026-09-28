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

## Authority hierarchy

1. **Verification authority:** synchronized 133-page W20 manuscript above.
2. **Lean-min reference:** `SM_Lean_Min_v4_SYNC_T025_T027_20260918`.
3. **Lean migration material:** `SM_V21_N001_N033_MEGA_RESYNC_20260920.lean`.

The 18-page and 36-page compressed manuscripts may be used for theorem indexing, but they are not the certified manuscript.

## Synchronization rule

A mathematically substantive Lean failure is handled in this order:

1. identify the exact W20 theorem/equation;
2. determine whether the dependency is standard/published or internal;
3. repair the ChatGPT-Library TeX proof if needed;
4. compile and inspect the Library PDF;
5. update the corresponding Lean theorem;
6. rerun Lean/CI;
7. update the hashes above.

No manuscript body, TeX source, or PDF may be committed to this public repository.
