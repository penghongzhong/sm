# Manuscript sync record

Public verification repository: `penghongzhong/sm`

This repository contains Lean verification material only. The manuscript source and PDF are stored separately in the user's ChatGPT Library and are intentionally not committed here.

## Current synchronized manuscript snapshot

- TeX filename: `stereo_scalar_scattering_v20_W20_LeanSync_v1.tex`
- TeX SHA-256: `be83fe09b191016005a0e2d20ff58528b8c97366e3d50412bc19e31eccf3d946`
- PDF filename: `stereo_scalar_scattering_v20_W20_LeanSync_v1.pdf`
- PDF SHA-256: `6d852a4b157c851cf57465c66a7de5fb504d59d21c541ce8e69250726c7a1e99`
- PDF pages: 133
- Sync date: 2026-09-28

## Synchronization rule

A mathematically substantive Lean failure must be handled in this order:

1. identify the exact manuscript theorem/equation;
2. repair the Library TeX source;
3. compile and visually verify the Library PDF;
4. update the corresponding Lean theorem;
5. rerun CI;
6. update the hashes above.

No manuscript body, TeX source, or PDF may be added to this public repository.
