# Manuscript sync record

Public verification repository: `penghongzhong/sm`.

This repository contains Lean verification material only. The manuscript source and PDF remain in the user's ChatGPT Library and are intentionally not committed here.

## Current synchronized manuscript snapshot

- TeX filename: `stereo_scalar_scattering_v20_W20_LeanSync_v2.tex`
- TeX SHA-256: `e933cd2229f959a239e1716c0a6961f7b6df1403f2035d3c5bdd8eb8130b5158`
- PDF filename: `stereo_scalar_scattering_v20_W20_LeanSync_v2.pdf`
- PDF SHA-256: `6b151b87d54a4041f6ff3ff99d0de2359dd96d3bc2d551e66a6a63e1c0c51166`
- PDF pages: 134
- Sync date: 2026-09-28

## Authority hierarchy — user reconfirmed 2026-09-28

1. **Verification target:** the full W20 manuscript, using the synchronized LeanSync v2 edition identified above.
2. **Master baseline:** `stereo_scalar_scattering_v20_W20`.
3. **Auxiliary Lean-min reference only:** `SM_Lean_Min_v4_SYNC_T025_T027_20260918`.
4. **Lean migration material:** `SM_V21_N001_N033_MEGA_RESYNC_20260920.lean`.

The previous instruction treating the 36-page compressed manuscript as the verification target is superseded. The compressed manuscript is not a substitute for the full W20 proof. Its T001–T094 inventory is an auxiliary index, not evidence of exhaustive W20 coverage.

The page count describes the current edition. LeanSync v2 became 134 pages after inserting the missing unit-modulus Poincare normalization in `v19:lem:phase-profile-constant`. Later corrections may change pagination; identify those editions by versioned filenames and hashes rather than forcing 133 pages.

## LeanSync v2 mathematical repair

The v19 phase-profile proof previously said that Poincare directly supplies a constant on the unit circle.  The rigorous step is:

- ordinary Poincare gives closeness to the complex mean on a fixed ball;
- because the multiplier has unit modulus, the variance identity forces the mean modulus to converge to one;
- normalize the nonzero mean to the unit circle;
- this normalized constant has the same local L2 limit.

The repair is applied in both the bounded-time and time-escaping branches of `v19:lem:phase-profile-constant`.  The v2 PDF was rebuilt and the modified page was visually inspected.

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
