# Manuscript sync record

Public verification repository: `penghongzhong/sm`

This repository contains Lean verification material only. The manuscript source and PDF are stored separately in the user's ChatGPT Library and are intentionally not committed here.

## Current verification target

The manuscript being verified is the short Lean-oriented Schrödinger-map scattering paper:

- TeX filename: `SM_Lean_Min_v4_SYNC_T025_T027_20260918.tex`
- PDF filename: `SM_Lean_Min_v4_SYNC_T025_T027_20260918.pdf`
- PDF pages: 36
- Title: `二维球极复标量 Schrödinger Map 阈下散射 — Lean 最短证明稿 v4（T025–T027 同步展开）`
- Main threshold: `E < E_car = ||Q_gs||_2^2 < 4π`
- TeX SHA-256: `86bebcf905183159be8e3e946e2151722b1786033c1a19e14bb976b435879836`
- PDF SHA-256: `f943390e6e86ae62431c2b2a7607366e71a8f79523b3eb4df043e00ed3a2f506`
- Sync date: 2026-09-28

## Source hierarchy

- Verification target: the 36-page Lean-min v4 manuscript above.
- Long proof source / proof-mining authority: `stereo_scalar_scattering_v20_W20`.
- Imported Lean migration batch: `SM_V21_N001_N033_MEGA_RESYNC_20260920.lean`.

The 133-page W20 manuscript is **not** the public verification target. It is used only as a private proof source when a compressed theorem in the Lean-min manuscript needs expansion.

Because the migration batch was later semantically resynchronized, every imported theorem must be checked against the 36-page target before it is promoted to PASS.

## Synchronization rule

A mathematically substantive Lean failure must be handled in this order:

1. identify the exact theorem/equation in the 36-page verification target;
2. if needed, proof-mine the corresponding long W20 source;
3. repair the ChatGPT-Library TeX target;
4. compile and visually verify the Library PDF;
5. update the corresponding Lean theorem;
6. rerun Lean/CI;
7. update the hashes above.

No manuscript body, TeX source, or PDF may be added to this public repository.
