# Schrödinger Maps — Lean Verification

Public Lean verification workspace for the short sub-`4π` Schrödinger-map scattering manuscript.

## Verification target

The manuscript being verified is **not** the 133-page W20 research master.

Current target:

- `SM_Lean_Min_v4_SYNC_T025_T027_20260918`
- 36 pages
- main threshold: `E < E_car = ||Q_gs||_2^2 < 4π`
- target conclusion: two-sided free Schrödinger scattering of the normalized Coulomb derivative field
- theorem inventory: T001–T094

The long `stereo_scalar_scattering_v20_W20` manuscript is used only as a private proof-mining source when an abbreviated Lean-min node needs expansion.

## Scope of this public repository

This repository intentionally contains only:

- Lean verification code;
- Lean/Lake configuration;
- CI configuration;
- verification/status ledgers.

It intentionally contains **no manuscript TeX, no manuscript PDF, and no unpublished proof source**.

## Verification policy

- no `sorry`;
- no `admit`;
- no custom `axiom` declarations for internal paper nodes;
- standard analysis / published external results must be explicitly registered;
- internal v*/w* nodes must be proved, not postulated;
- a node is PASS only when its Lean statement matches the synchronized 36-page manuscript.

## Current migration state

- imported migration batch: `SM_V21_N001_N033_MEGA_RESYNC_20260920.lean`;
- current public split files include T001 and Section-2/analytic kernels;
- remaining theorem-by-theorem work continues through T094.

The manuscript itself remains in the user's ChatGPT Library and is synchronized to this repository by filename/hash records only.
