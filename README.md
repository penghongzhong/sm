# Schrödinger Maps — Lean Verification

Public Lean verification workspace for the 2D stereographic complex-scalar Schrödinger-map subthreshold scattering project.

## Mathematical authority

The manuscript being verified is the synchronized W20 working manuscript:

- ChatGPT-Library TeX: `stereo_scalar_scattering_v20_W20_LeanSync_v1.tex`
- ChatGPT-Library PDF: `stereo_scalar_scattering_v20_W20_LeanSync_v1.pdf`
- PDF pages: 133
- long human-proof authority: `stereo_scalar_scattering_v20_W20`
- Lean-min reference: `SM_Lean_Min_v4_SYNC_T025_T027_20260918`
- current migration batch: `SM_V21_N001_N033_MEGA_RESYNC_20260920.lean`

The shorter 18-page and 36-page theorem-chain/Lean-min manuscripts are auxiliary compression references only. They are not the manuscript being certified.

## Verification goal

Verify the whole 133-page scattering proof relative only to:

1. Lean/Mathlib foundations and standard analysis;
2. explicitly source-audited published theorems used by the manuscript.

Internal proof-bearing nodes must be proved, not postulated.

## Public-repository scope

This repository intentionally contains only:

- Lean verification code;
- Lean/Lake configuration;
- CI configuration;
- verification/status ledgers.

It contains **no manuscript TeX and no manuscript PDF**.

## Verification rule

1. No `sorry`, `admit`, or custom `axiom` declarations for internal nodes.
2. Published/standard external interfaces must be explicitly whitelisted.
3. If Lean exposes a genuine missing argument, repair the ChatGPT-Library TeX/PDF first, then update Lean.
4. A finite algebra kernel PASS does not imply the surrounding PDE theorem is fully formalized.
5. Final completion requires full dependency coverage through the scattering theorem.

## Current cut-set

Section 2 is formula/definition closed and several finite algebra kernels compile. The current unresolved analytic layer is:

- function-level stereographic derivative bridge;
- Hodge reconstruction in the exact function/distribution class;
- covariant product-rule derivative bridge;
- Plancherel/Fourier-multiplier connection;
- exact HLS connection to the manuscript norm objects.

After this cut-set is closed, verification proceeds through v13–v20 and W1–W20 to the final scattering theorem.
