# Manuscript sync record

Public verification repository: `penghongzhong/sm`.

This public repository contains Lean verification material only. The manuscript TeX/PDF remains in the user's ChatGPT Library and is synchronized here only by filename and hash.

## Closed manuscript authority

- TeX: `SM_Q_threshold_scattering_theorem_chain_repaired_cn.tex`
- PDF: `SM_Q_threshold_scattering_theorem_chain_repaired_cn.pdf`
- PDF pages: 18
- TeX SHA-256: `a55ff2da41d8013b0d494c10d1ce75b6915e02c1ed78e9c0302391461b7c41d4`
- PDF SHA-256: `cb82c3a5e69c965ee51c5e2471a910b33fe6fcf017887dbea7e736048c1349b8`
- threshold: `E < E_car = ||Q||_2^2 < 4π`
- sync date: 2026-09-28

## Authority hierarchy

1. **Verification authority:** the 18-page closed theorem-chain manuscript above.
2. **Lean migration source:** `SM_Lean_Min_v4_SYNC_T025_T027_20260918` and later N001–N033 semantic-resync material.
3. **Long proof-mining source:** `stereo_scalar_scattering_v20_W20`.

The 36-page Lean-min file and the 133-page W20 file are not the manuscript being certified.

## Verification boundary

The 18-page manuscript describes the proof as closed relative to:
- a standard critical analytic package; and
- a previously proved balanced-rigidity module.

During formal verification, each such input must be classified as either:
- an exact published theorem / standard-analysis interface; or
- an internal theorem that must itself be formalized from the private proof source.

A compressed internal module is never accepted merely because the short manuscript names it.

## Synchronization rule

If Lean exposes a substantive issue:

1. locate the exact theorem/equation in the 18-page authority;
2. classify the dependency as published/standard or internal;
3. if internal, proof-mine the longer private source and formalize the missing bridge;
4. repair the Library TeX if the human proof statement needs correction;
5. compile the Library PDF;
6. update Lean and rerun verification;
7. update hashes here.

No manuscript TeX/PDF may be committed to the public repository.
