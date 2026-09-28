# Schrödinger Maps — Lean Verification

Public Lean verification workspace for the **closed sub-`4π` Schrödinger-map scattering manuscript**.

## Verification authority

The manuscript being verified is:

- `SM_Q_threshold_scattering_theorem_chain_repaired_cn`
- 18 pages
- title: `二维球面 Schrödinger 映射在载波基态阈值以下的散射`
- subtitle: `只保留服务于主定理的定理链与公式化证明`
- proof status stated by the manuscript: closed relative to the standard critical analytic package and the proved balanced-rigidity module
- threshold: `E < E_car = ||Q||_2^2 < 4π`

The 36-page `SM_Lean_Min_v4_SYNC_T025_T027_20260918` file is **not** the mathematical authority. It is only a Lean-oriented compression/migration source.

The 133-page `stereo_scalar_scattering_v20_W20` file is also **not** the verification target. It is a private long proof-mining source used only when the short closed manuscript needs a derivation expanded.

## Public-repository scope

This repository contains only:

- Lean verification code;
- Lean/Lake configuration;
- CI configuration;
- verification/status ledgers.

It contains **no manuscript TeX and no manuscript PDF**.

## Verification standard

The target is full-paper coverage of the closed 18-page manuscript, relative only to:

1. Lean/Mathlib foundations and standard analysis;
2. exact, source-audited theorems already published in the literature.

Internal manuscript results may not be promoted to axioms merely to make Lean compile.

Every imported T/N-numbered Lean node from earlier work is migration material only until it is mapped to an exact theorem/equation in the 18-page authority.

Final PASS means the main scattering theorem is reached through a complete verified dependency tree with no unverified internal edge.
