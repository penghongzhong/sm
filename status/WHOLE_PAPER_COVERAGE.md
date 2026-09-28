# Whole-paper Lean coverage ledger

Goal: verify the full scattering proof relative only to explicitly registered standard analysis results and published external theorems. A row is **PASS** only when the Lean statement matches the synchronized manuscript claim and CI compiles it without `sorry`, `admit`, custom `axiom`, or a paper conclusion smuggled in as a hypothesis.

| Layer | Manuscript nodes | Public Lean status |
|---|---|---|
| Section 2 coefficient algebra | `v12:lem:coeff` | T001 finite/registered analytic kernel PASS; full analytic layer pending |
| Section 2 stereographic curvature | chart curvature identity | jet algebra PASS; function/derivative bridge pending |
| Section 2 Hodge reconstruction | Hodge uniqueness + kernel | Fourier-symbol uniqueness PASS; distribution/function-space bridge pending |
| Section 2 electric curvature | `v12:lem:electric` | finite product-rule algebra PASS; analytic derivative bridge pending |
| Section 2 low-frequency budget | low-curvature Plancherel/multiplier/HLS step | finite constants + Plancherel interface PASS; exact multiplier/HLS connection pending |
| v13-v14 analysis | Smith whitelist, HHL, weak forcing, Volterra, stability | migration N001-N033 imported; theorem-by-theorem promotion pending |
| v15 profile front end | mixed reduction / screening / minimal profile | pending |
| v16-v20 realization and finite-S scattering | realization, rough flow, peeling, finite-S scattering | pending |
| W1-W5 terminal radiation/profile reduction | wave operator, coherent propagation, TVAN -> PS, finite rigidity | pending |
| W7-W10 NLS shadow / observer / rigidity / REL-REAL | carrier shadow, covariance, observer, global rigidity, screen deletion | pending |
| W11-W14 RFCE reduction | affine freeze, projected torsion, grouped/Jacobian reductions | pending |
| W19-W20 RFCE closure | T1, T2, principal forest repair | pending |
| Final main chain | RFCE -> REL-REAL -> TVAN -> Palais-Smale -> Rigidity -> Ec=Ecar -> two-sided scattering | pending |

## Current first cut-set

The earliest unresolved analytic obligations are:

1. function-level stereographic derivative bridge;
2. Hodge reconstruction at the exact function/distribution level used by the paper;
3. covariant product-rule derivative bridge;
4. Plancherel + Fourier multiplier connection for the low-frequency estimates;
5. exact HLS instance connection to the paper norm objects.

Only after these are closed is Section 2 promoted from finite-kernel PASS to full analytic PASS.
