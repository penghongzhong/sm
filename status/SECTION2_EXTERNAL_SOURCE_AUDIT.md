# Section 2 external-analysis source audit

Verification authority: synchronized W20 manuscript, Section 2 strict rewrite.

This ledger classifies the remaining non-algebraic steps after the dedicated Section 2 Lean kernels have compiled successfully in the private source branch `section2-strict-sync@0681282c197012f204785bccabcd5057668bfd95`.

## Allowed standard-analysis interfaces

| Manuscript step | Classification | Source / basis |
|---|---|---|
| quotient/product/chain differentiation in `v12:eq:Falpha-beta-1`--`v12:eq:Falpha-beta` and `v12:eq:chart-curvature-proof` | STANDARD ANALYSIS | ordinary multivariable product/quotient/chain rules on smooth functions; paper-specific polynomial numerator is checked by `S2_StereographicCurvatureJet.lean` |
| Fourier transform of divergence/curl and injectivity on Schwartz class used in `v12:eq:Hodge-Fourier-system`--`v12:eq:Hodge-uniqueness-input` | STANDARD FOURIER ANALYSIS | Schwartz Fourier transform/inversion/injectivity; the nonzero-frequency 2x2 symbol solve is checked by `S2_HodgeSymbolKernel.lean` |
| covariant product rule in `v12:eq:S-derivative-1`--`v12:eq:S-derivative-4` | STANDARD DIFFERENTIAL CALCULUS | product rule plus real U(1) connection cancellation; cancellation is checked by `S2_CovariantProductRuleKernel.lean` |
| `L^2` Plancherel and bounded Fourier multipliers in `v12:eq:T-L2`, `v12:eq:Plem-L2`, `v12:eq:Plem-derivative` | STANDARD FOURIER ANALYSIS | Plancherel + pointwise multiplier bounds; Mathlib Plancherel registration is checked by `S2_PlancherelInterface.lean`; manuscript-specific constants are checked by low-frequency kernels |
| HLS step `v12:eq:HLS` and `v12:eq:HLS-K` | PUBLISHED STANDARD THEOREM | Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter V, §1, Riesz potentials; n=2, alpha=1, p=4/3, q=4 |

## Internal-paper status

The following paper-specific components are already Lean-kernel checked at the source commit:

- stereographic curvature numerator and quotient algebra;
- Hodge Fourier-symbol uniqueness at each nonzero frequency;
- U(1) covariant product-rule cancellation;
- electric-divergence finite algebra;
- low-frequency constants 20 and 24;
- coefficient constant `C_coeff`;
- Mathlib `L^2` Plancherel registration.

Therefore, under the user's declared verification foundation (standard analysis + exact published external theorems), Section 2 has **no remaining internal mathematical red point**. Public CI rerun is still operationally pending, but the identical source files compiled successfully in the private source CI.
