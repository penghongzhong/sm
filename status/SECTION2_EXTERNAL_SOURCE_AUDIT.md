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

## Certification correction (2026-09-30)

The former claim that Section 2 had “no remaining internal mathematical red
point” is withdrawn as a formal-verification claim. The compiled items above
are algebraic kernels or individual standard-library applications. They do
not establish the full smooth-field derivative/Hodge/HLS construction, its
function-space conditions, or the concrete application hypotheses throughout
Section 2. In particular a chapter/section citation without an exact theorem
and checked hypotheses does not discharge the HLS application.

The dedicated Q0 tactic repair is historical implementation evidence; it is
not a certificate for these still-open analytic steps. Current authoritative
scope is the whole-paper coverage ledger and semantic verification correction.

## Precise HLS source recovered (2026-09-30; application still open)

Terence Tao, *An Epsilon of Room, I: Real Analysis*, author/AMS-authorized
preliminary edition, Corollary1.11.18, printed page182 (PDF index190),
https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf .
Hypotheses: n-dimensional Euclidean Lebesgue space, 1<p,r<infinity,
0<alpha<n, 1/p+alpha/n=1+1/r, f in Lp. Conclusion: convolution with
|x|^(-alpha) is defined a.e., belongs to Lr and has norm <=C(p,alpha,n)*norm(f).
This source uses alpha as the kernel exponent, not the potential order.
Concrete instance: n2,alpha1,p4/3,r4; 3/4+1/2=1+1/4.

The source derives the result from weak Young/Schur interpolation immediately
above it. Registration is not a Lean application certificate. Remaining:
identify the real/complex/vector Lebesgue conventions, prove the actual
B-slice L^(4/3) hypotheses, dominate the concrete Hodge kernel, prove the
time interpolation/Fubini estimates and carry the original M/Z constants.
No new unproved axiom has been added to the Lean environment.
