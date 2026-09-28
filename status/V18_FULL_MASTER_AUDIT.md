# W20 v18 full-master audit

Authority: synchronized 133-page W20 manuscript.

Exact v18 proof-bearing inventory: **7 nodes**.

## 1. \`v18:lem:weighted-persistence\`

This is the v13 dyadic proof with one \(2^{sk}\) weight placed on the highest
frequency input.  The only new algebraic identity is

\[
sk+(k-m)=sm+(s+1)(k-m),
\]

which is checked in \`lean/v18/V18_CriticalFlowKernels.lean\`.
The remaining summation is the same geometric \(\ell^1\) sequence analysis
already registered for v13.

Status after compilation: **GREEN relative to the v13 source boundary.**

## 2. \`v18:cor:smooth-continuation\`

Finite \(S^0\) implies finite \(L^4\); absolute continuity gives finitely many
small windows; node 1 propagates a fixed high Sobolev norm.  The only external
PDE input is the classical smooth local existence/continuation theorem for
smooth Schrödinger maps, cited in the manuscript as McGahagan (2007).

Status: **GREEN relative to that published smooth local theory.**

## 3. \`v18:thm:rough-local-flow\`

The proof uses:
- v17 strong Coulomb density;
- one smooth reference solution from the published smooth local theory;
- the first-exit improvement \(1/8+1/8=1/4<1/2\);
- v15 full-\(N^0\) stability;
- node 2 smooth continuation;
- standard Banach completeness;
- v12 distributional closure and v16 realization.

The first-exit and Cauchy bookkeeping are machine checked in
\`V18_CriticalFlowKernels.lean\`.

Status after compilation: **GREEN relative to standard completeness and the
published smooth local theory.**

## 4. \`v18:cor:critflow-delete\`

Dependency-only consequence of node 3 at \(E_0=E_c<E_{\rm car}\).

Status: **GREEN.**

## 5. \`v18:prop:S0-not-small\`

The manuscript uses only that each \(G_k\) contains
\(L_t^\infty L_x^2\), followed by Littlewood--Paley square summation.
The positive-mass obstruction is kernelized in
\`V18_CriticalFlowKernels.lean\`.

Status after compilation: **GREEN relative to standard LP equivalence.**

## 6. \`v18:prop:ESC-reduction\`

This proposition is intentionally conditional:

\[
\mathrm{GPEEL}_{18}+\mathrm{TVAN}_{18}
\Longrightarrow \mathrm{ESC\!-RAD}_{17}.
\]

Its proof uses free 2D Strichartz to transfer the \(L^2\) peeling error to the
free \(L^4\) remainder, then v17 screened superposition and v15 stability.
The logical reduction is kernelized; neither GPEEL nor TVAN is assumed to
have been proved here.

Status: **GREEN as a conditional reduction.**

## 7. \`v18:cor:new-cutset\`

Combines node 4 and node 6.  The exact remaining front is

\[
\boxed{\mathrm{GPEEL}_{18}+\mathrm{TVAN}_{18}}.
\]

Status: **GREEN as a dependency reduction.**

## v18 conclusion

The v18 section does not close GPEEL or TVAN; rather, it proves that these two
are the only profile-front obligations remaining after the critical local-flow
repair.  Thus the full-paper verification must next inspect v19/v20, whose
purpose is to close these two interfaces without circular use of
Palais--Smale.
