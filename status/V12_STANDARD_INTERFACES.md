# v12 allowed standard-analysis interfaces

Authority: W20 full-master v12 block. This ledger is intentionally narrower than
"standard analysis in general": every retained external interface is listed with
the exact role it plays. None of the W20 conclusions below is itself an
external hypothesis.

## S1 — Hilbert-valued interval trace / FTC sampling

For a Hilbert-valued absolutely continuous function \(f\) on an interval of
length \(\ell\), the v12 sampling proof uses only the one-interval estimate

\[
\ell\,\|f(s_c)\|_{\mathcal H}^{2}
\le
2\int_{s_c}^{s_c+\ell}\|f(s)\|_{\mathcal H}^{2}\,ds
+
2\ell^{2}\int_{s_c}^{s_c+\ell}\|f'(s)\|_{\mathcal H}^{2}\,ds .
\]

Summing disjoint intervals and using the band-limited Plancherel derivative
bound gives \`v12:lem:sampling\`. The manuscript-specific constant aggregation
is checked by \`lean/v12/V12_SamplingBudgetKernel.lean\`.

Classification: **standard Hilbert FTC/trace + Plancherel**.

## S2 — Band-limited Bernstein / Plancherel derivative estimates

For spatial Fourier support \(|\xi|\lesssim 2^m\), v12 uses:

\[
\|\partial_\rho f\|_2\lesssim 2^m\|f\|_2,\qquad
\|f(t)\|_\infty\lesssim 2^m\|f(t)\|_2.
\]

The exact \(L^2\) Plancherel registration already has a public Lean interface.
These estimates are used in \`v12:prop:axial\` and \`v12:thm:tightness\`.

Classification: **standard Fourier support estimate**.

## S3 — Vector-valued Minkowski / pointwise Cauchy-Schwarz

The only external input in \`v12:lem:lattice\` is the standard direction of
Minkowski for the exponent ranges \(1\le p,q\le2\) and \(2\le p,q\le\infty\),
combined with pointwise Cauchy--Schwarz.

The square-partition coefficient identities are checked in
\`lean/v12/V12_LatticeKernel.lean\`.

Classification: **standard mixed-norm/vector-valued Minkowski**.

## S4 — Smooth translated packet / Fourier-support invariance

For \`v12:prop:countermodel\`, translation in the physical variables changes
only the Fourier phase and therefore preserves a common compact Fourier
support. Disjoint time translates of a compactly supported time bump have
the exact \(L_t^\infty\) norm behavior used in the construction; Schwartz
separation gives the uniform lateral square-sum bound.

The finite many-cell lower-bound accounting is checked by
\`lean/v12/V12_CountermodelKernel.lean\`.

Classification: **elementary Fourier translation + Schwartz decay**.

## S5 — Covariant product/chain rules and finite locally supported sums

For \`v12:thm:IMS\`, \`v12:cor:IMS-forcing\`,
\`v12:thm:relative\`, and \`v12:cor:relative-cocycle\`, the only external
calculus is the ordinary product/chain rule for smooth functions and finite
(or locally finite) sums. The paper-specific cancellations are checked by:

- \`lean/v12/V12_IMSKernel.lean\`;
- \`lean/v12/V12_RelativeConnectionKernel.lean\`;
- \`lean/v12/V12_RelativeCocycleKernel.lean\`.

Classification: **standard differential calculus**.

## S6 — Local compactness / weak convergence package

The closure theorem uses only the following generic facts after the
paper-specific coefficient estimates:

1. bounded sequences in the relevant \(L^p\) spaces admit weak/weak-star
   subsequences;
2. strong local \(L^2\) convergence implies local \(L^1\) convergence of
   quadratic products under the uniform \(L^2\) bound;
3. bounded linear \(L^2\) Fourier multipliers preserve weak convergence;
4. strong \(L^2_{\rm loc}\) times bounded/strong \(L^2_{\rm loc}\) gives the
   stated local \(L^1\) product convergence;
5. distributional derivatives pass to limits under these convergences.

The Hodge far/near split remains paper-specific; its scalar tail and product
bookkeeping is isolated in \`lean/v12/V12_CompactnessKernels.lean\`.

Classification: **standard Banach/measure/distribution convergence**.

## S7 — Arzela--Ascoli + diagonal extraction

For fixed frequency cutoff \(P_{\le N}\), the manuscript derives uniform
spatial smoothness and a time Holder \(1/4\) modulus. Compact convergence on
each finite cylinder then uses Arzela--Ascoli; a countable diagonal extraction
over \((N,R)\), followed by the frequency-tail Cauchy estimate, yields the
local strong \(L^2\) subsequence in \`v12:thm:tightness\`.

The exponent and final three-error Cauchy closure are checked in
\`lean/v12/V12_CompactnessKernels.lean\`.

Classification: **standard compactness theorem + diagonal argument**.

## Certification rule

A v12 node is promoted to GREEN only when:

1. every paper-specific algebra/scale estimate has a compiled Lean kernel;
2. every remaining analytic step is one of S1--S7 with the same hypotheses
   and exponent range as the manuscript;
3. no downstream W20 conclusion is used as an interface to prove an upstream
   v12 node.
