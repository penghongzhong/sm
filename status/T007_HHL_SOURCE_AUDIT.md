# T007 HHL standard-analysis source audit

Paper node: `v13:prop:HHL`.

## Paper-specific algebra formalized

`lean/v13/T007_HHLNullKernel.lean` contains:

1. the exact two-dimensional output-frequency cancellation
   `eta wedge xi = eta wedge (xi - eta)`;
2. the 2D Lagrange identity underlying the wedge Cauchy bound;
3. the cross-multiplied symbol-order estimate showing that after the output Riesz factor and the two high-input gradient factors, the localized Jacobian symbol is order `O(M^{-1})` when the second high input is comparable to `M`;
4. the polarized Jacobian difference identity;
5. the final `Z_*^2 <= Z_*` absorption on `0 <= Z_* <= 1`.

These are the non-generic algebraic pieces specific to the manuscript's HHL reduction.

## Registered standard harmonic-analysis interfaces

### Bilinear Coifman-Meyer

For a translation-invariant bilinear Fourier multiplier whose localized symbol satisfies the classical Coifman-Meyer derivative bounds, use the boundedness

[
T_m:L^{p_1}	imes L^{p_2}	o L^p,
qquad
1/p=1/p_1+1/p_2,
]

in particular ((p_1,p_2,p)=(4,4,2)).

Exact published source used in the synchronized manuscript:

A. Benyi, *On a Class of Bilinear Pseudodifferential Operators*, Journal of Function Spaces 2013, Article ID 560976, Theorem A, DOI 10.1155/2013/560976.  The paper explicitly identifies this as the classical Coifman-Meyer bilinear multiplier theorem.

Historical source: R. R. Coifman and Y. Meyer, *Au-dela des operateurs pseudo-differentiels*, Asterisque 57 (1978).

### HLS / Riesz potential

The torsion/Hodge branch uses only the already registered two-dimensional HLS instance
[
I_1:L_x^{4/3}	o L_x^4,
]
with Stein, Chapter V, Section 1, plus standard Holder/Bernstein.

### Littlewood-Paley / sequence estimates

The remaining passage from the per-((k,m)) estimates to the global square sum uses:
- standard LP almost orthogonality/square-function equivalence;
- discrete Young convolution for the `l^1` kernel `2^{k-m} 1_{m >= k-Lambda+C0}`;
- Cauchy-Schwarz in the frequency index.

These are registered as standard analysis, not manuscript-specific hypotheses.

## Resulting T007 boundary

The old scalar migration theorem accepts `hGG,hTor,hDGG,hDTor` as parameters.  Under full-paper verification those parameters are **not** treated as new axioms.  They are obligations discharged by:

- the manuscript-specific Lean null-form kernel above;
- the published bilinear Coifman-Meyer theorem;
- T006 Hodge estimate;
- registered HLS/Holder/Bernstein/LP/sequence inequalities.

Classification after source decomposition:

**T007 ANALYTICALLY SOURCE-REDUCED; fresh Lean/CI integration pending.**
