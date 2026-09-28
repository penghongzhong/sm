# W20 W3 full-master audit

Verification authority:
\`stereo_scalar_scattering_v20_W20_LeanSync_v2\`.

Exact W3 proof-bearing inventory: **12 nodes**.

W3 is a correction/infrastructure block.  Its final first-exit theorem is
explicitly conditional on the still-unproved diagonal-transfer estimate.
Certifying W3 must therefore *not* mark that diagonal input as proved.

## 1. \`w3:lem:cutoff\`

The exact cutoff source identity is ordinary phase/product/commutator
calculus.  The local \(L^4\) estimate uses only the free two-dimensional
Strichartz estimate (Keel--Tao) and Duhamel--Minkowski for the
\(L_t^1L_x^2\) atom.  The cutoff-energy bound is Plancherel plus the assumed
frequency support.

The source aggregation is machine checked.

**Status: GREEN relative to free Strichartz/Plancherel.**

## 2. \`w3:lem:norm-order\`

\(D\le X\le Y\) follows from pointwise finite sums, Minkowski, and monotone
convergence.  The counterexample to a uniform
\(\ell^2_kL^4\leftarrow L^4\) reverse bound uses only:
- \(L^2\) Fourier orthogonality;
- 2D Schrödinger scaling;
- spatial translation;
- finite compact-support approximation in \(L^4\).

It is a guardrail, not an SM counterexample.

**Status: GREEN.**

## 3. \`w3:thm:coherent\`

For a pointwise square partition,
\(T^*T=I\), \(P=TT^*\) is a projection, and
\(\mathcal V_A=T U_A T^*\) inherits the cocycle exactly on the coherent range.
Compression of Duhamel is finite Hilbert-space operator algebra.
In the free case the only estimate is free Strichartz.

The partition-isometry scalar core is compiled.

**Status: GREEN relative to standard Hilbert operator algebra/free Strichartz.**

## 4. \`w3:cor:equivalence\`

The homogeneous coherent \(X_I\) norm is exactly the underlying
\(U_A\)-propagator \(L^4\) norm.  Thus stitching cannot manufacture magnetic
dispersion from unitarity.

**Status: GREEN.**

## 5. \`w3:thm:Berry\`

Differentiating \(a^*a=1\) gives the induced Berry connection and normal
derivative energy.  The key load-bearing identity
\[
A_\alpha
=\gamma_\alpha+\sum_\nu\zeta_\nu^2\widetilde A_\alpha^\nu
\]
is finite partition algebra and is machine checked.

**Status: GREEN relative to standard differentiation/finite-dimensional
matrix algebra.**

## 6. \`w3:lem:potential-model\`

The explicit \(h=(1+|x|^2)^{-1}\) / \(V_*\) model is direct radial calculus.
A bounded real multiplication potential is a bounded self-adjoint
perturbation of \(-\Delta\); hence the propagator is unitary.
The stationary algebra is kernelized; the displayed \(L^2,L^4\) integrals are
elementary radial integrals.

This is only a guardrail against an abstract "small coefficient + unitarity
implies global dispersion" argument.

**Status: GREEN relative to standard bounded-perturbation self-adjointness.**

## 7. \`w3:lem:lateral-bilinear\`

The proof is directly from the already-defined \(G_k\) lateral components:
finite angular partition plus mixed Hölder
\[
1/3+1/6=1/2,\qquad 1/6+1/3=1/2.
\]
The reciprocal-exponent algebra is compiled.  No magnetic PDE estimate and no
WMB hypothesis are used.

**Status: GREEN.**

## 8. \`w3:thm:recombine\`

Littlewood--Paley square function reduces the \(L^4\) norm to pairwise
\(L^2\) products.  Near pairs use
\(a^2b^2\le(a^4+b^4)/2\); far pairs use node 7 and a geometric convolution.
The logarithmic modulus follows by the explicit choice
\(L\sim12\log_2(M/\mathcal D)\).

The near-pair inequality is machine checked.

**Status: GREEN relative to standard LP/sequence convolution.**

## 9. \`w3:thm:constant-drift\`

A time-dependent but spatially constant connection is removed exactly by
translation \(X_k'=2b_k\) and scalar phase
\(\beta_k'=c_k^0-|b_k|^2\).  Both extra coefficients vanish algebraically,
which is machine checked.  The \(L^4\) bound then uses free Strichartz and
\(\ell^4\) summation, not an invalid coherent \(\ell^2\) exchange.

**Status: GREEN.**

## 10. \`w3:prop:zero-order\`

This reuses v12 coefficient estimates:
\(A\in L^4\), \(A_0,V,W\in L^2\), hence the zero-order forcing is in
\(L^{4/3}\).  LP/Minkowski converts it into the fourth-power diagonal forcing
budget.  Cubic scale bookkeeping is machine checked.

**Status: GREEN relative to v12 + standard LP.**

## 11. \`w3:lem:actual-residual\`

Exact decomposition after subtracting a spatially constant drift:
\[
(A_{\le m_k}-b_k)\cdot\nabla Q
+A_{>m_k}\cdot\nabla Q+F^{(0)}.
\]
The full magnetic terms remain.  The split is machine checked.

**Status: GREEN.**

## 12. \`w3:thm:first-exit\`

This theorem is **conditional by statement** on
\[
\mathcal D_J(Q)\le B(\delta_J+Z_J^2)
\]
with fixed constants.  Under that hypothesis, node 8 and a first-exit
continuity argument give \(Z\to0\).  The terminal contradiction
\(r^4\le r^4/4\) for \(r>0\) is machine checked.

**Status: GREEN as a conditional theorem.**

## W3 boundary — not GREEN yet as a global paper edge

The following is **not** proved by W3 and must remain an internal obligation:

\[
\boxed{
\mathcal D_J(\mathbf Q)
\le B\bigl(\delta_J+Z_J^2\bigr)
}
\]

for the true self-generated connection, or a strictly weaker estimate that
still closes the same first-exit argument.

Hence W3's 12 statements can all be certified while the global TVAN chain is
still blocked.  W4 begins the source-square estimates designed to attack this
remaining diagonal/self-magnetic transfer.
