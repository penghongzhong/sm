# W20 v19 full-master audit

> **Historical audit — certification withdrawn.** The GREEN labels and
> whole-block conclusions below record an earlier, insufficient standard of
> evidence. They are not current full-statement certificates. See
> `SEMANTIC_VERIFICATION_CORRECTION_20260928.md` and
> `WHOLE_PAPER_COVERAGE.md`; actual objects, internal proof steps and concrete
> external-theorem hypotheses must still be checked against the full manuscript.


Verification authority: \`stereo_scalar_scattering_v20_W20_LeanSync_v2\`
(134-page synchronized edition).

Exact v19 proof-bearing inventory: **13 nodes**.

## Important manuscript repair already incorporated in LeanSync v2

The original proof of \`v19:lem:phase-profile-constant\` said that Poincare
directly produces a constant \(c_{n,R}\in S^1\).  That is too fast: ordinary
Poincare gives closeness to the complex mean
\(\bar g_{n,R}\), which need not lie exactly on the unit circle.

LeanSync v2 inserts the missing normalization:

\[
\|g_n-\bar g_{n,R}\|_{L^2(B_R)}\to0,
\qquad
1-|\bar g_{n,R}|^2
=
|B_R|^{-1}\|g_n-\bar g_{n,R}\|_2^2\to0,
\]

hence \(|\bar g_{n,R}|\to1\), and one may define

\[
c_{n,R}:=\bar g_{n,R}/|\bar g_{n,R}|\in S^1.
\]

The scalar variance bookkeeping is compiled in
\`lean/v19/V19_CanonicalPeelingKernels.lean\`.

## Node-by-node status

### 1. \`v19:lem:Ecar-4pi\`

Input: the sharp 2D Gagliardo--Nirenberg inequality with optimizer
\(Q_{\rm gs}\) (Weinstein 1983).

The Gaussian test is not an optimizer, so the sharp inequality is strict for
that test.  The final implication
\(\pi/2 < 2\pi^2/E_{\rm car}\Rightarrow E_{\rm car}<4\pi\)
is machine checked.

**Status: GREEN relative to Weinstein's sharp GN theorem.**

### 2. \`v19:prop:A-L2\`

The local moving-frame input is Plotnikov--Toland (2023), Theorem 1.2:
if
\[
\int_D |\partial_1n\times\partial_2n|\le4\pi-\delta,
\]
then an oriented orthonormal Coulomb moving frame exists with quantitative
\(W^{1,2}\) control.

The manuscript then uses standard degree-zero bundle patching:
zero Euler number -> zero winding transition -> \(W^{1,2}\) phase lift and
extension -> global frame.  Minimization over global phase gives a Coulomb
connection.  The final uniqueness of this connection against the fixed Hodge
normalization is the Fourier div/curl argument compiled in the v19 kernel.

Nahmod--Shatah--Vega--Zeng is corroborative for the global Coulomb frame
construction; the manuscript's argument does not need a stronger theorem from
that source.

**Status: GREEN relative to Plotnikov--Toland Theorem 1.2 and standard
degree-zero Sobolev bundle patching.**

### 3. \`v19:lem:time-dispersed-gradient\`

The torsion right side vanishes against a large-time free test by:
- node 2 uniform \(A_n\in L^2\);
- uniform energy \(Q_n\in L^2\);
- the standard 2D free dispersive estimate
  \(L^1\to L^\infty\), giving \(|t_n|^{-1}\).

The limit curl relation is then solved in Fourier space away from the single
point \(-\zeta\); smooth cutoff and Schwartz density give the approximate
potential.

**Status: GREEN relative to the standard free dispersive estimate, Fourier
transform, and density.**

### 4. \`v19:cor:td-amplitude\`

Uses the same free dispersive estimate and node 2:
\[
\|A_na_{n,\eta}\|_2
\le \|A_n\|_2\|a_{n,\eta}\|_\infty\to0.
\]

**Status: GREEN.**

### 5. \`v19:lem:exp-linear\`

This is the standard Jacobi-field expansion on the constant-curvature unit
sphere applied to the pointwise exponential map, with the manuscript's
current normalization:
the complex coefficient of \(\partial_jN\) is \(2Q_j\), while that of
\(\nabla_jV\) is \(D_j^Aa\).  Dividing the transported Jacobi expansion by 2
gives the displayed \(1/2\) coefficient.

**Status: GREEN relative to the standard constant-curvature Jacobi equation
and its short-geodesic Duhamel estimate.**

### 6. \`v19:lem:spatial-regauge\`

The curvature homotopy identity yields the transported-connection error.
The canonical phase is the \(L^2\) Hodge projection of that error; its
operator norm is 1.  The projection-to-phase estimate is machine checked.

**Status: GREEN relative to the standard \(L^2\) Hodge projection theorem.**

### 7. \`v19:lem:phase-profile-constant\`

After the LeanSync v2 repair, the proof uses only:
- Poincare on fixed balls;
- the unit-modulus variance identity;
- strong continuity of the free group for bounded \(t_n\);
- the standard pseudoconformal/Fourier representation for \(|t_n|\to\infty\);
- density of Schwartz data in \(L^2\);
- compactness of \(S^1\).

**Status: GREEN after the v2 repair.**

### 8. \`v19:cor:no-profile-multiplier\`

Uses the inverse implication in the standard/Keraani \(L^2\) linear profile
decomposition: failure of free \(L^4\) vanishing produces a nonzero profile.
Node 7 transfers such a profile through the slowly varying phase, contradicting
the original no-profile remainder.

**Status: GREEN relative to the Keraani inverse profile theorem.**

### 9. \`v19:cor:profile-phase-transport\`

Finite application of node 7 to each existing profile plus node 8 for the
remainder.

**Status: GREEN.**

### 10. \`v19:prop:true-time-block\`

Combines nodes 3--7 with a two-parameter diagonal
\(\eta=2^{-m}\), \(m=m(n)\to\infty\), then restores the physical symmetry.

**Status: GREEN relative to the standard diagonal argument.**

### 11. \`v19:thm:finite-canonical-peel\`

Fixed finite iteration of:
- time-escape blocks from node 10;
- already certified high-carrier blocks;
- tangent exponential peeling (node 5);
- canonical re-gauge (node 6);
- phase transport/no-profile preservation (nodes 7--9).

The finite error and energy-ledger bookkeeping is compiled in the v19 kernel.

**Status: GREEN relative to the previously certified carrier module and
standard finite iteration.**

### 12. \`v19:cor:GPEEL-pass\`

Direct dependency assembly of nodes 3--11.

**Status: GREEN.**

### 13. \`v19:cor:new-cutset\`

The geometric peeling obligation is removed.  The exact remaining profile
front becomes

\[
\boxed{\mathrm{TVAN}_{19}}.
\]

**Status: GREEN as a dependency reduction.**

## v19 conclusion

Under the declared foundation, the v19 proof-bearing block is **13/13 GREEN**
provided the new v19 support file compiles in public CI.

The first remaining genuinely dynamical obligation is \(\mathrm{TVAN}_{19}\),
which is addressed beginning in v20 and later W-sections.
