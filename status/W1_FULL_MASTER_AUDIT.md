# W20 W1 full-master audit

> **Historical audit — certification withdrawn.** The GREEN labels and
> whole-block conclusions below record an earlier, insufficient standard of
> evidence. They are not current full-statement certificates. See
> `SEMANTIC_VERIFICATION_CORRECTION_20260928.md` and
> `WHOLE_PAPER_COVERAGE.md`; actual objects, internal proof steps and concrete
> external-theorem hypotheses must still be checked against the full manuscript.


Verification authority:
\`stereo_scalar_scattering_v20_W20_LeanSync_v2\`.

Exact W1 proof-bearing inventory: **12 nodes**.

The inherited assumptions (A0)--(A4) are not external axioms:
A1/A2/A3/A4 refer to already-audited v12--v20 internal results.  A0 is the
generic Banach/restriction/completeness behavior of the explicitly defined
resolution spaces.

## 1. \`w1:lem:barrier\`

Pure scalar continuity/first-exit lemma.  The relative absorption arithmetic
is compiled in \`lean/w1/W1_WaveOperatorKernels.lean\`.

**Status: GREEN.**

## 2. \`w1:lem:defect\`

Direct stereographic/covariant differentiation.  The spatial connection is
identified by the already-certified Coulomb-Hodge reconstruction; the temporal
correction follows by the v12 electric identity and Hodge normalization.

**Status: GREEN relative to standard differentiation and v12.**

## 3. \`w1:lem:kernel\`

The \(L^\infty\) inverse-derivative estimate is obtained by splitting
\(|x-y|\le R\) / \(>R\), then optimizing \(RA+R^{-1}B\).

**Status: GREEN as elementary integration/optimization.**

## 4. \`w1:prop:approx\`

For \(z_b=U(t)b\), the proof uses only:
- the standard 2D free dispersive estimate for Schwartz derivatives;
- Plancherel;
- node 3 inverse-derivative estimate;
- Fourier \(H^2\to L^\infty\);
- ordinary product estimates;
- the exact defect formula from node 2.

The \(t^{-1},t^{-2},t^{-3}\) powers are explicit and the forcing tail lies in
the already-defined \(L_t^1L_x^2\) atom.

**Status: GREEN relative to standard free dispersive/Fourier estimates.**

## 5. \`w1:lem:shadow\`

Conditional only on the already-audited (A0)--(A3).  The strict first-exit
improvement \(\eta/8+\eta/8=\eta/4<\eta/2\) is kernelized.  Rough data are
obtained by A3 strong density/completeness.

**Status: GREEN.**

## 6. \`w1:thm:seed\`

Launch at late time from the exact real datum \(P_b(S)\), use node 5, compare
two launch times, and take a Banach-space Cauchy limit.  No scattering theorem
is used in the construction.

**Status: GREEN relative to standard completeness/exhaustion.**

## 7. \`w1:lem:density\`

Fourier characterization of curl-free \(L^2\) vector fields plus smooth
annular cutoff and Schwartz \(H^1\) density.

**Status: GREEN relative to standard Fourier density.**

## 8. \`w1:lem:final-stability\`

Apply A2 backward from a finite \(S\), restrict to \([T,R]\), then send
\(S\to\infty\) using the prescribed scattering states and unitarity.

**Status: GREEN.**

## 9. \`w1:thm:rough-wave\`

Node 7 approximates the rough terminal state by Schwartz gradients; node 6
constructs the seed waves; node 8 puts all sufficiently close states on one
common tail.  The common-tail arithmetic is compiled.

**Status: GREEN relative to standard Banach completeness.**

## 10. \`w1:prop:curl\`

Uses the transverse Hodge projector, the v12 torsion identity, HLS/Bernstein
on one fixed dyadic shell, and a sequence of times where the integrable
\(L^4_x\)-slice tends to zero.  The frequency exponent \(-k/2\) is compiled.
The proof fixes \(k\) before taking the time limit, so there is no illicit
low-frequency summation.

**Status: GREEN.**

## 11. \`w1:thm:compact\`

Local common-tail continuity from node 9 plus a finite cover of the compact
terminal set.  Uniform tail convergence follows from a finite delta-net and
node 8; finite-net arithmetic is compiled.

**Status: GREEN relative to ordinary compactness in \(L^2\).**

## 12. \`w1:cor:escape\`

Use node 11 as the late-time reference, node 5 to shadow the true initial
datum, and A4 (v20 finite-S scattering) only at the final step to name the
scattering state.  The state-match bound is kernelized.

**Status: GREEN.**

## W1 boundary

W1 closes fixed rough terminal states and compact terminal families.  It
explicitly does **not** prove nonlinear vanishing for an arbitrary noncompact
terminal remainder sequence with free \(L^4\to0\).  That is the later
self-magnetic/mixed-forcing problem.

Under the declared foundation, W1 is 12/12 GREEN once its support kernel
compiles in public CI.
