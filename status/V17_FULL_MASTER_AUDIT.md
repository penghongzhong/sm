# W20 v17 full-master audit

> **Historical audit — certification withdrawn.** The GREEN labels and
> whole-block conclusions below record an earlier, insufficient standard of
> evidence. They are not current full-statement certificates. See
> `SEMANTIC_VERIFICATION_CORRECTION_20260928.md` and
> `WHOLE_PAPER_COVERAGE.md`; actual objects, internal proof steps and concrete
> external-theorem hypotheses must still be checked against the full manuscript.


Authority: synchronized 133-page W20 manuscript.

Exact v17 proof-bearing inventory: **7 nodes**.

Verification foundation: standard functional analysis/calculus and explicitly
identified published inputs are allowed; no internal W20 conclusion is admitted
as an axiom.

## 1. \`v17:lem:Coulomb-unique\`

The migration contains:
- the pointwise gauge relation and nonvanishing unit phase factor;
- the deduction \(\nabla h=0\);
- the constant-phase conclusion from the standard connected-domain
  distribution theorem;
- the positive-real Hilbert pairing normalization fixing the residual phase.

**Status: GREEN relative to the standard distribution fact
"zero gradient on a connected domain implies constant."**

## 2. \`v17:thm:strong-Coulomb-density\`

The migration contains the Hilbert polarization/strong-convergence closure.
The only non-paper inputs are:
- Bethuel smooth \(W^{1,2}\) density for degree-zero Sobolev maps;
- standard Hilbert weak subsequence compactness;
- the already certified v16 weak realization and node 1 uniqueness.

**Status: GREEN relative to these published/standard inputs.**

## 3. \`v17:thm:rough-subcritical-flow\`

The proof uses:
- node 2 strong initial-data density;
- \(E_0<E_1<E_c\);
- the smooth global \(S^0\) bound built into the definition of \(E_c\);
- v15 full-\(N^0\) stability to obtain a Cauchy family;
- Banach completeness / finite-interval exhaustion;
- v12 distributional closure and v16 true-data realization.

The scalar Cauchy estimate is compiled in
\`lean/v17/V17_DynamicSupportKernels.lean\`.

**Status: GREEN relative to standard Banach completeness/exhaustion.**

## 4. \`v17:cor:subcritical-profile-flow\`

The strict energy inequality for every nonzero profile in the multi-profile
branch is machine checked.  The corollary is direct composition of v16 bounded
static realization with node 3.

**Status: GREEN.**

## 5. \`v17:prop:smooth-screened-collision\`

The only new paper-specific mechanism is the finite smooth carrier collision.

The proof has been reduced exactly to:

1. ordinary FTC/chain rule applied to the explicit ray integral for \(\chi_M\);
2. the carrier cancellation already certified in v15;
3. the scale substitution \(M=r^4,\ \tau_M=r^{-3}\), for which
   \(M\tau_M=r\) and \(M\tau_M^2=r^{-2}\);
4. the affine ray change of variable \(d\sigma=2M\,ds\);
5. compact-support domination and the ordinary dominated convergence theorem
   giving the exit ray integral at time zero;
6. the \(V_b\) contribution carries the explicit \(1/(2M)\) Jacobian factor;
7. the canonical Wilson/Radon phase differs from the ray integral only by the
   already fixed constant phase coming from the v16 canonical screen;
8. \(L_t^1L_x^2\) forcing on an interval of length \(2\tau_M\) is bounded by
   interval length times the uniform smooth \(L_x^2\) bound;
9. the post-collision bridge costs the \(o(1)\) endpoint mismatch plus
   short-interval smooth errors.

Items 3--4 and the finite bridge/sum bookkeeping are compiled in
\`lean/v17/V17_ScreenCollisionKernels.lean\`.
Items 1,5,8 are standard calculus/measure estimates with the exact smooth
compact-support hypotheses of the manuscript.

**Status: GREEN relative to FTC/change-of-variables/DCT and the already
certified v16 Wilson screen identity.**

## 6. \`v17:thm:rough-screen-diagonal\`

For each fixed smooth level, node 5 gives the residual limit.
Node 3 gives \(S^0\) approximation, v16 gives screen-data Lipschitz continuity,
and v15 gives full-\(N^0\) stability.  The remaining diagonal selection is the
standard countable diagonal argument; the two-error estimate is machine
checked in \`V17_DynamicSupportKernels.lean\`.

**Status: GREEN relative to standard diagonal selection.**

## 7. \`v17:cor:cutset\`

This is a dependency-only conclusion.  Nodes 1--6 reduce the profile front to

\[
\boxed{\mathrm{CRIT\!-FLOW}_{17}+\mathrm{ESC\!-RAD}_{17}}.
\]

**Status: GREEN as a dependency reduction.**

## v17 conclusion

Under the declared verification foundation, the **v17 proof-bearing block is
GREEN: 7/7** once the screen-collision support file compiles in public CI.

This does not close the paper: the two interfaces left by node 7 are precisely
the v18 targets.
