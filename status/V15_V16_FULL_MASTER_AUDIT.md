# W20 v15-v16 full-master audit

> **Historical audit — certification withdrawn.** The GREEN labels and
> whole-block conclusions below record an earlier, insufficient standard of
> evidence. They are not current full-statement certificates. See
> `SEMANTIC_VERIFICATION_CORRECTION_20260928.md` and
> `WHOLE_PAPER_COVERAGE.md`; actual objects, internal proof steps and concrete
> external-theorem hypotheses must still be checked against the full manuscript.


Authority:
\`stereo_scalar_scattering_v20_W20_LeanSync_v2\` (134 pages).

## v15 — 7 proof-bearing nodes

1. \`v15:thm:fullN-stability\`
   - compiled as T028;
   - the epsilon-to-zero infimal-sum closure is machine checked;
   - upstream weak-forcing/Volterra inputs are v13-v14 GREEN.

2. \`v15:lem:cross-quadratic\`
   - finite ordered-pair quadratic expansion;
   - generic finite-sum kernels in \`V15_MixedScreenKernels.lean\`;
   - passage between ordered pairs and the manuscript's \(a<b\) notation is
     finite reindexing only.

3. \`v15:prop:mixed-reduction\`
   - first-order mixed residual identity is checked by
     \(\sum A_a\sum dU_b-\sum A_a dU_a\) plus the explicit cross connection;
   - zero-order terms are finite polynomial expansion of
     \(V=-A_0+|A|^2-2m\) and \(W\).

4. \`v15:lem:smooth-screen\`
   - carrier-size cancellation is checked exactly from
     \((\partial_t+2\xi\cdot\nabla)\chi=A_0+2A\cdot\xi\);
   - remaining terms use standard product/chain rules.

5. \`v15:prop:mix-reduction\`
   - conditional statement:
     realized/approximable profiles + \(\mathrm{SCREEN\!-SUP}_{15}\)
     imply the old \(\mathrm{MIX\!-FORC}_{14}\) interface;
   - pairwise separated smooth products are controlled by the already
     certified WMB/translation-orthogonality mechanisms;
   - rough passage uses full-\(N^0\) stability;
   - the exact dependency assembly is now compiled in
     \`V15_MixedScreenKernels.lean\`.

6. \`v15:thm:minimal-one-profile\`
   - finite energy-ledger contradiction core is compiled in the migration;
   - vector \(L^2\) linear profile decomposition is an explicit standard/
     Keraani input;
   - theorem is exactly conditional on
     \(\mathrm{REALIZE}_{15}\) and \(\mathrm{SCREEN\!-SUP}_{15}\).

7. \`v15:cor:cutset\`
   - dependency-only corollary combining nodes 5 and 6.

Thus v15 is a conditional reduction block: its own seven proof-bearing
statements are covered while the two named interfaces are discharged
downstream in v16-v18.

## v16 — 6 proof-bearing nodes

1. \`v16:lem:triad-identities\`
   - explicit stereographic triad, differentiated-frame equations and energy
     identity are compiled in the migration batch.

2. \`v16:lem:frame-compactness\`
   - paper scalar norm bookkeeping is compiled;
   - weak \(I_1:L^1\to L^{2,\infty}\) and finite-measure Lorentz embedding are
     registered standard analysis.

3. \`v16:thm:weak-profile-realization\`
   - exact energy/frame packing is compiled;
   - the exponent relation \(p'<p^*\) has a separate kernel;
   - Banach--Alaoglu/Rellich/diagonal extraction and weak-times-strong passage
     are registered standard compactness interfaces.

4. \`v16:cor:bounded-profile-static\`
   - strong \(L^2\) continuity of the free group/fixed modulation plus node 3;
   - dependency assembly compiled.

5. \`v16:lem:screen-Lipschitz\`
   - Fubini/Cauchy--Schwarz/unit-phase Lipschitz are standard;
   - constants 2 and 4 and final norm chaining are compiled.

6. \`v16:cor:new-cutset\`
   - dependency reduction to
     \(\mathrm{FLOW\!-PEEL}_{16}+\mathrm{DYN\!-SCREEN}_{16}\).

## Forward cut-set

The first new dynamics after v16 are the v17 rough-flow and dynamic-screen
nodes, which are audited separately.
