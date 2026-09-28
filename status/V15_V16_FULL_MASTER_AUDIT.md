# W20 v15-v16 full-master audit

Authority: synchronized 133-page W20 manuscript.

## v15 — 6 proof-bearing nodes

1. \`v15:thm:fullN-stability\`
   - compiled as T028;
   - the epsilon-to-zero infimal-sum closure is machine checked;
   - upstream weak-forcing/Volterra inputs are v13-v14 GREEN.

2. \`v15:lem:cross-quadratic\`
   - finite ordered-pair quadratic expansion;
   - generic finite-sum kernels added in \`V15_MixedScreenKernels.lean\`;
   - passage between ordered pairs and the manuscript's \(a<b\) notation is
     finite reindexing only.

3. \`v15:prop:mixed-reduction\`
   - first-order mixed residual identity is checked by the generic
     \(\sum A_a\sum dU_b-\sum A_a dU_a\) kernel plus the explicit cross
     connection;
   - zero-order terms are finite polynomial expansion of
     \(V=-A_0+|A|^2-2m\) and \(W\).

4. \`v15:lem:smooth-screen\`
   - the carrier-size coefficient cancellation is checked exactly from
     \((\partial_t+2\xi\cdot\nabla)\chi=A_0+2A\cdot\xi\);
   - the remaining product-rule terms use standard differential calculus.

5. \`v15:thm:minimal-one-profile\`
   - the finite energy-ledger contradiction core is already compiled in the
     migration batch;
   - Keraani-type vector \(L^2\) profile decomposition is an explicit external
     published/standard input;
   - the theorem is conditional on the manuscript-defined
     \(\mathrm{REALIZE}_{15}\) and \(\mathrm{SCREEN\!-SUP}_{15}\), exactly as
     stated in W20; those interfaces are not silently assumed in the final
     main theorem and must be discharged downstream.

6. \`v15:cor:cutset\`
   - dependency-only corollary: combines the previous theorem with the
     mixed-forcing reduction.

Thus v15 is a conditional reduction block: its internal algebra/logic can be
GREEN while the two named interfaces remain obligations for v16-v18.

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
     are registered standard compactness/function-analysis interfaces.

4. \`v16:cor:bounded-profile-static\`
   - uses strong \(L^2\) continuity of the free Schrödinger group and fixed
     modulation plus the preceding weak-realization theorem;
   - a dependency assembly is added in the v16 screen kernel.

5. \`v16:lem:screen-Lipschitz\`
   - Fubini/Cauchy--Schwarz/unit-phase Lipschitz are standard;
   - the constants \(2\) and \(4\), and the final multiplier norm chaining,
     are checked in \`V16_ScreenLipschitzKernel.lean\`.

6. \`v16:cor:new-cutset\`
   - dependency-only reduction: after static realization and static screen
     continuity, the remaining obligations are exactly
     \(\mathrm{FLOW\!-PEEL}_{16}+\mathrm{DYN\!-SCREEN}_{16}\).

## Forward cut-set

The first genuinely new unresolved dynamics after v16 are therefore the v17
rough-flow/strong-density and dynamic screen diagonal nodes, not any hidden
v15/v16 finite algebra.
