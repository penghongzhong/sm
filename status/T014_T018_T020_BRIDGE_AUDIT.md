# T014/T018/T020 bridge audit

Verification authority: synchronized W20 manuscript.

## T014 — relative causal Bony estimate

Paper node: `v13:lem:relative-causal`.

The two Bony orderings are:
- `R_r Q_s ∇P_k`;
- `P_r R_s ∇P_k`.

Each ordering uses:
1. source-audited Smith Lemma 3.9 for the separated bilinear pair;
2. the exact dyadic exponent identity already formalized in T009;
3. standard Cauchy-Schwarz and discrete Young for the geometric kernel
   `2^{(r-s)/2}`;
4. the already proved l2 bounds for the two background envelopes.

The current Lean T014 theorem formalizes the final squaring step.  The unsquared
Bony estimate is therefore standard/source-reduced rather than a new paper axiom.

Classification: **T014 SOURCE-REDUCED**.

## T018 — derived tensor contraction

Paper node: `v14:lem:tensor-contract`.

The manuscript proof uses only:
- the explicit low multiplier bound `O(2^{r-k})`;
- the explicit narrow-cone high multiplier bound `O(eta_0)`;
- fixed fattened Fourier cutoffs whose convolution kernels have the corresponding
  L1 bounds;
- Minkowski on each translation-invariant norm;
- the Leibniz rule for the joint directional derivative;
- the ordinary binomial theorem for commuting low/high operators.

Thus the analytic content is standard Fourier-multiplier/L1-kernel boundedness,
and the remaining algebra is the binomial theorem.  No Schrödinger-map theorem
is hidden in the T018 scalar parameters.

Classification: **T018 STANDARD-ANALYSIS REDUCED**.

## T020 — weak Smith extension

Paper node: `v14:thm:weak-Smith`.

Published Smith source:
Paul Smith, Analysis & PDE 6 (2013), Theorem 5.5.

Exact proof spine checked in the source:
- (5-18) reduces the local-smoothing energy to data/adapted forcing plus the
  second derived term;
- (5-19)--(5-20) introduce the best bootstrap constant and apply it to the
  derived sequence;
- (5-21)--(5-22) prove a positive-power narrow-angle contraction on the
  relevant Lp spaces;
- the proof concludes with `K_{T,k} ≲ 1 + eta^q K_{T,k}` and absorption.

The manuscript's extension does **not** put the sixth local-smoothing forcing
atom into Smith's modified forcing space.  Instead:
- T015 supplies the explicit first-generation weak pairing;
- T018 supplies low/high multiplier contraction;
- T019 proves all finite derived generations contract geometrically;
- T020 Lean proves only the final scalar absorption
  `K <= C(1 + theta K)`.

Therefore the weak extension is an internal derivation from Smith's published
identity plus already separated manuscript lemmas, not a mislabelled external
Smith theorem.

Classification: **T020 PROOF-SPINE SOURCE-AUDITED; dependent on T015/T018/T019.**

## Consequence

After these reductions the earliest unresolved v13-v14 items are no longer
T014/T018/T020 as opaque black boxes.  Remaining attention moves to the exact
T023 relative-WMB recurrence and T024 near/far causal convolution, and to fresh
CI of the assembled Lean files.
