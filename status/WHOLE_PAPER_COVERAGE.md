# Whole-paper Lean coverage ledger

Target: full W20 master originally supplied as 133 pages, 207 proof-bearing
environments. Registered Library baseline: private LeanSync v4, 135 pages.
Current generated private working expansion: v10 HLSSource, 138 pages,
all 207 original statements byte-identical. See MANUSCRIPT_SYNC.md for the
explicit v4-based provenance, hashes, build checks and storage boundary.
The 36-page Lean-min and T001-T094 remain auxiliary references only.

## Certification correction

SEMANTIC_VERIFICATION_CORRECTION_20260928.md supersedes historical blanket
GREEN labels. Compiled scalar kernels, propositional assemblies and lists
of external references are not complete formalizations of PDE statements.
Allowed foundations remain Lean/Mathlib, standard analysis and precisely
identified published results. Concrete applications and internal bridges
must be checked; all standard analysis need not be rebuilt from scratch.

## Latest completed verification: Run 152 (partial, FAILURE)

Run 36749557505 / job 110004370152, checked
`84487d95576eaa949c8b6ad0457cb88158fe6dd5`: 71 COMPILE_OK, 4 COMPILE_FAIL.
NEW PASS: actual spacetime cutoff class/norm (YW), raw Q/F/G time realizations
(YZRawSourceTimeBounds), fixed-frequency compactness from raw PDE (ZI), and
common strongly measurable local limit from raw PDE + actual class-frequency
tail (ZJ). These construct integral identity, budget, cutoff representative,
compact sets, compatibility and gluing internally. No hIntegral/hRep/hBudget/
hCompact premise is present at the ZJ endpoint.

Root failures: the new Hodge-kernel measurability proof needs typed scalar
multiplication; drift-product continuity times out in definitional unfolding,
and bounded-test convergence needs Function.comp unfolded. Near-kernel and
quadratic-limit files are import-blocked. Their repairs use explicit proved
application equalities, not increased axioms or weaker statements.

Next candidates identify class tails with raw convolution tails, eliminate all
supplied Q/F/G time objects using their proved construction, and handle a=b.
Original Hodge/MZ applications and Theorem7.1 nonlinear closure remain open.
No full Theorem7.2, scattering or whole-paper certificate is claimed.

## Layers and remaining actual correspondence

| Layer | Verified support | Still open for full W20 statement |
|---|---|---|
| Section 2 | Algebra, geometry, Fourier symbols and actual Plancherel | Complete function/derivative/Hodge/HLS applications |
| v12 Fourier/local L2 | Actual cutoff symbol/kernels, local restrictions, tail-sup adapter, common radius/frequency subsequence | Original raw tail identification candidate; exact Fourier profile instantiation |
| v12 source products | Actual A_j Q and VQ+W conjugate(Q), Holder estimates, MemLp | Hodge-defined coefficients and their actual M/Z bounds; Fubini time-Lp realization now compiled |
| v12 time integration | Source L43 budget, interval Holder, weak-test residual and limit machinery | Original-system regularity, same-field time-Bochner realizations and Hodge/MZ hypotheses remain open; ZC–ZG compiled in Run 146 |
| v12 fixed-cutoff compactness | NEW: actual cylinder representatives constructed; joint equicontinuity and L2 compact closure derived from energy/source integrals | ZI/ZJ now discharge budget/integral/representative/compactness internally; original Hodge/MZ field instance remains open |
| v12 local limits | Common-sequence nested compatibility and one strongly measurable glued limit, Run150 | Original-field common sequence and exact Theorem-7.1 nonlinear limit passage |
| v13-v20 | Existing scalar/finite/dependency kernels | Exact norm objects and transitive analytic hypotheses |
| v19 Lemma 14.7 | Fixed-anchor phase and dense-class/quantifier support | Actual Poincare measure-space and Fourier-operator instance |
| W1-W3 | Existing kernels | Not a continuous full-theorem verified prefix |
| Later W/RFCE/rigidity | No full-main-theorem certificate established | Full correspondence and reverse dependency audit |

## Current next load-bearing leaves

The ZJ endpoint now derives fixed-frequency compactness and a common strongly
measurable local limit from the raw smooth divergence PDE and concrete
representatives/time-source bounds. It does not assume hIntegral/hCompact.
The next ZK candidate constructs all Q/F/G objects from the actual raw field,
a.e. energy and spacetime source estimates, and states frequency tightness on
the raw convolution. The zero-length slab is treated separately.

Still prove the original reconstructed Hodge coefficients' estimates and
original-system instantiation, then the full Theorem7.1 Hodge/nonlinear weak
limit passage, preserved bounds and distributional equations. Theorem7.2
includes that closure conclusion; ZJ alone does not certify the full statement.
Continue through all later dependencies after these exact applications.

No audited full-theorem numerator or completion percentage is certified.
Historical scalar-kernel and whole-block GREEN claims are explicitly withdrawn.
File compilation counts are not counts of the 207 verified paper environments.
