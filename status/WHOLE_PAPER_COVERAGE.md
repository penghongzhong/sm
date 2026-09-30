# Whole-paper Lean coverage ledger

Target: full W20 master originally supplied as 133 pages, 207 proof-bearing
environments. Registered Library baseline: private LeanSync v4, 135 pages.
Current generated private working expansion: v8 BochnerGluing, 138 pages,
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

## Latest completed verification: Run 148 (partial, FAILURE)

Run 36743902458 / job 109985075036, checked
`a269cd6b429016cbd53e47c5b59715ae5355bee8`: 59 COMPILE_OK, 5 COMPILE_FAIL.
Previously passed ZA–ZH, YC and YSpacetimeSlices remain passed. New nested
compatibility failed on the addition-side lemma; Bochner measurability failed
on namespace, Lp carrier and zero-representative elaboration; gluing, Bochner
norm transfer and every-time Bochner energy were dependency-blocked.
The next batch fixes these and supplies actual global/spacetime cutoff
representatives. It also revises ZF/ZG to accept a.e.-time F/G representatives,
matching the actual Fubini construction rather than demanding all-time source
Lp membership. These changed ZF/ZG statements require fresh compilation.
No full Theorem 7.2/7.1, scattering or whole-paper certificate is claimed.

## Layers and remaining actual correspondence

| Layer | Verified support | Still open for full W20 statement |
|---|---|---|
| Section 2 | Algebra, geometry, Fourier symbols and actual Plancherel | Complete function/derivative/Hodge/HLS applications |
| v12 Fourier/local L2 | Actual cutoff symbol/kernels, local restrictions, tail-sup adapter, common radius/frequency subsequence | Whole-spacetime realization and precise same-field operator inputs |
| v12 source products | Actual A_j Q and VQ+W conjugate(Q), Holder estimates, MemLp | Hodge-defined coefficients, M/Z bounds, Fubini time-Lp realization |
| v12 time integration | Source L43 budget, interval Holder, weak-test residual and limit machinery | Original-system regularity, same-field time-Bochner realizations and Hodge/MZ hypotheses remain open; ZC–ZG compiled in Run 146 |
| v12 fixed-cutoff compactness | NEW: actual cylinder representatives constructed; joint equicontinuity and L2 compact closure derived from energy/source integrals | Prove the terminal source/budget/integral/representative inputs from the original PDE; instantiate downstream common-subsequence theorem |
| v12 local limits | Conditional common-subsequence/tail support | Compatible measurable gluing and exact Theorem-7.1 limit passage |
| v13-v20 | Existing scalar/finite/dependency kernels | Exact norm objects and transitive analytic hypotheses |
| v19 Lemma 14.7 | Fixed-anchor phase and dense-class/quantifier support | Actual Poincare measure-space and Fourier-operator instance |
| W1-W3 | Existing kernels | Not a continuous full-theorem verified prefix |
| Later W/RFCE/rigidity | No full-main-theorem certificate established | Full correspondence and reverse dependency audit |

## Current next load-bearing leaves

The new terminal cylinder theorem no longer requires hCompact, hEq, ambient
spacetime continuity, or pointwise Banach-valued HasDerivAt. These were
replaced by proved constructions, not suppressed assumptions.

It still requires the actual cutoff time integral identity and the actual
local L2 representative equality. Prove these for the SAME spacetime Q,
F_j=A_j Q, G=VQ+W conjugate(Q), with Hodge-defined coefficients and uniform
M/Z bounds. Every-time energy must follow from a justified representative
argument, not an a.e.-to-everywhere conversion by assertion. ZA/ZB now verify the concrete compact-test derivative and source limits.
The raw PDE, spatial IBP, finite-test FTC and cutoff identity chain ZC–ZG
compiled in Run 146, with its concrete original-field inputs still open. The private V7 text spells out
the spatial integrability and integration-by-parts calculation.

Then connect the verified compactness conclusion to common local limits,
measurable gluing and Theorem 7.1, before auditing later dependencies.

No audited full-theorem numerator is available, so no percentage is certified.
Earlier 55-60% whole-paper / 75% v12 estimates remain withdrawn as certified
figures. File compilation counts are not a count of 207 verified paper environments.
Full Theorem 7.2, scattering and complete TeX/PDF/Lean equivalence are not
certified by this run. This describes available evidence, not a claim that
the unformalized mathematics is false.

## Run 149 evidence and next batch

Commit 15dd0bc0c218ecb06191b523c00dfbe2807a4e4d, Run 149
(36745397232), completed with failure. YLocalLimitCompatibility and
YVGlobalCutoffRepresentative compiled; the revised ZF/ZG a.e.-time source
statements also compiled. Measurable gluing needs classical decidability
for Nat.find. Lp section measurability needs explicit pointwise subtraction
before eLpNorm_congr_ae. The blocked Bochner norm / cutoff / energy modules
are not certified.

The next batch repairs these two roots and submits actual canonical cutoff
classes, raw slab realization, and fixed-frequency compactness from the raw
PDE. The latter constructs hIntegral, hRep and hBudget internally. Its
upstream raw-system/Hodge/MZ applications remain open. All new declarations
remain candidates until an actual successful run.
