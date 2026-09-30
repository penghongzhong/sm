# Whole-paper Lean coverage ledger

Target: full W20 master originally supplied as 133 pages, 207 proof-bearing
environments. Registered Library baseline: private LeanSync v4, 135 pages.
Current generated private working expansion: v6 CylinderBridge, 137 pages,
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

## Latest actual code verification: Run 123

Run 36660803283 / job 109714901632: SUCCESS.
CHECKED_SHA=2f9e348dad3f5d1c6f5a8db5d444d5c46c2738d2.
42 files attempted, 42 COMPILE_OK, 0 COMPILE_FAIL. Completed log read.
New cylinder-module printed axioms: only propext, Classical.choice,
Quot.sound. Independent secondary checkers were not run.
Read V12_RUN123_SUCCESS_20260930.md for declaration-level scope.
A later metadata-only commit is not a separately compiled code revision.

## Layers and remaining actual correspondence

| Layer | Verified support | Still open for full W20 statement |
|---|---|---|
| Section 2 | Algebra, geometry, Fourier symbols and actual Plancherel | Complete function/derivative/Hodge/HLS applications |
| v12 Fourier/local L2 | Actual cutoff symbol/kernels, local restrictions, tail-sup adapter, common radius/frequency subsequence | Whole-spacetime realization and precise same-field operator inputs |
| v12 source products | Actual A_j Q and VQ+W conjugate(Q), Holder estimates, MemLp | Hodge-defined coefficients, M/Z bounds, Fubini time-Lp realization |
| v12 time integration | Source L43 budget, interval Holder, weak-test residual and limit machinery | Concrete compact spatial tests, PDE residual and their approximation limits |
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
argument, not an a.e.-to-everywhere conversion by assertion. The v6 text
spells out compact tests and approximation errors; those written derivations
are not yet a complete Lean instance of the generic weak-test machinery.

Then connect the verified compactness conclusion to common local limits,
measurable gluing and Theorem 7.1, before auditing later dependencies.

No audited full-theorem numerator is available, so no percentage is certified.
Earlier 55-60% whole-paper / 75% v12 estimates remain withdrawn as certified
figures. File count 42/42 is not a count of 207 verified paper environments.
Full Theorem 7.2, scattering and complete TeX/PDF/Lean equivalence are not
certified by this run. This describes available evidence, not a claim that
the unformalized mathematics is false.
