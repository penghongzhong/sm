# Whole-paper Lean coverage ledger

Target: full W20 master originally supplied as 133 pages, 207 proof-bearing
environments. Registered Library baseline: private LeanSync v4, 135 pages.
Current generated private working expansion: v24 TimeSourceIdentification, 141 pages,
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

## Latest completed verification: Run173 (partial, FAILURE)

Run36809570011/job110201386138 checked
`a064fa329b5aff50f0ebe43a447acce361953c68`:167 COMPILE_OK,13 COMPILE_FAIL.
Thirteen new PASS: angular Fourier normalization; BT potential representative;
GU actual Fubini; GV spatial/time test integrability; K actual source PDE;
N/ND/NE distribution PDE closures; S canonical predicates; SD all-real
coefficient limits; U original constraint closure; ZDD interior FTC;
ZDE compact residual uniqueness. No previous PASS regressed.
Six direct roots: BU extension abbreviation; BZ missing energy-lemma import;
GT second-derivative simp ordering and I^2; SE extension abbreviation;
SF/V implicit AE restriction set argument. Seven dependent import failures.
See RUN173_ACTUAL_RESULTS.json. Counts are not paper coverage.

Batch174 fixes these roots and submits nine original-data candidates:
CA reconstructed coefficient budgets; ZDG original MZ/source instantiation;
ZDH original vector FTC; ZES same-field source/Lp match; ZFS compact Lp time
identity; ZGS original cutoff identity; ZIS fixed-frequency compactness;
ZKS common measurable limit (including zero/empty slabs); ZKT SAME-subsequence
closure. These are NOT certified. Actual Lean execution of the entire chain
and literal original-statement/normalization audit remain required.

The new end-to-end candidate has only original smoothness, compatibility,
M/Z and raw frequency-tightness inputs. It does not assume hIntegral,
hCompact, source budgets, representatives, coefficient convergence or a
local limit. Full7.1/7.2 and all later paper branches remain OPEN.

The original applications derive component/second coordinate derivatives,
the zero-extended canonical PDE with actual V, and spatial constraints.
The original-local-closure candidate also constructs a strongly measurable
limit representative from local L2 membership instead of assuming global
measurability. Its time derivative is constructed from original smoothness.
All original-data applications remain CANDIDATE until actual successful Lean
execution. Original smooth-gauge and concrete statement applicability,
pointwise/distributional equivalence, cofinal real cylinders and full7.2
combined conclusions remain under audit. Full7.1/7.2 and later branches OPEN.
No internal hIntegral/hCompact or source/coefficient convergence conclusion
is a whole-theorem input. No scattering or whole-paper certificate is claimed.

The only registered external interface remains an explicit proposition
parameter: Tao, An Epsilon of Room I, Corollary1.11.18 (n=2), with exact
hypotheses/conclusion in SECTION2_EXTERNAL_SOURCE_AUDIT.md. No new axiom,
instance, external schema or weakened paper statement.

## Layers and remaining actual correspondence

| Layer | Verified support | Still open for full W20 statement |
|---|---|---|
| Section 2 | Algebra, geometry, Fourier symbols and actual Plancherel | Complete function/derivative/Hodge/HLS applications |
| v12 Fourier/local L2 | Actual cutoff symbol/kernels, local restrictions, tail-sup adapter, common radius/frequency subsequence | Raw tail identification PASS154; exact paper Fourier profile instantiation |
| v12 source products | Actual A_j Q and VQ+W conjugate(Q), Holder estimates, MemLp | Actual Hodge M/Z and Fubini realization checked; original A0/V/source budget correspondence still blocked |
| v12 time integration | Source L43 budget, interval Holder, weak-test residual and limit machinery | ZC–ZG compiled in Run146; raw original regularity and reconstructed A0/V budget applications still audited |
| v12 fixed-cutoff compactness | NEW: actual cylinder representatives constructed; joint equicontinuity and L2 compact closure derived from energy/source integrals | ZI/ZJ now discharge budget/integral/representative/compactness internally; same-Q Hodge/MZ instance checked; original A0/V source application remains open |
| v12 local limits | Common-sequence nested compatibility and one strongly measurable glued limit, Run150 | Original-field common sequence and exact Theorem-7.1 nonlinear limit passage |
| v13-v20 | Existing scalar/finite/dependency kernels | Exact norm objects and transitive analytic hypotheses |
| v19 Lemma 14.7 | Fixed-anchor phase and dense-class/quantifier support | Actual Poincare measure-space and Fourier-operator instance |
| W1-W3 | Existing kernels | Not a continuous full-theorem verified prefix |
| Later W/RFCE/rigidity | No full-main-theorem certificate established | Full correspondence and reverse dependency audit |

## Current next load-bearing leaves

The ZJ endpoint now derives fixed-frequency compactness and a common strongly
measurable local limit from the raw smooth divergence PDE and concrete
representatives/time-source bounds. It does not assume hIntegral/hCompact.
ZK (PASS154) constructs all Q/F/G objects from the actual raw field,
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
