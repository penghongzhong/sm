# Run 132: verified concrete test-source modules, not a green full build

Repository: penghongzhong/sm
Branch: whole-paper-lean
PR: #6, Draft and unmerged
Run ID: 36668224411
Job ID: 109737443907
CHECKED_SHA: 6e42a20a40912ba9f7acd17da96a957c8a262eee
Lean: 4.35.0-rc3
Mathlib: a98628e16c11f5167f16124105ddce53efa9bfe5
Overall result: FAILURE
CHECKED_FILE_COUNT: 49
COMPILE_OK: 45
COMPILE_FAIL: 4

The completed job log was read. Checked SHA was printed at
2026-09-30T04:18:51.1685937Z; the final count was printed at
2026-09-30T04:25:26.3729042Z. This record does not promote successful
individual modules into a successful whole-branch build.

## Newly verified modules

### V12_YTestSourcePairingLimit.lean

COMPILE_OK at 2026-09-30T04:24:15.3545073Z.
All eight printed declarations depend only on propext, Classical.choice,
Quot.sound, without sorryAx:

- v12_pairing_norm_L1_le
- v12_pairing_norm_L1_tendsto
- v12_norm_L1_add_tendsto
- v12_testSourceFromLpKernels_integrable
- v12_testSourceFromLpKernels_L1_tendsto
- v12_testSourceFromLpKernels_L1_tendsto_of_MemLp
- v12_schwartzL2_convolutionRep_integral
- v12_compactSpatialTest_endpoint_to_BCF

The module proves the actual continuous-bilinear estimate
integral ||B(u,f(t))-B(v,f(t))|| <= ||B|| ||u-v|| integral ||f(t)||.
It deduces time norm-L1 convergence from spatial kernel norm convergence,
then combines all four actual source terms, with weak-test signs i,-2,-2,-i.
The finite-time specialization uses Linfty_t L2_x, L2_t L2_x and L43_t L43_x.
The endpoint theorem identifies the concrete compact-test integral limit
with the actual BCF convolution representative, using explicit Lebesgue
measure in the Schwartz-to-Lp representative conversions.

The generic four-term theorem still requires the spatial derivative-kernel
Lp limits; it does not manufacture the original PDE residual.

### V12_YZeroOrderTestLimit.lean

COMPILE_OK at 2026-09-30T04:24:21.7580003Z.
All seven printed declarations depend only on the same standard axioms:

- v12_Lp_tendsto_of_ae_eLpNorm_error
- v12_compactSpatialTestSchwartz_apply
- v12_compactSpatialTestL4_ae
- v12_reflectedSchwartzL4_ae
- v12_compactSpatialTestL4_tendsto
- v12_L4L43Pairing_eq_integral_of_ae
- v12_actual_zeroOrder_test_source_L1_tendsto

The same concrete test psi_R,x(y)=chi(y/(R+1)) K(x-y) is realized as a
Schwartz function and an L4 class. Its L4 convergence is derived from the
actual cutoff error, not supplied as an assumption. The actual zero-order
source integral then converges in time L1 to the same K*G point value.
The raw-function/quotient-class norm identity is proved explicitly.
All these limits are for FIXED x; no uniform-in-all-x conclusion is asserted.

### V12_TestCutoffApproximation.lean

COMPILE_OK at 2026-09-30T04:22:45.8783094Z, with standard printed axioms.
This proves smooth compact support, finite nonzero-p zero-order errors and
actual endpoint integral convergence for the concrete spatial tests.

## Failed files and subsequent repair boundary

At the immutable Run-132 SHA, TestDerivatives and YEveryTimeEnergy failed;
TestNormLimits and ZATestDerivativeRealization could not import failed
upstream oleans. Recovery sorryAx in failed files are NOT valid proofs.

Subsequent code commit cc061b608dfa509463f84b48c88056ed453c441a splits the
scale/reflection chain rules into separately proved declarations and uses
the proved first-derivative equality when differentiating the second time.
Run 135 (36669156573) is its separate check. Its result must be recorded
from its completed log; Run 132 does not certify that later source.
The every-time-energy filter has also been made explicit in a later source.
Further staged source-identification code is not certified by this report.

## Remaining original-PDE obligations

Complete the actual derivative-kernel instances, identify the limiting
source with the same cutoffTimeSource, instantiate the original Coulomb
PDE compact-test residual and the tested curve's time identity, and prove
the same-field Hodge coefficient and time-Bochner realization inputs.
Then discharge the actual local representative input, common local limits,
measurable gluing and Theorem 7.1. Full Theorem 7.2, full-paper scattering
and complete TeX/PDF/Lean correspondence remain uncertified.

This user-turn's work did not modify or recompile the private v6
CylinderBridge manuscript. No full manuscript or private Git history is
uploaded to this public repository. File count is not theorem coverage;
no whole-paper percentage is inferred. Independent secondary proof
checkers were not run.

Six finite SymPy identities were actually checked in the conversation
workspace: first and second test derivatives in two directions, reflected
gradient sign, and the quarter Holder exponent. These do not certify
analytic convergence, the PDE residual or Lean compilation.

This is metadata only. No source exclusion, axiom addition or statement
weakening is used to label an unsuccessful build successful.
