# V12 cutoff time-source bridge — 2026-09-30

## Authority and repair

Work stays on `whole-paper-lean`; draft PR #6 remains unmerged.
The manuscript remains private LeanSync v4 (135 pages); no TeX/PDF or private
history is added to the public verification repository.

Run 116 checked 48cc9c20fa40dc9838f66caaaa5ba27eeb3ef4a7 and FAILED.
Actual errors: ambiguous `k.toLp 2 (x-y)` used a spatial point as the optional
measure argument; bare ENNReal `norm_num` did not prove Holder conjugacy;
`v12_cutoffLineDerivBCFCLM` was used before its definition.

The core file is restored byte-for-byte to the Run-114 blob
f658154bdf75ab078f1c85fef76d3c082d3d177c from commit
857acba0cc922de825051734a5e6a84e39cc3a65. This retains the already-compiled
real-to-ENNReal conjugacy proof. All Run-115 mathematical additions are
moved to `lean/v12/V12_TimeSourceBridge.lean`, with their original names,
explicit Lp typing and correct dependency order. No theorem is dropped.

## New analytic chain

The new module defines the actual BCF source

`i (Delta K_N)*Q + 2 (partial_1 K_N)*F_1 + 2 (partial_2 K_N)*F_2 - i K_N*G`.

It proves its time-L43 bound from the time-Linfinity spatial-L2 norm of Q,
the time-L2 spatial-L2 norms of F, and the time-L43 spatial-L43 norm of G.
The explicit budget retains measure(I)^(3/4) and measure(I)^(1/4).
It then proves budget finiteness, source MemLp, FTC, the actual interval
integral bound and the symmetric quarter-Holder increment inequality.
The terminal field is the existing actual cutoff convolution representative,
not an arbitrary abstract norm or an unspecified operator.

## Remaining paper-specific hypotheses — NOT closed

- Construct the time-Lp classes from the same spacetime Coulomb fields.
- Instantiate F_j=A_j Q and G=V Q+W conjugate(Q), with the actual M,Z bounds.
- Derive the BCF derivative identity from the original distributional PDE,
  including justified differentiation/convolution and time representatives.
- Combine the time estimate with spatial equicontinuity and actual cylinder
  representative identities to discharge fixed-cutoff hCompact.
- Prove compatible measurable gluing and the Theorem-7.1 limit passage.

No conclusion of Theorem 7.2, compactness or scattering is an input to the
new estimates. Nevertheless, compiling their explicit conditional statement
is NOT a full PDE certificate. Earlier conversational estimates of 55–60%
whole-paper coverage and 75% V12 coverage have no verified numerator and
must not be used as certified completion figures.

## CI boundary

PENDING for this batch until a completed job log has been read. The workflow
now checks an immutable event SHA and emits local .olean files so the new
module imports the exact core instead of duplicating its definitions.
No source is rewritten at build time, no file is excluded, and no additional
write permission is granted to Actions.
