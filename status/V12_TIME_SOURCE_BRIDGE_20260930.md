# V12 cutoff time-source bridge — current status

## Verified code authority

Run 119 (36654904541), job 109697026316, SUCCESS.
Actual CHECKED_SHA: c655aabab7c715fcc2bd1b0c8dfe281e7258f27b.
40/40 public Lean files compiled; no compile failure. All printed axiom
lists of the four new modules contain only the standard logical axioms.
Read V12_RUN119_SUCCESS_20260930.md for the completed-log evidence.
Draft PR #6 remains unmerged; no manuscript is published here.

## Repair history and retained declarations

Run 116 failed on an ambiguous Schwartz-to-Lp measure argument, a regressed
ENNReal conjugacy proof, and use of a source operator before its definition.
The core was restored byte-for-byte to the Run-114 blob
f658154bdf75ab078f1c85fef76d3c082d3d177c, preserving its compiled proofs.
Run-115 additions were retained with their original theorem names.

The general Schwartz representative identity now lives in
V12_KernelConvolutionIdentity.lean; derivative identities live in
V12_TimeSourceBridge.lean after importing their actual operator definitions.
Runs 117/118 located further elaboration, multiplication and rpow issues.
They were fixed without deleting a theorem or adding a target-as-hypothesis.

## Verified analytic modules

V12_KernelConvolutionIdentity: actual integral/Lp/Schwartz identification.
V12_SourceProducts: F_j=A_j Q and G=V Q+W conjugate(Q), with actual Holder
product bounds and MemLp, including conjugation on the two-component field.
V12_SpatialEquicontinuity: actual fixed-kernel convolution equicontinuity
from uniform input L2 bounds and L2 translation continuity.
V12_TimeSourceBridge: exact derivative source CLMs, source time-L43 budget,
finite budget, source MemLp, FTC and a symmetric quarter-Holder estimate.

The terminal time theorem applies to the actual cutoff representative,
but still requires its exact Banach-valued derivative identity and source
membership. Compiling this conditional theorem is not a full PDE certificate.

## Remaining paper-specific bridges

- Hodge coefficient reconstruction estimates and their same-field M,Z inputs.
- Spacetime-to-time-Lp realization of Q, A_j Q and VQ+W conjugate(Q).
- Original distributional evolution to the cutoff time integral identity;
  endpoint/all-time representative regularity must be justified.
- Actual cylinder identification and fixed-cutoff hCompact.
- Measurable local-limit gluing and the Theorem-7.1 passage to the limit.

Private manuscript: LeanSync v4, unchanged at 135 pages. No new PDF compiled.
The previous 55–60% whole-paper and 75% v12 estimates lack an audited
full-theorem numerator and must not be used as completion certificates.
