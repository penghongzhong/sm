# N001–N033 repair status

Source migration batch:
`lean/MIGRATION/SM_V21_N001_N033_MEGA_RESYNC_20260920.lean`

Current public repair commit:
`a841dcbe91be13511156161a3d7738cc948d96a2`.

## Historical real-CI evidence

The private source repository previously ran Lean CI on the same migration family.

At failing run 36255074469:
- environment smoke test: PASS;
- T001 coefficient budget: PASS;
- Section 2 coefficient constant: PASS;
- Section 2 electric algebra kernel: PASS;
- Section 2 low-frequency kernels: PASS;
- N001–N033 migration batch: FAIL.

The logged hard failures were:

1. T026 short-stability / Volterra absorption proof: unsolved inequalities and a syntax break.
2. `helper_v17_Coulomb_unique_gradient_zero`: malformed proof line after deriving
   `(-i * conj(h)) * dh = 0`.

## Repairs now present in public branch

- synchronized the newer private repair-line version, in which the T026 Volterra/short-stability proof is already rewritten and the historical unsolved goals are removed from the source;
- repaired the Coulomb uniqueness step into two commands:
  first obtain the product-zero equality, then apply `mul_eq_zero` with the proved nonzero phase factor;
- static scan: zero `sorry`, zero `admit`, zero custom `axiom` declarations.

## Current classification

There is no remaining hard error known from the historical CI log after the repairs above.

A fresh public GitHub Actions run is still required before promoting the complete N001–N033 batch to machine PASS. The public repository currently has no workflow-run record, so this ledger does not claim a new CI PASS yet.


## Fresh public CI — 2026-09-28

Manual public run:
- workflow run: `36408846241`;
- branch: `whole-paper-lean`;
- tested commit: `f98566fefedba1bc45863898c7d5bec40727b182`;
- environment/setup/cache/placeholder scan: **PASS**;
- compilation reached the N001–N033 migration batch;
- first hard failure: `T026 = v13:thm:short-stability`, around source lines 2921–2999.

The failure is an implementation-level Lean proof break in the coefficient-enlargement step
[
C_E\le C_E+1
]
and the associated monotone multiplication, not a new PDE or manuscript contradiction.
The log also showed that the earlier T007–T025 declarations had elaborated before this point; their `#print axioms` output used only Lean's standard logical axioms `propext`, `Classical.choice`, and `Quot.sound`, with no custom paper axiom.

Repair commit:
- `b1b805b7161870a1c42268edc120f763ca0f3806`;
- rewrote the T026 coefficient enlargement as an explicit two-step `calc`, separating
  `CE * oldSum <= CE * newSum` and `CE * newSum <= (CE+1) * newSum`.

Status: **REPAIR COMMITTED; fresh rerun required**.
