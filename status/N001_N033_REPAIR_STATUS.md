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
