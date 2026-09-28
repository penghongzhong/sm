# Full W20 theorem inventory and coverage distance

Verification authority: synchronized 133-page W20 manuscript.

## Exact proof-bearing inventory

A direct parse of the synchronized TeX gives **207** theorem-like proof-bearing environments:

- 89 lemmas;
- 53 theorems;
- 31 propositions;
- 34 corollaries.

Counts by manuscript block:

| Block | Count |
|---|---:|
| v12 | 12 |
| v13 | 19 |
| v14 | 6 |
| v15 | 7 |
| v16 | 6 |
| v17 | 7 |
| v18 | 7 |
| v19 | 13 |
| v20 | 4 |
| W1 | 12 |
| W2 | 3 |
| W3 | 12 |
| W4 | 13 |
| W5 | 12 |
| W7 | 4 |
| W8 | 10 |
| W9 | 10 |
| W10 | 6 |
| W11 | 4 |
| W12 | 9 |
| W13 | 8 |
| W14 | 6 |
| W19 | 13 |
| W20 | 4 |
| **Total** | **207** |

The v12–v20 part contains 81 proof-bearing environments.  The later W1–W20 chain contains 126.

## Machine-green baseline reached on 2026-09-28

Public GitHub Actions run `36410664584`, attempt 2, concluded **SUCCESS** after checking out the latest `whole-paper-lean` head.

This certifies every Lean file that was present in the public repository at that run, including:

- the current Section 2 algebra/Fourier kernels;
- the repaired N001–N033 migration batch and its support declarations;
- T007 HHL null-form kernel;
- T033 exponent kernel;
- T001 coefficient kernel.

This does **not** mean 207/207 W20 statements are covered.  The short Lean-min inventory omits proof-bearing nodes that remain in the full W20 master.

## First full-master-only obligations

The earliest W20 nodes not exhausted by the compressed Lean-min spine include:

1. `v12:lem:sampling`;
2. `v12:prop:axial`;
3. `v12:lem:lattice`;
4. `v12:prop:countermodel`;
5. `v12:thm:IMS`;
6. `v12:cor:IMS-forcing`;
7. `v12:thm:relative`;
8. `v12:cor:relative-cocycle`;
9. `v12:thm:closure`;
10. `v12:thm:tightness`.

The first of these is now being split into exact standard-analysis interfaces plus a Lean-checked paper-specific constant kernel in
`lean/v12/V12_SamplingBudgetKernel.lean`.

## Distance convention

No percentage is declared from T001–T094 alone.

For full-master reporting, use:

- **green** = exact W20 statement mapped to compiled Lean or to a precisely registered allowed external theorem plus compiled paper-specific bridge;
- **yellow** = partial kernel/source reduction exists but exact W20 statement mapping is incomplete;
- **red** = an internal W20 proof-bearing edge remains neither proved nor source-reduced.

Since 126/207 proof-bearing environments lie in the later W-chain and most are not yet exact public-Lean mappings, the full-master project remains substantially incomplete even though the present public Lean corpus is machine-green.
