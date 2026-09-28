# Full W20 theorem inventory and coverage distance

Verification authority: synchronized 133-page W20 manuscript
`stereo_scalar_scattering_v20_W20_LeanSync_v1`.

## Exact proof-bearing inventory — corrected from the actual synchronized TeX

A direct parse of the exact Library TeX gives **192** labeled theorem-like proof-bearing environments:

- 83 lemmas;
- 50 theorems;
- 27 propositions;
- 32 corollaries.

Counts by manuscript block:

| Block | Count |
|---|---:|
| v12 | 12 |
| v13 | 19 |
| v14 | 6 |
| v15 | 6 |
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
| W19 | 13 |
| W20 | 4 |
| **Total** | **192** |

The earlier provisional value 207 was incorrect and is superseded by this direct parse.

The private `section2-strict-sync` proof source contains two additional explicit v12 proof environments,
`v12:lem:chart-hodge` and `v12:lem:low-curv`, which are not theorem environments in the current 133-page Library edition.
When that stricter Section 2 is synchronized into the Library manuscript, the synchronized target will therefore gain those two explicit nodes; its filename/hash/page count must then be updated rather than silently treating the old 133-page file as unchanged.

## Machine-green baseline reached on 2026-09-28

Public GitHub Actions run `36410664584`, attempt 2, concluded **SUCCESS** while the workflow was configured to checkout the latest `whole-paper-lean` branch.

That run compiled every Lean file present at the then-current branch head, including:

- the Section 2 algebra/Fourier kernels;
- the repaired N001–N033 migration batch and its support declarations;
- T007 HHL null-form kernel;
- T033 exponent kernel;
- T001 coefficient kernel.

This does **not** mean 192/192 W20 statements are covered.  The compressed Lean-min inventory omits proof-bearing nodes that remain in the full W20 master.

## Current v12 full-master obligations

The exact current 133-page manuscript contains these 12 v12 proof-bearing nodes:

1. `v12:lem:coeff`;
2. `v12:lem:electric`;
3. `v12:lem:sampling`;
4. `v12:prop:axial`;
5. `v12:lem:lattice`;
6. `v12:prop:countermodel`;
7. `v12:thm:IMS`;
8. `v12:cor:IMS-forcing`;
9. `v12:thm:relative`;
10. `v12:cor:relative-cocycle`;
11. `v12:thm:closure`;
12. `v12:thm:tightness`.

The strict Section 2 source additionally isolates `v12:lem:chart-hodge` and `v12:lem:low-curv`; these are being retained as explicit verification nodes because they support the concrete reconstruction and low-frequency estimates used downstream.

## Distance convention

No percentage is inferred from T001–T094 alone.

For full-master reporting:

- **green** = exact W20 statement mapped to compiled Lean, or to a precisely registered allowed external theorem plus compiled paper-specific bridge;
- **yellow** = partial kernel/source reduction exists but exact W20 statement mapping is incomplete;
- **red** = an internal W20 proof-bearing edge remains neither proved nor source-reduced.

The denominator is the exact synchronized manuscript inventory, and it must be recomputed whenever the Library TeX is revised.
