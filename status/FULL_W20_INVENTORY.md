# Full W20 theorem inventory and coverage distance

Verification authority:
\`stereo_scalar_scattering_v20_W20_LeanSync_v2\` (134 pages).

The original 133-page W20 master remains the baseline; LeanSync v2 is its
current synchronized correction. Pagination increased by one page after the
v19 unit-modulus Poincare normalization was made explicit.

## Exact proof-bearing inventory

A whitespace-tolerant parse of every
\`theorem/lemma/proposition/corollary\` environment in LeanSync v2 gives
**207** labeled proof-bearing environments:

- 89 lemmas;
- 53 theorems;
- 31 propositions;
- 34 corollaries.

The temporary value 192 was a parser error: it missed environments whose
\`\\label{...}\` begins on the following line.  In particular it missed
\`v15:prop:mix-reduction\` and the W13/W14 blocks.

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

Thus the pre-W blocks v12--v20 contain **81** proof-bearing environments and
the later W blocks contain **126**.

## Current verified front

Machine-green public CI has certified the current Lean corpus through v19.
Exact full-master audits are present for v12--v19, and v20 is the current
next block.

A node is GREEN only when every paper-specific step has a compiled kernel or
exact dependency proof and every remaining analytic step has a
hypothesis-matched standard/published source registration.

## Distance convention

The denominator is always the 207 exact proof-bearing environments of the
current synchronized manuscript. Definitions are audited as dependencies but
are not counted in this denominator.

No claim of "full-paper verified" is made until W1--W20 are also exact-mapped
and machine-green.
