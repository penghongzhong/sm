# Full W20 manuscript inventory -- not a coverage certificate

Current authority: `stereo_scalar_scattering_v20_W20_LeanSync_v4` (135 pages).
The target remains the full W20 manuscript originally supplied as 133 pages.
The 36-page Lean-min edition is only an auxiliary reference.

## Documentary count

The actual v4 TeX retains 207 labeled theorem/lemma/proposition/corollary
environments (89 lemmas, 53 theorems, 31 propositions, 34 corollaries).
The v4 change expands the proof of v12:thm:tightness, not its statement or
the inventory. The temporary historical value 192 missed labels placed on a
line after their environment opening.

| Block | Environments |
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
| Total | 207 |

The pre-W blocks contain 81 environments; later W blocks contain 126.
Neither ratio measures proof difficulty, elapsed work or certified completion.
Definitions and unlabeled analytic steps also belong to the dependency audit.

## Corrected formal-evidence boundary

Read `SEMANTIC_VERIFICATION_CORRECTION_20260928.md` and
`WHOLE_PAPER_COVERAGE.md`. Historical claims that all v12 or v19 statements
were GREEN are superseded: a compiled scalar kernel and a prose list of
standard theorems do not instantiate the actual PDE objects.

This v4 batch moves beyond the earlier abstract cutoff lemma: it instantiates
actual Bochner L2 spaces and continuous linear restriction and constructs a
common subsequence for all radius-cutoff pairs. Its concrete theorem still
assumes the uniform tail and fixed-cutoff compactness. Actual Fourier
cutoffs, energy-to-MemLp, compactness from space/time estimates and measurable
gluing remain proof obligations. Read the actual CI result for each commit.

Kernel construction has reached W1--W3. This is not a continuous fully
verified prefix of the manuscript. No certified full-statement numerator or
completion percentage is currently recorded. Count a statement only after
its hypotheses, conclusion, operators, regularity and quantifiers match the
manuscript and all internal dependencies are discharged.

Standard analysis and precise published external theorems remain allowed;
the task is not to reconstruct all analysis from zero.
