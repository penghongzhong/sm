# v12 actual L2 and common-cutoff subsequence bridge

Private target: W20 LeanSync v4, 135 pages, Theorem 7.2, pages 12–13.
Full manuscript inventory remains 207; this document does not count the whole theorem as closed.

## Exact verified-program structure

Module: lean/v12/V12_FrequencyTightnessLimit.lean
Actually compiled code: 297a68ba3cc6dbe0ff6cc4583b1b814f22ab295c

The radius and frequency-cutoff indices are collected BEFORE selecting a
subsequence. The compact product has index type Nat x Nat. Projection of one
convergent product subsequence gives Cauchyness of every fixed cutoff in every
fixed local space. The cutoff limit theorem then uses that same subsequence.

The concrete spaces use EuclideanSpace R (Fin 2), EuclideanSpace C (Fin 2),
Lp at exponent 2, and the product of restricted time Lebesgue measure with
spatial Lebesgue measure. Integer spatial cylinders have radius R+1.
The localization is Mathlib's actual LpToLpRestrictCLM, not an arbitrary norm.

## Declaration-to-step map

- v12_cauchy_of_uniform_cutoff: epsilon/3 target Cauchy proof.
- v12_limit_of_uniform_cutoff: complete-space limit of that Cauchy sequence.
- v12_shared_cutoff_subsequence: one strictly increasing sigma for all (R,k).
- v12_countable_cutoff_limits: complete-space limits for every R on that sigma.
- v12_localize_coeFn: AE identity of the actual local restriction.
- v12_localize_norm_le: concrete Lp restriction is contractive.
- v12_localize_dist_le: contraction for the difference of two Lp elements.
- v12_spacetime_L2_common_subsequence: actual Bochner local L2 instantiation.

## Mathlib dependencies actually applied

Version: a98628e16c11f5167f16124105ddce53efa9bfe5; Lean 4.35.0-rc3.
- isCompact_pi_infinite
- IsCompact.tendsto_subseq and continuous_apply
- Metric.cauchySeq_iff, dist_triangle and complete-space Cauchy convergence
- MeasureTheory.LpToLpRestrictCLM and LpToLpRestrictCLM_coeFn
- MeasureTheory.norm_Lp_toLp_restrict_le
- the actual Lp metric/complete-space instances for exponent 2

## What the concrete theorem assumes

Q is an element of the slab L2 space; P is a family of cutoff maps on that
space; err tends to zero; norm(Q n - P k (Q n)) <= err k; each fixed localized
cutoff range has compact closure. Target Cauchyness, target convergence and a
common extracted subsequence are NOT assumptions.

## Remaining proof obligations

1. Derive Q's slab MemLp from the actual finite-time energy bound.
2. Construct P as the manuscript's spatial Fourier cutoff and instantiate hTail.
3. Derive the fixed-cutoff compactness hypothesis from the actual derivative
   estimates, Arzela–Ascoli and the continuous C-to-L2 embedding.
4. Formalize compatibility and measurable gluing of the local limit classes.

Items 1–4 are expanded in the private v4 proof but are not yet discharged by
this Lean module. Full coefficient closure (Theorem 7.1), the v19 operator
instance and the final RFCE/rigidity/scattering dependency audit remain.

## Compilation evidence

Run 40 (36423737538): prior full-file verification job SUCCESS.
Run 41 (36425511082), checked SHA 952466cb06af03fccb78edda176a3dba4c8bd0fa:
36 files attempted; 35 OK and the new L2 module failed at two unannotated Lp
aliases and the resulting dependent-family coercion. Seven other declarations
printed only standard logical axioms. Explicit : Type aliases in 297a68ba fix
that implementation error without weakening any hypothesis/conclusion.
Run 42 (36426551083), job 108941818434: SUCCESS.
Actual CHECKED_SHA: 297a68ba3cc6dbe0ff6cc4583b1b814f22ab295c.
The complete job log reports CHECKED_FILE_COUNT=36, all 36 COMPILE_OK,
zero COMPILE_FAIL. All eight declarations listed above compiled and their
printed axiom dependencies were exactly propext, Classical.choice, Quot.sound;
no sorryAx occurred in their dependency lists. The module compiled at
2026-09-28T13:12:14Z; the full-file sweep finished at 13:13:12Z.
Metadata-only commits after this code revision are not relabeled as newly
compiled code. This records an actual read of the completed job log, not a
prediction from a submitted repair.

Compilation of this conditional bridge does not certify the full W20 theorem.
