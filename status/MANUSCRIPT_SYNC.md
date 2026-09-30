# Manuscript sync record

Public verification repository: penghongzhong/sm.
Working branch: whole-paper-lean. Draft PR #6 remains unmerged.

## Current private manuscript snapshot — LeanSync v4

- TeX: stereo_scalar_scattering_v20_W20_LeanSync_v4.tex
- TeX SHA-256: 9f4f842d3981f4d1fc2c8172808a65837fcdd7faea8214996bf2524be5f98902
- PDF: stereo_scalar_scattering_v20_W20_LeanSync_v4.pdf
- PDF SHA-256: a6e98b81b0df8725d57464f0b91fe26657f9f9e55d8dc4adcef5e1e0323dec69
- PDF pages: 135
- Expanded node: v12:thm:tightness, printed Theorem 7.2,
  PDF pages 12–13, equations (7.8)–(7.24) in this private snapshot.
- Native Library TeX ID: libfile_73fc8ddbb50c8191b167d9a07c73e110
- Native Library PDF ID: libfile_69c2918b8db0819183b1b6bfc45e10dc

This remains the full master, originally 133 pages, not the 36-page Lean-min.
All 207 proof-bearing environments and the v3 fixed-anchor repair are retained.

## Historical v4 production record

The private v4 TeX/PDF were created/compiled and uploaded on 2026-09-28.
That build recorded zero undefined references and zero overfull boxes, with
modified pages inspected. Three finite SymPy identities were checked at that
stage; they were not a certificate of the analytic compactness argument.

The expansion defines finite-slab/cylinder L2 spaces, restrictions, a common
radius/frequency subsequence, local Cauchyness and compatible limit gluing.
Its original Lean bridge batch was 952466cb06af03fccb78edda176a3dba4c8bd0fa;
the later Run-42 checked repair was 297a68ba3cc6dbe0ff6cc4583b1b814f22ab295c.

## 2026-09-30 code update — not a new manuscript build

Run 119 verified code commit c655aabab7c715fcc2bd1b0c8dfe281e7258f27b:
40/40 public Lean files compiled, including the four analytic modules
V12_KernelConvolutionIdentity, V12_SourceProducts,
V12_SpatialEquicontinuity and V12_TimeSourceBridge.
Read V12_RUN119_SUCCESS_20260930.md for exact machine evidence and scope.

The private v4 manuscript files/hashes above are unchanged in this batch.
No new TeX/PDF was compiled. The new Lean lemmas support and refine parts
of its proof, but the full Theorem-7.2 statement and complete manuscript/Lean
equivalence are not yet certified. Code verification and manuscript build
identity are deliberately recorded separately.

## Formalization boundary

Actual spatial Fourier cutoff, local Lp restriction, common-subsequence,
source-product, spatial equicontinuity and conditional time-Holder support
are now compiled. Still required are the same-field spacetime/time-Lp
realization, Hodge-coefficient applications, original distributional PDE to
cutoff time integral identity, actual hCompact, measurable gluing, and the
exact Theorem-7.1 passage to the limit. The v19 full operator instance and
later scattering dependencies also remain subject to audit.

Standard analysis and precisely registered published results remain allowed;
the application hypotheses and internal bridges must be checked. No whole
paper completion percentage or full TeX/PDF/Lean equivalence is certified.

## Privacy

No manuscript TeX/PDF, private build artifacts or private Git history are
uploaded to this public repository. The present batch changes Lean and audit
metadata only. The original private repository is unchanged by this work.
