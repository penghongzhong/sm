# Manuscript sync record

Public verification repository: `penghongzhong/sm`; working branch:
`whole-paper-lean`; draft PR #6 remains unmerged.

## Current private manuscript snapshot -- LeanSync v4

- TeX: `stereo_scalar_scattering_v20_W20_LeanSync_v4.tex`
- TeX SHA-256: `9f4f842d3981f4d1fc2c8172808a65837fcdd7faea8214996bf2524be5f98902`
- PDF: `stereo_scalar_scattering_v20_W20_LeanSync_v4.pdf`
- PDF SHA-256: `a6e98b81b0df8725d57464f0b91fe26657f9f9e55d8dc4adcef5e1e0323dec69`
- PDF pages: 135
- Expanded node: `v12:thm:tightness`, printed Theorem 7.2,
  PDF pages 12--13, equations (7.8)--(7.24).
- Native Library TeX ID: `libfile_73fc8ddbb50c8191b167d9a07c73e110`
- Native Library PDF ID: `libfile_69c2918b8db0819183b1b6bfc45e10dc`
- Both artifacts were actually compiled/created and uploaded to the Library.

The target remains the FULL W20 master originally supplied as 133 pages,
not the 36-page Lean-min. This proof expansion retains all 207 proof-bearing
environments and the v3 fixed-anchor phase correction.

## v4 expansion and correspondence

The proof explicitly defines the finite-slab L2 space, each cylinder L2
space and restriction map before use. A compact product indexed by radius
and frequency cutoff selects one subsequence for every pair. Restriction
contraction and the uniform cutoff tail then imply local Cauchyness.
The manuscript also writes out consistency and measurable gluing of the
local limits.

The code is `lean/v12/V12_FrequencyTightnessLimit.lean`.
The batch at `952466cb06af03fccb78edda176a3dba4c8bd0fa` adds the common
subsequence extraction and actual Bochner L2 restriction instances.
Its CI result must be recorded separately; this identity record does not
predeclare compiler success or full theorem certification.

XeLaTeX was run to stable references. Undefined-reference warnings: 0.
Overfull-box warnings: 0. Modified PDF pages were rendered and inspected.
Three finite SymPy identities passed; they do not certify compactness,
Fourier estimates, measure-theoretic limits or subsequence extraction.

## Formalization boundary

Read `SEMANTIC_VERIFICATION_CORRECTION_20260928.md` and
`WHOLE_PAPER_COVERAGE.md`. Full v12:thm:tightness still needs:
1. the actual field's slab MemLp from the energy bound;
2. the spatial Fourier cutoff and its matching global tail;
3. fixed-cutoff compactness from the concrete space/time estimates;
4. consistency/gluing of local representatives at the Lean level.

The new theorem's explicit local compactness and tail assumptions are not
being declared proved merely by writing this file. The v19 full
function-space/Fourier-operator instance also remains outstanding.
Standard analysis and precisely registered published results are allowed;
the concrete application hypotheses and internal bridges must be checked.
No full-paper percentage is certified.

## Privacy

TeX, PDF, private build artifacts and private Git history are not uploaded to
this public repository. Only version metadata, Lean code and audits are
public. The original private repository is unchanged by this batch.
