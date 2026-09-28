# Manuscript sync record

Public verification repository: `penghongzhong/sm`; working branch:
`whole-paper-lean`; draft PR #6 remains unmerged.

## Current private manuscript snapshot — LeanSync v3

- TeX: `stereo_scalar_scattering_v20_W20_LeanSync_v3.tex`
- TeX SHA-256: `ffe45c28db9d118eb2366b745a46aa9d10d17b120197a6d83433ea696bd72fa0`
- PDF: `stereo_scalar_scattering_v20_W20_LeanSync_v3.pdf`
- PDF SHA-256: `25f8be5278d37fcdab0db87659b7e3b01f9a436a966fb6859efab389ea121e85`
- PDF pages: 134
- Repaired node: `v19:lem:phase-profile-constant`, printed Lemma 14.7,
  PDF pages 51–52, equations (14.43)–(14.59).
- Native Library TeX ID: `libfile_c9179dd89bc08191a058b8de066bdee0`
- Native Library PDF ID: `libfile_85efd32c5ea0819189bd053d248f859d`
- Both artifacts were actually created and uploaded to the ChatGPT Library.

The target is the FULL W20 master originally supplied as 133 pages.
This remains the same manuscript project, not the 36-page Lean-min reference.
The v3 proof expansion retains all 207 proof-bearing environments.

## v3 repair

The phase sequence is selected from a fixed unit-ball mean before any choice
of test function or larger ball. An overlap estimate then proves local L2
agreement on all fixed larger balls for the same sequence. Bounded and
escaping free-time cases and the uniform density extension are explicit.
The zero-mean branch and local Sobolev regularity are explicitly defined.

XeLaTeX was run to stable references. Undefined-reference warnings: 0.
Overfull-box warnings: 0. Modified PDF pages were rendered and inspected.
Five finite SymPy identities passed; they do not certify analytic limits.

## Formalization boundary

Read `SEMANTIC_VERIFICATION_CORRECTION_20260928.md` and
`WHOLE_PAPER_COVERAGE.md`. Compilation of kernels is not full statement
coverage. The new anchor kernels have not yet been instantiated as the full
function-space/Fourier-operator theorem. A successful CI run must not be
reported as full-paper certification.

Standard analysis and precisely registered published theorems remain allowed
foundations. Concrete hypotheses and all internal analytical bridges must be
proved/instantiated; they cannot be replaced by Markdown labels.

## Privacy

TeX, PDF, private build artifacts and private Git history are not uploaded to
this public repository. Only the version metadata, Lean code and audits are
public. The original private repository is not modified by this batch.
