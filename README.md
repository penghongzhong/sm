# Schrödinger Maps — Whole-Manuscript Lean Verification

## Verification target — confirmed 2026-09-28

Verify the **full W20 Schrödinger-map scattering manuscript**, whose current synchronized edition has **133 pages**. Do not substitute the 36-page Lean-min manuscript for this target.

- Master baseline: `stereo_scalar_scattering_v20_W20`.
- Current private TeX: `stereo_scalar_scattering_v20_W20_LeanSync_v1.tex`.
- Current private PDF: `stereo_scalar_scattering_v20_W20_LeanSync_v1.pdf`.
- Exact file digests: `status/MANUSCRIPT_SYNC.md`.
- Auxiliary index only: `SM_Lean_Min_v4_SYNC_T025_T027_20260918`.
- Imported migration material: `SM_V21_N001_N033_MEGA_RESYNC_20260920.lean`.

The 36-page edition and its T001–T094 identifiers may help locate proofs. They do not define or limit the full-master coverage requirement. Imported Lean code must be checked against the actual W20 statements and all of their internal dependencies.

The page count identifies the current edition, not an artificial limit on later corrected manuscripts. Versioned filenames and hashes identify future revisions.

## Public/private separation

This public repository contains Lean verification code, Lean/Lake and CI configuration, and verification metadata only. Manuscript TeX/PDF files remain in the user's ChatGPT Library/private working area. Do not publish manuscript sources, PDFs, manuscript build artifacts, or private repository history here. The original private repository is not to be made public or deleted by this workflow.

The imported code snapshot originated from private verification branch `section2-strict-sync`, commit `0681282c197012f204785bccabcd5057668bfd95`; this identifies provenance, not completed whole-paper certification.

## Foundations and acceptance

- Use Lean/Mathlib foundations and explicitly registered standard analysis or published external theorems.
- Record each external theorem's exact statement, source, hypotheses, and its application to the manuscript's objects.
- Prove internal manuscript results and the bridges between concrete PDE objects and abstract Lean statements; do not assume the result being verified or an equivalent internal conclusion.
- No `sorry`, `admit`, or custom axioms for internal proof obligations.
- A compiled finite-algebra kernel or imported migration batch does not certify the full surrounding analytic theorem.
- Whole-paper completion requires the full W20 inventory and reverse dependency audit, exact statement correspondence, actual Lean build evidence, and matching manuscript digests. It is not determined by the T001–T094 count alone.

## Working route

Continue on `whole-paper-lean` through PR #6. The current ledger starts with the Section 2 analytic bridges, then proceeds through v13–v20 and W1–W20 to the scattering theorem. See `status/WHOLE_PAPER_COVERAGE.md` for recorded obligations.

For each mathematical repair: identify the W20 equation/theorem, repair the private TeX, compile and inspect the matching private PDF, update the Lean proof, run verification, then update the synchronization record. A hash match identifies files; mathematical correspondence requires a separate theorem-by-theorem check.

This scope confirmation does not itself claim a new Lean PASS or completion of the scattering proof.
