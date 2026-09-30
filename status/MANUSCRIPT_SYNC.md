# Manuscript sync record

Public verification repository: penghongzhong/sm.
Working branch: whole-paper-lean. Draft PR #6 remains unmerged.
Public content remains Lean, build configuration and audit metadata only.

## Current generated private working snapshot: LeanSync v6 CylinderBridge

- TeX: stereo_scalar_scattering_v20_W20_LeanSync_v6_CylinderBridge.tex
- TeX SHA-256: b62d8e90e0c60497b8bce741624c3aceafd03a1cf0dd9bc4193357d4e2515a95
- PDF: stereo_scalar_scattering_v20_W20_LeanSync_v6_CylinderBridge.pdf
- PDF SHA-256: 862167a8f0b93fb8949416002d377ddda1808e8ed777818427c856d12f693a0c
- PDF pages: 137
- Expanded node: v12:thm:tightness, printed Theorem 7.2, pages 12-16.
- New cylinder argument: equations (7.49)-(7.55), page 15.
- All 207 proof-bearing statements match v4 byte-for-byte; all old labels retained.
- 1263 unique labels; 0 missing references; 0 overfull boxes; 0 undefined
  references; 0 duplicate labels. There are 21 inherited hyperref PDF-string
  warnings, not a warning-free build. Final pages 12-16 rendered and inspected.
- SymPy: 10/10 finite product-rule/sign/exponent checks, not analytic certification.

The full TeX source recovered for this build was the registered v4 below.
Only interrupted v5 screenshots were available; no saved full v5 source was
recovered. Thus v6 is explicitly a v4-based working expansion, not an
assertion of complete v5 continuity. No historical manuscript was overwritten.
The artifacts were generated in the conversation workspace; this batch did
not save them back to Library. No new Library IDs are invented here.

## Registered private Library baseline: LeanSync v4

- TeX: stereo_scalar_scattering_v20_W20_LeanSync_v4.tex
- TeX SHA-256: 9f4f842d3981f4d1fc2c8172808a65837fcdd7faea8214996bf2524be5f98902
- PDF: stereo_scalar_scattering_v20_W20_LeanSync_v4.pdf
- PDF SHA-256: a6e98b81b0df8725d57464f0b91fe26657f9f9e55d8dc4adcef5e1e0323dec69
- PDF pages: 135
- Native Library TeX ID: libfile_73fc8ddbb50c8191b167d9a07c73e110
- Native Library PDF ID: libfile_69c2918b8db0819183b1b6bfc45e10dc

The target remains the full master originally supplied as 133 pages, not
its 36-page Lean-min. The v3 fixed-anchor phase repair is retained.
The v4 files were created/compiled and uploaded on 2026-09-28. That build
recorded zero undefined references and overfull boxes and inspected modified
pages. Three finite SymPy identities were checked at that historical stage.
Its original bridge batch was 952466cb06af03fccb78edda176a3dba4c8bd0fa;
the Run-42 checked repair was 297a68ba3cc6dbe0ff6cc4583b1b814f22ab295c.

## Current machine-checked code and precise correspondence

Run 123 / 36660803283 / job 109714901632: SUCCESS.
CHECKED_SHA=2f9e348dad3f5d1c6f5a8db5d444d5c46c2738d2.
42 public files compiled successfully. Read V12_RUN123_SUCCESS_20260930.md.
Run 119 previously verified c655aabab7c715fcc2bd1b0c8dfe281e7258f27b
with 40 files; Run 122 verified the weak-time integration support.

The new terminal compactness theorem uses actual cutoff/source operators
and constructs the compact-cylinder continuous representative. It derives
spatial/time equicontinuity and compactness, rather than accepting them as
hypotheses. It still takes source-space realization, uniform energy and
budget bounds, the PDE time integral identity and the actual local L2
representative equality as explicit inputs.

The v6 written proof additionally constructs compact spatial tests and
expands their kernel errors. Complete Lean instantiation of these tests,
their weak PDE residual, every-time representatives and the same-field
Hodge/source bounds remains open. So do the full common-limit/gluing and
Theorem-7.1 applications and later scattering dependencies.

A compiled conditional bridge is not full statement certification.
No full-paper completion percentage or complete TeX/PDF/Lean equivalence
is certified. Standard analysis and precisely registered published theorems
remain allowed; actual application hypotheses must be proved.

## Privacy

TeX/PDF, private build artifacts and private Git history are not uploaded
to this public repository. The original private repository and registered
Library v4 files are unchanged. Only metadata about the new private build
and the verified Lean work are recorded here.

## 2026-09-30: private V7 spatial integration-by-parts expansion

Private full V7 SpatialIBP TeX and PDF were built and saved. The PDF is
137 pages; all 207 original theorem/lemma/proposition/corollary environments
remain byte-identical to the full V6 source. The new equations 7.32–7.35
on page 14 spell out compact product integrability, first and second spatial
integration by parts, and the tested raw-PDE source. Intended Lean matches:
`v12_compact_test_spatial_ibp`, `v12_compact_test_spatial_ibp_twice`, and
`v12_compact_test_raw_pde_source` in ZC. These matches are not certification
until the corresponding declaration compiles without recovery axioms.

V7 TeX SHA256: cce7627d59799fc70b7c6561c8713de1a913a2e625abcd843b5edf47573af641.
V7 PDF SHA256: 5af9cb8be95afedff9cea061bf4532f01903fd6b60dcf633521ce97ce40f0eb8.
Final build: no overfull boxes, unresolved references or duplicate labels;
1267 distinct labels. Changed pages 13–15 visually inspected. Three SymPy
checks verify the first/second test derivative algebra and reflected sign;
they do not certify analytic/PDE claims. Private manuscript files remain
outside this public repository.

Run 144 actually compiled ZA and ZB successfully; ZC still had a final
basis-unfolding goal, blocking ZD–ZG. Run 145 tests that repair. The current
coverage ledger supersedes the historical Run-123 frontier above.

Run 145 subsequently compiled ZC and ZD with only the standard three axioms.
The V7 equations 7.33–7.35 now have compiled spatial-IBP/raw-source matches.
ZE still needs an explicit measure annotation; ZF/ZG remain dependency-blocked.
This is not full-paper certification.
