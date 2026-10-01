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

Run 146 compiled ZE–ZG: exact raw/Lp source identification, compact-test
time identity, and removal of the test cutoff. The new gluing candidates map
to existing labels v12:eq:localL2-compatible and v12:eq:localL2-gluing; the
least containing cylinder is exactly the paper's disjoint annulus selector.
These gluing candidates are pending compilation. No manuscript statement
has been weakened to obtain these results.

## Private V8 Bochner/Gluing build

Full V8 was generated from saved V7 and compiled to 138 pages. All 207 original
theorem-class environments remain byte-identical, with 1269 unique labels
and no missing references, overfull boxes or duplicate-label warnings.
Pages 13 and 16 were rendered and inspected. Inherited bookmark/font-substitution
warnings remain; no missing glyph or clipping was observed.

V8 TeX SHA256: ff22a5880c2f761ce02d71a157f52c6d7d2fa489b3a6500111e23276fe9c0119.
V8 PDF SHA256: c1d6cb201368f7aadf582c37f85f2ad9d83e54d9baac066fa97d53975af7767e.

New labels v8:eq:section-distance-measurable (7.22) and
v8:eq:section-fubini-norm (7.23), page 13, correspond to the pending
YMeasurableLpSections/YTBochnerSectionNorm declarations. The same page explains
why the every-time energy representative also has Bochner measurability.
Existing local compatibility/gluing labels (7.68–7.69), page 16, now explain
least-cylinder selection and the strongly measurable representative.
The original statements and the paper's hypotheses were not weakened.

Run 147 compiled Coulomb RHS conversion and spatial Fubini slices; full
Bochner and gluing modules are pending. Written mathematics and PDF generation
do not imply a Lean pass. Private manuscript artifacts stay outside GitHub.

## Private V9 ActualSlab sync (2026-09-30)

138 pages; 207 original theorem-class environments byte-identical to V8;
1271 unique labels, no missing references, duplicates or overfull boxes.
Three XeLaTeX passes and XDV conversion succeeded; pages13–14 visually checked.
New v9:eq:actual-slab-cutoff (7.24) and v9:eq:actual-slab-cutoff-bound (7.25),
page13, identify the same raw/cutoff slab classes and finite-time norm bounds.
The associated YW/YX Lean candidates are blocked by YT in Run150, so these
new formulas are not marked formally verified. Original statements unchanged.
TeX SHA256 c4bb9fa5d1b72d85d65d71bb22bd7ea511715b051e566d370aa53ff934461642
PDF SHA256 8c5dcd566e0ebf3513f325a7b4f30b0da000e7a10150987c07ab9ccf37c7d469
Both artifacts were privately saved; neither is committed to this public repository.

## Private V10 exact HLS-source sync (2026-09-30)

138pages;207 original theorem-class environments unchanged. The author/AMS
primary source Tao, An Epsilon of Room I, Corollary1.11.18 p182 is now cited
with exact assumptions and the dimension2/exponent4/3-to4 specialization.
No Lean HLS application is claimed by this bibliographic registration.
Three complete XeLaTeX passes and PDF conversion succeeded after clearing
truncated auxiliary files; pages5 and137 visually checked. No overfull boxes
or missing references in the final log.
TeX SHA256 d3577339c3fb30401eb0cad5ef6cde874b55a11717c348aa33ee920658e709cc
PDF SHA256 1bc33e06fe8890978ba34038a95a071b701bae19c8b32bc1334d97c202c23081
Privately saved; no TeX/PDF is included in this public repository.

## Private v11 HodgeBounds (2026-09-30)

138 pages; all207 original statement environments unchanged fromv10.
Adds actual |B|<=2|Q|² and normalized far-field bound2M²/(pi L), plus
near-kernel p<dimension2 check in Theorem7.1 proof. Label
v11:eq:actual-Hodge-far=(7.6),page11, visually inspected.
Three XeLaTeX passes/PDF conversion complete; no unresolved references,
no overfull boxes. Corresponding curvature/far-application Lean files remain
candidates pending CI; Hodge kernel itself passedRun153.
TeX SHA256 c8fff49d67fbbad7625b20d9adb2eff8d8bbf98d967272ae1067d6566a77cd87
PDF SHA256 fef8b666253488b025857ec9315e6cf69515cfca69ab2bc744b5d753ab3ecfdb
Private TeX/PDF never included in public repository.

## Private v12 ClosureBounds (2026-09-30)
138pages, all207 original statement environments unchanged. Theorem7.1
proof now gives explicit local subsequence/Fubini/Fatou and countable
exhaustion for inherited M/Z bounds, without invoking unspecified weak-star
compactness. ThreeTeXpasses/PDFconversion complete, pages11/12 visually
checked, nooverfull or unresolved references. Lean counterparts YOInheritedBounds
and YPInheritedEnergy are candidates, not yet compiled.
TeX SHA256 f5f01522fb988eba5ee0db916d2d36a9270bc0e38e9498ae678a2870196ffe42
PDF SHA256 7f070cf3a3294a399c246e17628495fc2dbb335488ad4c074d07b750a8486c7c
Private manuscript files remain outside public Git history.


## Private working v13 CoefficientClosure

139 pages; all 207 original proof-bearing environments byte-identical to v12.
Expanded the concrete dense-test weak closure and the exact zero-homogeneous
Riesz multiplier normalization. Three XeLaTeX passes and PDF conversion
completed; pages12/13 visually checked. No overfull boxes or unresolved
references. Existing CJK bold-font fallback warning is unchanged.
TeX SHA256 475e25e84e4203126cc90e6283433b7b4db6782cc71078401f36e5b621ce9303
PDF SHA256 f6f4c32b021cc5a58c36e4350ac0ffe566b35dd45d44507b56a51fe5c2167ea7
These private files are not included in this public repository.

## Private working v14 HodgeLocalLimit

139 pages; all 207 original proof-bearing environments byte-identical.
Expanded the same-field near/far argument at p=4/3: actual cutoff density,
Young convolution, time-norm upgrade, and explicit finite-cylinder far error.
Three XeLaTeX passes and PDF conversion completed; pages12/13 visually checked.
No overfull boxes or unresolved references. Existing font fallback unchanged.
TeX SHA256 b1083bfae1ebbc11872ec5def2d5ea4e06b052ab9f051ead00f2ca04ed08b23a
PDF SHA256 9177c8aa0e84afe9cba87955af63d37d024159591d9e19cbefa2ead5b0a0a121
These private files are excluded from public Git history.

## Private working v15 FubiniRiesz

139 pages; all 207 original proof-bearing environments byte-identical.
Expanded the scalar spacetime/Bochner L2 isometry, its onto proof by simple
functions and closed range, joint Riesz realization and same-field S/m/A0
weak closure. Three XeLaTeX passes/PDF conversion completed; pages12/13
visually checked. No overfull boxes or unresolved references; existing font
fallback unchanged. This text update does not mark candidate Lean files green.
TeX SHA256 b187a1d2bc71f46648abbeae3125310ef50d98c89303fc3cacab11ea31b4324e
PDF SHA256 4ba685851d4f7dbbedd260c0e3f4ebf14b9821251d2ff38c7a3b6ce33e162938
Private manuscript files remain excluded from public Git history.

## Private working v16 OriginalTests

139 pages; all207 original theorem/lemma/proposition/corollary environments
byte-identical to v15. Expanded exact original tensor/S/mass/Riesz section
correspondence and local-domain compact-test integration by parts, including
twice differentiating tests and proving weighted integrability from support.
Three XeLaTeX passes/PDF conversion completed; pages13/14 visually checked.
No overfull boxes or unresolved references; existing CJK font fallback only.
Corresponding YSFBOriginalTemporalSlices and YZZGLocalSmoothIntegration are
unverified candidates; this manuscript sync is not a Lean certificate.
TeX SHA256 80cae09bb1593a7e073bfa3fe394d53788a705eaf8bfc249c720f1fd0dc9a23b
PDF SHA256 00f706ef314d2d60b57968e4e7a5d8c967fc6ad87bc0e480d5902a6c15c9eba2
Private manuscript files are excluded from public Git history.

## Private working v17 SlabSourceClosure

139 pages; all207 original statement environments byte-identical to v16.
Added interval-only smooth-field zero extension, exact preservation of raw
Q/Hodge/tensor/A0 on the slab, and actual zero-order weighted integrability.
Three XeLaTeX passes/PDF conversion completed; pages12/13 visually checked.
No overfull boxes or unresolved references; existing font fallback only.
Pending Lean applications are not certified by this manuscript sync.
TeX SHA256 94e6627adbf8108f9a347edebd1c21700dc8ec5f358028189fc60e4b826f3b78
PDF SHA256 e43e1e968d6a4711a83d9b15389c78b12cef5c956d9f8030fb05aa99955ebc8d
Private manuscript files remain excluded from public Git history.

## Private working v18 SpatialConstraints

139 pages; all207 original statement environments byte-identical to v17.
Expanded original div/curl compact identities, same-sequence curvature and
connection limits, torsion AQ tests and internally proved integrability.
Three XeLaTeX passes/PDF conversion completed; pages12/13 visually checked.
No overfull boxes or unresolved references; existing font fallback only.
Corresponding new Lean modules remain candidates pending actual compiler.
TeX SHA256 de73499d4941d8890364a32cc1cc449c911d05e51f4ecc3261cc032bfd303675
PDF SHA256 24f2eaeda37c42e90688d18debd80cf05bee39130e09212566e98b8b12fd8a3e
Private TeX/PDF remain excluded from public Git history.

## Private working v19 OriginalSourceBudgets

140 pages; all207 original statement environments byte-identical to v18.
Expanded zero-extension local first/second derivative preservation,
measurable converse Fubini for original A0, exact raw V correspondence and
same-Q A/V/W coefficient budgets used by the common-subsequence application.
Three XeLaTeX passes and PDF conversion successful; page13 visually checked.
Zero overfull boxes, unresolved references or duplicate labels; existing
font fallback remains. New Lean correspondence modules are still candidates.
TeX SHA256 ef4c9fbf6341d1e4a96da15a209a4bfc3aa86cec4e15b48b4fa0ff1e6b964002
PDF SHA256 7b8f1a018779195975f01d7ac3fa42643952d5bea9aa9138895f4c8a9616d2ce
Private TeX/PDF excluded from public Git history.

## Private v20 canonical application sync (2026-10-01)

Private working expansion v20 CanonicalClosure has 140 pages. All207 original
statement environments are byte-identical to v19. Three XeLaTeX passes and
xdvipdfmx completed successfully; no overfull boxes, undefined references or
duplicate labels. Existing CJK bold font fallback remains. Page19 visually
inspected. Added canonical first/second slice derivatives, countable-cover
measurable representative, and finite-norm all-real-radius restriction.
Verification text distinguishes actual Run168 from pending Run169 and the
open original smooth-gauge applicability audit. No full7.1/7.2 certificate.

TeX SHA256:291542454f7cf96b5d521747141ce6f0fc7d899f380b96ca1a2d43de18188c40
PDF SHA256:e0d2236250735c87b4420dc387063064e6c0fb6d60ea265ea0b26dd83ebe5514
Both private artifacts saved successfully. Only correspondence/build metadata
is public; no private manuscript text or PDF is committed.

A later audit identifies joint space-time smoothness of A as an unproved
extra premise in the original-local-closure candidate. Do not treat it as
implied by the displayed Q bounds. The next proof uses f times a compact
test in the ORIGINAL distributional div A equation, deriving the advective
to divergence-form conversion with only local integrability of A.

## Private v21 weak-divergence sync (2026-10-01)

Private working expansion v21 WeakDivergence:140pages,207 original theorem
statements byte-identical to v20. Three XeLaTeX passes plus xdvipdfmx; no
overfull boxes, undefined references or duplicate labels. Page14 visually
inspected. Actual proof text now uses the genuine Q_j times compact test in
the original distributional div A=0 equation. This avoids imposing joint
space-time smoothness on the nonlocal connection. Source coefficients need
not be pointwise continuous representatives. Added equation label
v21:eq:weak-divergence-product. Both pointwise-original-PDE and original
advective-distributional-PDE routes are described separately and precisely.

Actual status synchronized to Run169:134/152 modules compiled,18failed;
Run170 candidates pending. Counts are not paper coverage. Full7.1/7.2 and
all later scattering branches remain OPEN pending whole-statement proof.
TeX SHA256:d5829e3b5897b69446bf78652389cebee05f41a593685e465cd68e1490428570
PDF SHA256:250f89e6563d075ec799f943cc91ecff789e6a4c4ec6c668bb7388deca92df7b
Private artifacts saved successfully; only metadata is committed publicly.

## 2026-10-01 v22 OriginalDistribution

Private v22:141 pages;207 original theorem/lemma/proposition/corollary
statement environments byte-identical to v21. Three XeLaTeX passes plus
xdvipdfmx succeeded; pages14/19 visually checked, no overfull boxes or
undefined references. Existing CJK bold-font substitution warning remains.
Original advective distributional test formula is explicit; weak-divergence
product identity is derived, and no extra joint connection smoothness or
A0 continuity is imposed. Certification boundary updated to actual
Run170142/160PASS18FAIL;Run171 pending. Full7.1/7.2 remainOPEN.
TeX SHA256:12b1a508480ead1891ef9ab78b8454d46b591a104a59e4468d4f7396678d2342
PDF SHA256:80d70b6fc76f6652373710f3a0965f7bee77299220b1bbcbf2dfc5ffaff6333a
Private files remain outside the public repository.

## 2026-10-01 v23 WeakTimeTests

Private141pages;207original statement environments unchanged fromv22.
Replaced unjustified pointwise differentiation of F=AQ in the time-test proof
by genuine eta(t)*psi(x) distribution tests, actual source integrability,
Fubini and the integrable-derivative FTC. No A0/V continuous representative
is required by this human proof. Lean tensor/Fubini/source applications remain
candidates, not whole-Theorem7.2 certification. Run171150/171PASS21FAIL;
Run172pending. ThreeXeLaTeX+xdvipdfmxsuccess,nooverfull/undefinedrefs/duplicates,
page17visuallychecked.
TeX SHA256:50bb18a43fb5a4536edebb6b05ae97f8b3ef6129cfa1de8abcd974c8415d9def
PDF SHA256:901d3eaf3377e958e2a74431e383f596335b5feb21ce2dceb735ae1123571d62
Private TeX/PDF excluded from public repository.
