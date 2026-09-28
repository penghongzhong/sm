# Whole-paper Lean coverage ledger

## Mathematical authority

`SM_Q_threshold_scattering_theorem_chain_repaired_cn` — 18 pages.

Main target:
[
E(z_0)<E_{car}=|Q|_2^2<4pi
quadLongrightarrowquad
	ext{global two-sided scattering}.
]

The 36-page Lean-min and 133-page W20 files are support sources only.

## Foundation boundary

The verification may use:

- Lean/Mathlib foundations and standard analysis;
- exact theorems already published in the literature.

It may **not** use an internal result of this manuscript as an axiom.

The short manuscript's compressed `Hgeo` module must therefore be expanded from the private proof source and verified as an internal dependency. The `Hstd` package must be split into exact source-audited published interfaces; any component not justified by a published theorem becomes an internal obligation.

## Closed-manuscript theorem chain

| ID | Manuscript label | Role | Lean status |
|---|---|---|---|
| C00 | `def:Hstd` | standard critical analytic package | SOURCE AUDIT REQUIRED |
| C01 | `hyp:Hgeo` | proved balanced geometry / finite-time rigidity / observer ledger | INTERNAL EXPANSION REQUIRED |
| C02 | `thm:carrier` | carrier scalarization + energy compression + subthreshold NLS scattering | pending |
| C03 | `thm:carrier-shadow` | full-time true-map shadowing of strict-subthreshold carrier | pending |
| C04 | `thm:wilson` | Wilson conjugation + energy barrier + threshold preservation | pending |
| C05 | `thm:superposition` | finite Wilson-renormalized nonlinear-profile superposition | pending |
| C06 | `thm:stability` | finite-control stability + energy-space closure | pending |
| C07 | `thm:covcoer` | actual covariance + carrier-center removal + NLS coercivity | pending |
| C08 | `thm:cluster` | finite-carrier cluster normal form + nonresonant quadratic structure | pending |
| C09 | `thm:packing` | packet covariance packing + IMS + LCA no-reuse | pending |
| C10 | `thm:rpsum` | rough phase-space packet summation | pending |
| C11 | `thm:profile-lift` | true nonlinear S²-valued lift of linear profiles | pending |
| C12 | `thm:gforest` | coarse-to-fine relative-frame forest | pending |
| C13 | `thm:PS` | enhanced balanced/carrier Palais-Smale reduction | pending |
| C14 | `thm:rigidity` | actual-covariance observer rigidity | pending |
| C15 | `thm:main` | main scattering theorem | pending |

## Dependency spine

[
egin{aligned}
&C00+C01\
&Downarrow\
&C02	o C03	o C04	o C05	o C06,\
&C07	o C08	o C09	o C10,\
&C11	o C12,\
&(C05,C06,C10,C11,C12)	o C13,\
&(C01,C07,C10)	o C14,\
&(C13,C14)	o C15.
end{aligned}
]

## Migration material

Earlier T001–T094 and N001–N033 files are **not authoritative numbering**. They are proof-mining/formalization material. Each may be reused only after an explicit mapping to one of C00–C15 or to a sublemma in the 18-page authority.

## Full verification completion criterion

Full-paper PASS requires:

1. C00 is reduced entirely to exact published/standard interfaces;
2. C01 is internally proved/formalized rather than assumed;
3. C02–C14 compile with exact manuscript statements;
4. C15 follows from C13+C14 with no hidden internal premise;
5. no `sorry`, `admit`, or custom internal `axiom`;
6. the Library TeX/PDF hashes match `status/MANUSCRIPT_SYNC.md`.
