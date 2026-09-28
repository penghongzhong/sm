# Whole-paper Lean coverage ledger

Goal: verify the full 133-page W20 scattering proof relative only to explicitly registered standard analysis results and published external theorems.

A row is **PASS** only when the Lean statement matches the synchronized W20 manuscript claim and compiles without `sorry`, `admit`, custom `axiom`, or a paper conclusion smuggled in as a hypothesis.

## Scope lock — user reconfirmed 2026-09-28

The verification target is the full W20 master, not the 36-page Lean-min edition. The T001–T094 identifiers are useful cross-references, not a certified exhaustive inventory of the long manuscript. They also include definitions; their count must not be reported as a count of fully proved theorems.

Before reporting whole-paper completion, extract the inventory from the full W20 source: all theorem/lemma/proposition/corollary statements, their definitions and actual proof dependencies, and any unlabelled analytic bridge used in those proofs. Map every retained claim to its exact Lean statement or precisely sourced allowed external input. Check quantities, hypotheses, quantifiers, constants and concrete PDE objects, not merely matching names.

A short-manuscript node that omits an internal proof does not remove that proof obligation from the full-master verification. Full coverage must be demonstrated by this mapping and the reverse dependency audit, not by reaching T094 alone.

The status entries below retain the pre-existing component ledger; this authority correction did not recompile Lean and does not promote any new node to PASS. Historical component PASS and current-public-commit PASS must be distinguished in subsequent build records.

| Layer | Manuscript nodes | Recorded component status |
|---|---|---|
| Section 2 coefficient algebra | `v12:lem:coeff` | T001 finite/registered analytic kernel PASS; full analytic layer pending |
| Section 2 stereographic curvature | chart curvature identity | jet algebra PASS; function/derivative bridge pending |
| Section 2 Hodge reconstruction | Hodge uniqueness + kernel | Fourier-symbol uniqueness PASS; distribution/function-space bridge pending |
| Section 2 electric curvature | `v12:lem:electric` | finite product-rule algebra PASS; analytic derivative bridge pending |
| Section 2 low-frequency budget | low-curvature Plancherel/multiplier/HLS step | finite constants + Plancherel interface PASS; exact multiplier/HLS connection pending |
| v13-v14 analysis | Smith whitelist, HHL, weak forcing, Volterra, stability | migration N001-N033 imported; theorem-by-theorem promotion pending |
| v15 profile front end | mixed reduction / screening / minimal profile | pending |
| v16-v20 realization and finite-S scattering | realization, rough flow, peeling, finite-S scattering | pending |
| W1-W5 terminal radiation/profile reduction | wave operator, coherent propagation, TVAN -> PS, finite rigidity | pending |
| W7-W10 NLS shadow / observer / rigidity / REL-REAL | carrier shadow, covariance, observer, global rigidity, screen deletion | pending |
| W11-W14 RFCE reduction | affine freeze, projected torsion, grouped/Jacobian reductions | pending |
| W19-W20 RFCE closure | T1, T2, principal forest repair | pending |
| Final main chain | RFCE -> REL-REAL -> TVAN -> Palais-Smale -> Rigidity -> Ec=Ecar -> two-sided scattering | pending |

## Current first cut-set

1. function-level stereographic derivative bridge;
2. Hodge reconstruction at the exact function/distribution level used by the paper;
3. covariant product-rule derivative bridge;
4. Plancherel + Fourier multiplier connection for the low-frequency estimates;
5. exact HLS instance connection to the paper norm objects.

Only after these are closed is Section 2 promoted from finite-kernel PASS to full analytic PASS.

## Completion evidence

Final certification requires exact full-master statement coverage, no unverified internal edge, a source-bounded external-input register, actual build evidence for the identified Lean commit, and a checked manuscript-to-Lean correspondence for the TeX/PDF digests in `status/MANUSCRIPT_SYNC.md`. File hashes establish version identity, not mathematical correctness by themselves.
